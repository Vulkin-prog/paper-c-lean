"""Mutation tests for the candidate preflight, with no Lean/network execution."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import yaml
import check_v3prel_candidates as guard


class CandidateGuardTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root/'Challenge.lean'
        self.good = 'import Mathlib.Data.Nat.Basic\nnamespace Candidate\ntheorem selected : True := by sorry\nend Candidate\n'

    def check(self, text=None, *, challenge=True):
        self.source.write_text(text if text is not None else self.good)
        return guard.source_contract(self.source,['Candidate.selected'],challenge)

    def reject(self, text, *, challenge=True):
        with self.assertRaises(guard.InvalidCandidate): self.check(text,challenge=challenge)

    def test_selected_placeholder_is_allowed_only_in_challenge(self):
        self.assertEqual(self.check()['intentional_placeholders'],1)
        self.reject(self.good,challenge=False)
        self.assertEqual(self.check(self.good.replace('sorry','trivial'),challenge=False)['intentional_placeholders'],0)

    def test_comments_strings_and_nested_comments_are_not_holes(self):
        text = self.good.replace('namespace Candidate','/- sorry /- axiom -/ sorry -/\n-- sorry\ndef message := "sorry axiom"\nnamespace Candidate')
        self.assertEqual(self.check(text)['intentional_placeholders'],1)

    def test_helper_placeholder_is_rejected(self):
        self.reject(self.good.replace('theorem selected','theorem hidden : True := by sorry\ntheorem selected'))
        self.reject(self.good.replace('theorem selected : True := by sorry','def hidden : Prop := by sorry\ntheorem selected : True := by trivial'))

    def test_omitted_or_duplicate_selected_theorem_is_rejected(self):
        self.reject(self.good.replace('selected','different'))
        self.reject(self.good.replace('end Candidate','theorem selected : True := by sorry\nend Candidate'))

    def test_local_import_and_challenge_import_in_solution_are_rejected(self):
        self.reject(self.good.replace('Mathlib.Data.Nat.Basic','PaperCV282.Main'))
        self.reject(self.good.replace('Mathlib.Data.Nat.Basic','ChallengeV3CriticalField').replace('sorry','trivial'),challenge=False)

    def test_hard_line_and_byte_caps_are_independent(self):
        self.reject(self.good + '\n'*1001)
        self.reject(self.good + '/-'+'x'*102400+'-/')

    def test_axiom_opaque_native_and_metaprogramming_escape_are_rejected(self):
        for extra in ['axiom hidden : False','opaque hidden : Prop := True','def h := by native_decide',
                      'elab "escape" : tactic => pure ()','#eval 1','unsafe def h := 1']:
            with self.subTest(extra=extra): self.reject(extra+'\n'+self.good)

    def test_unterminated_comments_and_strings_are_rejected(self):
        self.reject(self.good+'/- unfinished')
        self.reject(self.good+'def s := "unfinished')

    def test_json_and_yaml_duplicate_keys_are_rejected(self):
        p=self.root/'x.json';p.write_text('{"x":1,"x":2}')
        with self.assertRaises(guard.InvalidCandidate): guard.read_json(p)
        with self.assertRaises(guard.InvalidCandidate): yaml.load('x: 1\nx: 2\n',Loader=guard.UniqueYaml)
        with self.assertRaises(guard.InvalidCandidate): yaml.load('x: &x {a: 1}\ny: {<<: *x}\n',Loader=guard.UniqueYaml)

    def test_path_escape_is_rejected(self):
        for relative in ['../outside','/tmp/outside']:
            with self.assertRaises(guard.InvalidCandidate): guard.contained(self.root,relative)

    def test_toolchain_and_mathlib_pin_cannot_drift(self):
        (self.root/'lean-toolchain').write_text(guard.TOOLCHAIN+'\n')
        data={'packages':[{'name':'mathlib','type':'git','url':'https://github.com/leanprover-community/mathlib4.git','rev':guard.MATHLIB_COMMIT,'inputRev':'v4.32.0'}]}
        p=self.root/'lake-manifest.json';p.write_text(json.dumps(data));self.assertEqual(len(guard.pin_contract(self.root)),1)
        (self.root/'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
        with self.assertRaises(guard.InvalidCandidate): guard.pin_contract(self.root)
        (self.root/'lean-toolchain').write_text(guard.TOOLCHAIN+'\n');data['packages'][0]['rev']='0'*40;p.write_text(json.dumps(data))
        with self.assertRaises(guard.InvalidCandidate): guard.pin_contract(self.root)

    def test_metadata_selected_names_and_source_hashes_are_exact(self):
        config=guard.REGISTRY['critical_field']
        original=guard.ROOT/'palomar/v3prel/critical_field/formalization.yaml'
        metadata=yaml.safe_load(original.read_text());p=self.root/'formalization.yaml'
        p.write_text(yaml.safe_dump(metadata));guard.metadata_contract(p,config,'critical_field')
        altered=copy.deepcopy(metadata);altered['status']['main_results'].pop();p.write_text(yaml.safe_dump(altered))
        with self.assertRaises(guard.InvalidCandidate): guard.metadata_contract(p,config,'critical_field')
        p.write_text(yaml.safe_dump(metadata).replace(next(iter(guard.PDF_HASHES.values())),'0'*64))
        with self.assertRaises(guard.InvalidCandidate): guard.metadata_contract(p,config,'critical_field')

    def test_fixed_registry_rejects_changed_config(self):
        p=self.root/'comparator/v3prel_critical_field.json';p.parent.mkdir();d=copy.deepcopy(guard.REGISTRY['critical_field']);d['enable_nanoda']=False;p.write_text(json.dumps(d))
        with self.assertRaises(guard.InvalidCandidate): guard.check_family(self.root,'critical_field')

    def test_anonymous_section_does_not_consume_next_namespace(self):
        self.assertEqual(self.check('noncomputable section\n'+self.good)['intentional_placeholders'],1)
        found=guard.declarations(guard.lean_code('section\nnamespace Candidate\ntheorem selected : True := by sorry\nend Candidate\nend\n'))
        self.assertEqual([row[0] for row in found],['Candidate.selected'])

    def test_header_keeps_imports_after_module_doc_and_stops_at_body(self):
        source='module\n/-! module documentation -/\npublic import Mathlib.Foo\n/- nested /- x -/ -/\nimport all Lean.Elab\ndef x := 0\nimport Fake.Example\n'
        self.assertEqual(guard.header_imports(source),['Mathlib.Foo','Lean.Elab'])

    def test_import_all_is_not_a_module(self):
        self.assertEqual(guard.imports(guard.lean_code('public meta import all Lean.Elab\nimport Mathlib.Data.Nat.Basic -- comment\n')),['Lean.Elab','Mathlib.Data.Nat.Basic'])

    def test_transitive_project_import_is_rejected(self):
        package=self.root/'.lake/packages/mathlib';p=package/'Mathlib/Test.lean';p.parent.mkdir(parents=True);p.write_text('import PaperCV282.Hidden\n')
        packages=[{'name':'mathlib','rev':'1'*40}]
        def fake_git(path,*args):
            return {'rev-parse':'1'*40,'status':'','ls-files':'Mathlib/Test.lean\0'}[args[0]]
        with patch.object(guard,'git_output',side_effect=fake_git):
            with self.assertRaises(guard.InvalidCandidate): guard.import_closure(self.root,['Mathlib.Test'],packages)
        p.write_text('import Lean.Elab\n')
        with patch.object(guard,'git_output',side_effect=fake_git):
            self.assertEqual(guard.import_closure(self.root,['Mathlib.Test'],packages)['source_count'],1)
        shadow=self.root/'Mathlib/Test.lean';shadow.parent.mkdir();shadow.write_text('-- shadow')
        with patch.object(guard,'git_output',side_effect=fake_git):
            with self.assertRaises(guard.InvalidCandidate): guard.import_closure(self.root,['Mathlib.Test'],packages)


if __name__ == '__main__':
    unittest.main()
