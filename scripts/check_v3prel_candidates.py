#!/usr/bin/env python3
"""Read-only V3PREL candidate preflight. This is not a kernel or editorial qualification.

The registry is deliberately closed. Default mode also resolves every Challenge
import through pinned local package sources. --metadata-only explicitly defers
that check; the dual-kernel job always repeats the complete check after setup.
No Lean, Lake, network, package installation, or project mutation is performed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import yaml
import check_v3prel_sources

ROOT = Path(__file__).resolve().parents[1]
SUBMISSION_COMMIT = "c605f23466450a52999fcfb3c6d68ed8febc56bf"
POLICY_COMMIT = "42cc43f70b1b019d20d4b64e9016396e666a6bc7"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
MATHLIB_TAG = "v4.33.1"
MATHLIB_COMMIT = "0df444a360eaa60ab8c11dca51a86af692955474"
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
PDF_HASHES = {
 "paper_C_version_3PREL_en.pdf": "0ec4144dc81c4ee9930a8e4e4815ae274da36e3c1ebeae4a5c0ffa411853a9d7",
 "paper_C_version_3PREL_technical_companion_en.pdf": "d64150c995f07ee39b016bb20a16b5fc3a01ce53b0ddcda893d1ceb41eefadee",
}
REGISTRY = {'critical_field': {'challenge_module': 'ChallengeV3CriticalField', 'solution_module': 'SolutionV3CriticalField', 'theorem_names': ['PaperCV3Audit.CriticalField.exact_source_coefficients', 'PaperCV3Audit.CriticalField.critical_lattice', 'PaperCV3Audit.CriticalField.critical_start_count', 'PaperCV3Audit.CriticalField.deterministic_statistic', 'PaperCV3Audit.CriticalField.hard_conditional', 'PaperCV3Audit.CriticalField.soft_conditional', 'PaperCV3Audit.CriticalField.spatial_hard_conditioning', 'PaperCV3Audit.CriticalField.spatial_soft_conditioning', 'PaperCV3Audit.CriticalField.uniform_quenched_scalar', 'PaperCV3Audit.CriticalField.critical_diffuse', 'PaperCV3Audit.CriticalField.stable_small_prime_record', 'PaperCV3Audit.CriticalField.masked_conditional_kernel', 'PaperCV3Audit.CriticalField.spatial_conditional_mean'], 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'], 'enable_nanoda': True}, 'patterns': {'challenge_module': 'ChallengeV3Patterns', 'solution_module': 'SolutionV3Patterns', 'theorem_names': ['PaperCV3Audit.Patterns.word_overlap_probability', 'PaperCV3Audit.Patterns.dictionary_critical', 'PaperCV3Audit.Patterns.exact_marked_quantitative', 'PaperCV3Audit.Patterns.exact_sign_partition', 'PaperCV3Audit.Patterns.aggregate_hard_budget', 'PaperCV3Audit.Patterns.geometric_joint_configuration', 'PaperCV3Audit.Patterns.geometric_compound_weight', 'PaperCV3Audit.Patterns.geometric_compound_pgf', 'PaperCV3Audit.Patterns.constant_windows_compound'], 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'], 'enable_nanoda': True}, 'limits': {'challenge_module': 'ChallengeV3Limits', 'solution_module': 'SolutionV3Limits', 'theorem_names': ['PaperCV3Audit.paper_c_v3_limits_joint_poisson_gaussian', 'PaperCV3Audit.paper_c_v3_limits_gaussian_covariance', 'PaperCV3Audit.paper_c_v3_limits_ar_covariance', 'PaperCV3Audit.paper_c_v3_limits_ar_recursion', 'PaperCV3Audit.paper_c_v3_limits_ar_independent_innovations', 'PaperCV3Audit.paper_c_v3_limits_ar_normal_innovations', 'PaperCV3Audit.paper_c_v3_limits_local_stirling_bounds', 'PaperCV3Audit.paper_c_v3_limits_local_stirling_relative_error', 'PaperCV3Audit.paper_c_v3_limits_poisson_local_limit', 'PaperCV3Audit.paper_c_v3_limits_poisson_moderate_bound', 'PaperCV3Audit.paper_c_v3_limits_poisson_moderate_limit', 'PaperCV3Audit.paper_c_v3_limits_poisson_gaussian_cdf_bound', 'PaperCV3Audit.paper_c_v3_limits_hard_central_local', 'PaperCV3Audit.paper_c_v3_limits_soft_central_local', 'PaperCV3Audit.paper_c_v3_limits_hard_moderate_tail', 'PaperCV3Audit.paper_c_v3_limits_integer_process_moving_laplace', 'PaperCV3Audit.paper_c_v3_limits_integer_process_phase_limit', 'PaperCV3Audit.paper_c_v3_limits_integer_process_target_laplace', 'PaperCV3Audit.paper_c_v3_limits_integer_process_locally_finite', 'PaperCV3Audit.paper_c_v3_limits_integer_process_infinite_mass', 'PaperCV3Audit.paper_c_v3_limits_integer_process_independent_counts', 'PaperCV3Audit.paper_c_v3_limits_integer_process_poisson_counts', 'PaperCV3Audit.paper_c_v3_limits_integer_process_finite_upper_tails', 'PaperCV3Audit.paper_c_v3_limits_integer_process_conditioned_positions', 'PaperCV3Audit.paper_c_v3_limits_extreme_phase_limit', 'PaperCV3Audit.paper_c_v3_limits_d4_full_half_count_law', 'PaperCV3Audit.paper_c_v3_limits_d4_entire_upper_point_law', 'PaperCV3Audit.paper_c_v3_limits_d4_conditional_upper_point_law', 'PaperCV3Audit.paper_c_v3_limits_d4_half_line_is_whole_restriction'], 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'], 'enable_nanoda': True}, 'boundary': {'challenge_module': 'ChallengeV3Boundary', 'solution_module': 'SolutionV3Boundary', 'theorem_names': ['PaperCV3Audit.v3_boundary_exact', 'PaperCV3Audit.v3_boundary_microscopic', 'PaperCV3Audit.v3_boundary_mesoscopic', 'PaperCV3Audit.v3_boundary_prefix_quantitative', 'PaperCV3Audit.v3_boundary_prefix_critical', 'PaperCV3Audit.v3_boundary_asymmetric_envelopes', 'PaperCV3Audit.v3_boundary_longest_loglog'], 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'], 'enable_nanoda': True}, 'crossover': {'challenge_module': 'ChallengeV3Crossover', 'solution_module': 'SolutionV3Crossover', 'theorem_names': ['PaperCV3Audit.v3_crossover_affine_border_mass', 'PaperCV3Audit.v3_crossover_complete_moving_mixture', 'PaperCV3Audit.v3_crossover_locations', 'PaperCV3Audit.v3_crossover_locations_atTop', 'PaperCV3Audit.v3_crossover_locations_atBot', 'PaperCV3Audit.v3_crossover_sign', 'PaperCV3Audit.v3_crossover_affine_complete_clock', 'PaperCV3Audit.v3_crossover_affine_locations', 'PaperCV3Audit.v3_crossover_affine_locations_atTop', 'PaperCV3Audit.v3_crossover_affine_locations_atBot', 'PaperCV3Audit.v3_crossover_affine_sign'], 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'], 'enable_nanoda': True}}

class InvalidCandidate(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise InvalidCandidate(message)


def unique_mapping(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate key: {key}")
        result[key] = value
    return result


class UniqueYaml(yaml.SafeLoader):
    pass


def yaml_mapping(loader, node, deep=False):
    require(all(k.tag != 'tag:yaml.org,2002:merge' for k, _ in node.value), 'YAML merge key')
    return unique_mapping([(loader.construct_object(k, deep=deep),
                            loader.construct_object(v, deep=deep)) for k, v in node.value])


UniqueYaml.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, yaml_mapping)


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique_mapping)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def contained(root, relative):
    require(isinstance(relative, str) and relative and not Path(relative).is_absolute(),
            f'invalid relative path: {relative!r}')
    path = root / relative
    require(path.resolve().is_relative_to(root.resolve()), f'path escapes root: {relative}')
    require(path.is_file() and not path.is_symlink(), f'missing/non-regular file: {relative}')
    return path


def lean_code(text):
    """Blank nested comments and strings, preserving offsets and line breaks.

    Conservative lexer for the fixed candidates, not a replacement Lean parser.
    Unterminated comments/strings are rejected, never silently skipped.
    """
    out, i, depth, string = list(text), 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\':
                out[i] = ' '; i += 1
                if i < len(text):
                    if text[i] != '\n': out[i] = ' '
                    i += 1
            else:
                if text[i] == '"': string = False
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out[i:end] = ' ' * (end-i); i = end
        elif text[i] == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    require(not depth and not string, 'unterminated Lean comment/string')
    return ''.join(out)


IMPORT = re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', re.M)
IDENT = r"[\w'.]+"
COMMAND = re.compile(r'^\s*(?:@\[[^\n]*?\]\s*)?(?:(?:noncomputable|private|protected|local|scoped)\s+)*(namespace|section|end|theorem|lemma|def|abbrev|instance|structure|inductive)\b(?:[ \t]+('+IDENT+r'))?', re.M)


def imports(code):
    result = []
    for match in IMPORT.finditer(code):
        modules = match.group(1).split()
        if modules and modules[0] == 'all': modules = modules[1:]
        require(all(re.fullmatch(r'[A-Za-z_][\w.]*(?:\.[A-Za-z_][\w]*)*', m) for m in modules),
                'unsupported import syntax')
        result.extend(modules)
    return result


def header_imports(text):
    """Read only the real import header, including module docs before imports.

    Stop at the first non-header command, so quoted examples in later proofs
    cannot add imports. Nested comments may span lines. This is a conservative
    source preflight; the official Lean header parser remains authoritative.
    """
    found, depth = [], 0
    for raw in text.splitlines():
        clean, i = [], 0
        while i < len(raw):
            if raw.startswith('/-',i): depth += 1; i += 2
            elif depth and raw.startswith('-/',i): depth -= 1; i += 2
            elif depth: i += 1
            elif raw.startswith('--',i): break
            else: clean.append(raw[i]); i += 1
        line=''.join(clean).strip()
        if not line or line in ('module','prelude'): continue
        if IMPORT.fullmatch(line): found.extend(imports(line))
        else: return found
    require(not depth, 'unterminated comment in import header')
    return found


def declarations(code):
    matches = list(COMMAND.finditer(code))
    stack, result = [], []
    for i, match in enumerate(matches):
        kind, name = match.group(1, 2)
        if kind in ('namespace', 'section'):
            stack.append((kind, name if kind == 'namespace' else None)); continue
        if kind == 'end':
            if stack: stack.pop()
            continue
        if name is None:
            continue
        namespace = '.'.join(n for k, n in stack if k == 'namespace' and n)
        full = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(x for x in [namespace,name] if x)
        end = matches[i+1].start() if i+1 < len(matches) else len(code)
        result.append((full, kind, code[match.end():end], match.start()))
    return result


def source_contract(path, expected, challenge):
    text = path.read_text(encoding='utf-8')
    code = lean_code(text)
    if challenge:
        require(len(text.splitlines()) <= 1000, f'{path.name}: Challenge exceeds 1000 lines')
        require(len(text.encode('utf-8')) <= 100*1024, f'{path.name}: Challenge exceeds 100 KiB')
    forbidden = r'\b(?:axiom|opaque|unsafe|admit|sorryAx|native_decide|ofReduceBool|run_tac|elab|macro|syntax|initialize)\b'
    require(not re.search(forbidden, code), f'{path.name}: forbidden declaration/escape')
    require(not re.search(r'^\s*#', code, re.M), f'{path.name}: unexpected command')
    decls = declarations(code)
    for name in expected:
        found = [d for d in decls if d[0] == name]
        require(len(found) == 1 and found[0][1] in ('theorem','lemma'),
                f'{path.name}: missing/duplicate selected theorem {name}')
    holes = [m.start() for m in re.finditer(r'\bsorry\b', code)]
    if challenge:
        owners = [name for name, kind, body, _ in decls if re.search(r'\bsorry\b', body)]
        require(owners == expected and len(holes) == len(expected),
                f'{path.name}: placeholders must be exactly the selected theorems, one per theorem')
    else:
        require(not holes, f'{path.name}: solution has proof holes')
    direct = imports(code)
    require(direct, f'{path.name}: missing imports')
    if challenge:
        require(all(m.startswith('Mathlib.') or m == 'Mathlib' for m in direct),
                f'{path.name}: Challenge directly imports outside Mathlib')
    else:
        require(not any(m.startswith('Challenge') for m in direct),
                f'{path.name}: Solution imports Challenge')
    return {'path':path.name,'sha256':sha256(path),'bytes':len(text.encode('utf-8')),
            'lines':len(text.splitlines()),'direct_imports':direct,'selected_names':expected,
            'intentional_placeholders':len(holes)}


def pin_contract(root):
    require(contained(root,'lean-toolchain').read_text().strip() == TOOLCHAIN, 'Lean toolchain changed')
    manifest = read_json(contained(root,'lake-manifest.json'))
    packages = manifest['packages']
    mathlib = [p for p in packages if p['name'] == 'mathlib']
    require(len(mathlib) == 1, 'mathlib package missing/duplicated')
    m = mathlib[0]
    require(m.get('url') == 'https://github.com/leanprover-community/mathlib4.git'
            and m.get('rev') == MATHLIB_COMMIT and m.get('inputRev') == MATHLIB_TAG
            and m.get('type') == 'git', 'mathlib pin/provenance changed')
    require(all(p.get('type') == 'git' and re.fullmatch('[0-9a-f]{40}',p.get('rev','')) for p in packages),
            'unpinned or non-git package')
    return packages


def source_snapshot(root):
    check_v3prel_sources.check(root)
    base = root/'manuscripts/v3prel'
    manifest = read_json(contained(base,'manifest.json'))
    require(manifest.get('version') == '3PREL', 'wrong manuscript version')
    seen, rows = set(), []
    for entry in manifest['files']:
        name = entry['path']; require(name not in seen, f'duplicate source file: {name}'); seen.add(name)
        path = contained(base,name)
        require(sha256(path) == entry['sha256'] and path.stat().st_size == entry['size_bytes'],
                f'manuscript snapshot mismatch: {name}')
        rows.append({'path':'manuscripts/v3prel/'+name,'sha256':entry['sha256']})
    for name, expected in PDF_HASHES.items():
        require(name in seen and sha256(contained(base,name)) == expected, f'wrong source PDF: {name}')
    return {'manifest_sha256':sha256(base/'manifest.json'),'files':rows}


def git_output(path, *args):
    proc = subprocess.run(['git','-C',str(path),*args], text=True,capture_output=True,check=False)
    require(proc.returncode == 0, f'cannot inspect pinned package {path.name}')
    return proc.stdout.strip()


def import_closure(root, direct, packages):
    """DFS through pinned source packages; core leaves are fixed by the toolchain.

    Every non-core module must resolve uniquely inside a manifest package, with
    no project shadow. Git HEAD and all tracked source bytes are checked first.
    This supplements the canonical Challenge compilation of the registry.
    """
    roots = []
    tracked_files = {}
    for package in packages:
        path = root/'.lake/packages'/package['name']
        require(path.is_dir(), f'package sources unavailable: {package["name"]}; run full check after setup')
        require(git_output(path,'rev-parse','HEAD') == package['rev'], f'package HEAD mismatch: {package["name"]}')
        require(not git_output(path,'status','--porcelain','--untracked-files=no'), f'modified tracked package: {package["name"]}')
        roots.append(path)
        tracked_files[path] = set(git_output(path,'ls-files','-z').split('\0'))
    visited, core, rows = set(), set(), []
    def visit(module):
        if module in visited: return
        visited.add(module)
        relative = module.replace('.','/')+'.lean'
        require(not (root/relative).exists(), f'project shadows trusted import: {module}')
        if module.split('.')[0] in ('Init','Lean','Std','Lake'):
            core.add(module); return
        matches = [r/relative for r in roots if (r/relative).is_file()]
        require(len(matches) == 1, f'trusted import does not resolve uniquely: {module}')
        path = matches[0]
        package_root = next(r for r in roots if path.is_relative_to(r))
        require(path.resolve().is_relative_to(package_root.resolve()) and not path.is_symlink(),
                f'import escapes trusted package: {module}')
        require(str(path.relative_to(package_root)) in tracked_files[package_root], f'untracked trusted import: {module}')
        rows.append({'module':module,'path':str(path.relative_to(root)),'sha256':sha256(path)})
        for child in header_imports(path.read_text(encoding='utf-8')): visit(child)
    for module in direct: visit(module)
    return {'algorithm':'source DFS, pinned git HEAD and clean tracked package sources; unique resolution; no project shadow; core leaves fixed by lean-toolchain',
            'source_count':len(rows),'core_leaves':sorted(core),'sources':sorted(rows,key=lambda r:r['module'])}


def metadata_contract(path, config, family):
    metadata = yaml.load(path.read_text(encoding='utf-8'),Loader=UniqueYaml)
    require(metadata.get('version') == 'v0.4', f'{family}: metadata version')
    project = metadata.get('project',{})
    for key in ['name','description','authors','responsible_maintainers','license']:
        require(project.get(key), f'{family}: missing project.{key}')
    require('Brice Pouly' in project['responsible_maintainers'], f'{family}: human maintainer missing')
    require(project['license'] == 'Apache-2.0', f'{family}: project license')
    require(metadata.get('classification',{}).get('arxiv'), f'{family}: classification missing')
    require(metadata.get('review',{}).get('status'), f'{family}: review status missing')
    require(metadata.get('automation',{}).get('methods'), f'{family}: automation disclosure missing')
    require(metadata.get('fidelity',{}).get('divergences'), f'{family}: fidelity disclosure missing')
    sources = metadata.get('sources',[])
    require(sources and any(s.get('relationship') in ('adapts','formalizes','independently-proves') for s in sources), f'{family}: no substantive source')
    prose = json.dumps(sources,ensure_ascii=False)
    for name, digest in PDF_HASHES.items():
        require(name in prose and digest in prose, f'{family}: source PDF provenance missing: {name}')
    status = metadata.get('status',{})
    require(status.get('sorry_count') == 0 and status.get('sorry_in_definitions') == 0, f'{family}: solution hole disclosure')
    require(status.get('axioms') == AXIOMS, f'{family}: axioms disclosure')
    results = status.get('main_results',[])
    require([r.get('declaration') for r in results] == config['theorem_names'], f'{family}: metadata selected names differ')
    for result in results:
        require(result.get('file') == config['solution_module']+'.lean'
                and result.get('comparator_config') == f'comparator/v3prel_{family}.json'
                and result.get('sorry_count') == 0 and result.get('axioms') == AXIOMS,
                f'{family}: selected result metadata mismatch')
    return metadata


def check_submission_checkout(contract_root):
    require(git_output(contract_root,'rev-parse','HEAD') == SUBMISSION_COMMIT,
            'submission contract HEAD mismatch')
    require(not git_output(contract_root,'status','--porcelain','--untracked-files=no'),
            'submission contract tracked files modified in worktree or index')


def check_family(root, family, *, contract_root=None):
    expected = REGISTRY[family]
    config_path = contained(root,f'comparator/v3prel_{family}.json')
    config = read_json(config_path)
    require(config == expected, f'{family}: config differs from fixed selected registry')
    metadata_path = contained(root,f'palomar/v3prel/{family}/formalization.yaml')
    metadata = metadata_contract(metadata_path,config,family)
    if contract_root:
        check_submission_checkout(contract_root)
        sys.path.insert(0,str(contract_root.resolve()))
        from scripts.submission_contract import load_formalization_metadata, normalized_provenance
        from scripts.verify_submission import load_comparator_config
        official = load_formalization_metadata(metadata_path)
        provenance = normalized_provenance(official)
        require(provenance['repository_role'] == 'substantive-development'
                and provenance['result_origin'] == 'source-based', f'{family}: official provenance mismatch')
        require(load_comparator_config(config_path) == config, f'{family}: official config mismatch')
    challenge = source_contract(contained(root,config['challenge_module']+'.lean'),config['theorem_names'],True)
    solution = source_contract(contained(root,config['solution_module']+'.lean'),config['theorem_names'],False)
    return {'family':family,'challenge':challenge,'solution':solution,
            'config':{'path':str(config_path.relative_to(root)),'sha256':sha256(config_path)},
            'metadata':{'path':str(metadata_path.relative_to(root)),'sha256':sha256(metadata_path)},
            'preferred_surface_warning':challenge['lines']>300 or challenge['bytes']>32*1024}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=ROOT)
    selector=parser.add_mutually_exclusive_group()
    selector.add_argument('--family',choices=list(REGISTRY))
    selector.add_argument('--config',choices=[f'comparator/v3prel_{f}.json' for f in REGISTRY])
    parser.add_argument('--metadata-only',action='store_true',help='defer package-source import closure until the dual-kernel job')
    parser.add_argument('--contract-root',type=Path,help='also use the exact pinned official metadata/config loader')
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    root=args.root.resolve()
    try:
        packages=pin_contract(root)
        snapshot=source_snapshot(root)
        family=args.family or (Path(args.config).stem.removeprefix('v3prel_') if args.config else None)
        families=[family] if family else list(REGISTRY)
        rows=[check_family(root,f,contract_root=args.contract_root) for f in families]
        direct=sorted(set(m for row in rows for m in row['challenge']['direct_imports']))
        closure=None if args.metadata_only else import_closure(root,direct,packages)
        receipt={'status':'static_preflight_passed','kernel_qualification':False,'editorial_qualification':False,
                 'metadata_only':args.metadata_only,'official_contract_checked':bool(args.contract_root),
                 'submission_contract':SUBMISSION_COMMIT,'policy_snapshot':POLICY_COMMIT,
                 'toolchain':TOOLCHAIN,'mathlib_commit':MATHLIB_COMMIT,'source_snapshot':snapshot,
                 'families':rows,'challenge_import_closure':closure}
        if args.receipt:
            args.receipt.parent.mkdir(parents=True,exist_ok=True)
            args.receipt.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({'status':receipt['status'],'families':families,
                          'selected_theorems':sum(len(r['challenge']['selected_names']) for r in rows),
                          'closure_sources':None if closure is None else closure['source_count'],
                          'kernel_qualification':False},sort_keys=True))
        return 0
    except (InvalidCandidate,KeyError,ValueError,OSError,yaml.YAMLError) as error:
        print(f'V3PREL_PREFLIGHT_FAILED: {error}',file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
