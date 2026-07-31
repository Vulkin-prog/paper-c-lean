import PaperC.Arithmetic.PrimeCountBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Prime-number-theorem input

This file contains the single source-level external input used by the
low-zone argument in Paper C, Lemma 15.1.  The uniform specialization needed
there is deliberately not part of this statement: it is derived in
`PaperC.Asymptotics.LowZoneCritical`.
-/

namespace PaperC
namespace PrimeNumberTheoremInput

open Filter

noncomputable section

/--
**External bridge (published prime-number theorem).**

The standard sequential form `π(L) log L / L → 1`.
-/
/- AUDIT_BRIDGE
{
  "id": "ADGR07-PNT",
  "kind": "external",
  "status": "open",
  "lean_name": "PaperC.PrimeNumberTheoremInput.PrimeNumberTheoremStatement",
  "citation": {
    "authors": ["Jeremy Avigad", "Kevin Donnelly", "David Gray", "Paul Raff"],
    "title": "A formally verified proof of the prime number theorem",
    "journal": "ACM Transactions on Computational Logic 9 (2007), no. 1, Article 2, 1–23",
    "doi": "10.1145/1297658.1297660",
    "locator": "Abstract, p. 1"
  },
  "source_statement": {
    "verbatim": "the density of primes in the positive integers is asymptotic to 1/ln x.",
    "source_url": "https://doi.org/10.1145/1297658.1297660",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Lemma 15.1",
    "equation": "r(x) = π(L) - π(sqrt(x+L)) = (1-o(1))π(L)",
    "pages": "49"
  },
  "formalization_relation": "exact sequential real-valued form of the cited prime number theorem: (π(L) * log L) / L tends to 1. The uniform low-zone estimate and its exponential-decay consequence are proved in Lean from this statement."
}
AUDIT_BRIDGE -/
def PrimeNumberTheoremStatement : Prop :=
  Tendsto
    (fun L : ℕ ↦
      (PrimesUpTo.count L : ℝ) * Real.log (L : ℝ) / (L : ℝ))
    atTop (nhds 1)

end

end PrimeNumberTheoremInput
end PaperC
