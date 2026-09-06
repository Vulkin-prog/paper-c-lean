import PaperCV282.MaskedPairBounds

/-! # The exact-mark arithmetic ledger with distinct base and maximal lengths -/
namespace PaperC.V282.ExactMarkedLedger

open MaskedArithmeticGeometry MaskedPairGeometry SectionTwelveMoments TwoWindowParity

noncomputable section

/-- Defect and relation masses use L; deletion and dependency supports use L+E+1. -/
def exactMarkedLedger (N L E Y : ℕ) (mask : Finset ℕ) : ℝ :=
  (1/(2 : ℝ)^L) * ((fullDefectMass L mask : ℝ) + 2*(fullBadMask N (L+E+1) Y mask).card) +
  (1/(2 : ℝ)^L)^2 * (20*(N : ℝ)*(L+E+2) + 4*(maskedSupportEdges (L+E+1) Y mask).card +
    2*(jointDefectMass N L (separatedPairs mask L) : ℝ))

theorem exactMarkedLedger_nonneg (N L E Y : ℕ) (mask : Finset ℕ) :
    0 ≤ exactMarkedLedger N L E Y mask := by unfold exactMarkedLedger; positivity

end
end PaperC.V282.ExactMarkedLedger
