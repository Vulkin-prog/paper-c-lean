import PaperCPrel8.PairRankExampleLaw
import PaperC.Asymptotics.PrefixBoundaryProbability

/-! # Identification of the example matrix with the original multiplicative sample -/
namespace PaperC.Prel8.PairRankExampleSource
open PairRankExample PrefixBoundaryProbability
noncomputable section
def p2 : PrimeUpTo 117 := ⟨⟨2,by norm_num⟩,by norm_num⟩
def p3 : PrimeUpTo 117 := ⟨⟨3,by norm_num⟩,by norm_num⟩
def p5 : PrimeUpTo 117 := ⟨⟨5,by norm_num⟩,by norm_num⟩
def p7 : PrimeUpTo 117 := ⟨⟨7,by norm_num⟩,by norm_num⟩
def p13 : PrimeUpTo 117 := ⟨⟨13,by norm_num⟩,by norm_num⟩
def p19 : PrimeUpTo 117 := ⟨⟨19,by norm_num⟩,by norm_num⟩
def p23 : PrimeUpTo 117 := ⟨⟨23,by norm_num⟩,by norm_num⟩
def p29 : PrimeUpTo 117 := ⟨⟨29,by norm_num⟩,by norm_num⟩
def p31 : PrimeUpTo 117 := ⟨⟨31,by norm_num⟩,by norm_num⟩
def p47 : PrimeUpTo 117 := ⟨⟨47,by norm_num⟩,by norm_num⟩
def p113 : PrimeUpTo 117 := ⟨⟨113,by norm_num⟩,by norm_num⟩

def smallSample (w : SampleSpace 117) : SmallBits := ![w p2,w p3,w p5,w p7]
def largeSample (w : SampleSpace 117) : Large := ![w p13,w p19,w p23,w p29,w p31,w p47,w p113]

/-- Original arithmetic raw values, with all inactive prime coordinates still present. -/
theorem actual_values (w : SampleSpace 117) :
    (fun i : Fin 10 ↦ valueBit w (vertices i))=full (smallSample w,largeSample w) := by
  have htwo : (2:F₂)=0 := by decide
  have h2 : valueBit w 2=w p2 := valueBit_primeUpTo w p2
  have h3 : valueBit w 3=w p3 := valueBit_primeUpTo w p3
  have h5 : valueBit w 5=w p5 := valueBit_primeUpTo w p5
  have h7 : valueBit w 7=w p7 := valueBit_primeUpTo w p7
  have h13 : valueBit w 13=w p13 := valueBit_primeUpTo w p13
  have h19 : valueBit w 19=w p19 := valueBit_primeUpTo w p19
  have h23 : valueBit w 23=w p23 := valueBit_primeUpTo w p23
  have h29 : valueBit w 29=w p29 := valueBit_primeUpTo w p29
  have h31 : valueBit w 31=w p31 := valueBit_primeUpTo w p31
  have h47 : valueBit w 47=w p47 := valueBit_primeUpTo w p47
  have h113 : valueBit w 113=w p113 := valueBit_primeUpTo w p113
  funext i
  fin_cases i
  · change valueBit w 91 = _
    rw [show 91=7*13 by norm_num]
    rw [valueBit_mul w (a:=7) (b:=13) (by norm_num) (by norm_num)]
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
  · change valueBit w 92 = _
    rw [show 92=2*2*23 by norm_num]
    rw [valueBit_mul w (a:=2*2) (b:=23) (by norm_num) (by norm_num), valueBit_mul w (a:=2) (b:=2) (by norm_num) (by norm_num)]
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
  · change valueBit w 93 = _
    rw [show 93=3*31 by norm_num]
    rw [valueBit_mul w (a:=3) (b:=31) (by norm_num) (by norm_num)]
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
  · change valueBit w 94 = _
    rw [show 94=2*47 by norm_num]
    rw [valueBit_mul w (a:=2) (b:=47) (by norm_num) (by norm_num)]
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
  · change valueBit w 95 = _
    rw [show 95=5*19 by norm_num]
    rw [valueBit_mul w (a:=5) (b:=19) (by norm_num) (by norm_num)]
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
  · change valueBit w 113 = _
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
  · change valueBit w 114 = _
    rw [show 114=2*3*19 by norm_num]
    rw [valueBit_mul w (a:=2*3) (b:=19) (by norm_num) (by norm_num), valueBit_mul w (a:=2) (b:=3) (by norm_num) (by norm_num)]
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
  · change valueBit w 115 = _
    rw [show 115=5*23 by norm_num]
    rw [valueBit_mul w (a:=5) (b:=23) (by norm_num) (by norm_num)]
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
  · change valueBit w 116 = _
    rw [show 116=2*2*29 by norm_num]
    rw [valueBit_mul w (a:=2*2) (b:=29) (by norm_num) (by norm_num), valueBit_mul w (a:=2) (b:=2) (by norm_num) (by norm_num)]
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
  · change valueBit w 117 = _
    change valueBit w (3*3*13) = _
    rw [valueBit_mul w (a:=3*3) (b:=13) (by norm_num) (by norm_num), valueBit_mul w (a:=3) (b:=3) (by norm_num) (by norm_num)]
    simp [h2,h3,h5,h7,h13,h19,h23,h29,h31,h47,h113,full,TwoRankPair.combined,small,sp,rough,smallSample,largeSample]
    <;> ring_nf <;> simp [htwo]
end
end PaperC.Prel8.PairRankExampleSource
