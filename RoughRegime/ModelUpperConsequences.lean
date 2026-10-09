module

public import RoughRegime.ModelUpper
public import RoughRegime.ModelPredicates


@[expose] public section
/-! The proved main upper theorem in the paper's bracket convention, including
empty classes and restriction to genuine application subclasses. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RoughRegime.Model
universe u

def Parameters.bracketParameters (A : Parameters) : BracketParameters where
  theta := A.theta
  lo := A.gminus
  hi := A.gplus
  htheta := A.theta_pos
  hlo := A.hgminus
  hinterval := A.hgplus

theorem perModelUpperClaim (A : Parameters) {Z : Type u} [MeasurableSpace Z]
    (F : Observables Z A) : PerModelUpperClaim A F := by
  obtain ⟨MW, _, hMW⟩ := F.boundW
  obtain ⟨C,hC,n0,hn0,hupper⟩ := uniformUpperClaim.{u} A |F.lam| MW
  exact ⟨C,hC,n0,hn0,hupper Z inferInstance F rfl hMW⟩

@[simp] theorem minimaxRMSE_empty {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ProbabilityMeasure Ω → ℝ) :
    minimaxRMSE n T ∅ = 0 := by
  simp [minimaxRMSE]

theorem model_upperBracket (A : Parameters) {Z : Type u} [MeasurableSpace Z]
    (F : Observables Z A) :
    UpperBracket (target A F) (modelClass A F) A.bracketParameters (A.nu : ℝ) := by
  obtain ⟨C,hC,n0,hn0,hupper⟩ := perModelUpperClaim A F
  refine ⟨by exact_mod_cast A.nu_ge_two,C,hC,n0,hn0,?_⟩
  intro n hn
  change minimaxRMSE n (target A F) (modelClass A F) ≤ ENNReal.ofReal
    (C * (if A.theta < 1/2 then
      RoughRegime.Rates.subcriticalScale n A.theta (RoughRegime.Rates.tau A.gminus A.gplus) *
        (Real.log n) ^ ((A.nu : ℝ)/2+1/4)
      else (n : ℝ)^(-(1/2:ℝ))))
  by_cases hne : (modelClass A F).Nonempty
  · obtain ⟨hp,hs⟩ := hupper n hn hne
    by_cases hθ : A.theta < 1 / 2
    · rw [ite_eq_left hθ]
      simpa only [mul_assoc] using hs ⟨A.theta_pos,hθ⟩
    · rw [ite_eq_right hθ]
      exact hp (le_of_not_gt hθ)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,minimaxRMSE_empty]
    exact bot_le

theorem upperBracket_mono_class {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω → ℝ) {C D : Set (ProbabilityMeasure Ω)}
    (S : BracketParameters) (ν : ℝ) (hCD : C ⊆ D)
    (hD : UpperBracket T D S ν) : UpperBracket T C S ν := by
  obtain ⟨hν,c,hc,n0,hn0,hrisk⟩ := hD
  exact ⟨hν,c,hc,n0,hn0,fun n hn =>
    (minimaxRMSE_mono_class n T hCD).trans (hrisk n hn)⟩

theorem minimaxRMSE_congr_target {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T U : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (hTU : ∀ P ∈ C, T P = U P) : minimaxRMSE n T C = minimaxRMSE n U C := by
  unfold minimaxRMSE
  apply iInf_congr
  intro E
  apply iSup_congr
  intro P
  apply iSup_congr
  intro hP
  rw [hTU P hP]

theorem upperBracket_congr_target {Ω : Type*} [MeasurableSpace Ω]
    (T U : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (ν : ℝ) (hTU : ∀ P ∈ C, T P = U P)
    (hU : UpperBracket U C S ν) : UpperBracket T C S ν := by
  obtain ⟨hν,c,hc,n0,hn0,hrisk⟩ := hU
  refine ⟨hν,c,hc,n0,hn0,fun n hn => ?_⟩
  rw [minimaxRMSE_congr_target n T U C hTU]
  exact hrisk n hn

end RoughRegime.Model
