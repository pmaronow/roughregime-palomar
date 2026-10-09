module

public import RoughRegime.RatioRisk
public import RoughRegime.BracketCombination


@[expose] public section
/-! Fully proved upper-bracket composition for differences and positive ratios. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem same_upperBracket_difference {Ω : Type*} [MeasurableSpace Ω]
    (T U V : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (ν : ℝ) (hU : UpperBracket U C S ν) (hV : UpperBracket V C S ν)
    (hrelation : ∀ P ∈ C, T P = U P - V P) : UpperBracket T C S ν := by
  let Ti : Fin 2 → ProbabilityMeasure Ω → ℝ := ![U,V]
  apply finite_upperBracket_transfer T Ti C (fun _ => S) (fun _ => ν) S ν 1 hU.1 zero_lt_one
    (fun _ => rfl) (fun _ => rfl) (fun _ => le_rfl) (fun _ _ => le_rfl)
  · intro i
    fin_cases i
    · exact hU
    · exact hV
  · intro n
    simpa only [Ti,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      ENNReal.ofReal_one,one_mul] using difference_minimax n T U V C hrelation

theorem ratio_upperBracket_selected {Ω : Type*} [MeasurableSpace Ω]
    (N D : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (SN SD S : BracketParameters) (νN νD ν : ℝ)
    (hNup : UpperBracket N C SN νN) (hDup : UpperBracket D C SD νD) (hν : 2 ≤ ν)
    (hloN : SN.lo = S.lo) (hhiN : SN.hi = S.hi)
    (hloD : SD.lo = S.lo) (hhiD : SD.hi = S.hi)
    (hthetaN : S.theta ≤ SN.theta) (hthetaD : S.theta ≤ SD.theta)
    (hnuN : S.theta = SN.theta → νN ≤ ν) (hnuD : S.theta = SD.theta → νD ≤ ν)
    (M c upper : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hcu : c ≤ upper)
    (hN : ∀ P ∈ C, N P ∈ Icc (-M) M) (hD : ∀ P ∈ C, D P ∈ Icc c upper) :
    UpperBracket (fun P => N P / D P) C S ν := by
  let Ti : Fin 2 → ProbabilityMeasure Ω → ℝ := ![N,D]
  let Si : Fin 2 → BracketParameters := ![SN,SD]
  let νi : Fin 2 → ℝ := ![νN,νD]
  have hL : 0 < 1/c+M/c^2 := add_pos_of_pos_of_nonneg (one_div_pos.mpr hc) (div_nonneg hM (sq_nonneg _))
  apply finite_upperBracket_transfer _ Ti C Si νi S ν (1/c+M/c^2) hν hL
  · intro i
    fin_cases i
    · exact hloN
    · exact hloD
  · intro i
    fin_cases i
    · exact hhiN
    · exact hhiD
  · intro i
    fin_cases i
    · exact hthetaN
    · exact hthetaD
  · intro i
    fin_cases i
    · exact hnuN
    · exact hnuD
  · intro i
    fin_cases i
    · exact hNup
    · exact hDup
  · intro n
    simpa only [Ti,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      using ratio_minimax n N D C M c upper hM hc hcu hN hD

theorem ratio_upperBracket {Ω : Type*} [MeasurableSpace Ω]
    (N D : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (ν : ℝ) (hNup : UpperBracket N C S ν) (hDup : UpperBracket D C S ν)
    (M c upper : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hcu : c ≤ upper)
    (hN : ∀ P ∈ C, N P ∈ Icc (-M) M) (hD : ∀ P ∈ C, D P ∈ Icc c upper) :
    UpperBracket (fun P => N P/D P) C S ν :=
  ratio_upperBracket_selected N D C S S S ν ν ν hNup hDup hNup.1
    rfl rfl rfl rfl le_rfl le_rfl (fun _ => le_rfl) (fun _ => le_rfl)
    M c upper hM hc hcu hN hD

end RoughRegime.Model
