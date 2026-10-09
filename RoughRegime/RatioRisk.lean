module

public import RoughRegime.ModelLipschitzCombination


@[expose] public section
/-! Actual projected-estimator risk bounds for the application ratios. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem ratio_lipschitz (a x b y M c : ℝ) (hc : 0 < c) (hb : c ≤ b) (hy : c ≤ y)
    (hx : |x| ≤ M) :
    |a / b - x / y| ≤ (1 / c + M / c ^ 2) * (|a - x| + |b - y|) := by
  have hb0 := hc.trans_le hb
  have hy0 := hc.trans_le hy
  have hM : 0 ≤ M := (abs_nonneg x).trans hx
  have hby : c ^ 2 ≤ b * y := by
    calc
      c ^ 2 = c*c := by ring
      _ ≤ b*y := mul_le_mul hb hy hc.le hb0.le
  have he : a / b - x / y = (a-x)/b + x*(y-b)/(b*y) := by
    field_simp [ne_of_gt hb0,ne_of_gt hy0]
    ring
  have h1 : |a-x|/b ≤ |a-x|/c :=
    div_le_div_of_nonneg_left (abs_nonneg _) hc hb
  have h2 : |x| *|y-b|/(b*y) ≤ M*|b-y|/c^2 := by
    calc
      _ ≤ (M*|y-b|)/(b*y) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hx (abs_nonneg _)) (mul_pos hb0 hy0).le
      _ ≤ (M*|y-b|)/c^2 := div_le_div_of_nonneg_left
        (mul_nonneg hM (abs_nonneg _)) (sq_pos_of_pos hc) hby
      _ = _ := by rw [abs_sub_comm y b]
  calc
    _ = |(a-x)/b + x*(y-b)/(b*y)| := congrArg abs he
    _ ≤ |(a-x)/b| + |x*(y-b)/(b*y)| := abs_add_le _ _
    _ = |a-x|/b + |x| *|y-b|/(b*y) := by
      rw [abs_div,abs_div,abs_mul,abs_mul,abs_of_pos hb0,abs_of_pos hy0]
    _ ≤ |a-x|/c + M*|b-y|/c^2 := add_le_add h1 h2
    _ ≤ _ := by
      have hp : 0 ≤ (1/c)*|b-y| := mul_nonneg (one_div_nonneg.mpr hc.le) (abs_nonneg _)
      have hq : 0 ≤ (M/c^2)*|a-x| := mul_nonneg (div_nonneg hM (sq_nonneg _)) (abs_nonneg _)
      simp only [div_eq_mul_inv,one_mul] at hp hq ⊢
      nlinarith only [hp,hq]

/-- Ratios use the same sample for the numerator and denominator estimators,
and the denominator is genuinely projected onto its known positive interval. -/
theorem ratio_minimax {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (N D : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (M c upper : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hcu : c ≤ upper)
    (hN : ∀ P ∈ C, N P ∈ Icc (-M) M)
    (hD : ∀ P ∈ C, D P ∈ Icc c upper) :
    minimaxRMSE n (fun P => N P / D P) C ≤ ENNReal.ofReal (1/c+M/c^2) *
      (minimaxRMSE n N C + minimaxRMSE n D C) := by
  let Ti : Fin 2 → ProbabilityMeasure Ω → ℝ := ![N,D]
  let lo : Fin 2 → ℝ := ![-M,c]
  let hi : Fin 2 → ℝ := ![M,upper]
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    fin_cases i
    · exact neg_le_self hM
    · exact hcu
  let Φ : ((i : Fin 2) → Icc (lo i) (hi i)) → ℝ := fun a => (a 0 : ℝ)/(a 1 : ℝ)
  have hL : 0 ≤ 1/c+M/c^2 := add_nonneg (one_div_nonneg.mpr hc.le) (div_nonneg hM (sq_nonneg _))
  have h := lipschitz_minimax_combination n (fun P => N P/D P) Ti C lo hi hlohi Φ
    (1/c+M/c^2) hL
    (by
      intro a b
      simp only [Fin.sum_univ_two]
      exact ratio_lipschitz (a 0) (b 0) (a 1) (b 1) M c hc (a 1).property.1
        (b 1).property.1 (abs_le.mpr (b 0).property))
    (by
      intro P hP i
      fin_cases i
      · exact hN P hP
      · exact hD P hP)
    (by
      intro P hP
      have hm : ∀ i, Ti i P ∈ Icc (lo i) (hi i) := by
        intro i
        fin_cases i
        · exact hN P hP
        · exact hD P hP
      have hp : ∀ i, (projIcc (lo i) (hi i) (hlohi i) (Ti i P) : ℝ) = Ti i P :=
        fun i => congrArg Subtype.val (projIcc_of_mem (hlohi i) (hm i))
      change N P / D P = (projIcc (lo 0) (hi 0) (hlohi 0) (Ti 0 P) : ℝ) /
        (projIcc (lo 1) (hi 1) (hlohi 1) (Ti 1 P) : ℝ)
      rw [hp 0,hp 1]
      rfl)
  simpa only [Ti,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

end RoughRegime.Model
