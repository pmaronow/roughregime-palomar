module

public import RoughRegime.SourceBands
public import RoughRegime.LatticeCutoffs


@[expose] public section
/-! The literal fixed source choices of analytic order, smoothing exponent,
collar width and gate scale, with every numeric budget derived. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory
open RoughRegime.LatticeFourier

 def sourceAlpha0 (α β : ℝ) : ℝ := min (min α β) 1 / 2
 def sourceGateOrder (α β : ℝ) : ℕ := Nat.ceil (max α β) + 2
 /-- The derivative budget is `k_max+1=Q-1`, as in the source composition proof. -/
 def sourceJetBudget (α β : ℝ) : ℕ := sourceGateOrder α β - 1

 theorem sourceAlpha0_pos (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : 0 < sourceAlpha0 α β := by
  unfold sourceAlpha0
  exact div_pos (lt_min (lt_min hα hβ) zero_lt_one) (by norm_num)
 theorem sourceAlpha0_lt_one (α β : ℝ) : sourceAlpha0 α β < 1 := by
  unfold sourceAlpha0
  linarith [min_le_right (min α β) (1 : ℝ)]
 theorem sourceAlpha0_lt_alpha (α β : ℝ) (hα : 0 < α) : sourceAlpha0 α β < α := by
  unfold sourceAlpha0
  linarith [(min_le_left (min α β) (1 : ℝ)).trans (min_le_left α β)]
 theorem sourceAlpha0_lt_beta (α β : ℝ) (hβ : 0 < β) : sourceAlpha0 α β < β := by
  unfold sourceAlpha0
  linarith [(min_le_left (min α β) (1 : ℝ)).trans (min_le_right α β)]

 theorem sourceGateOrder_ge_three (α β : ℝ) (hα : 0 < α) : 3 ≤ sourceGateOrder α β := by
  have hc : 1 ≤ Nat.ceil (max α β) := Nat.one_le_ceil_iff.mpr (hα.trans_le (le_max_left _ _))
  unfold sourceGateOrder
  omega
 theorem sourceJetBudget_pos (α β : ℝ) : 0 < sourceJetBudget α β := by
  unfold sourceJetBudget sourceGateOrder
  omega
 theorem sourceJetBudget_le_twice_order (α β : ℝ) : sourceJetBudget α β ≤ 2 * sourceGateOrder α β := by
  unfold sourceJetBudget
  omega
 theorem sourceJetBudget_eq (α β : ℝ) : sourceJetBudget α β = Nat.ceil (max α β) + 1 := by
  unfold sourceJetBudget sourceGateOrder
  omega
 theorem source_alpha_derivative_budget (α β : ℝ) (hα : 0 < α) :
    Model.holderOrder α + 2 ≤ sourceJetBudget α β := by
  have ha := Nat.one_le_ceil_iff.mpr hα
  have hc := Nat.ceil_mono (le_max_left α β)
  rw [sourceJetBudget_eq]
  unfold Model.holderOrder
  omega
 theorem source_beta_derivative_budget (α β : ℝ) (hβ : 0 < β) :
    Model.holderOrder β + 2 ≤ sourceJetBudget α β := by
  have hb := Nat.one_le_ceil_iff.mpr hβ
  have hc := Nat.ceil_mono (le_max_right α β)
  rw [sourceJetBudget_eq]
  unfold Model.holderOrder
  omega

 theorem source_analytic_parameter_budget (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 < sourceAlpha0 α β ∧ sourceAlpha0 α β < 1 ∧ sourceAlpha0 α β < α ∧ sourceAlpha0 α β < β ∧
    3 ≤ sourceGateOrder α β ∧ 0 < sourceJetBudget α β ∧ sourceJetBudget α β ≤ 2 * sourceGateOrder α β ∧
    Model.holderOrder α + 2 ≤ sourceJetBudget α β ∧ Model.holderOrder β + 2 ≤ sourceJetBudget α β :=
  ⟨sourceAlpha0_pos α β hα hβ, sourceAlpha0_lt_one α β, sourceAlpha0_lt_alpha α β hα,
    sourceAlpha0_lt_beta α β hβ, sourceGateOrder_ge_three α β hα, sourceJetBudget_pos α β,
    sourceJetBudget_le_twice_order α β, source_alpha_derivative_budget α β hα,
    source_beta_derivative_budget α β hβ⟩

 def sourceInnerSquareIntegral (d : ℕ) : ℝ := ∫ x, (innerBump d x) ^ 2 ∂Model.cubeVolume d
 def sourceGammaStar (d : ℕ) : ℝ := min (1 / 4) (sourceInnerSquareIntegral d / (16 * d))
 def sourceLambdaStar (d : ℕ) (α β : ℝ) : ℝ :=
  max 1 (Real.sqrt (8 * sourceGateOrder α β * d * sincSecondMoment (sourceGateOrder α β) / 3))

 theorem sourceGammaStar_bounds (d : ℕ) (hd : 0 < d) :
    0 < sourceGammaStar d ∧ sourceGammaStar d ≤ 1 / 4 ∧
      sourceGammaStar d ≤ sourceInnerSquareIntegral d / (16 * d) := by
  have hI : 0 < sourceInnerSquareIntegral d := innerBump_square_integral_pos d
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  exact ⟨lt_min (by norm_num) (div_pos hI (mul_pos (by norm_num) hdr)), min_le_left _ _, min_le_right _ _⟩
 theorem sourceLambdaStar_ge_one (d : ℕ) (α β : ℝ) : 1 ≤ sourceLambdaStar d α β := le_max_left _ _
 theorem sourceLambdaStar_budget (d : ℕ) (α β : ℝ) (hα : 0 < α) :
    8 * sourceGateOrder α β * d * sincSecondMoment (sourceGateOrder α β) / 3 ≤
      sourceLambdaStar d α β ^ 2 := by
  have hm := sincSecondMoment_nonneg (sourceGateOrder α β) (by have := sourceGateOrder_ge_three α β hα; omega)
  have ht : 0 ≤ 8 * sourceGateOrder α β * d * sincSecondMoment (sourceGateOrder α β) / 3 := by positivity
  have hs := Real.sq_sqrt ht
  have hl : Real.sqrt (8 * sourceGateOrder α β * d * sincSecondMoment (sourceGateOrder α β) / 3) ≤
      sourceLambdaStar d α β := le_max_right _ _
  have hlam : 0 ≤ sourceLambdaStar d α β := zero_le_one.trans (sourceLambdaStar_ge_one d α β)
  nlinarith [Real.sqrt_nonneg (8 * sourceGateOrder α β * d * sincSecondMoment (sourceGateOrder α β) / 3)]

 def sourceBandConstant (d : ℕ) (α β : ℝ) : ℝ :=
  sourceCStar (sourceGateOrder α β) (sourceGammaStar d) (sourceLambdaStar d α β) (sourceAlpha0 α β)

 theorem sourceBandConstant_bounds (d : ℕ) (hd : 0 < d) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 < sourceBandConstant d α β ∧ sourceBandConstant d α β < 1 :=
  sourceCStar_bounds _ _ _ _ (by have := sourceGateOrder_ge_three α β hα; omega)
    (sourceGammaStar_bounds d hd).1 (sourceGammaStar_bounds d hd).2.1
    (sourceLambdaStar_ge_one d α β) (sourceAlpha0_pos α β hα hβ)

 theorem literal_source_lattice_band (d : ℕ) (hd : 0 < d) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (M : ℕ) (m : ℝ) (hm : 0 < m) (hscale : m ≤ sourceBandConstant d α β * M) (b : ℕ) :
    4 * (6 * sourceGateOrder α β / sourceEta (sourceGammaStar d) (sourceLambdaStar d α β)
      (sourceAlpha0 α β) m b) ≤ (M : ℝ) :=
  source_lattice_band _ _ _ _ _ _ (by have := sourceGateOrder_ge_three α β hα; omega)
    (sourceGammaStar_bounds d hd).1 (sourceGammaStar_bounds d hd).2.1
    (sourceLambdaStar_ge_one d α β) (sourceAlpha0_pos α β hα hβ) hm hscale b

 theorem literal_source_pattern_budget (d : ℕ) (hd : 0 < d) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (J M k : ℕ),
      (2 : ℝ) ^ ((J : ℝ) * min α β) ≤ M → (k : ℝ) ≤ Real.sqrt M →
      (∑ _q : Fin d, ∑ i : Fin J, mismatchWeight d i.val *
        ((k : ℝ) + 6 * sourceGateOrder α β / sourceEta (sourceGammaStar d) (sourceLambdaStar d α β)
          (sourceAlpha0 α β) ((2 : ℝ) ^ ((J : ℝ) * min α β)) i.val)) ≤ CE * M :=
  source_pattern_budget_bound_exact d _ hd _ _ _ _ (sourceGammaStar_bounds d hd).1
    (zero_lt_one.trans_le (sourceLambdaStar_ge_one d α β)) (sourceAlpha0_pos α β hα hβ) (lt_min hα hβ)

end RoughRegime.LatticePriors
