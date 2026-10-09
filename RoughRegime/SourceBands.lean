module

public import RoughRegime.LatticeScales


@[expose] public section
/-! The construction's exact supremum band constant and lattice admissibility. -/
noncomputable section
namespace RoughRegime.LatticePriors
open Set
open scoped BigOperators

 def sourceBandCoefficient (Q : ℕ) (gammaStar lambdaStar alpha0 : ℝ) (b : ℕ) : ℝ :=
  (6 * Q * lambdaStar / gammaStar) * ((b : ℝ) + 1) ^ 3 * ((2 : ℝ) ^ (-alpha0)) ^ b

 def sourceBarK (Q : ℕ) (gammaStar lambdaStar alpha0 : ℝ) : ℝ :=
  sSup (Set.range (sourceBandCoefficient Q gammaStar lambdaStar alpha0))

 def sourceCStar (Q : ℕ) (gammaStar lambdaStar alpha0 : ℝ) : ℝ :=
  1 / (4 * sourceBarK Q gammaStar lambdaStar alpha0)

 theorem sourceBandCoefficient_summable (Q : ℕ) (gammaStar lambdaStar alpha0 : ℝ)
    (hγ : 0 < gammaStar) (hlam : 0 < lambdaStar) (ha : 0 < alpha0) :
    Summable (sourceBandCoefficient Q gammaStar lambdaStar alpha0) := by
  have hr0 : 0 < (2 : ℝ) ^ (-alpha0) := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-alpha0) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs := (summable_shifted_polynomial_geometric 3 _ hr0 hr1).mul_left (6 * Q * lambdaStar / gammaStar)
  convert hs using 1
  funext b
  unfold sourceBandCoefficient
  ring

 theorem sourceBandCoefficient_bddAbove (Q : ℕ) (gammaStar lambdaStar alpha0 : ℝ)
    (hγ : 0 < gammaStar) (hlam : 0 < lambdaStar) (ha : 0 < alpha0) :
    BddAbove (Set.range (sourceBandCoefficient Q gammaStar lambdaStar alpha0)) := by
  have hs := sourceBandCoefficient_summable Q gammaStar lambdaStar alpha0 hγ hlam ha
  refine ⟨∑' b, sourceBandCoefficient Q gammaStar lambdaStar alpha0 b, ?_⟩
  rintro x ⟨b, rfl⟩
  exact hs.le_tsum b (fun b hb => by unfold sourceBandCoefficient; positivity)

 theorem sourceBandCoefficient_le_barK (Q : ℕ) (gammaStar lambdaStar alpha0 : ℝ)
    (hγ : 0 < gammaStar) (hlam : 0 < lambdaStar) (ha : 0 < alpha0) (b : ℕ) :
    sourceBandCoefficient Q gammaStar lambdaStar alpha0 b ≤ sourceBarK Q gammaStar lambdaStar alpha0 :=
  le_csSup (sourceBandCoefficient_bddAbove Q gammaStar lambdaStar alpha0 hγ hlam ha) (Set.mem_range_self b)

 theorem sourceBarK_gt_one (Q : ℕ) (gammaStar lambdaStar alpha0 : ℝ)
    (hQ : 1 ≤ Q) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4)
    (hlam : 1 ≤ lambdaStar) (ha : 0 < alpha0) :
    1 < sourceBarK Q gammaStar lambdaStar alpha0 := by
  have hlam0 : 0 < lambdaStar := zero_lt_one.trans_le hlam
  have hh := sourceBandCoefficient_le_barK Q gammaStar lambdaStar alpha0 hγ hlam0 ha 0
  simp only [sourceBandCoefficient, Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one] at hh
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hnum : gammaStar < 6 * Q * lambdaStar := by nlinarith
  have hquot : 1 < 6 * Q * lambdaStar / gammaStar := (lt_div_iff₀ hγ).mpr (by simpa using hnum)
  exact hquot.trans_le hh

 theorem sourceCStar_bounds (Q : ℕ) (gammaStar lambdaStar alpha0 : ℝ)
    (hQ : 1 ≤ Q) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4)
    (hlam : 1 ≤ lambdaStar) (ha : 0 < alpha0) :
    0 < sourceCStar Q gammaStar lambdaStar alpha0 ∧ sourceCStar Q gammaStar lambdaStar alpha0 < 1 := by
  have hb := sourceBarK_gt_one Q gammaStar lambdaStar alpha0 hQ hγ hγ1 hlam ha
  unfold sourceCStar
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : 0 < 4 * sourceBarK Q gammaStar lambdaStar alpha0)).mpr
    nlinarith

 theorem source_scale_le_M (Q M : ℕ) (gammaStar lambdaStar alpha0 m : ℝ)
    (hQ : 1 ≤ Q) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4)
    (hlam : 1 ≤ lambdaStar) (ha : 0 < alpha0)
    (hmM : m ≤ sourceCStar Q gammaStar lambdaStar alpha0 * M) : m ≤ M := by
  have hc := (sourceCStar_bounds Q gammaStar lambdaStar alpha0 hQ hγ hγ1 hlam ha).2.le
  exact hmM.trans (by simpa using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg M : (0 : ℝ) ≤ M))

 theorem source_lattice_band (Q M : ℕ) (gammaStar lambdaStar alpha0 m : ℝ)
    (hQ : 1 ≤ Q) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4)
    (hlam : 1 ≤ lambdaStar) (ha : 0 < alpha0) (hm : 0 < m)
    (hmM : m ≤ sourceCStar Q gammaStar lambdaStar alpha0 * M) (b : ℕ) :
    4 * (6 * Q / sourceEta gammaStar lambdaStar alpha0 m b) ≤ (M : ℝ) := by
  have hlam0 : 0 < lambdaStar := zero_lt_one.trans_le hlam
  have hbpos := zero_lt_one.trans (sourceBarK_gt_one Q gammaStar lambdaStar alpha0 hQ hγ hγ1 hlam ha)
  have hcoef := sourceBandCoefficient_le_barK Q gammaStar lambdaStar alpha0 hγ hlam0 ha b
  have hstep := mul_le_mul_of_nonneg_left hmM (by positivity : 0 ≤ 4 * sourceBarK Q gammaStar lambdaStar alpha0)
  have hid : 4 * sourceBarK Q gammaStar lambdaStar alpha0 * sourceCStar Q gammaStar lambdaStar alpha0 = 1 := by
    unfold sourceCStar
    field_simp
  rw [← mul_assoc, hid, one_mul] at hstep
  rw [source_band_geometric Q b gammaStar lambdaStar alpha0 m hγ hlam0 hm]
  change 4 * (sourceBandCoefficient Q gammaStar lambdaStar alpha0 b * m) ≤ _
  have hh := mul_le_mul_of_nonneg_right hcoef hm.le
  nlinarith

end RoughRegime.LatticePriors
