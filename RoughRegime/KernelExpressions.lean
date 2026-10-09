module

public import RoughRegime.KernelUniform


@[expose] public section
/-! Uniform combined-index truncation bounds for actual finite kernel expressions. -/
noncomputable section
set_option maxHeartbeats 600000
universe u
open scoped BigOperators Matrix.Norms.L2Operator
open Set Metric
namespace RoughRegime.KernelExpressions
open RoughRegime.ComplexKernel

/-- All fixed finite sums and products of kernel entries and parameter polynomials. -/
inductive Expression (p : ℕ) {I : Type u} (dims : I → ℕ) : Type u
  | polynomial : MvPolynomial (Fin p) ℂ → Expression p dims
  | kernelEntry : (i : I) → Fin (dims i) → Fin (dims i) → Expression p dims
  | add : Expression p dims → Expression p dims → Expression p dims
  | mul : Expression p dims → Expression p dims → Expression p dims

/-- Actual common-index power series, retaining the entry polynomials proved earlier. -/
def Expression.series {p : ℕ} {I : Type*} {dims : I → ℕ}
    (lo hi : ℝ) (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (t : Fin p → ℂ) : Expression p dims → PowerSeries ℂ
  | .polynomial P => PowerSeries.C (MvPolynomial.eval t P)
  | .kernelEntry i a b => PowerSeries.mk (fun k => kernelCoefficient lo hi (M i t) k a b)
  | .add f g => f.series lo hi M t + g.series lo hi M t
  | .mul f g => f.series lo hi M t * g.series lo hi M t

/-- Entry evaluation is bounded in the genuine Euclidean operator norm. -/
def entryCLM {n : ℕ} (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

lemma coeff_add_norm_sum_le (f g : PowerSeries ℂ)
    (hf : Summable (fun k => ‖PowerSeries.coeff k f‖))
    (hg : Summable (fun k => ‖PowerSeries.coeff k g‖)) :
    Summable (fun k => ‖PowerSeries.coeff k (f + g)‖) ∧
      (∑' k, ‖PowerSeries.coeff k (f + g)‖) ≤
        (∑' k, ‖PowerSeries.coeff k f‖) + ∑' k, ‖PowerSeries.coeff k g‖ := by
  have hb (k : ℕ) : ‖PowerSeries.coeff k (f + g)‖ ≤
      ‖PowerSeries.coeff k f‖ + ‖PowerSeries.coeff k g‖ := by
    rw [map_add]
    exact norm_add_le _ _
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hf.add hg)
  refine ⟨hs, ?_⟩
  exact (hs.tsum_le_tsum hb (hf.add hg)).trans_eq (hf.tsum_add hg)

lemma coeff_mul_norm_sum_le (f g : PowerSeries ℂ)
    (hf : Summable (fun k => ‖PowerSeries.coeff k f‖))
    (hg : Summable (fun k => ‖PowerSeries.coeff k g‖)) :
    Summable (fun k => ‖PowerSeries.coeff k (f * g)‖) ∧
      (∑' k, ‖PowerSeries.coeff k (f * g)‖) ≤
        (∑' k, ‖PowerSeries.coeff k f‖) * ∑' k, ‖PowerSeries.coeff k g‖ := by
  have hs : Summable (fun k => ‖PowerSeries.coeff k (f * g)‖) := by
    have hs0 := summable_norm_sum_mul_antidiagonal_of_summable_norm (R := ℂ)
      (f := fun k => PowerSeries.coeff k f) (g := fun k => PowerSeries.coeff k g) hf hg
    convert hs0 using 1
    funext k
    rw [PowerSeries.coeff_mul]
  have hb (k : ℕ) : ‖PowerSeries.coeff k (f * g)‖ ≤
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
        ‖PowerSeries.coeff ij.1 f‖ * ‖PowerSeries.coeff ij.2 g‖ := by
    rw [PowerSeries.coeff_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_mul_le _ _))
  have hfg : Summable (fun ij : ℕ × ℕ =>
      ‖PowerSeries.coeff ij.1 f‖ * ‖PowerSeries.coeff ij.2 g‖) :=
    Summable.mul_of_nonneg hf hg (fun k => norm_nonneg (PowerSeries.coeff k f))
      (fun k => norm_nonneg (PowerSeries.coeff k g))
  have hr : Summable (fun k : ℕ => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
      ‖PowerSeries.coeff ij.1 f‖ * ‖PowerSeries.coeff ij.2 g‖) :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (f := fun k : ℕ => ‖PowerSeries.coeff k f‖)
      (g := fun k : ℕ => ‖PowerSeries.coeff k g‖) hfg
  refine ⟨hs, ?_⟩
  exact (hs.tsum_le_tsum hb hr).trans_eq
    (hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg).symm

/-- Every finite expression has a uniform absolutely summable coefficient bound
on an actual complex parameter neighborhood, independent of truncation degree. -/
theorem uniform_expression_coefficients {p : ℕ} {I : Type*} {dims : I → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℂ)) (hV : Bornology.IsBounded V)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hM : ∀ i, Continuous (M i))
    (hHerm : ∀ i t, t ∈ V → (M i t).IsHermitian)
    (hSpec : ∀ i t, t ∈ V → spectrum ℝ (M i t) ⊆ Icc lo hi)
    (f : Expression p dims) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ t, (∃ t0 ∈ V, ‖t - t0‖ < ε) →
        Summable (fun k => ‖PowerSeries.coeff k (f.series lo hi M t)‖) ∧
          (∑' k, ‖PowerSeries.coeff k (f.series lo hi M t)‖) ≤ C := by
  induction f with
  | polynomial P =>
    obtain ⟨C0, hC0⟩ := hV.isCompact_closure.cthickening.exists_bound_of_continuousOn
      (P.continuous_eval.continuousOn : ContinuousOn (fun t => MvPolynomial.eval t P)
        (cthickening 1 (closure V)))
    refine ⟨1, max C0 0, zero_lt_one, le_rfl, le_max_right _ _, ?_⟩
    intro t ht
    obtain ⟨t0, ht0, hnear⟩ := ht
    have hmem : t ∈ cthickening 1 (closure V) := mem_cthickening_of_dist_le t t0 1 _
      (subset_closure ht0) (by simpa only [dist_eq_norm] using hnear.le)
    have hs : Summable (fun k => ‖PowerSeries.coeff k (PowerSeries.C (MvPolynomial.eval t P))‖) := by
      apply summable_of_ne_finset_zero (s := {0})
      intro k hk
      simp only [Finset.mem_singleton] at hk
      simp [PowerSeries.coeff_C, hk]
    refine ⟨hs, ?_⟩
    simp only [Expression.series, PowerSeries.coeff_C, apply_ite norm, norm_zero, tsum_ite_eq]
    exact (hC0 t hmem).trans (le_max_left _ _)
  | kernelEntry i a b =>
    have : Nonempty (Fin (dims i)) := ⟨a⟩
    obtain ⟨ε, B, q, hε, hε1, hB, hq, hq1, hb⟩ :=
      bounded_uniform_kernel_coefficients lo hi hlo hlt V hV (M i) (hM i) (hHerm i) (hSpec i)
    let D := ‖entryCLM a b‖ * B
    have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) hB
    refine ⟨ε, D * (1 - q)⁻¹, hε, hε1, by positivity, ?_⟩
    intro t ht
    have hc (k : ℕ) : ‖PowerSeries.coeff k
        ((Expression.kernelEntry i a b).series lo hi M t)‖ ≤ D * q ^ k := by
      simp only [Expression.series, PowerSeries.coeff_mk]
      exact (ContinuousLinearMap.le_opNorm (entryCLM a b) _).trans
        ((mul_le_mul_of_nonneg_left (hb t ht k) (norm_nonneg _)).trans_eq (by dsimp [D]; ring))
    have hg := (summable_geometric_of_lt_one hq hq1).mul_left D
    have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hc hg
    refine ⟨hs, ?_⟩
    exact (hs.tsum_le_tsum hc hg).trans_eq (by rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1])
  | add f g hf hg =>
    obtain ⟨εf, Cf, hεf, hεf1, hCf, hfb⟩ := hf
    obtain ⟨εg, Cg, hεg, hεg1, hCg, hgb⟩ := hg
    refine ⟨min εf εg, Cf + Cg, lt_min hεf hεg,
      (min_le_left _ _).trans hεf1, add_nonneg hCf hCg, ?_⟩
    intro t ht
    obtain ⟨t0, ht0, hnear⟩ := ht
    have hf' := hfb t ⟨t0, ht0, hnear.trans_le (min_le_left _ _)⟩
    have hg' := hgb t ⟨t0, ht0, hnear.trans_le (min_le_right _ _)⟩
    have hh := coeff_add_norm_sum_le _ _ hf'.1 hg'.1
    exact ⟨hh.1, hh.2.trans (add_le_add hf'.2 hg'.2)⟩
  | mul f g hf hg =>
    obtain ⟨εf, Cf, hεf, hεf1, hCf, hfb⟩ := hf
    obtain ⟨εg, Cg, hεg, hεg1, hCg, hgb⟩ := hg
    refine ⟨min εf εg, Cf * Cg, lt_min hεf hεg,
      (min_le_left _ _).trans hεf1, mul_nonneg hCf hCg, ?_⟩
    intro t ht
    obtain ⟨t0, ht0, hnear⟩ := ht
    have hf' := hfb t ⟨t0, ht0, hnear.trans_le (min_le_left _ _)⟩
    have hg' := hgb t ⟨t0, ht0, hnear.trans_le (min_le_right _ _)⟩
    have hh := coeff_mul_norm_sum_le _ _ hf'.1 hg'.1
    exact ⟨hh.1, hh.2.trans (mul_le_mul hf'.2 hg'.2 (tsum_nonneg (fun _ => norm_nonneg _)) hCf)⟩

/-- Lemma 5(b): the same constant bounds every combined-index truncation. -/
theorem uniform_expression_truncations {p : ℕ} {I : Type*} {dims : I → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℂ)) (hV : Bornology.IsBounded V)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hM : ∀ i, Continuous (M i))
    (hHerm : ∀ i t, t ∈ V → (M i t).IsHermitian)
    (hSpec : ∀ i t, t ∈ V → spectrum ℝ (M i t) ⊆ Icc lo hi)
    (f : Expression p dims) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ t, (∃ t0 ∈ V, ‖t - t0‖ < ε) → ∀ m : ℕ,
        ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (f.series lo hi M t)‖ ≤ C := by
  obtain ⟨ε, C, hε, hε1, hC, hb⟩ :=
    uniform_expression_coefficients lo hi hlo hlt V hV M hM hHerm hSpec f
  refine ⟨ε, C, hε, hε1, hC, ?_⟩
  intro t ht m
  exact (norm_sum_le _ _).trans (((hb t ht).1.sum_le_tsum _ (fun _ _ => norm_nonneg _)).trans (hb t ht).2)

/-- Coordinatewise inclusion of the source real parameter space. Its function-space
norm is exactly the infinity norm used in the paper. -/
def realParametersCLM (p : ℕ) : (Fin p → ℝ) →L[ℝ] (Fin p → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

/-- Literal real-parameter affine-map formulation of Lemma 5(b), including empty
matrix dimensions and arbitrary bounded, possibly nonclosed source sets. -/
theorem real_affine_expression_truncations {p : ℕ} {I : Type*} {dims : I → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℝ)) (hV : Bornology.IsBounded V)
    (M : (i : I) → (Fin p → ℂ) →ᵃ[ℂ] Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hHerm : ∀ i t, t ∈ V → (M i (realParametersCLM p t)).IsHermitian)
    (hSpec : ∀ i t, t ∈ V → spectrum ℝ (M i (realParametersCLM p t)) ⊆ Icc lo hi)
    (f : Expression p dims) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ t : Fin p → ℂ, (∃ t0 ∈ V, ‖t - realParametersCLM p t0‖ < ε) → ∀ m : ℕ,
        ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k
          (f.series lo hi (fun i => M i) t)‖ ≤ C := by
  obtain ⟨ε, C, hε, hε1, hC, hb⟩ := uniform_expression_truncations lo hi hlo hlt
    (realParametersCLM p '' V) (hV.image (realParametersCLM p)) (fun i => M i)
    (fun i => (M i).continuous_of_finiteDimensional)
    (by
      intro i t ht
      obtain ⟨t0, ht0, rfl⟩ := ht
      exact hHerm i t0 ht0)
    (by
      intro i t ht
      obtain ⟨t0, ht0, rfl⟩ := ht
      exact hSpec i t0 ht0) f
  refine ⟨ε, C, hε, hε1, hC, ?_⟩
  intro t ht
  apply hb t
  obtain ⟨t0, ht0, hnear⟩ := ht
  exact ⟨realParametersCLM p t0, ⟨t0, ht0, rfl⟩, hnear⟩

end RoughRegime.KernelExpressions
