module

public import RoughRegime.ParametricJets
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.Compact


@[expose] public section
/-! Actual uniform partial-derivative bounds for smooth compact parameter
families that vanish when their amplitude parameter is zero. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.Calculus
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Uniform compactness and the mean value theorem supply the amplitude factor
in every true partial jet. The derivative bound is proved from smoothness. -/
theorem compact_amplitude_jet_bound (f : ℝ → E → G) (K : Set E) (hK : IsCompact K)
    (hf : ∀ p ∈ (Icc (0 : ℝ) 1) ×ˢ K, ContDiffAt ℝ ∞ (Function.uncurry f) p)
    (hzero : ∀ x, f 0 x = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ n (f s) x‖ ≤ C * s := by
  let J : ℝ × E → E [×n]→L[ℝ] G := fun p => iteratedFDeriv ℝ n (f p.1) p.2
  let T := (Icc (0 : ℝ) 1) ×ˢ K
  have hJ (p : ℝ × E) (hp : p ∈ T) : ContDiffAt ℝ ∞ J p :=
    contDiffAt_parametric_iteratedFDeriv f p.1 p.2 (hf p hp) n
  have hc : ContinuousOn (fun p => ‖fderiv ℝ J p‖) T := fun p hp =>
    ((hJ p hp).continuousAt_fderiv (by simp)).norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).bddAbove_image hc
  let C : ℝ := max B 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound (p : ℝ × E) (hp : p ∈ T) : ‖fderiv ℝ J p‖ ≤ C :=
    (hB ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro s hs x hx
  let L : ℝ →L[ℝ] ℝ × E := ContinuousLinearMap.inl ℝ ℝ E
  let g : ℝ → E [×n]→L[ℝ] G := fun u => J (u, x)
  have hd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : DifferentiableAt ℝ g u := by
    change DifferentiableAt ℝ (fun v : ℝ => J (v, x)) u
    exact ((hJ (u, x) ⟨hu, hx⟩).differentiableAt (by simp)).comp u
      (show DifferentiableAt ℝ (fun v : ℝ => (v, x)) u from
        differentiableAt_id.prodMk (differentiableAt_const x))
  have hderiv (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ‖fderiv ℝ g u‖ ≤ C := by
    have hj := ((hJ (u, x) ⟨hu, hx⟩).differentiableAt (by simp)).hasFDerivAt
    have hl := (L.hasFDerivAt (x := u)).add_const (0, x)
    have he : (fun v : ℝ => L v + (0, x)) = (fun v => (v, x)) := by
      funext v
      simp [L, ContinuousLinearMap.inl_apply]
    rw [he] at hl
    have hh := (hj.comp u hl).fderiv
    change fderiv ℝ g u = (fderiv ℝ J (u, x)).comp L at hh
    rw [hh]
    calc
      _ ≤ ‖fderiv ℝ J (u, x)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C := by simpa only [L, ContinuousLinearMap.norm_inl, mul_one] using hbound (u, x) ⟨hu, hx⟩
  have hh := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_fderiv_le hd hderiv
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) hs
  have hg0 : g 0 = 0 := by
    have he : f 0 = (fun _ => (0 : G)) := funext hzero
    dsimp [g, J]
    rw [he]
    simp
  rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hs.1] at hh
  exact hh

/-- A fixed smooth function has a uniform finite family of true jets on every
compact set. -/
theorem compact_finite_jet_bound (f : E → G) (K : Set E) (hK : IsCompact K)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  have he (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
    have hc : ContinuousOn (fun x => ‖iteratedFDeriv ℝ k f x‖) K :=
      (hf.continuous_iteratedFDeriv (by simp)).norm.continuousOn
    obtain ⟨C,hC⟩ := hK.bddAbove_image hc
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro x hx
    exact (hC ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  choose C hC hb using he
  refine ⟨∑ k ∈ Finset.range (n+1), C k, Finset.sum_nonneg (fun k _ => hC k),?_⟩
  intro k hk x hx
  exact (hb k x hx).trans (Finset.single_le_sum (fun i _ => hC i)
    (Finset.mem_range.mpr (by omega)))

end RoughRegime.Calculus
