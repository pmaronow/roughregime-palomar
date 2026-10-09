module

public import Mathlib


@[expose] public section
/-! Uniform invertibility and inverse bounds around compact parameter sets. -/
noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.L2Operator
namespace RoughRegime.KernelNeighborhood

/-- Compactness provides one complex parameter tube and one inverse bound for
all points on a fixed closed complex disk. Properness includes every finite
dimensional complex normed parameter space. -/
theorem uniform_inverse_tube {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {n : ℕ} (S : Set E) (hS : IsCompact S) (r0 : ℝ)
    (Q : ℂ × E → Matrix (Fin n) (Fin n) ℂ) (hQ : Continuous Q)
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r0, ∀ t ∈ S, IsUnit (Q (z, t))) :
    ∃ ε B : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧
      ∀ t, (∃ t0 ∈ S, ‖t - t0‖ < ε) →
        ∀ z ∈ closedBall (0 : ℂ) r0,
          IsUnit (Q (z, t)) ∧ ‖Ring.inverse (Q (z, t))‖ ≤ B := by
  let K : Set (ℂ × E) := closedBall (0 : ℂ) r0 ×ˢ S
  let U : Set (ℂ × E) := {p | (Q p).det ≠ 0}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) r0).prod hS
  have hU : IsOpen U := isOpen_ne_fun hQ.matrix_det continuous_const
  have hKU : K ⊆ U := by
    intro p hp
    exact ((Q p).isUnit_iff_isUnit_det.mp (hunit p.1 hp.1 p.2 hp.2)).ne_zero
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hδK : IsCompact (cthickening δ K) := hK.cthickening
  have hi : ContinuousOn (fun p => Ring.inverse (Q p)) (cthickening δ K) := by
    intro p hp
    have hdet : (Q p).det ≠ 0 := hδU hp
    have hscalar : ContinuousAt Ring.inverse (Q p).det := by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
    have hm := (continuousAt_matrix_inv (Q p) hscalar).comp hQ.continuousAt
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using hm.continuousWithinAt
  obtain ⟨B0, hB0⟩ := hδK.exists_bound_of_continuousOn hi
  let ε := min δ 1
  let B := max B0 0
  have hε : 0 < ε := lt_min hδ zero_lt_one
  refine ⟨ε, B, hε, min_le_right _ _, le_max_right _ _, ?_⟩
  intro t ht z hz
  obtain ⟨t0, ht0, hnear⟩ := ht
  have hp : (z, t) ∈ cthickening δ K := by
    apply thickening_subset_cthickening δ K
    apply mem_thickening_iff.mpr
    refine ⟨(z, t0), ⟨hz, ht0⟩, ?_⟩
    have hdist : dist (z, t) (z, t0) = ‖t - t0‖ := by
      simp [dist_eq_norm, Prod.norm_def]
    rw [hdist]
    exact hnear.trans_le (min_le_left _ _)
  refine ⟨(Q (z, t)).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr (hδU hp)), ?_⟩
  exact (hB0 (z, t) hp).trans (le_max_left _ _)

end RoughRegime.KernelNeighborhood
