module

public import RoughRegime.KernelNeighborhood


@[expose] public section
/-! The compact inverse tube also holds for kernels continuous on an open
parameter domain. This permits varying positive density endpoints without
extending inverse or square-root formulas across singular endpoints. -/
noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.L2Operator
namespace RoughRegime.KernelNeighborhood

theorem uniform_inverse_tube_on {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {n : ℕ} (O : Set E) (hO : IsOpen O) (S : Set E) (hS : IsCompact S) (hSO : S⊆O) (r0 : ℝ)
    (Q : ℂ×E→Matrix (Fin n) (Fin n) ℂ)
    (hQ : ContinuousOn Q (univ×ˢO))
    (hunit : ∀ z∈closedBall (0:ℂ) r0, ∀ t∈S, IsUnit (Q (z,t))) :
    ∃ ε B : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧
      ∀ t, (∃ t0∈S, ‖t-t0‖ < ε) → ∀ z∈closedBall (0:ℂ) r0,
        IsUnit (Q (z,t)) ∧ ‖Ring.inverse (Q (z,t))‖ ≤ B := by
  let K : Set (ℂ×E) := closedBall (0:ℂ) r0×ˢS
  let U : Set (ℂ×E) := (univ×ˢO)∩{p | (Q p).det≠0}
  have hDomain : IsOpen (univ×ˢO : Set (ℂ×E)) := isOpen_univ.prod hO
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hc : ContinuousAt Q p := (hQ p hp.1).continuousAt (hDomain.mem_nhds hp.1)
    exact inter_mem (hDomain.mem_nhds hp.1) ((continuous_id.matrix_det.continuousAt.comp hc).eventually_ne hp.2)
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) r0).prod hS
  have hKU : K⊆U := by
    intro p hp
    exact ⟨⟨mem_univ _,hSO hp.2⟩,
      ((Q p).isUnit_iff_isUnit_det.mp (hunit p.1 hp.1 p.2 hp.2)).ne_zero⟩
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hi : ContinuousOn (fun p => Ring.inverse (Q p)) (cthickening δ K) := by
    intro p hp
    have hpu := hδU hp
    have hc : ContinuousAt Q p := (hQ p hpu.1).continuousAt (hDomain.mem_nhds hpu.1)
    have hs : ContinuousAt Ring.inverse (Q p).det := by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hpu.2
    have hm := (continuousAt_matrix_inv (Q p) hs).comp hc
    simpa only [Matrix.nonsing_inv_eq_ringInverse,Function.comp_def] using hm.continuousWithinAt
  obtain ⟨B0,hB0⟩ := hK.cthickening.exists_bound_of_continuousOn hi
  let ε := min δ 1
  let B := max B0 0
  refine ⟨ε,B,lt_min hδ zero_lt_one,min_le_right _ _,le_max_right _ _,?_⟩
  intro t ht z hz
  obtain ⟨t0,ht0,hnear⟩ := ht
  have hp : (z,t)∈cthickening δ K := by
    apply thickening_subset_cthickening δ K
    apply mem_thickening_iff.mpr
    refine ⟨(z,t0),⟨hz,ht0⟩,?_⟩
    have hd : dist (z,t) (z,t0)=‖t-t0‖ := by simp [dist_eq_norm,Prod.norm_def]
    rw [hd]
    exact hnear.trans_le (min_le_left _ _)
  exact ⟨(Q (z,t)).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr (hδU hp).2),
    (hB0 (z,t) hp).trans (le_max_left _ _)⟩

end RoughRegime.KernelNeighborhood
