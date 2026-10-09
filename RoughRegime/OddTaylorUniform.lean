module

public import RoughRegime.OddTaylor


@[expose] public section
/-! The true C⁴ odd-part expansion uniformly on compact parameter families. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace RoughRegime.OddTaylor

/-- A compact family with genuine local C⁴ slices and continuous fourth partials
has a single odd/odd Taylor neighborhood and remainder constant. The hypotheses
are regularity of the actual derivatives, rather than an assumed expansion. -/
theorem uniform_oddOdd_taylor {Θ : Type*} [NormedAddCommGroup Θ] [ProperSpace Θ]
    (F : Θ → Plane → ℝ) (K : Set Θ) (hK : IsCompact K)
    (U : Set (Θ × Plane)) (hU : IsOpen U) (hKU : K ×ˢ {0} ⊆ U)
    (hF : ∀ p ∈ U, ContDiffAt ℝ 4 (F p.1) p.2)
    (hD : ContinuousOn (fun p : Θ × Plane =>
      fderiv ℝ (fderiv ℝ (mixedDerivative (F p.1))) p.2) U) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ θ ∈ K, ∀ u v : ℝ, |u| ≤ ε → |v| ≤ ε →
      |oddOdd (F θ) u v - mixedDerivative (F θ) 0 * u * v| ≤
        C * |u * v| * (u ^ 2 + v ^ 2) := by
  have hL : IsCompact (K ×ˢ {(0 : Plane)}) := hK.prod isCompact_singleton
  obtain ⟨δ, hδ, hδU⟩ := hL.exists_cthickening_subset_open hU hKU
  have hT : IsCompact (cthickening δ (K ×ˢ {(0 : Plane)})) := hL.cthickening
  obtain ⟨B, hB⟩ := hT.exists_bound_of_continuousOn (E := Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (f := fun p : Θ × Plane => fderiv ℝ (fderiv ℝ (mixedDerivative (F p.1))) p.2)
    (hD.mono hδU)
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hpoint (θ : Θ) (hθ : θ ∈ K) (x : Plane) (hx : ‖x‖ < δ) :
      (θ, x) ∈ cthickening δ (K ×ˢ {(0 : Plane)}) := by
    apply thickening_subset_cthickening δ _
    apply mem_thickening_iff.mpr
    refine ⟨(θ, 0), ⟨hθ, rfl⟩, ?_⟩
    simpa only [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg x)] using hx
  refine ⟨δ / 2, by positivity, C, hC, ?_⟩
  intro θ hθ u v hu hv
  apply oddOdd_remainder_of_second_bound (F θ) δ C hδ
    (fun x hx => hF (θ, x) (hδU (hpoint θ hθ x (by simpa using hx))))
    (fun x hx => (hB (θ, x) (hpoint θ hθ x (by simpa using hx))).trans (le_max_left _ _))
  · exact hu.trans_lt (by linarith)
  · exact hv.trans_lt (by linarith)

end RoughRegime.OddTaylor
