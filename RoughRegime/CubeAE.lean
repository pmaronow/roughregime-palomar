module

public import RoughRegime.HolderGeometry
public import RoughRegime.HolderModulus
public import Mathlib.MeasureTheory.Measure.Support


@[expose] public section
/-! Continuous restrictions on the source cube extend almost-everywhere
bounds to every cube point, including its boundary. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Model

theorem closure_interior_cube (d : ℕ) : closure (interior (cube d))=cube d := by
  rw [(convex_cube d).closure_interior_eq_closure_of_nonempty_interior
    (cube_nonempty_interior d),(isCompact_cube d).isClosed.closure_eq]

theorem cube_subset_measure_support (d : ℕ) : cube d ⊆ (cubeVolume d).support := by
  have hi := Measure.interior_inter_support (μ := (volume : Measure (Covariate d))) (s := cube d)
  rw [Measure.support_eq_univ,inter_univ] at hi
  rw [←closure_interior_cube d]
  exact closure_minimal hi Measure.isClosed_support

theorem continuousOn_ae_mem_Icc_cube {d : ℕ} {f : Covariate d → ℝ}
    (hf : ContinuousOn f (cube d)) (a b : ℝ)
    (hbound : ∀ᵐ x ∂cubeVolume d,f x ∈ Icc a b) :
    ∀ x ∈ cube d,f x ∈ Icc a b := by
  have hclosed : IsClosed (cube d ∩ f ⁻¹' Icc a b) :=
    hf.preimage_isClosed_of_isClosed (isCompact_cube d).isClosed isClosed_Icc
  have hae : (cube d ∩ f ⁻¹' Icc a b) ∈ ae (cubeVolume d) := by
    filter_upwards [ae_restrict_mem (isCompact_cube d).isClosed.measurableSet,hbound]
      with x hx hb
    exact ⟨hx,hb⟩
  intro x hx
  exact (Measure.support_subset_of_isClosed hclosed hae (cube_subset_measure_support d hx)).2

theorem holderBall_ae_mem_Icc_cube {d : ℕ} (f : Covariate d → ℝ) (t H a b : ℝ)
    (hf : f ∈ holderBall t H) (hbound : ∀ᵐ x ∂cubeVolume d,f x ∈ Icc a b) :
    ∀ x ∈ cube d,f x ∈ Icc a b :=
  continuousOn_ae_mem_Icc_cube (holderBall_regular f t H hf).2.continuousOn a b hbound

end RoughRegime.Model
