module

public import RoughRegime.CanonicalAdmissibility


@[expose] public section
/-! Actual fixed smooth inner and outer cutoffs in the interior of the cube,
with the source's positive inner square integral. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set Metric
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

 def cubeCenter (d : ℕ) : Model.Covariate d := WithLp.toLp 2 (fun _ => (1 : ℝ) / 2)
 def innerBump (d : ℕ) : ContDiffBump (cubeCenter d) :=
  ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩
 def outerBump (d : ℕ) : ContDiffBump (cubeCenter d) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

 theorem cubeCenter_ball_subset (d : ℕ) :
    Metric.ball (cubeCenter d) (1 / 4) ⊆ unitCubeOpen d := by
  intro x hx q
  have hn : ‖x - cubeCenter d‖ < 1 / 4 := by simpa [dist_eq_norm] using hx
  have hq := (PiLp.norm_apply_le (x - cubeCenter d) q).trans_lt hn
  simp only [PiLp.sub_apply, cubeCenter, Real.norm_eq_abs] at hq
  have hh := abs_lt.mp hq
  constructor <;> linarith

 theorem innerBump_smooth (d : ℕ) : ContDiff ℝ ∞ (innerBump d : Model.Covariate d → ℝ) :=
  (innerBump d).contDiff
 theorem outerBump_smooth (d : ℕ) : ContDiff ℝ ∞ (outerBump d : Model.Covariate d → ℝ) :=
  (outerBump d).contDiff

 theorem innerBump_zero_outside (d : ℕ) (x : Model.Covariate d) (hx : x ∉ unitCubeOpen d) :
    innerBump d x = 0 := by
  apply (innerBump d).zero_of_le_dist
  by_contra h
  have hxball : x ∈ Metric.ball (cubeCenter d) (1 / 4) := by
    simp only [innerBump] at h
    exact (lt_of_lt_of_le (lt_of_not_ge h) (by norm_num : (1 : ℝ) / 8 ≤ 1 / 4))
  exact hx (cubeCenter_ball_subset d hxball)
 theorem outerBump_zero_outside (d : ℕ) (x : Model.Covariate d) (hx : x ∉ unitCubeOpen d) :
    outerBump d x = 0 := by
  apply (outerBump d).zero_of_le_dist
  by_contra h
  exact hx (cubeCenter_ball_subset d (by simpa [outerBump] using lt_of_not_ge h))

 theorem outerBump_one_on_inner (d : ℕ) (x : Model.Covariate d) (hx : innerBump d x ≠ 0) :
    outerBump d x = 1 := by
  apply (outerBump d).one_of_mem_closedBall
  have hm : x ∈ Function.support (innerBump d) := hx
  rw [(innerBump d).support_eq] at hm
  exact (by simpa [innerBump, outerBump] using le_of_lt (Metric.mem_ball.mp hm))

 theorem innerBump_compact (d : ℕ) : HasCompactSupport (innerBump d : Model.Covariate d → ℝ) :=
  (innerBump d).hasCompactSupport
 theorem outerBump_compact (d : ℕ) : HasCompactSupport (outerBump d : Model.Covariate d → ℝ) :=
  (outerBump d).hasCompactSupport

 theorem innerBump_tsupport_subset (d : ℕ) :
    tsupport (innerBump d : Model.Covariate d → ℝ) ⊆ unitCubeOpen d := by
  rw [(innerBump d).tsupport_eq]
  intro x hx
  apply cubeCenter_ball_subset d
  exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by norm_num [innerBump]))
 theorem outerBump_tsupport_subset (d : ℕ) :
    tsupport (outerBump d : Model.Covariate d → ℝ) ⊆ unitCubeOpen d := by
  rw [(outerBump d).tsupport_eq]
  intro x hx q
  have hn : ‖x - cubeCenter d‖ ≤ 1 / 4 := by simpa [dist_eq_norm, outerBump] using hx
  have hq := (PiLp.norm_apply_le (x - cubeCenter d) q).trans hn
  simp only [PiLp.sub_apply, cubeCenter, Real.norm_eq_abs] at hq
  have hh := abs_le.mp hq
  constructor <;> linarith

 theorem innerBump_square_integral_pos (d : ℕ) :
    0 < ∫ x, (innerBump d x) ^ 2 ∂Model.cubeVolume d := by
  have hc : Continuous (fun x : Model.Covariate d => innerBump d x ^ 2) :=
    (innerBump_smooth d).continuous.pow 2
  have hs : Function.support (fun x : Model.Covariate d => innerBump d x ^ 2) ⊆ Model.cube d := by
    intro x hx q
    have hi : innerBump d x ≠ 0 := by simpa [Function.mem_support] using hx
    have hm : x ∈ Function.support (innerBump d) := hi
    rw [(innerBump d).support_eq] at hm
    have hcball : x ∈ Metric.ball (cubeCenter d) (1 / 4) :=
      Metric.ball_subset_ball (by norm_num [innerBump]) hm
    exact ⟨(cubeCenter_ball_subset d hcball q).1.le, (cubeCenter_ball_subset d hcball q).2.le⟩
  have hi : Integrable (fun x : Model.Covariate d => innerBump d x ^ 2) volume :=
    (integrableOn_iff_integrable_of_support_subset hs).mp
      (hc.continuousOn.integrableOn_compact (Model.isCompact_cube d))
  have hp : 0 < ∫ x : Model.Covariate d, innerBump d x ^ 2 := by
    apply integral_pos_of_integrable_nonneg_nonzero (x := cubeCenter d) hc hi (fun x => sq_nonneg _)
    have hone : innerBump d (cubeCenter d) = 1 :=
      (innerBump d).one_of_mem_closedBall (Metric.mem_closedBall_self (innerBump d).rIn_pos.le)
    simp [hone]
  have heq : (∫ x, innerBump d x ^ 2 ∂Model.cubeVolume d) =
      ∫ x : Model.Covariate d, innerBump d x ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : x ∉ unitCubeOpen d := by
      intro hx'
      exact hx (fun q => ⟨(hx' q).1.le, (hx' q).2.le⟩)
    rw [innerBump_zero_outside d x hx', zero_pow (by norm_num : 2 ≠ 0)]
  rw [heq]
  exact hp

 theorem exists_source_cutoffs (d : ℕ) :
    ∃ inner outer : Model.Covariate d → ℝ,
      ContDiff ℝ ∞ inner ∧ ContDiff ℝ ∞ outer ∧
      (∀ x, x ∉ unitCubeOpen d → inner x = 0) ∧
      (∀ x, x ∉ unitCubeOpen d → outer x = 0) ∧
      (∀ x, 0 ≤ inner x ∧ inner x ≤ 1) ∧
      (∀ x, 0 ≤ outer x ∧ outer x ≤ 1) ∧
      (∀ x, inner x ≠ 0 → outer x = 1) ∧
      (0 < ∫ x, inner x ^ 2 ∂Model.cubeVolume d) := by
  refine ⟨innerBump d, outerBump d, innerBump_smooth d, outerBump_smooth d,
    innerBump_zero_outside d, outerBump_zero_outside d, ?_, ?_, outerBump_one_on_inner d,
    innerBump_square_integral_pos d⟩
  · intro x; exact ⟨(innerBump d).nonneg, (innerBump d).le_one⟩
  · intro x; exact ⟨(outerBump d).nonneg, (outerBump d).le_one⟩

end RoughRegime.LatticePriors
