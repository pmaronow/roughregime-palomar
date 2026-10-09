module

public import RoughRegime.GlobalLatticeMass


@[expose] public section
/-! The baseline density and strictly positive margins are consequences of
the fixed small-volume choice used by the construction. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set Filter

 def sourceBaseline (v I r0 : ℝ) : ℝ := (1 - v * I * r0) / (1 - v * I)

 theorem exists_small_baseline_volume (rminus rplus r0 I : ℝ)
    (hrminus : rminus < 1) (hrplus : 1 < rplus) (hI0 : 0 ≤ I) (hI1 : I ≤ 1) :
    ∃ vmax : ℝ, 0 < vmax ∧ vmax ≤ 1 / 2 ∧ ∀ v, 0 < v → v ≤ vmax →
      0 < 1 - v * I ∧ (rminus + 1) / 2 < sourceBaseline v I r0 ∧ sourceBaseline v I r0 < (rplus + 1) / 2 := by
  have hf : ContinuousAt (fun v => sourceBaseline v I r0) 0 := by
    unfold sourceBaseline
    exact (continuousAt_const.sub ((continuousAt_id.mul continuousAt_const).mul continuousAt_const)).div
      (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)) (by simp)
  have h0 : sourceBaseline 0 I r0 ∈ Ioo ((rminus + 1) / 2) ((rplus + 1) / 2) := by
    simp only [sourceBaseline, zero_mul, sub_zero, div_one, mem_Ioo]
    constructor <;> linarith
  have hev := hf.eventually (isOpen_Ioo.mem_nhds h0)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (ε / 2) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro v hv hvmax
  have hvε : v < ε := by have hh := hvmax.trans (min_le_left _ _); linarith
  have hvhalf : v ≤ 1 / 2 := hvmax.trans (min_le_right _ _)
  have hp := he (show dist v 0 < ε by simpa only [Real.dist_eq, sub_zero, abs_of_pos hv] using hvε)
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hI1 hv.le], hp.1, hp.2⟩

 theorem source_margin_parameters (rminus rplus p0 δ : ℝ)
    (hδ0 : 0 < δ) (_hlt : rminus < rplus)
    (hδr : δ ≤ ((rminus + rplus) / 2 - rminus) / 2)
    (hδp0 : δ ≤ (p0 - rminus) / 2) (hδp1 : δ ≤ (rplus - p0) / 2) :
    let r0 := (rminus + rplus) / 2
    let h := (rplus - rminus) / 2 - δ
    0 < h ∧ rminus + δ ≤ p0 ∧ p0 ≤ rplus - δ ∧
      rminus + δ ≤ r0 - |h| ∧ r0 + |h| ≤ rplus - δ := by
  dsimp only
  have hh : 0 < (rplus - rminus) / 2 - δ := by linarith
  rw [abs_of_pos hh]
  constructor
  · exact hh
  · constructor
    · linarith
    · constructor
      · linarith
      · constructor <;> linarith

end RoughRegime.LatticePriors
