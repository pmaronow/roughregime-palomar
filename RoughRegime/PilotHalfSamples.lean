module

public import RoughRegime.PilotSampleSplit


@[expose] public section
/-! Both actual halves of an iid sample grow without bound. -/
namespace RoughRegime.Applications
open Filter

theorem pilotHalf_tendsto : Tendsto (fun n : ℕ=>n/2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2*b)] with n hn
  omega

theorem estimationHalf_tendsto : Tendsto (fun n : ℕ=>n-n/2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2*b)] with n hn
  omega

theorem halfSample_sum (n : ℕ) : n/2+(n-n/2)=n := by omega

end RoughRegime.Applications
