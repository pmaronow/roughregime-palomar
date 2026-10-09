module

public import RoughRegime.OddTaylorDerivative
public import Mathlib.Topology.Order.ProjIcc


@[expose] public section
/-! A globally continuous representative of every local C⁴ integrand germ.
No measurability away from the source neighborhood is assumed. -/
noncomputable section
open Set Metric Filter
namespace RoughRegime.OddTaylor

 theorem mixedDerivative_congr_germ (F G : Plane→ℝ) {x : Plane}
    (he : F=ᶠ[nhds x]G) : mixedDerivative F x=mixedDerivative G x := by
  have hd : firstPartial F=ᶠ[nhds x]firstPartial G := by
    filter_upwards [he.fderiv (𝕜:=ℝ)] with y hy
    exact congrArg (fun D : Plane→L[ℝ]ℝ=>D eU) hy
  exact congrArg (fun D : Plane→L[ℝ]ℝ=>D eV) hd.fderiv_eq

 theorem exists_continuous_representative (F : Plane→ℝ) (hF : ContDiffAt ℝ 4 F 0) :
    ∃r:ℝ,0<r ∧ ∃G:Plane→ℝ,Continuous G ∧ ContDiffAt ℝ 4 G 0 ∧
      (∀u v,|u|≤r→|v|≤r→G (u,v)=F (u,v)) ∧
      mixedDerivative G 0=mixedDerivative F 0 := by
  obtain ⟨e,he,hball⟩:=Metric.mem_nhds_iff.mp (hF.eventually (by norm_num))
  let r:=e/2
  have hr : 0<r := by dsimp [r];positivity
  have hre : r<e := by dsimp [r];linarith
  have hinterval : -r≤r := by linarith
  let clip : Plane→Plane:=fun x=>((projIcc (-r) r hinterval x.1:ℝ),(projIcc (-r) r hinterval x.2:ℝ))
  have hc : Continuous clip := by dsimp [clip];fun_prop
  have hclip : ∀x,clip x ∈ ball (0 : Plane) e := by
    intro x
    simp only [mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff]
    exact ⟨(abs_le.mpr (projIcc (-r) r hinterval x.1).property).trans_lt hre,
      (abs_le.mpr (projIcc (-r) r hinterval x.2).property).trans_lt hre⟩
  let G:=F∘clip
  have hG : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro x
    have hx : ContDiffAt ℝ 4 F (clip x) := hball (hclip x)
    exact hx.continuousAt.comp hc.continuousAt
  have hbox : ∀u v,|u|≤r→|v|≤r→G (u,v)=F (u,v) := by
    intro u v hu hv
    dsimp [G,clip]
    rw [projIcc_of_mem hinterval (abs_le.mp hu),projIcc_of_mem hinterval (abs_le.mp hv)]
  have hEq : G=ᶠ[nhds (0:Plane)]F := by
    filter_upwards [ball_mem_nhds (0:Plane) hr] with x hx
    have hx' : |x.1|<r ∧ |x.2|<r := by
      simpa only [mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using hx
    exact hbox x.1 x.2 hx'.1.le hx'.2.le
  exact ⟨r,hr,G,hG,hF.congr_of_eventuallyEq hEq,hbox,mixedDerivative_congr_germ G F hEq⟩

end RoughRegime.OddTaylor
