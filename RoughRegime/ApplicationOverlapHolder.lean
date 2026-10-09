module

public import RoughRegime.ApplicationOverlapCoefficientBound
public import RoughRegime.HolderFiniteComparison
public import RoughRegime.HolderFiniteLinear


@[expose] public section
/-! The source's two smoothness conventions, compared in the actual finite
Hölder classes with constants fixed before the regression functions. -/
noncomputable section
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false

/-- If beta is no larger than alpha, passing between m and m-gamma*w changes
only a fixed Hölder radius, for every bounded overlap coefficient. -/
theorem nuisance_radius_equivalence {d:ℕ} (α β Hm Hw Hr gamma:ℝ)
    (hβ:0<β) (hβα:β ≤ α) (hHm:0 ≤ Hm) (hHw:0 ≤ Hw) (hHr:0 ≤ Hr)
    (hgamma:|gamma| ≤ 1) (w m:Model.Covariate d→ℝ) (hw:w∈Model.holderBall α Hw) :
    (m∈Model.holderBall β Hm →
      (fun x=>m x-gamma*w x)∈Model.holderBall β (Hm+Model.finiteLowerExponentConstant d α*Hw)) ∧
    ((fun x=>m x-gamma*w x)∈Model.holderBall β Hr →
      m∈Model.holderBall β (Hr+Model.finiteLowerExponentConstant d α*Hw)) := by
  have hwβ:=Model.holderBall_lower_exponent_finite w β α Hw hβ hβα hHw hw
  have hC:0 ≤ Model.finiteLowerExponentConstant d α*Hw:=by
    unfold Model.finiteLowerExponentConstant;positivity
  constructor
  · intro hm
    have hneg:=Model.holderBall_const_mul_contraction w β _ (-gamma) hwβ (by simpa using hgamma)
    have hsum:=Model.holderBall_add_finite m (fun x=>-gamma*w x) β Hm _ hHm hC hm hneg
    have he:(m+(fun x=>-gamma*w x))=(fun x=>m x-gamma*w x):=by funext x;dsimp;ring
    rw [he] at hsum
    exact hsum
  · intro hr
    have hpos:=Model.holderBall_const_mul_contraction w β _ gamma hwβ hgamma
    have hsum:=Model.holderBall_add_finite (fun x=>m x-gamma*w x) (fun x=>gamma*w x) β Hr _ hHr hC hr hpos
    have he:((fun x=>m x-gamma*w x)+(fun x=>gamma*w x))=m:=by funext x;dsimp;ring
    rw [he] at hsum
    exact hsum

/-- The literal overlap class satisfies the residual smoothness convention
with a radius depending only on its fixed dimension and exponents. -/
theorem Witness.smooth_overlap_residual (Q:Model.Parameters) (ε:ℝ) (hε:0<ε) (hεhalf:ε<1/2)
    (P:MeasureTheory.ProbabilityMeasure (Model.Covariate Q.d×Response)) (W:Witness Q ε P)
    (hβα:Q.β ≤ Q.α) :
    (fun x=>W.mV x-effect Q.d P*W.mU x)∈Model.holderBall Q.β
      ((1+Model.finiteLowerExponentConstant Q.d Q.α)*Q.H) := by
  have h:= (nuisance_radius_equivalence Q.α Q.β Q.H Q.H Q.H (effect Q.d P)
    Q.hβ hβα Q.hH.le Q.hH.le Q.hH.le (effect_abs_le_one Q ε hε hεhalf P W)
    W.mU W.mV W.smoothU).1 W.smoothV
  have he:Q.H+Model.finiteLowerExponentConstant Q.d Q.α*Q.H=
      (1+Model.finiteLowerExponentConstant Q.d Q.α)*Q.H:=by ring
  rw [he] at h
  exact h

end RoughRegime.Applications.Overlap
