module

public import RoughRegime.ApplicationOverlapBounds


@[expose] public section
/-! The overlap coefficient is the genuine least-squares optimum over every
square-integrable nuisance measurable with respect to the covariates.
The exact loss decomposition also characterizes the quadratic in gamma. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : @Measure Ω mΩ)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)

 def nuisance (A Y : Ω→ℝ) (gamma : ℝ) : Ω→ℝ:=fun x=>μ[Y|m] x-gamma*μ[A|m] x
 def leastSquaresLoss (A Y : Ω→ℝ) (gamma : ℝ) (h : Ω→ℝ) : ℝ:=
   ∫ x,(Y x-gamma*A x-h x)^2 ∂μ
 def profiledLoss (A Y : Ω→ℝ) (gamma : ℝ) : ℝ:=
   leastSquaresLoss μ A Y gamma (nuisance μ m A Y gamma)
 def covarianceMean (A Y : Ω→ℝ) : ℝ:=∫ x,ConditionalExamples.conditionalCovariance m A Y μ x ∂μ
 def varianceMean (A : Ω→ℝ) : ℝ:=∫ x,condVar m A μ x ∂μ
 def optimalCoefficient (A Y : Ω→ℝ) : ℝ:=covarianceMean μ m A Y/varianceMean μ m A

 omit [IsProbabilityMeasure μ] hm in
 theorem nuisance_measurable (A Y : Ω→ℝ) (gamma : ℝ) : StronglyMeasurable[m] (nuisance μ m A Y gamma):=
   stronglyMeasurable_condExp.sub (stronglyMeasurable_condExp.const_mul gamma)

 omit [IsProbabilityMeasure μ] hm in
 theorem nuisance_memLp (A Y : Ω→ℝ) (hA : MemLp A 2 μ) (hY : MemLp Y 2 μ) (gamma : ℝ) :
     MemLp (nuisance μ m A Y gamma) 2 μ:=
   (hY.condExp one_le_two).sub ((hA.condExp one_le_two).const_mul gamma)

 theorem nuisance_condExp (A Y : Ω→ℝ) (hA : MemLp A 2 μ) (hY : MemLp Y 2 μ) (gamma : ℝ) :
     μ[(fun x=>Y x-gamma*A x)|m]=ᵐ[μ] nuisance μ m A Y gamma := by
   have hs:=condExp_sub (hY.integrable one_le_two) ((hA.integrable one_le_two).const_mul gamma) m
   have hc:=condExp_smul (μ:=μ) gamma A m
   filter_upwards [hs,hc] with x hx hc
   change μ[(fun x=>Y x-gamma*A x)|m] x=μ[Y|m] x-gamma*μ[A|m] x
   change μ[Y-(fun x=>gamma*A x)|m] x=μ[Y|m] x-gamma*μ[A|m] x
   rw [hx]
   change μ[Y|m] x-μ[(gamma • A)|m] x=_
   rw [hc]
   rfl

 include hm in
 theorem fixed_gamma_loss_decomposition (A Y : Ω→ℝ) (hA : MemLp A 2 μ) (hY : MemLp Y 2 μ)
     (gamma : ℝ) (h : Ω→ℝ) (hh : MemLp h 2 μ) (hhm : StronglyMeasurable[m] h) :
     leastSquaresLoss μ A Y gamma h=profiledLoss μ m A Y gamma+
       ∫ x,(nuisance μ m A Y gamma x-h x)^2 ∂μ := by
   let V : Ω→ℝ:=fun x=>Y x-gamma*A x
   have hV : MemLp V 2 μ:=hY.sub (hA.const_mul gamma)
   have hN:=nuisance_memLp μ m A Y hA hY gamma
   exact Conditional.prediction_loss_decomposition hm V h (nuisance μ m A Y gamma)
     (hV.integrable one_le_two) hhm (nuisance_measurable μ m A Y gamma)
     (nuisance_condExp μ m A Y hA hY gamma) hV.integrable_sq
     (memLp_one_iff_integrable.mp (hV.mul hh)) (memLp_one_iff_integrable.mp (hV.mul hN))
     hh.integrable_sq hN.integrable_sq (memLp_one_iff_integrable.mp (hN.mul hh))

 include hm in
 theorem fixed_gamma_minimizes (A Y : Ω→ℝ) (hA : MemLp A 2 μ) (hY : MemLp Y 2 μ)
     (gamma : ℝ) (h : Ω→ℝ) (hh : MemLp h 2 μ) (hhm : StronglyMeasurable[m] h) :
     profiledLoss μ m A Y gamma ≤ leastSquaresLoss μ A Y gamma h := by
   rw [fixed_gamma_loss_decomposition μ m hm A Y hA hY gamma h hh hhm]
   exact le_add_of_nonneg_right (integral_nonneg (fun x=>sq_nonneg _))

 omit [IsProbabilityMeasure μ] hm in
 theorem quadratic_integral (f g : Ω→ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (gamma : ℝ) :
     (∫ x,(f x-gamma*g x)^2 ∂μ)=
       (∫ x,(f x)^2 ∂μ)-2*gamma*(∫ x,f x*g x ∂μ)+gamma^2*(∫ x,(g x)^2 ∂μ) := by
   have hfg : Integrable (fun x=>f x*g x) μ:=memLp_one_iff_integrable.mp (hf.mul hg)
   have he : (fun x=>(f x-gamma*g x)^2)=fun x=>(f x)^2-(2*gamma)*(f x*g x)+gamma^2*(g x)^2:=by
     funext x;ring
   rw [he,integral_add (f:=fun x=>f x^2-(2*gamma)*(f x*g x))
     (g:=fun x=>gamma^2*g x^2)
     (hf.integrable_sq.sub (hfg.const_mul (2*gamma))) (hg.integrable_sq.const_mul (gamma^2)),
     integral_sub (f:=fun x=>f x^2) (g:=fun x=>(2*gamma)*(f x*g x))
       hf.integrable_sq (hfg.const_mul (2*gamma)),integral_const_mul,integral_const_mul]

 include hm in
 theorem profiled_loss_quadratic (A Y : Ω→ℝ) (hA : MemLp A 2 μ) (hY : MemLp Y 2 μ) (gamma : ℝ) :
     profiledLoss μ m A Y gamma=varianceMean μ m Y-2*gamma*covarianceMean μ m A Y+
       gamma^2*varianceMean μ m A := by
   let f:=Y-μ[Y|m]
   let g:=A-μ[A|m]
   have hf : MemLp f 2 μ:=hY.sub (hY.condExp one_le_two)
   have hg : MemLp g 2 μ:=hA.sub (hA.condExp one_le_two)
   have he : profiledLoss μ m A Y gamma=∫ x,(f x-gamma*g x)^2 ∂μ:=by
     unfold profiledLoss leastSquaresLoss nuisance
     congr 1
     funext x
     dsimp [f,g]
     congr 1
     ring
   rw [he,quadratic_integral μ f g hf hg gamma]
   unfold varianceMean covarianceMean ConditionalExamples.conditionalCovariance condVar
   rw [integral_condExp hm,integral_condExp hm,integral_condExp hm]
   dsimp [f,g]
   simp only [mul_comm]

 include hm in
 theorem profiled_loss_completed_square (A Y : Ω→ℝ) (hA : MemLp A 2 μ) (hY : MemLp Y 2 μ)
     (hden : 0<varianceMean μ m A) (gamma : ℝ) :
     profiledLoss μ m A Y gamma=profiledLoss μ m A Y (optimalCoefficient μ m A Y)+
       varianceMean μ m A*(gamma-optimalCoefficient μ m A Y)^2 := by
   rw [profiled_loss_quadratic μ m hm A Y hA hY gamma,
     profiled_loss_quadratic μ m hm A Y hA hY (optimalCoefficient μ m A Y)]
   unfold optimalCoefficient
   field_simp [hden.ne']
   ring

 include hm in
 theorem joint_loss_decomposition (A Y : Ω→ℝ) (hA : MemLp A 2 μ) (hY : MemLp Y 2 μ)
     (hden : 0<varianceMean μ m A) (gamma : ℝ) (h : Ω→ℝ)
     (hh : MemLp h 2 μ) (hhm : StronglyMeasurable[m] h) :
     leastSquaresLoss μ A Y gamma h=profiledLoss μ m A Y (optimalCoefficient μ m A Y)+
       varianceMean μ m A*(gamma-optimalCoefficient μ m A Y)^2+
       ∫ x,(nuisance μ m A Y gamma x-h x)^2 ∂μ := by
   rw [fixed_gamma_loss_decomposition μ m hm A Y hA hY gamma h hh hhm,
     profiled_loss_completed_square μ m hm A Y hA hY hden gamma]

 include hm in
 theorem overlap_coefficient_minimizes (A Y : Ω→ℝ) (hA : MemLp A 2 μ) (hY : MemLp Y 2 μ)
     (hden : 0<varianceMean μ m A) (gamma : ℝ) (h : Ω→ℝ)
     (hh : MemLp h 2 μ) (hhm : StronglyMeasurable[m] h) :
     leastSquaresLoss μ A Y (optimalCoefficient μ m A Y)
       (nuisance μ m A Y (optimalCoefficient μ m A Y)) ≤ leastSquaresLoss μ A Y gamma h := by
   rw [joint_loss_decomposition μ m hm A Y hA hY hden gamma h hh hhm]
   change profiledLoss μ m A Y (optimalCoefficient μ m A Y) ≤ _
   have hterm : 0 ≤ varianceMean μ m A*(gamma-optimalCoefficient μ m A Y)^2:=mul_nonneg hden.le (sq_nonneg _)
   have hrem : 0 ≤ ∫ x,(nuisance μ m A Y gamma x-h x)^2 ∂μ:=integral_nonneg (fun _=>sq_nonneg _)
   linarith



include hm in
/-- Equality with the optimal loss forces the unique coefficient and the
profiled nuisance, with nuisance functions identified almost everywhere. -/
theorem optimizer_characterization (A Y : Ω→ℝ) (hA : MemLp A 2 μ) (hY : MemLp Y 2 μ)
    (hden : 0<varianceMean μ m A) (gamma : ℝ) (h : Ω→ℝ)
    (hh : MemLp h 2 μ) (hhm : StronglyMeasurable[m] h)
    (he : leastSquaresLoss μ A Y gamma h=profiledLoss μ m A Y (optimalCoefficient μ m A Y)) :
    gamma=optimalCoefficient μ m A Y ∧ h=ᵐ[μ] nuisance μ m A Y gamma := by
  have hd:=joint_loss_decomposition μ m hm A Y hA hY hden gamma h hh hhm
  have hn:0 ≤ ∫ x,(nuisance μ m A Y gamma x-h x)^2 ∂μ:=integral_nonneg (fun _=>sq_nonneg _)
  have hs:0 ≤ varianceMean μ m A*(gamma-optimalCoefficient μ m A Y)^2:=
    mul_nonneg hden.le (sq_nonneg _)
  have hg:gamma=optimalCoefficient μ m A Y:=by
    have hsq:(gamma-optimalCoefficient μ m A Y)^2=0:=by nlinarith
    nlinarith [sq_nonneg (gamma-optimalCoefficient μ m A Y)]
  refine ⟨hg,?_⟩
  have hzero:(∫ x,(nuisance μ m A Y gamma x-h x)^2 ∂μ)=0:=by
    have hs0:varianceMean μ m A*(gamma-optimalCoefficient μ m A Y)^2=0:=by rw [hg];ring
    rw [he,hs0,add_zero] at hd
    linarith
  have hi:=((nuisance_memLp μ m A Y hA hY gamma).sub hh).integrable_sq
  have hz: (fun x=>(nuisance μ m A Y gamma x-h x)^2)=ᵐ[μ] fun _=>0:=
    (integral_eq_zero_iff_of_nonneg (fun _=>sq_nonneg _) hi).mp hzero
  filter_upwards [hz] with x hx
  nlinarith [sq_nonneg (nuisance μ m A Y gamma x-h x)]

omit [IsProbabilityMeasure μ] hm in
/-- The profiled optimum is an actual measurable function of the covariate. -/
 theorem nuisance_factors_through {E : Type*} [MeasurableSpace E]
     (X : Ω→E) (A Y : Ω→ℝ) (gamma : ℝ) :
     ∃ h : E→ℝ, StronglyMeasurable h ∧
       nuisance μ (MeasurableSpace.comap X inferInstance) A Y gamma=h∘X := by
   exact (nuisance_measurable μ (MeasurableSpace.comap X inferInstance) A Y gamma).exists_eq_measurable_comp (mY:=inferInstance) (f:=X)

/-- Literal overlap effect, optimized over every measurable square-integrable
covariate nuisance, with the optimum also in that unrestricted class. -/
 theorem effect_is_unrestricted_least_squares_optimum (Q : Model.Parameters)
     (ε : ℝ) (hε : 0<ε) (hεhalf : ε<1/2)
     (P : ProbabilityMeasure (Model.Covariate Q.d×Response)) (W : Witness Q ε P) :
     ∃ hopt : Model.Covariate Q.d→ℝ, StronglyMeasurable hopt ∧
       MemLp (hopt∘Prod.fst) 2 (P:Measure (Model.Covariate Q.d×Response)) ∧
       ∀ (gamma : ℝ) (h : Model.Covariate Q.d→ℝ),
         StronglyMeasurable h → MemLp (h∘Prod.fst) 2 (P:Measure (Model.Covariate Q.d×Response)) →
         leastSquaresLoss (P:Measure (Model.Covariate Q.d×Response))
           (treatment∘Prod.snd) (outcome∘Prod.snd) (effect Q.d P) (hopt∘Prod.fst) ≤
         leastSquaresLoss (P:Measure (Model.Covariate Q.d×Response))
           (treatment∘Prod.snd) (outcome∘Prod.snd) gamma (h∘Prod.fst) := by
   let ν : Measure (Model.Covariate Q.d×Response):=P
   let info : MeasurableSpace (Model.Covariate Q.d×Response):=MeasurableSpace.comap Prod.fst inferInstance
   let : MeasurableSpace (Model.Covariate Q.d×Response):=
     (inferInstance : MeasurableSpace (Model.Covariate Q.d)).prod (inferInstance : MeasurableSpace Response)
   let a : Model.Covariate Q.d×Response→ℝ:=treatment∘Prod.snd
   let y : Model.Covariate Q.d×Response→ℝ:=outcome∘Prod.snd
   have hm : info ≤ (inferInstance : MeasurableSpace (Model.Covariate Q.d×Response)):=(measurable_fst : Measurable (Prod.fst : Model.Covariate Q.d×Response→Model.Covariate Q.d)).comap_le
   have ha : MemLp a 2 ν:=bounded_memLp ν a (treatment_measurable.comp measurable_snd) 1
     (fun o=>treatment_bound o.2)
   have hy : MemLp y 2 ν:=bounded_memLp ν y (outcome_measurable.comp measurable_snd) 1
     (fun o=>outcome_bound o.2)
   have hden : 0<varianceMean ν info a:=
     (mul_pos hε (by linarith : 0<1-ε)).trans_le (denominator_bounds Q ε hε hεhalf P W).1
   obtain ⟨hopt,hoptm,he⟩:=nuisance_factors_through ν Prod.fst a y (effect Q.d P)
   refine ⟨hopt,hoptm,?_,?_⟩
   · rw [← he]
     exact nuisance_memLp ν info a y ha hy _
   · intro gamma h hh hhL
     rw [← he]
     exact overlap_coefficient_minimizes ν info hm a y ha hy hden gamma (h∘Prod.fst) hhL
       (hh.comp_measurable (Measurable.of_comap_le le_rfl))

end RoughRegime.Applications.Overlap
