module

public import RoughRegime.CausalTreatment
public import RoughRegime.ApplicationEffects
public import RoughRegime.ApplicationOverlapProjection


@[expose] public section
/-! Conditional-exchangeability identification of the actual overlap effect. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Expected conditional covariance is invariant under an actual observation
map, when the conditioning information is pulled back along that map. -/
theorem covarianceMean_map {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω→E) (hT : Measurable T)
    (m : MeasurableSpace E) (hm : m ≤ mE) (f g : E→ℝ)
    (hf : Measurable[mE] f) (hg : Measurable[mE] g)
    (hfL : MemLp f 2 (@Measure.map Ω E mΩ mE T μ)) (hgL : MemLp g 2 (@Measure.map Ω E mΩ mE T μ))
    (hfT : MemLp (f∘T) 2 μ) (hgT : MemLp (g∘T) 2 μ) :
    Applications.Overlap.covarianceMean (@Measure.map Ω E mΩ mE T μ) m f g=
      Applications.Overlap.covarianceMean μ (MeasurableSpace.comap T m) (f∘T) (g∘T) := by
  let : MeasurableSpace Ω:=mΩ
  let : MeasurableSpace E:=mE
  have hmT : MeasurableSpace.comap T m ≤ mΩ:=
    (MeasurableSpace.comap_mono hm).trans hT.comap_le
  unfold Applications.Overlap.covarianceMean
  rw [ConditionalExamples.mean_conditional_covariance hm f g (μ:=@Measure.map Ω E mΩ mE T μ) hfL hgL,
    ConditionalExamples.mean_conditional_covariance hmT (f∘T) (g∘T) (μ:=μ) hfT hgT,
    integral_map (f:=fun x=>f x*g x) hT.aemeasurable (hf.mul hg).aestronglyMeasurable,
    integral_map (f:=fun x=>(@Measure.map Ω E mΩ mE T μ)[f|m] x*(@Measure.map Ω E mΩ mE T μ)[g|m] x) hT.aemeasurable
      (((stronglyMeasurable_condExp (μ:=@Measure.map Ω E mΩ mE T μ) (m:=m) (f:=f)).mono hm).mul
        ((stronglyMeasurable_condExp (μ:=@Measure.map Ω E mΩ mE T μ) (m:=m) (f:=g)).mono hm)).aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  filter_upwards [condExp_map_pullback μ T hT m hm f hf (hfT.integrable one_le_two),
    condExp_map_pullback μ T hT m hm g hg (hgT.integrable one_le_two)] with ω hfe hge
  exact congrArg₂ (fun a b : ℝ=>a*b) hfe hge

/-- The analogous invariance for expected conditional variance. -/
theorem varianceMean_map {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω→E) (hT : Measurable T)
    (m : MeasurableSpace E) (hm : m ≤ mE) (f : E→ℝ)
    (hf : Measurable[mE] f) (hfL : MemLp f 2 (@Measure.map Ω E mΩ mE T μ)) (hfT : MemLp (f∘T) 2 μ) :
    Applications.Overlap.varianceMean (@Measure.map Ω E mΩ mE T μ) m f=
      Applications.Overlap.varianceMean μ (MeasurableSpace.comap T m) (f∘T) := by
  let : MeasurableSpace Ω:=mΩ
  let : MeasurableSpace E:=mE
  have hmT : MeasurableSpace.comap T m ≤ mΩ:=
    (MeasurableSpace.comap_mono hm).trans hT.comap_le
  unfold Applications.Overlap.varianceMean
  rw [ConditionalExamples.mean_conditional_variance hm f (μ:=@Measure.map Ω E mΩ mE T μ) hfL,
    ConditionalExamples.mean_conditional_variance hmT (f∘T) (μ:=μ) hfT,
    integral_map (f:=fun x=>f x^2) hT.aemeasurable (hf.pow_const 2).aestronglyMeasurable,
    integral_map (f:=fun x=>(@Measure.map Ω E mΩ mE T μ)[f|m] x^2) hT.aemeasurable
      (((stronglyMeasurable_condExp (μ:=@Measure.map Ω E mΩ mE T μ) (m:=m) (f:=f)).mono hm).pow 2).aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  filter_upwards [condExp_map_pullback μ T hT m hm f hf (hfT.integrable one_le_two)] with ω hfe
  exact congrArg (fun a : ℝ=>a^2) hfe

theorem regression_potential_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (d : ℕ) (P : ProbabilityMeasure Ω) (j : Bool)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y potential : Ω→Applications.MAR.Outcome)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) (hp : Measurable potential)
    (hconsistency : ∀ᵐ ω ∂(P:Measure Ω),A ω=j→Y ω=potential ω)
    (hexchangeability : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A potential (P:Measure Ω))
    (hpositive : ∀ᵐ ω ∂(P:Measure Ω),
      (P:Measure Ω)[binaryIndicator j∘A|MeasurableSpace.comap X inferInstance] ω≠0) :
    Applications.MAR.regression d j (P.map (treatmentObservation d X A Y))∘
      treatmentObservation d X A Y=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[(fun ω=>(potential ω:ℝ))|MeasurableSpace.comap X inferInstance] := by
  let μ := (P:Measure Ω)
  let T := treatmentObservation d X A Y
  let m : MeasurableSpace (Model.Covariate d×Applications.MAR.TreatmentResponse) :=
    MeasurableSpace.comap Prod.fst inferInstance
  let info := MeasurableSpace.comap X inferInstance
  let r := binaryIndicator j∘A
  let y : Ω→ℝ := fun ω=>(Y ω:ℝ)
  let p : Ω→ℝ := fun ω=>(potential ω:ℝ)
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace (Model.Covariate d×Applications.MAR.TreatmentResponse) :=
    (inferInstance : MeasurableSpace (Model.Covariate d)).prod (inferInstance : MeasurableSpace Applications.MAR.TreatmentResponse)
  have hT : Measurable T := treatmentObservation_measurable d X A Y hX hA hY
  have hr : Measurable r := (binaryIndicator_measurable j).comp hA
  have hy : Measurable y := measurable_subtype_coe.comp hY
  have hp' : Measurable p := measurable_subtype_coe.comp hp
  have hir : Integrable r μ := Integrable.of_mem_Icc 0 1 hr.aemeasurable
    (Eventually.of_forall (fun ω=>binaryIndicator_range j (A ω)))
  have hip : Integrable p μ := Integrable.of_mem_Icc 0 1 hp'.aemeasurable
    (Eventually.of_forall (fun ω=>(potential ω).property))
  have hiry : Integrable (fun ω=>r ω*y ω) μ :=
    hir.mul_bdd (c:=1) hy.aestronglyMeasurable (Eventually.of_forall (fun ω=>by
      simpa only [y,Real.norm_eq_abs,abs_of_nonneg (Y ω).property.1] using (Y ω).property.2))
  have hirp : Integrable (fun ω=>r ω*p ω) μ :=
    hir.mul_bdd (c:=1) hp'.aestronglyMeasurable (Eventually.of_forall (fun ω=>by
      simpa only [p,Real.norm_eq_abs,abs_of_nonneg (potential ω).property.1] using (potential ω).property.2))
  have hv : (Applications.MAR.armOutcome j∘Prod.snd)∘T=(fun ω=>r ω*y ω) := rfl
  have hd : (Applications.MAR.armIndicator j∘Prod.snd)∘T=r := rfl
  have hinfo : MeasurableSpace.comap T m=info := by rw [MeasurableSpace.comap_comp];rfl
  have hV : Integrable ((Applications.MAR.armOutcome j∘Prod.snd)∘T) μ := by rw [hv];exact hiry
  have hD : Integrable ((Applications.MAR.armIndicator j∘Prod.snd)∘T) μ := by rw [hd];exact hir
  have heV:=condExp_map_pullback μ T hT m measurable_fst.comap_le
    (Applications.MAR.armOutcome j∘Prod.snd)
    ((Applications.MAR.armOutcome_measurable j).comp measurable_snd) hV
  have heD:=condExp_map_pullback μ T hT m measurable_fst.comap_le
    (Applications.MAR.armIndicator j∘Prod.snd)
    ((Applications.MAR.armIndicator_measurable j).comp measurable_snd) hD
  rw [hv,hinfo] at heV
  rw [hd,hinfo] at heD
  have hi : CondIndepFun info hX.comap_le r p μ :=
    hexchangeability.comp (binaryIndicator_measurable j) measurable_subtype_coe
  have hc : (fun ω=>r ω*y ω)=ᵐ[μ] fun ω=>r ω*p ω := by
    filter_upwards [hconsistency] with ω hω
    by_cases h : A ω=j
    · simp only [r,binaryIndicator,Function.comp_apply,h,ite_true,y,p,hω h]
    · simp only [r,binaryIndicator,Function.comp_apply,h,ite_false,zero_mul]
  have he:=selection_conditional_identification μ info hX.comap_le r y p hr hp' hir hip hirp hc hi hpositive
  filter_upwards [heV,heD,he] with ω hV hD he
  change ((μ.map T)[Applications.MAR.armOutcome j∘Prod.snd|m]∘T) ω /
    ((μ.map T)[Applications.MAR.armIndicator j∘Prod.snd|m]∘T) ω=μ[p|info] ω
  rw [hV,hD]
  exact he


/-- Algebra of the actual conditional covariance and variance of a binary
exposure, after the conditional potential-outcome identities are established. -/
theorem binary_potential_covariance {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (a y p0 p1 : Ω→ℝ) (ha : MemLp a 2 μ) (hy : MemLp y 2 μ)
    (habinary : ∀ᵐ ω ∂μ,a ω^2=a ω)
    (hap1 : μ[(fun ω=>a ω*y ω)|m]=ᵐ[μ] fun ω=>μ[a|m] ω*μ[p1|m] ω)
    (hymean : μ[y|m]=ᵐ[μ] fun ω=>μ[a|m] ω*μ[p1|m] ω+(1-μ[a|m] ω)*μ[p0|m] ω) :
    Applications.Overlap.covarianceMean μ m a y=
      ∫ ω,μ[a|m] ω*(1-μ[a|m] ω)*(μ[p1|m] ω-μ[p0|m] ω) ∂μ ∧
    Applications.Overlap.varianceMean μ m a=
      ∫ ω,μ[a|m] ω*(1-μ[a|m] ω) ∂μ := by
  let : MeasurableSpace Ω:=mΩ
  have haw := ha.condExp (m:=m) one_le_two
  have hym := hy.condExp (m:=m) one_le_two
  have hiwy : Integrable (fun ω=>μ[a|m] ω*μ[y|m] ω) μ:=
    memLp_one_iff_integrable.mp (haw.mul hym)
  constructor
  · unfold Applications.Overlap.covarianceMean
    rw [ConditionalExamples.mean_conditional_covariance hm a y ha hy,
      ← integral_condExp hm (f:=fun ω=>a ω*y ω),
      ← integral_sub (f:=μ[(fun ω=>a ω*y ω)|m])
        (g:=fun ω=>μ[a|m] ω*μ[y|m] ω) integrable_condExp hiwy]
    apply integral_congr_ae
    filter_upwards [hap1,hymean] with ω h1 h2
    change μ[(fun ω=>a ω*y ω)|m] ω-μ[a|m] ω*μ[y|m] ω=_
    rw [h1,h2]
    ring
  · unfold Applications.Overlap.varianceMean
    rw [ConditionalExamples.mean_conditional_variance hm a ha,
      integral_congr_ae habinary,← integral_condExp hm (f:=a),
      ← integral_sub (f:=μ[a|m]) (g:=fun ω=>μ[a|m] ω^2)
        integrable_condExp haw.integrable_sq]
    apply integral_congr_ae
    filter_upwards with ω
    ring

/-- Consistency and genuine conditional independence imply the conditional
outcome mixture, without an affine model for the observed regression. -/
theorem conditional_outcome_mixture {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (a y p0 p1 : Ω→ℝ)
    (ha : Measurable[mΩ] a) (h0 : Measurable[mΩ] p0) (h1 : Measurable[mΩ] p1)
    (haL : MemLp a 2 μ) (h0L : MemLp p0 2 μ) (h1L : MemLp p1 2 μ)
    (hc : y=ᵐ[μ] fun ω=>a ω*p1 ω-a ω*p0 ω+p0 ω)
    (hi0 : CondIndepFun m hm a p0 μ) (hi1 : CondIndepFun m hm a p1 μ) :
    μ[y|m]=ᵐ[μ] fun ω=>μ[a|m] ω*μ[p1|m] ω+(1-μ[a|m] ω)*μ[p0|m] ω := by
  let : MeasurableSpace Ω:=mΩ
  have hprod0 : Integrable (fun ω=>a ω*p0 ω) μ:=memLp_one_iff_integrable.mp (haL.mul h0L)
  have hprod1 : Integrable (fun ω=>a ω*p1 ω) μ:=memLp_one_iff_integrable.mp (haL.mul h1L)
  have he0:=condExp_product_of_condIndep μ m hm a p0 ha h0
    (haL.integrable one_le_two) (h0L.integrable one_le_two) hprod0 hi0
  have he1:=condExp_product_of_condIndep μ m hm a p1 ha h1
    (haL.integrable one_le_two) (h1L.integrable one_le_two) hprod1 hi1
  have hs:=condExp_sub hprod1 hprod0 m
  have hp:=condExp_add (hprod1.sub hprod0) (h0L.integrable one_le_two) m
  have he:=condExp_congr_ae hc (m:=m)
  filter_upwards [he,hs,hp,he0,he1] with ω he hs hp h0 h1
  rw [he]
  change μ[((fun ω=>a ω*p1 ω)-(fun ω=>a ω*p0 ω))+p0|m] ω=_
  rw [hp]
  change μ[(fun ω=>a ω*p1 ω)-(fun ω=>a ω*p0 ω)|m] ω+μ[p0|m] ω=_
  rw [hs]
  change μ[(fun ω=>a ω*p1 ω)|m] ω-μ[(fun ω=>a ω*p0 ω)|m] ω+μ[p0|m] ω=_
  rw [h0,h1]
  ring


/-- Literal observed-law covariance and variance identify the overlap-weighted
conditional treatment effect under consistency and conditional exchangeability. -/
theorem overlap_potential_moments {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (d : ℕ) (P : ProbabilityMeasure Ω)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y Y0 Y1 : Ω→Applications.MAR.Outcome)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y)
    (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hconsistency : ∀ᵐ ω ∂(P:Measure Ω),Y ω=if A ω then Y1 ω else Y0 ω)
    (hexchangeability : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le
      A (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω)) :
    let w:=(P:Measure Ω)[binaryIndicator true∘A|MeasurableSpace.comap X inferInstance]
    let t0:=(P:Measure Ω)[(fun ω=>(Y0 ω:ℝ))|MeasurableSpace.comap X inferInstance]
    let t1:=(P:Measure Ω)[(fun ω=>(Y1 ω:ℝ))|MeasurableSpace.comap X inferInstance]
    Applications.Overlap.numerator d (P.map (treatmentObservation d X A Y))=
      ∫ ω,w ω*(1-w ω)*(t1 ω-t0 ω) ∂(P:Measure Ω) ∧
    Applications.Overlap.denominator d (P.map (treatmentObservation d X A Y))=
      ∫ ω,w ω*(1-w ω) ∂(P:Measure Ω) := by
  let μ:Measure Ω:=P
  let T:=treatmentObservation d X A Y
  let info:MeasurableSpace Ω:=MeasurableSpace.comap X inferInstance
  let m:MeasurableSpace (Model.Covariate d×Applications.Overlap.Response):=
    MeasurableSpace.comap Prod.fst inferInstance
  let :MeasurableSpace Ω:=mΩ
  let :MeasurableSpace (Model.Covariate d×Applications.Overlap.Response):=
    (inferInstance:MeasurableSpace (Model.Covariate d)).prod
      (inferInstance:MeasurableSpace Applications.Overlap.Response)
  let a:=binaryIndicator true∘A
  let y:Ω→ℝ:=fun ω=>(Y ω:ℝ)
  let p0:Ω→ℝ:=fun ω=>(Y0 ω:ℝ)
  let p1:Ω→ℝ:=fun ω=>(Y1 ω:ℝ)
  let f:Model.Covariate d×Applications.Overlap.Response→ℝ:=Applications.Overlap.treatment∘Prod.snd
  let g:Model.Covariate d×Applications.Overlap.Response→ℝ:=Applications.Overlap.outcome∘Prod.snd
  have hT:Measurable T:=treatmentObservation_measurable d X A Y hX hA hY
  have hm:m ≤ (inferInstance:MeasurableSpace (Model.Covariate d×Applications.Overlap.Response)):=
    (measurable_fst:Measurable (Prod.fst:Model.Covariate d×Applications.Overlap.Response→Model.Covariate d)).comap_le
  have hinfo:MeasurableSpace.comap T m=info:=by rw [MeasurableSpace.comap_comp];rfl
  have ha:Measurable a:=(binaryIndicator_measurable true).comp hA
  have hp0:Measurable p0:=measurable_subtype_coe.comp hY0
  have hp1:Measurable p1:=measurable_subtype_coe.comp hY1
  have haL:MemLp a 2 μ:=Applications.bounded_memLp μ a ha 1 fun ω=>by
    change |binaryIndicator true (A ω)|≤1
    rw [abs_of_nonneg (binaryIndicator_range true (A ω)).1]
    exact (binaryIndicator_range true (A ω)).2
  have hyL:MemLp y 2 μ:=Applications.bounded_memLp μ y (measurable_subtype_coe.comp hY) 1 fun ω=>by
    rw [abs_of_nonneg (Y ω).property.1];exact (Y ω).property.2
  have h0L:MemLp p0 2 μ:=Applications.bounded_memLp μ p0 hp0 1 fun ω=>by
    rw [abs_of_nonneg (Y0 ω).property.1];exact (Y0 ω).property.2
  have h1L:MemLp p1 2 μ:=Applications.bounded_memLp μ p1 hp1 1 fun ω=>by
    rw [abs_of_nonneg (Y1 ω).property.1];exact (Y1 ω).property.2
  have hf:Measurable f:=Applications.Overlap.treatment_measurable.comp measurable_snd
  have hg:Measurable g:=Applications.Overlap.outcome_measurable.comp measurable_snd
  have hfL:MemLp f 2 (μ.map T):=Applications.bounded_memLp (μ.map T) f hf 1
    (fun o=>Applications.Overlap.treatment_bound o.2)
  have hgL:MemLp g 2 (μ.map T):=Applications.bounded_memLp (μ.map T) g hg 1
    (fun o=>Applications.Overlap.outcome_bound o.2)
  have hi0:CondIndepFun info hX.comap_le a p0 μ:=
    (hexchangeability.comp measurable_id measurable_fst).comp
      (binaryIndicator_measurable true) measurable_subtype_coe
  have hi1:CondIndepFun info hX.comap_le a p1 μ:=
    (hexchangeability.comp measurable_id measurable_snd).comp
      (binaryIndicator_measurable true) measurable_subtype_coe
  have hc:y=ᵐ[μ] fun ω=>a ω*p1 ω-a ω*p0 ω+p0 ω:=by
    filter_upwards [hconsistency] with ω hω
    cases he:A ω <;> simp [y,a,p0,p1,binaryIndicator,he] at hω ⊢ <;> rw [hω]
  have hc1:(fun ω=>a ω*y ω)=ᵐ[μ] fun ω=>a ω*p1 ω:=by
    filter_upwards [hconsistency] with ω hω
    cases he:A ω <;> simp [y,a,p1,binaryIndicator,he] at hω ⊢
    exact congrArg (fun z:Applications.MAR.Outcome=>(z:ℝ)) hω
  have hproduct:=selection_conditional_product μ info hX.comap_le a y p1 ha hp1
    (haL.integrable one_le_two) (h1L.integrable one_le_two)
    (memLp_one_iff_integrable.mp (haL.mul h1L)) hc1 hi1
  have hmean:=conditional_outcome_mixture μ info hX.comap_le a y p0 p1 ha hp0 hp1
    haL h0L h1L hc hi0 hi1
  have hbinary:∀ᵐ ω ∂μ,a ω^2=a ω:=Eventually.of_forall fun ω=>by
    cases he:A ω <;> simp [a,binaryIndicator,he]
  have hresult:=binary_potential_covariance μ info hX.comap_le a y p0 p1 haL hyL hbinary hproduct hmean
  have hN:Applications.Overlap.numerator d (P.map T)=Applications.Overlap.covarianceMean μ info a y:=by
    change Applications.Overlap.covarianceMean (μ.map T) m f g=_
    rw [covarianceMean_map μ T hT m hm f g hf hg hfL hgL haL hyL,hinfo]
    rfl
  have hD:Applications.Overlap.denominator d (P.map T)=Applications.Overlap.varianceMean μ info a:=by
    change Applications.Overlap.varianceMean (μ.map T) m f=_
    rw [varianceMean_map μ T hT m hm f hf hfL haL,hinfo]
    rfl
  exact ⟨hN.trans hresult.1,hD.trans hresult.2⟩

/-- The source's overlap-weighted causal effect, on the actual observed law. -/
theorem overlap_effect_potential_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (d : ℕ) (P : ProbabilityMeasure Ω)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y Y0 Y1 : Ω→Applications.MAR.Outcome)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y)
    (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hconsistency : ∀ᵐ ω ∂(P:Measure Ω),Y ω=if A ω then Y1 ω else Y0 ω)
    (hexchangeability : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le
      A (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω)) :
    let w:=(P:Measure Ω)[binaryIndicator true∘A|MeasurableSpace.comap X inferInstance]
    let t0:=(P:Measure Ω)[(fun ω=>(Y0 ω:ℝ))|MeasurableSpace.comap X inferInstance]
    let t1:=(P:Measure Ω)[(fun ω=>(Y1 ω:ℝ))|MeasurableSpace.comap X inferInstance]
    Applications.Overlap.effect d (P.map (treatmentObservation d X A Y))=
      (∫ ω,w ω*(1-w ω)*(t1 ω-t0 ω) ∂(P:Measure Ω)) /
      (∫ ω,w ω*(1-w ω) ∂(P:Measure Ω)) := by
  have h:=overlap_potential_moments d P X A Y Y0 Y1 hX hA hY hY0 hY1 hconsistency hexchangeability
  unfold Applications.Overlap.effect
  rw [h.1,h.2]

end RoughRegime.Causal
