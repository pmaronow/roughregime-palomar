module

public import RoughRegime.ApplicationTransport
public import RoughRegime.ModelUpperConsequences
public import RoughRegime.ModelBasicUpper


@[expose] public section
/-! The upper bounds also permit the response observables to depend measurably
on the design coordinate. We prove this by duplicating the observed covariate
inside the response space. Conditional moments and the actual functional are
transported, and the deterministic observation kernel preserves every sample.
No independent design/response assumption is introduced. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Model
universe u
set_option backward.isDefEq.respectTransparency false

 def covariateLift (A : Parameters) {Z : Type*} (o : Observation A Z) :
     Observation A (Observation A Z) := (o.1,o)

 theorem covariateLift_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z] :
     Measurable (covariateLift (Z:=Z) A) := measurable_fst.prodMk measurable_id

 def covariateLiftLaw (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (P : ProbabilityMeasure (Observation A Z)) : ProbabilityMeasure (Observation A (Observation A Z)) :=
   P.map (covariateLift A)

 structure CovariateDependentWitness (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables (Observation A Z) A) (P : ProbabilityMeasure (Observation A Z)) where
   p : Covariate A.d→ℝ
   w : Covariate A.d→ℝ
   a : Covariate A.d→ℝ
   b : Covariate A.d→ℝ
   measurableP : Measurable p
   measurableW : Measurable w
   measurableA : Measurable a
   measurableB : Measurable b
   nonnegativeP : 0≤ᵐ[cubeVolume A.d] p
   marginal : (P:Measure (Observation A Z)).map Prod.fst=
     (cubeVolume A.d).withDensity (fun x=>ENNReal.ofReal (p x))
   momentD : (P:Measure (Observation A Z))[F.D|covariateInformation A Z]=ᵐ[(P:Measure (Observation A Z))] w∘Prod.fst
   momentU : (P:Measure (Observation A Z))[F.U|covariateInformation A Z]=ᵐ[(P:Measure (Observation A Z))] fun o=>w o.1*a o.1
   momentV : (P:Measure (Observation A Z))[F.V|covariateInformation A Z]=ᵐ[(P:Measure (Observation A Z))] fun o=>w o.1*b o.1
   overlap : ∀ᵐx ∂cubeVolume A.d,A.δ≤w x
   smoothA : a∈holderBall A.α A.H
   smoothB : b∈holderBall A.β A.H
   densityBounds : ∀ᵐx ∂cubeVolume A.d,A.gminus≤w x*p x ∧ w x*p x≤A.gplus

 def covariateDependentClass (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables (Observation A Z) A) : Set (ProbabilityMeasure (Observation A Z)) :=
   {P|Nonempty (CovariateDependentWitness A F P)}

 def covariateDependentTarget (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables (Observation A Z) A) (P : ProbabilityMeasure (Observation A Z)) : ℝ :=
   (∫o,F.W o ∂(P:Measure (Observation A Z)))+F.lam*∫o,
     ((P:Measure (Observation A Z))[F.U|covariateInformation A Z]) o*
       ((P:Measure (Observation A Z))[F.V|covariateInformation A Z]) o/
         ((P:Measure (Observation A Z))[F.D|covariateInformation A Z]) o ∂(P:Measure (Observation A Z))

 theorem covariateLift_conditional (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (P : ProbabilityMeasure (Observation A Z)) (f : Observation A Z→ℝ)
     (hf : Measurable f) (hfi : Integrable f (P:Measure (Observation A Z)))
     (g : Covariate A.d→ℝ) (hg : Measurable g)
     (hc : (P:Measure (Observation A Z))[f|covariateInformation A Z]=ᵐ[(P:Measure (Observation A Z))] g∘Prod.fst) :
     (covariateLiftLaw A P:Measure (Observation A (Observation A Z)))[f∘Prod.snd|
       covariateInformation A (Observation A Z)]=ᵐ[(covariateLiftLaw A P:Measure (Observation A (Observation A Z)))] g∘Prod.fst := by
   have hinfo : MeasurableSpace.comap (covariateLift (Z:=Z) A) (covariateInformation A (Observation A Z))=
       covariateInformation A Z := by
     unfold covariateInformation
     rw [MeasurableSpace.comap_comp]
     rfl
   apply Applications.conditional_map (P:Measure (Observation A Z)) (covariateLift A) (covariateLift_measurable A)
     (covariateInformation A (Observation A Z)) measurable_fst.comap_le
     (f∘Prod.snd) (g∘Prod.fst) (hf.comp measurable_snd)
     (hg.comp (measurable_iff_comap_le.mpr le_rfl))
   · exact hfi
   · simpa only [hinfo,Function.comp_def,covariateLift] using hc

 def CovariateDependentWitness.lift {A : Parameters} {Z : Type*} [MeasurableSpace Z]
     {F : Observables (Observation A Z) A} {P : ProbabilityMeasure (Observation A Z)}
     (W : CovariateDependentWitness A F P) : ModelWitness A F (covariateLiftLaw A P) where
   p:=W.p
   w:=W.w
   a:=W.a
   b:=W.b
   measurableP:=W.measurableP
   measurableW:=W.measurableW
   measurableA:=W.measurableA
   measurableB:=W.measurableB
   nonnegativeP:=W.nonnegativeP
   marginal:=by
     change ((P:Measure (Observation A Z)).map (covariateLift A)).map Prod.fst=_
     rw [Measure.map_map measurable_fst (covariateLift_measurable A)]
     exact W.marginal
   momentD:=by
     apply covariateLift_conditional A P F.D F.measurableD
     · apply Integrable.of_bound F.measurableD.aestronglyMeasurable A.M0
       exact ae_of_all _ (fun o=>by rw [Real.norm_eq_abs,abs_of_nonneg (F.boundD o).1];exact (F.boundD o).2)
     · exact W.measurableW
     · exact W.momentD
   momentU:=by
     change _=ᵐ[_] (fun x=>W.w x*W.a x)∘Prod.fst
     apply covariateLift_conditional A P F.U F.measurableU
     · exact Integrable.of_bound F.measurableU.aestronglyMeasurable A.M0
         (ae_of_all _ (fun o=>by simpa only [Real.norm_eq_abs] using F.boundU o))
     · exact W.measurableW.mul W.measurableA
     · exact W.momentU
   momentV:=by
     change _=ᵐ[_] (fun x=>W.w x*W.b x)∘Prod.fst
     apply covariateLift_conditional A P F.V F.measurableV
     · exact Integrable.of_bound F.measurableV.aestronglyMeasurable A.M0
         (ae_of_all _ (fun o=>by simpa only [Real.norm_eq_abs] using F.boundV o))
     · exact W.measurableW.mul W.measurableB
     · exact W.momentV
   overlap:=W.overlap
   smoothA:=W.smoothA
   smoothB:=W.smoothB
   densityBounds:=W.densityBounds

 theorem covariateLift_mem_modelClass (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables (Observation A Z) A) (P : ProbabilityMeasure (Observation A Z))
     (hP : P∈covariateDependentClass A F) : covariateLiftLaw A P∈modelClass A F := by
   obtain ⟨W⟩:=hP
   exact ⟨W.lift⟩

 theorem covariateLift_target (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables (Observation A Z) A) (P : ProbabilityMeasure (Observation A Z))
     (W : CovariateDependentWitness A F P) :
     target A F (covariateLiftLaw A P)=covariateDependentTarget A F P := by
   let Q : Measure (Observation A (Observation A Z)) := covariateLiftLaw A P
   let d := Q[F.D∘Prod.snd|covariateInformation A (Observation A Z)]
   let u := Q[F.U∘Prod.snd|covariateInformation A (Observation A Z)]
   let v := Q[F.V∘Prod.snd|covariateInformation A (Observation A Z)]
   have hd : Measurable d := (stronglyMeasurable_condExp.mono measurable_fst.comap_le).measurable
   have hu : Measurable u := (stronglyMeasurable_condExp.mono measurable_fst.comap_le).measurable
   have hv : Measurable v := (stronglyMeasurable_condExp.mono measurable_fst.comap_le).measurable
   have hratio : (∫o,u o*v o/d o ∂Q)=∫o,
       ((P:Measure (Observation A Z))[F.U|covariateInformation A Z]) o*
         ((P:Measure (Observation A Z))[F.V|covariateInformation A Z]) o/
           ((P:Measure (Observation A Z))[F.D|covariateInformation A Z]) o ∂(P:Measure (Observation A Z)) := by
     change (∫o,u o*v o/d o ∂((P:Measure (Observation A Z)).map (covariateLift A)))=_
     have hm : Measurable (fun o=>u o*v o/d o) := (hu.mul hv).div hd
     rw [integral_map (covariateLift_measurable A).aemeasurable hm.aestronglyMeasurable]
     apply integral_congr_ae
     have hD := ae_of_ae_map (covariateLift_measurable A).aemeasurable W.lift.momentD
     have hU := ae_of_ae_map (covariateLift_measurable A).aemeasurable W.lift.momentU
     have hV := ae_of_ae_map (covariateLift_measurable A).aemeasurable W.lift.momentV
     filter_upwards [hD,hU,hV,W.momentD,W.momentU,W.momentV] with o hD hU hV hD0 hU0 hV0
     dsimp only [Function.comp_apply,covariateLift,CovariateDependentWitness.lift] at hD hU hV
     change d (covariateLift A o)=W.w o.1 at hD
     change u (covariateLift A o)=W.w o.1*W.a o.1 at hU
     change v (covariateLift A o)=W.w o.1*W.b o.1 at hV
     rw [hD,hU,hV,hD0,hU0,hV0]
     rfl
   have hmean : (∫o,F.W o.2 ∂Q)=∫o,F.W o ∂(P:Measure (Observation A Z)) := by
     change (∫o,F.W o.2 ∂((P:Measure (Observation A Z)).map (covariateLift A)))=_
     have hm : Measurable (fun o:Observation A (Observation A Z)=>F.W o.2) := F.measurableW.comp measurable_snd
     rw [integral_map (covariateLift_measurable A).aemeasurable hm.aestronglyMeasurable]
     rfl
   exact congrArg₂ (fun a b:ℝ=>a+F.lam*b) hmean hratio

 def covariateLiftKernel (A : Parameters) (Z : Type*) [MeasurableSpace Z] :
     Kernel (Observation A Z) (Observation A (Observation A Z)) :=
   Kernel.deterministic (covariateLift A) (covariateLift_measurable A)

 instance (A : Parameters) (Z : Type*) [MeasurableSpace Z] : IsMarkovKernel (covariateLiftKernel A Z) := by
   dsimp [covariateLiftKernel]
   infer_instance

 theorem covariateLiftKernel_law (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (P : ProbabilityMeasure (Observation A Z)) : kernelLaw (covariateLiftKernel A Z) P=covariateLiftLaw A P := by
   apply Subtype.ext
   change (covariateLiftKernel A Z)∘ₘ(P:Measure (Observation A Z))=(P:Measure (Observation A Z)).map (covariateLift A)
   simp only [covariateLiftKernel]
   exact Measure.bind_dirac_eq_map _ (covariateLift_measurable A)

 theorem covariate_dependent_risk_transfer (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables (Observation A Z) A) (n : ℕ) :
     minimaxRMSE n (covariateDependentTarget A F) (covariateDependentClass A F)≤
       minimaxRMSE n (target A F) (modelClass A F) := by
   apply (kernel_reduction n (covariateLiftKernel A Z) (covariateDependentTarget A F)
     (target A F) (covariateDependentClass A F) (modelClass A F) ?_ ?_ 0).2
   · intro P hP
     rw [covariateLiftKernel_law]
     exact covariateLift_mem_modelClass A F P hP
   · intro P hP
     rw [covariateLiftKernel_law]
     obtain ⟨W⟩:=hP
     exact covariateLift_target A F P W

 theorem covariate_dependent_uniform_upper (A : Parameters) (L MW : ℝ) :
     ∃C:ℝ,0<C ∧ ∃n0:ℕ,3≤n0 ∧
       ∀(Z:Type u)(_mZ:MeasurableSpace Z)(F:@Observables (Observation A Z) inferInstance A),
       |F.lam|=L → (∀o,|F.W o|≤MW) → ∀n:ℕ,n0≤n →
       (1/2≤A.theta → minimaxRMSE n (covariateDependentTarget A F) (covariateDependentClass A F)≤
         ENNReal.ofReal (C*(n:ℝ)^(-(1/2:ℝ)))) ∧
       (A.theta<1/2 → minimaxRMSE n (covariateDependentTarget A F) (covariateDependentClass A F)≤
         ENNReal.ofReal (C*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*
           (Real.log n)^((A.nu:ℝ)/2+1/4))) := by
   obtain ⟨C,hC,n0,hn0,hupper⟩:=uniformUpperClaim.{u} A L MW
   refine ⟨C,hC,n0,hn0,?_⟩
   intro Z mZ F hL hMW n hn
   have hr := covariate_dependent_risk_transfer A F n
   by_cases hnonempty : (modelClass A F).Nonempty
   · obtain ⟨hcrit,hrough⟩:=hupper (Observation A Z) inferInstance F hL hMW n hn hnonempty
     exact ⟨fun ht=>hr.trans (hcrit ht),fun ht=>hr.trans (hrough ⟨A.theta_pos,ht⟩)⟩
   · have hz : minimaxRMSE n (target A F) (modelClass A F)=0 := by simp [Set.not_nonempty_iff_eq_empty.mp hnonempty,minimaxRMSE]
     rw [hz] at hr
     exact ⟨fun _=>hr.trans bot_le,fun _=>hr.trans bot_le⟩

 theorem covariate_dependent_uniform_basic_upper (A : Parameters) (L MW : ℝ) :
     ∃C:ℝ,0<C ∧
       ∀(Z:Type u)(_mZ:MeasurableSpace Z)(F:@Observables (Observation A Z) inferInstance A),
       |F.lam|=L → (∀o,|F.W o|≤MW) → ∀n:ℕ,3≤n →
       ∃E:Estimator (Observation A Z) n,
       ∀P∈covariateDependentClass A F,
         eLpNorm (fun o=>E.val o-covariateDependentTarget A F P) 2 (randomizedExperiment n P)≤
           ENNReal.ofReal (C*basicUpperScale A n) := by
   obtain ⟨C,hC,hupper⟩:=uniform_basic_upper.{u} A L MW
   refine ⟨2*C,by positivity,?_⟩
   intro Z mZ F hL hMW n hn
   obtain ⟨E,hE⟩:=hupper (Observation A Z) inferInstance F hL hMW n hn
   have hb : minimaxRMSE n (target A F) (modelClass A F)≤ENNReal.ofReal (C*basicUpperScale A n) := by
     apply iInf_le_of_le E
     exact iSup_le (fun P=>iSup_le (fun hP=>hE P hP))
   have hr := (covariate_dependent_risk_transfer A F n).trans hb
   have hpos := basicUpperScale_pos A n (by omega)
   have hlt : minimaxRMSE n (covariateDependentTarget A F) (covariateDependentClass A F)<
       ENNReal.ofReal ((2*C)*basicUpperScale A n) :=
     hr.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0<(2*C)*basicUpperScale A n)).mpr
       (by nlinarith [mul_pos hC hpos]))
   change (⨅E:Estimator (Observation A Z) n,⨆P,⨆hP:P∈covariateDependentClass A F,
     eLpNorm (fun o=>E.val o-covariateDependentTarget A F P) 2 (randomizedExperiment n P))<_ at hlt
   obtain ⟨E,hE⟩:=iInf_lt_iff.mp hlt
   refine ⟨E,fun P hP=>?_⟩
   apply le_trans _ hE.le
   exact le_iSup_of_le P (le_iSup_of_le hP le_rfl)

end RoughRegime.Model
