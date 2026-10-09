module

public import RoughRegime.ApplicationNormalizedMAR
public import RoughRegime.PilotSampleSplit


@[expose] public section
/-! Actual pilot-dependent normalized estimators on the original MAR sample.
 Their joint measurability follows from the literal finite polynomial lift.
 The iid transport and conditional risks use the actual normalized law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem normalized_productTarget_eq_target (A : Model.Parameters)
     (P : ProbabilityMeasure (Model.Covariate A.d×Response))
     (h : Model.Covariate A.d→ℝ) (hh : Measurable h) (e : ℝ) (he : 0<e)
     (hlower : ∀ x,e≤h x) (hM : 1≤A.M0) (hMinv : 1/e≤A.M0)
     (W : Model.ModelWitness A (normalizedObservables A h hh e he hlower hM hMinv) (normalizedLaw A.d P)) :
     W.productTarget=Model.target A (normalizedObservables A h hh e he hlower hM hMinv) (normalizedLaw A.d P) := by
   have ht := W.target_eq_linear_product
   simpa only [normalizedObservables,integral_zero,zero_add,one_mul] using ht.symm

 def normalizedSample (d n : ℕ) (xs : Fin n→Model.Covariate d×Response) :
     Fin n→Model.Covariate d×NormalizedResponse d := fun i=>liftObservation d (xs i)

 theorem normalizedSample_measurable (d n : ℕ) : Measurable (normalizedSample d n) :=
   Measurable.of_eval (fun i=>(liftObservation_measurable d).comp (measurable_pi_apply i))

 theorem normalizedSample_measurePreserving (d n : ℕ)
     (P : ProbabilityMeasure (Model.Covariate d×Response)) :
     MeasurePreserving (normalizedSample d n) (Measure.pi (fun _ : Fin n=>(P:Measure _)))
       (Measure.pi (fun _ : Fin n=>(normalizedLaw d P:Measure _))) := by
   apply measurePreserving_pi
   intro i
   exact ⟨liftObservation_measurable d,rfl⟩

 def pilotObservables (A : Model.Parameters) {T : Type*} [MeasurableSpace T]
     (h : T→Model.Covariate A.d→ℝ) (hh : Measurable (Function.uncurry h))
     (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x) (hM : 1≤A.M0) (hMinv : 1/e≤A.M0)
     (t : T) : Model.Observables (NormalizedResponse A.d) A :=
   normalizedObservables A (h t) (hh.comp measurable_prodMk_left) e he (hlower t) hM hMinv

 theorem pilotObservables_jointD (A : Model.Parameters) {T : Type*} [MeasurableSpace T]
     (h : T→Model.Covariate A.d→ℝ) (hh : Measurable (Function.uncurry h))
     (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x) (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) :
     Measurable (fun q:T×NormalizedResponse A.d => (pilotObservables A h hh e he hlower hM hMinv q.1).D q.2) := by
   exact (MAR.observed_measurable.comp measurable_snd.snd).div
     (hh.comp (measurable_fst.prodMk measurable_snd.fst))

 theorem pilotObservables_jointU (A : Model.Parameters) {T : Type*} [MeasurableSpace T]
     (h : T→Model.Covariate A.d→ℝ) (hh : Measurable (Function.uncurry h))
     (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x) (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) :
     Measurable (fun q:T×NormalizedResponse A.d => (pilotObservables A h hh e he hlower hM hMinv q.1).U q.2) :=
   measurable_const

 theorem pilotObservables_jointV (A : Model.Parameters) {T : Type*} [MeasurableSpace T]
     (h : T→Model.Covariate A.d→ℝ) (hh : Measurable (Function.uncurry h))
     (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x) (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) :
     Measurable (fun q:T×NormalizedResponse A.d => (pilotObservables A h hh e he hlower hM hMinv q.1).V q.2) := by
   exact (MAR.observedOutcome_measurable.comp measurable_snd.snd).div
     (hh.comp (measurable_fst.prodMk measurable_snd.fst))

 def parametricNormalizedEstimate (A : Model.Parameters) (hαβ : A.α≤A.β)
     {T : Type*} [MeasurableSpace T] (h : T→Model.Covariate A.d→ℝ)
     (hh : Measurable (Function.uncurry h)) (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x)
     (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) (Cv : ℝ) (n : ℕ) :
     T×(Fin n→Model.Covariate A.d×Response)→ℝ :=
   (fun q:T×(Fin n→Model.Covariate A.d×NormalizedResponse A.d)=>
     Model.parametricProductEstimator A hαβ (pilotObservables A h hh e he hlower hM hMinv q.1) Cv n q.2)∘
       (fun q:T×(Fin n→Model.Covariate A.d×Response)=>(q.1,normalizedSample A.d n q.2))

 def subcriticalNormalizedEstimate (A : Model.Parameters) (hαβ : A.α≤A.β)
     {T : Type*} [MeasurableSpace T] (h : T→Model.Covariate A.d→ℝ)
     (hh : Measurable (Function.uncurry h)) (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x)
     (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) (Cv : ℝ) (n : ℕ) :
     T×(Fin n→Model.Covariate A.d×Response)→ℝ :=
   (fun q:T×(Fin n→Model.Covariate A.d×NormalizedResponse A.d)=>
     Model.subcriticalProductEstimator A hαβ (pilotObservables A h hh e he hlower hM hMinv q.1) Cv n q.2)∘
       (fun q:T×(Fin n→Model.Covariate A.d×Response)=>(q.1,normalizedSample A.d n q.2))

 theorem parametricNormalizedEstimate_measurable (A : Model.Parameters) (hαβ : A.α≤A.β)
     {T : Type*} [MeasurableSpace T] (h : T→Model.Covariate A.d→ℝ)
     (hh : Measurable (Function.uncurry h)) (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x)
     (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) (Cv : ℝ) (n : ℕ) :
     Measurable (parametricNormalizedEstimate A hαβ h hh e he hlower hM hMinv Cv n) := by
   unfold parametricNormalizedEstimate
   have hraw := Model.parametricProductEstimator_jointly_measurable A hαβ
     (pilotObservables A h hh e he hlower hM hMinv)
     (pilotObservables_jointD A h hh e he hlower hM hMinv)
     (pilotObservables_jointU A h hh e he hlower hM hMinv)
     (pilotObservables_jointV A h hh e he hlower hM hMinv) Cv n
   have hmap : Measurable (fun q:T×(Fin n→Model.Covariate A.d×Response) =>
       (q.1,normalizedSample A.d n q.2)) :=
     measurable_fst.prodMk ((normalizedSample_measurable A.d n).comp measurable_snd)
   exact hraw.comp hmap

 theorem subcriticalNormalizedEstimate_measurable (A : Model.Parameters) (hαβ : A.α≤A.β)
     {T : Type*} [MeasurableSpace T] (h : T→Model.Covariate A.d→ℝ)
     (hh : Measurable (Function.uncurry h)) (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x)
     (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) (Cv : ℝ) (n : ℕ) :
     Measurable (subcriticalNormalizedEstimate A hαβ h hh e he hlower hM hMinv Cv n) := by
   unfold subcriticalNormalizedEstimate
   have hraw := Model.subcriticalProductEstimator_jointly_measurable A hαβ
     (pilotObservables A h hh e he hlower hM hMinv)
     (pilotObservables_jointD A h hh e he hlower hM hMinv)
     (pilotObservables_jointU A h hh e he hlower hM hMinv)
     (pilotObservables_jointV A h hh e he hlower hM hMinv) Cv n
   have hmap : Measurable (fun q:T×(Fin n→Model.Covariate A.d×Response) =>
       (q.1,normalizedSample A.d n q.2)) :=
     measurable_fst.prodMk ((normalizedSample_measurable A.d n).comp measurable_snd)
   exact hraw.comp hmap

 theorem uniform_parametricNormalizedEstimate_risk (A : Model.Parameters) (hαβ : A.α≤A.β)
     (hθ : 1/2≤A.theta) :
     ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
       ∀ (P : ProbabilityMeasure (Model.Covariate A.d×Response))
         (h : Model.Covariate A.d→ℝ) (hh : Measurable h) (e : ℝ) (he : 0<e)
         (hlower : ∀ x,e≤h x) (hM : 1≤A.M0) (hMinv : 1/e≤A.M0)
         (W : Model.ModelWitness A (normalizedObservables A h hh e he hlower hM hMinv) (normalizedLaw A.d P)),
       eLpNorm (fun xs=>Model.parametricProductEstimator A hαβ
         (normalizedObservables A h hh e he hlower hM hMinv) Cv n (normalizedSample A.d n xs)-W.productTarget) 2
           (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤ENNReal.ofReal (C/Real.sqrt n) := by
   obtain ⟨Cv,C,hCv,hC,hevent⟩ := Model.uniform_parametricProductEstimator_risk.{0} A hαβ hθ
   refine ⟨Cv,C,hCv,hC,?_⟩
   filter_upwards [hevent] with n hn
   intro P h hh e he hlower hM hMinv W
   let F := normalizedObservables A h hh e he hlower hM hMinv
   let E := Model.parametricProductEstimator A hαβ F Cv n
   have hmem : MemLp (fun xs=>E xs-W.productTarget) 2
       (Measure.pi (fun _ : Fin n=>(normalizedLaw A.d P:Measure _))) := by
     exact (Model.productEstimator_memLp _ _ _ _ _ _ _).sub (memLp_const _)
   have herr := hmem.aestronglyMeasurable
   change eLpNorm ((fun xs=>E xs-W.productTarget)∘normalizedSample A.d n) 2
     (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤ENNReal.ofReal (C/Real.sqrt n)
   rw [eLpNorm_comp_measurePreserving herr (normalizedSample_measurePreserving A.d n P),←ofReal_lpNorm hmem]
   exact ENNReal.ofReal_le_ofReal (hn (NormalizedResponse A.d) F (normalizedLaw A.d P) W)

 theorem uniform_subcriticalNormalizedEstimate_risk (A : Model.Parameters) (hαβ : A.α≤A.β)
     (hθ : A.theta<1/2) :
     ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
       ∀ (P : ProbabilityMeasure (Model.Covariate A.d×Response))
         (h : Model.Covariate A.d→ℝ) (hh : Measurable h) (e : ℝ) (he : 0<e)
         (hlower : ∀ x,e≤h x) (hM : 1≤A.M0) (hMinv : 1/e≤A.M0)
         (W : Model.ModelWitness A (normalizedObservables A h hh e he hlower hM hMinv) (normalizedLaw A.d P)),
       eLpNorm (fun xs=>Model.subcriticalProductEstimator A hαβ
         (normalizedObservables A h hh e he hlower hM hMinv) Cv n (normalizedSample A.d n xs)-W.productTarget) 2
           (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤ENNReal.ofReal
             (C*RoughRegime.UpperSubcritical.rate n A.theta (RoughRegime.Rates.tau A.gminus A.gplus) A.nu) := by
   obtain ⟨Cv,C,hCv,hC,hevent⟩ := Model.uniform_subcriticalProductEstimator_risk.{0} A hαβ hθ
   refine ⟨Cv,C,hCv,hC,?_⟩
   filter_upwards [hevent] with n hn
   intro P h hh e he hlower hM hMinv W
   let F := normalizedObservables A h hh e he hlower hM hMinv
   let E := Model.subcriticalProductEstimator A hαβ F Cv n
   have hmem : MemLp (fun xs=>E xs-W.productTarget) 2
       (Measure.pi (fun _ : Fin n=>(normalizedLaw A.d P:Measure _))) := by
     exact (Model.productEstimator_memLp _ _ _ _ _ _ _).sub (memLp_const _)
   have herr := hmem.aestronglyMeasurable
   change eLpNorm ((fun xs=>E xs-W.productTarget)∘normalizedSample A.d n) 2
     (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤ENNReal.ofReal
       (C*RoughRegime.UpperSubcritical.rate n A.theta (RoughRegime.Rates.tau A.gminus A.gplus) A.nu)
   rw [eLpNorm_comp_measurePreserving herr (normalizedSample_measurePreserving A.d n P),←ofReal_lpNorm hmem]
   exact ENNReal.ofReal_le_ofReal (hn (NormalizedResponse A.d) F (normalizedLaw A.d P) W)

end RoughRegime.Applications.SeparatedMAR
