module

public import RoughRegime.NormalizedPilotEstimator
public import RoughRegime.ModelOrientedEstimator


@[expose] public section
/-! Actual normalized iid estimators with both smoothness orderings. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 def orientedParametricNormalizedEstimate (A : Model.Parameters)
     {T : Type*} [MeasurableSpace T] (h : T→Model.Covariate A.d→ℝ)
     (hh : Measurable (Function.uncurry h)) (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x)
     (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) (Cv : ℝ) (n : ℕ) :
     T×(Fin n→Model.Covariate A.d×Response)→ℝ :=
   (fun q:T×(Fin n→Model.Covariate A.d×NormalizedResponse A.d)=>
     Model.orientedParametricProductEstimator A (pilotObservables A h hh e he hlower hM hMinv q.1) Cv n q.2)∘
       (fun q:T×(Fin n→Model.Covariate A.d×Response)=>(q.1,normalizedSample A.d n q.2))

 def orientedSubcriticalNormalizedEstimate (A : Model.Parameters)
     {T : Type*} [MeasurableSpace T] (h : T→Model.Covariate A.d→ℝ)
     (hh : Measurable (Function.uncurry h)) (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x)
     (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) (Cv : ℝ) (n : ℕ) :
     T×(Fin n→Model.Covariate A.d×Response)→ℝ :=
   (fun q:T×(Fin n→Model.Covariate A.d×NormalizedResponse A.d)=>
     Model.orientedSubcriticalProductEstimator A (pilotObservables A h hh e he hlower hM hMinv q.1) Cv n q.2)∘
       (fun q:T×(Fin n→Model.Covariate A.d×Response)=>(q.1,normalizedSample A.d n q.2))

 theorem orientedParametricNormalizedEstimate_measurable (A : Model.Parameters)
     {T : Type*} [MeasurableSpace T] (h : T→Model.Covariate A.d→ℝ)
     (hh : Measurable (Function.uncurry h)) (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x)
     (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) (Cv : ℝ) (n : ℕ) :
     Measurable (orientedParametricNormalizedEstimate A h hh e he hlower hM hMinv Cv n) := by
   unfold orientedParametricNormalizedEstimate
   have hraw := Model.orientedParametricProductEstimator_jointly_measurable A
     (pilotObservables A h hh e he hlower hM hMinv)
     (pilotObservables_jointD A h hh e he hlower hM hMinv)
     (pilotObservables_jointU A h hh e he hlower hM hMinv)
     (pilotObservables_jointV A h hh e he hlower hM hMinv) Cv n
   have hmap : Measurable (fun q:T×(Fin n→Model.Covariate A.d×Response) =>
       (q.1,normalizedSample A.d n q.2)) :=
     measurable_fst.prodMk ((normalizedSample_measurable A.d n).comp measurable_snd)
   exact hraw.comp hmap

 theorem orientedSubcriticalNormalizedEstimate_measurable (A : Model.Parameters)
     {T : Type*} [MeasurableSpace T] (h : T→Model.Covariate A.d→ℝ)
     (hh : Measurable (Function.uncurry h)) (e : ℝ) (he : 0<e) (hlower : ∀ t x,e≤h t x)
     (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) (Cv : ℝ) (n : ℕ) :
     Measurable (orientedSubcriticalNormalizedEstimate A h hh e he hlower hM hMinv Cv n) := by
   unfold orientedSubcriticalNormalizedEstimate
   have hraw := Model.orientedSubcriticalProductEstimator_jointly_measurable A
     (pilotObservables A h hh e he hlower hM hMinv)
     (pilotObservables_jointD A h hh e he hlower hM hMinv)
     (pilotObservables_jointU A h hh e he hlower hM hMinv)
     (pilotObservables_jointV A h hh e he hlower hM hMinv) Cv n
   have hmap : Measurable (fun q:T×(Fin n→Model.Covariate A.d×Response) =>
       (q.1,normalizedSample A.d n q.2)) :=
     measurable_fst.prodMk ((normalizedSample_measurable A.d n).comp measurable_snd)
   exact hraw.comp hmap

 theorem uniform_orientedParametricNormalizedEstimate_risk (A : Model.Parameters)
     (hθ : 1/2≤A.theta) :
     ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
       ∀ (P : ProbabilityMeasure (Model.Covariate A.d×Response))
         (h : Model.Covariate A.d→ℝ) (hh : Measurable h) (e : ℝ) (he : 0<e)
         (hlower : ∀ x,e≤h x) (hM : 1≤A.M0) (hMinv : 1/e≤A.M0)
         (W : Model.ModelWitness A (normalizedObservables A h hh e he hlower hM hMinv) (normalizedLaw A.d P)),
       eLpNorm (fun xs=>Model.orientedParametricProductEstimator A
         (normalizedObservables A h hh e he hlower hM hMinv) Cv n (normalizedSample A.d n xs)-W.productTarget) 2
           (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤ENNReal.ofReal (C/Real.sqrt n) := by
   obtain ⟨Cv,C,hCv,hC,hevent⟩ := Model.uniform_orientedParametricProductEstimator_risk.{0} A hθ
   refine ⟨Cv,C,hCv,hC,?_⟩
   filter_upwards [hevent] with n hn
   intro P h hh e he hlower hM hMinv W
   let F := normalizedObservables A h hh e he hlower hM hMinv
   let E := Model.orientedParametricProductEstimator A F Cv n
   have hmem : MemLp (fun xs=>E xs-W.productTarget) 2
       (Measure.pi (fun _ : Fin n=>(normalizedLaw A.d P:Measure _))) := by
     exact (Model.orientedParametricProductEstimator_memLp A F (normalizedLaw A.d P) Cv n).sub (memLp_const _)
   have herr := hmem.aestronglyMeasurable
   change eLpNorm ((fun xs=>E xs-W.productTarget)∘normalizedSample A.d n) 2
     (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤ENNReal.ofReal (C/Real.sqrt n)
   rw [eLpNorm_comp_measurePreserving herr (normalizedSample_measurePreserving A.d n P),←ofReal_lpNorm hmem]
   exact ENNReal.ofReal_le_ofReal (hn (NormalizedResponse A.d) F (normalizedLaw A.d P) W)

 theorem uniform_orientedSubcriticalNormalizedEstimate_risk (A : Model.Parameters)
     (hθ : A.theta<1/2) :
     ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
       ∀ (P : ProbabilityMeasure (Model.Covariate A.d×Response))
         (h : Model.Covariate A.d→ℝ) (hh : Measurable h) (e : ℝ) (he : 0<e)
         (hlower : ∀ x,e≤h x) (hM : 1≤A.M0) (hMinv : 1/e≤A.M0)
         (W : Model.ModelWitness A (normalizedObservables A h hh e he hlower hM hMinv) (normalizedLaw A.d P)),
       eLpNorm (fun xs=>Model.orientedSubcriticalProductEstimator A
         (normalizedObservables A h hh e he hlower hM hMinv) Cv n (normalizedSample A.d n xs)-W.productTarget) 2
           (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤ENNReal.ofReal
             (C*RoughRegime.UpperSubcritical.rate n A.theta (RoughRegime.Rates.tau A.gminus A.gplus) A.nu) := by
   obtain ⟨Cv,C,hCv,hC,hevent⟩ := Model.uniform_orientedSubcriticalProductEstimator_risk.{0} A hθ
   refine ⟨Cv,C,hCv,hC,?_⟩
   filter_upwards [hevent] with n hn
   intro P h hh e he hlower hM hMinv W
   let F := normalizedObservables A h hh e he hlower hM hMinv
   let E := Model.orientedSubcriticalProductEstimator A F Cv n
   have hmem : MemLp (fun xs=>E xs-W.productTarget) 2
       (Measure.pi (fun _ : Fin n=>(normalizedLaw A.d P:Measure _))) := by
     exact (Model.orientedSubcriticalProductEstimator_memLp A F (normalizedLaw A.d P) Cv n).sub (memLp_const _)
   have herr := hmem.aestronglyMeasurable
   change eLpNorm ((fun xs=>E xs-W.productTarget)∘normalizedSample A.d n) 2
     (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤ENNReal.ofReal
       (C*RoughRegime.UpperSubcritical.rate n A.theta (RoughRegime.Rates.tau A.gminus A.gplus) A.nu)
   rw [eLpNorm_comp_measurePreserving herr (normalizedSample_measurePreserving A.d n P),←ofReal_lpNorm hmem]
   exact ENNReal.ofReal_le_ofReal (hn (NormalizedResponse A.d) F (normalizedLaw A.d P) W)

end RoughRegime.Applications.SeparatedMAR
