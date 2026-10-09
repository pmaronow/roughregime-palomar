module

public import RoughRegime.ObservableMeanUpper
public import RoughRegime.ModelUpperConsequences
public import RoughRegime.ModelSwap


@[expose] public section
/-! The unnumbered example in Section 2: when U=D, the literal conditional
ratio target is an observable mean and admits the ordinary empirical root-n
bound, regardless of nuisance smoothness. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RoughRegime.Model

 theorem target_eq_observableMean_of_U_eq_D (A : Parameters) {Z : Type*}
     [MeasurableSpace Z] (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
     (W : ModelWitness A F P) (hUD : F.U=F.D) :
     target A F P=∫o,F.W o.2+F.lam*F.V o.2 ∂(P:Measure (Observation A Z)) := by
   have hV : Integrable (fun o : Observation A Z=>F.V o.2) (P:Measure (Observation A Z)) := by
     apply Integrable.of_bound (F.measurableV.comp measurable_snd).aestronglyMeasurable A.M0
     exact ae_of_all _ (fun o=>by simpa only [Real.norm_eq_abs,Function.comp_apply] using F.boundV o.2)
   obtain ⟨MW,_,hbW⟩ := F.boundW
   have hW : Integrable (fun o : Observation A Z=>F.W o.2) (P:Measure (Observation A Z)) := by
     apply Integrable.of_bound (F.measurableW.comp measurable_snd).aestronglyMeasurable MW
     exact ae_of_all _ (fun o=>by simpa only [Real.norm_eq_abs,Function.comp_apply] using hbW o.2)
   have he : (∫o,
       ((P:Measure (Observation A Z))[F.U∘Prod.snd|covariateInformation A Z]) o*
       ((P:Measure (Observation A Z))[F.V∘Prod.snd|covariateInformation A Z]) o/
       ((P:Measure (Observation A Z))[F.D∘Prod.snd|covariateInformation A Z]) o
       ∂(P:Measure (Observation A Z)))=
       ∫o,F.V o.2 ∂(P:Measure (Observation A Z)) := by
     calc
       _ = ∫o,((P:Measure (Observation A Z))[F.V∘Prod.snd|covariateInformation A Z]) o
           ∂(P:Measure (Observation A Z)) := by
         apply integral_congr_ae
         filter_upwards [W.momentD,witness_overlap_on_observations A F P W] with o hD hw
         rw [hUD]
         have hne : ((P:Measure (Observation A Z))[F.D∘Prod.snd|covariateInformation A Z]) o≠0 := by
           rw [hD]
           exact (A.hδ.trans_le hw).ne'
         field_simp
       _ = _ := integral_condExp measurable_fst.comap_le
   unfold target
   rw [he,integral_add hW (hV.const_mul F.lam),integral_const_mul]

 theorem degenerate_target_rootN_minimax (A : Parameters) {Z : Type*}
     [MeasurableSpace Z] (F : Observables Z A) (hUD : F.U=F.D)
     (MW : ℝ) (hMW : 0≤MW) (hbW : ∀z,|F.W z|≤MW) (n : ℕ) (hn : 0<n) :
     minimaxRMSE n (target A F) (modelClass A F)≤
       ENNReal.ofReal ((MW+|F.lam| *A.M0)/Real.sqrt n) := by
   rw [minimaxRMSE_congr_target n (target A F)
     (fun P=>∫o,F.W o.2+F.lam*F.V o.2 ∂(P:Measure (Observation A Z)))
     (modelClass A F) (fun P hP=>target_eq_observableMean_of_U_eq_D A F P hP.some hUD)]
   apply observableMean_minimax n hn _
     ((F.measurableW.comp measurable_snd).add
       (measurable_const.mul (F.measurableV.comp measurable_snd)))
     (MW+|F.lam| *A.M0) (add_nonneg hMW (mul_nonneg (abs_nonneg _) A.hM0.le))
   intro o
   calc
     _ ≤ |F.W o.2|+|F.lam*F.V o.2| := abs_add_le _ _
     _ = |F.W o.2|+|F.lam| *|F.V o.2| := by rw [abs_mul]
     _ ≤ _ := add_le_add (hbW o.2) (mul_le_mul_of_nonneg_left (F.boundV o.2) (abs_nonneg _))

/-- The genuine empirical estimator of W+lambda*V, with one bound before
all observation laws in the model. -/
 theorem degenerate_target_rootN_estimator (A : Parameters) {Z : Type*}
     [MeasurableSpace Z] (F : Observables Z A) (hUD : F.U=F.D)
     (MW : ℝ) (hMW : 0≤MW) (hbW : ∀z,|F.W z|≤MW) (n : ℕ) (hn : 0<n) :
     ∃E : Estimator (Observation A Z) n,
       ∀P∈modelClass A F,eLpNorm (fun o=>E.val o-target A F P) 2
         (randomizedExperiment n P)≤
           ENNReal.ofReal ((MW+|F.lam| *A.M0)/Real.sqrt n) := by
   let f : Observation A Z→ℝ := fun o=>F.W o.2+F.lam*F.V o.2
   have hf : Measurable f := (F.measurableW.comp measurable_snd).add
     (measurable_const.mul (F.measurableV.comp measurable_snd))
   have hb : ∀o,|f o|≤MW+|F.lam| *A.M0 := by
     intro o
     calc
       _ ≤ |F.W o.2|+|F.lam*F.V o.2| := abs_add_le _ _
       _ = |F.W o.2|+|F.lam| *|F.V o.2| := by rw [abs_mul]
       _ ≤ _ := add_le_add (hbW o.2) (mul_le_mul_of_nonneg_left (F.boundV o.2) (abs_nonneg _))
   refine ⟨sampleMeanEstimator n f hf,?_⟩
   intro P hP
   rw [target_eq_observableMean_of_U_eq_D A F P hP.some hUD]
   exact sampleMeanEstimator_eLpNorm_error n hn P f hf (MW+|F.lam| *A.M0)
     (add_nonneg hMW (mul_nonneg (abs_nonneg _) A.hM0.le)) hb

 theorem target_eq_observableMean_of_V_eq_D (A : Parameters) {Z : Type*}
     [MeasurableSpace Z] (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
     (W : ModelWitness A F P) (hVD : F.V=F.D) :
     target A F P=∫o,F.W o.2+F.lam*F.U o.2 ∂(P:Measure (Observation A Z)) := by
   have hh := target_eq_observableMean_of_U_eq_D A.swap F.swap P W.swap hVD
   rw [target_swap] at hh
   exact hh

 theorem degenerate_target_rootN_minimax_of_V_eq_D (A : Parameters) {Z : Type*}
     [MeasurableSpace Z] (F : Observables Z A) (hVD : F.V=F.D)
     (MW : ℝ) (hMW : 0≤MW) (hbW : ∀z,|F.W z|≤MW) (n : ℕ) (hn : 0<n) :
     minimaxRMSE n (target A F) (modelClass A F)≤
       ENNReal.ofReal ((MW+|F.lam| *A.M0)/Real.sqrt n) := by
   have ht : target A.swap F.swap=target A F := funext (target_swap F)
   have hh := degenerate_target_rootN_minimax A.swap F.swap hVD MW hMW hbW n hn
   rw [ht,modelClass_swap] at hh
   exact hh

end RoughRegime.Model
