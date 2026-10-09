module

public import RoughRegime.ModelProductRates


@[expose] public section
/-! The literal finite polynomial estimator is jointly measurable when its
 known observables depend measurably on independent pilot data. The proof
 uses the same estimator and a measurable augmentation of the response. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RoughRegime.Model
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

 def familyObservables (A : Parameters) {P Z : Type*} [MeasurableSpace P] [MeasurableSpace Z]
     (F : P → Observables Z A)
     (hD : Measurable (fun q:P×Z => (F q.1).D q.2))
     (hU : Measurable (fun q:P×Z => (F q.1).U q.2))
     (hV : Measurable (fun q:P×Z => (F q.1).V q.2)) : Observables (P×Z) A where
   D q := (F q.1).D q.2
   U q := (F q.1).U q.2
   V q := (F q.1).V q.2
   W _ := 0
   lam := 1
   hlam := by norm_num
   measurableD := hD
   measurableU := hU
   measurableV := hV
   measurableW := measurable_const
   boundD q := (F q.1).boundD q.2
   boundU q := (F q.1).boundU q.2
   boundV q := (F q.1).boundV q.2
   boundW := ⟨0,le_refl _,fun _=>by simp⟩

 def familySample (A : Parameters) {P Z : Type*} (n : ℕ)
     (q : P×(Fin n→Observation A Z)) : Fin n→Observation A (P×Z) :=
   fun i => ((q.2 i).1,(q.1,(q.2 i).2))

 theorem familySample_measurable (A : Parameters) {P Z : Type*}
     [MeasurableSpace P] [MeasurableSpace Z] (n : ℕ) :
     Measurable (@familySample A P Z n) := by
   apply Measurable.of_eval
   intro i
   exact ((measurable_pi_apply i).comp measurable_snd |>.fst).prodMk
     (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd |>.snd))

 theorem productEstimator_family_eq (A : Parameters) (hαβ : A.α≤A.β)
     {P Z : Type*} [MeasurableSpace P] [MeasurableSpace Z]
     (F : P → Observables Z A) (hD : Measurable (fun q:P×Z => (F q.1).D q.2))
     (hU : Measurable (fun q:P×Z => (F q.1).U q.2))
     (hV : Measurable (fun q:P×Z => (F q.1).V q.2))
     (J : ℕ) (m : Fin (J+1)→ℕ) (n : ℕ) (q : P×(Fin n→Observation A Z)) :
     productEstimator A hαβ (F q.1) J m n q.2 =
       productEstimator A hαβ (familyObservables A F hD hU hV) J m n (familySample A n q) := by
   classical
   unfold productEstimator
   apply Finset.sum_congr rfl
   intro j _
   refine Fin.cases ?_ (fun i=>?_) j
   · simp only [levelEstimator,Fin.cases_zero,baseLevelEstimator,
       IIDPolynomialEstimator.sampleLift,Upper.polynomialLift,Upper.monomialLift,
       IIDPolynomialEstimator.sampleStatistics,basePackedStatistic,baseDesignStatistic,
       designFinStatistic,designStatistic,designRawCoordinate,familySample,familyObservables]
   · simp only [levelEstimator,Fin.cases_succ,localLevelEstimator,
       IIDPolynomialEstimator.sampleLift,Upper.polynomialLift,Upper.monomialLift,
       IIDPolynomialEstimator.sampleStatistics,dyadicPackedStatistic,localDesignStatistic,
       dyadicDesignStatistic,designStatistic,designRawCoordinate,familySample,familyObservables]

 theorem productEstimator_jointly_measurable (A : Parameters) (hαβ : A.α≤A.β)
     {P Z : Type*} [MeasurableSpace P] [MeasurableSpace Z]
     (F : P → Observables Z A) (hD : Measurable (fun q:P×Z => (F q.1).D q.2))
     (hU : Measurable (fun q:P×Z => (F q.1).U q.2))
     (hV : Measurable (fun q:P×Z => (F q.1).V q.2))
     (J : ℕ) (m : Fin (J+1)→ℕ) (n : ℕ) :
     Measurable (fun q:P×(Fin n→Observation A Z) => productEstimator A hαβ (F q.1) J m n q.2) := by
   have h := (productEstimator_measurable A hαβ (familyObservables A F hD hU hV) J m n).comp
     (familySample_measurable A n)
   have heq : (fun q:P×(Fin n→Observation A Z) => productEstimator A hαβ (F q.1) J m n q.2)=
       productEstimator A hαβ (familyObservables A F hD hU hV) J m n∘familySample A n := by
     funext q
     exact productEstimator_family_eq A hαβ F hD hU hV J m n q
   rwa [heq]

 theorem parametricProductEstimator_jointly_measurable (A : Parameters) (hαβ : A.α≤A.β)
     {P Z : Type*} [MeasurableSpace P] [MeasurableSpace Z]
     (F : P → Observables Z A) (hD : Measurable (fun q:P×Z => (F q.1).D q.2))
     (hU : Measurable (fun q:P×Z => (F q.1).U q.2))
     (hV : Measurable (fun q:P×Z => (F q.1).V q.2)) (Cv : ℝ) (n : ℕ) :
     Measurable (fun q:P×(Fin n→Observation A Z) => parametricProductEstimator A hαβ (F q.1) Cv n q.2) := by
   exact productEstimator_jointly_measurable A hαβ F hD hU hV _ _ n

 theorem subcriticalProductEstimator_jointly_measurable (A : Parameters) (hαβ : A.α≤A.β)
     {P Z : Type*} [MeasurableSpace P] [MeasurableSpace Z]
     (F : P → Observables Z A) (hD : Measurable (fun q:P×Z => (F q.1).D q.2))
     (hU : Measurable (fun q:P×Z => (F q.1).U q.2))
     (hV : Measurable (fun q:P×Z => (F q.1).V q.2)) (Cv : ℝ) (n : ℕ) :
     Measurable (fun q:P×(Fin n→Observation A Z) => subcriticalProductEstimator A hαβ (F q.1) Cv n q.2) := by
   exact productEstimator_jointly_measurable A hαβ F hD hU hV _ _ n

end RoughRegime.Model
