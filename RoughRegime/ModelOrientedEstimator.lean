module

public import RoughRegime.ModelParametricEstimator
public import RoughRegime.ModelSwap


@[expose] public section
/-! The explicit polynomial estimator with either ordering of the two
 smoothness indices. Swapping exchanges the observable means and preserves
 the exact target, model law, correction exponent and truncation degree. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Model
universe u
set_option backward.isDefEq.respectTransparency false

 theorem ModelWitness.swap_productTarget {A : Parameters} {Z : Type*} [MeasurableSpace Z]
     {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)} (W : ModelWitness A F P) :
     W.swap.productTarget=W.productTarget := by
   unfold ModelWitness.productTarget ModelWitness.swap ModelWitness.designDensity
   congr 1
   funext x
   ring

 def orientedParametricProductEstimator (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables Z A) (Cv : ℝ) (n : ℕ) : (Fin n→Observation A Z)→ℝ := by
   classical
   exact if h:A.α≤A.β then parametricProductEstimator A h F Cv n else
     parametricProductEstimator A.swap (le_of_lt (lt_of_not_ge h)) F.swap Cv n

 def orientedSubcriticalProductEstimator (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables Z A) (Cv : ℝ) (n : ℕ) : (Fin n→Observation A Z)→ℝ := by
   classical
   exact if h:A.α≤A.β then subcriticalProductEstimator A h F Cv n else
     subcriticalProductEstimator A.swap (le_of_lt (lt_of_not_ge h)) F.swap Cv n

 theorem orientedParametricProductEstimator_jointly_measurable (A : Parameters)
     {T Z : Type*} [MeasurableSpace T] [MeasurableSpace Z]
     (F : T→Observables Z A) (hD : Measurable (fun q:T×Z=>(F q.1).D q.2))
     (hU : Measurable (fun q:T×Z=>(F q.1).U q.2))
     (hV : Measurable (fun q:T×Z=>(F q.1).V q.2)) (Cv : ℝ) (n : ℕ) :
     Measurable (fun q:T×(Fin n→Observation A Z)=>orientedParametricProductEstimator A (F q.1) Cv n q.2) := by
   classical
   by_cases h:A.α≤A.β
   · simp only [orientedParametricProductEstimator,dite_eq_left h]
     exact parametricProductEstimator_jointly_measurable A h F hD hU hV Cv n
   · simp only [orientedParametricProductEstimator,dite_eq_right h]
     exact parametricProductEstimator_jointly_measurable A.swap (le_of_lt (lt_of_not_ge h))
       (fun t=>(F t).swap) hD hV hU Cv n

 theorem orientedSubcriticalProductEstimator_jointly_measurable (A : Parameters)
     {T Z : Type*} [MeasurableSpace T] [MeasurableSpace Z]
     (F : T→Observables Z A) (hD : Measurable (fun q:T×Z=>(F q.1).D q.2))
     (hU : Measurable (fun q:T×Z=>(F q.1).U q.2))
     (hV : Measurable (fun q:T×Z=>(F q.1).V q.2)) (Cv : ℝ) (n : ℕ) :
     Measurable (fun q:T×(Fin n→Observation A Z)=>orientedSubcriticalProductEstimator A (F q.1) Cv n q.2) := by
   classical
   by_cases h:A.α≤A.β
   · simp only [orientedSubcriticalProductEstimator,dite_eq_left h]
     exact subcriticalProductEstimator_jointly_measurable A h F hD hU hV Cv n
   · simp only [orientedSubcriticalProductEstimator,dite_eq_right h]
     exact subcriticalProductEstimator_jointly_measurable A.swap (le_of_lt (lt_of_not_ge h))
       (fun t=>(F t).swap) hD hV hU Cv n

 theorem orientedParametricProductEstimator_memLp (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (Cv : ℝ) (n : ℕ) :
     MemLp (orientedParametricProductEstimator A F Cv n) 2 (Measure.pi (fun _ : Fin n=>(P:Measure _))) := by
   classical
   by_cases h:A.α≤A.β
   · simp only [orientedParametricProductEstimator,dite_eq_left h,parametricProductEstimator]
     exact productEstimator_memLp _ _ _ _ _ _ _
   · simp only [orientedParametricProductEstimator,dite_eq_right h,parametricProductEstimator]
     exact productEstimator_memLp _ _ _ _ _ _ _

 theorem orientedSubcriticalProductEstimator_memLp (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (Cv : ℝ) (n : ℕ) :
     MemLp (orientedSubcriticalProductEstimator A F Cv n) 2 (Measure.pi (fun _ : Fin n=>(P:Measure _))) := by
   classical
   by_cases h:A.α≤A.β
   · simp only [orientedSubcriticalProductEstimator,dite_eq_left h,subcriticalProductEstimator]
     exact productEstimator_memLp _ _ _ _ _ _ _
   · simp only [orientedSubcriticalProductEstimator,dite_eq_right h,subcriticalProductEstimator]
     exact productEstimator_memLp _ _ _ _ _ _ _

 theorem uniform_orientedParametricProductEstimator_risk (A : Parameters) (hθ : 1/2≤A.theta) :
     ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
       ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
         (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P),
       lpNorm (fun xs=>orientedParametricProductEstimator A F Cv n xs-W.productTarget) 2
         (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤C/Real.sqrt n := by
   classical
   by_cases h:A.α≤A.β
   · simpa only [orientedParametricProductEstimator,dite_eq_left h] using
       uniform_parametricProductEstimator_risk.{u} A h hθ
   · obtain ⟨Cv,C,hCv,hC,he⟩ := uniform_parametricProductEstimator_risk.{u} A.swap
       (le_of_lt (lt_of_not_ge h)) (by simpa using hθ)
     refine ⟨Cv,C,hCv,hC,?_⟩
     filter_upwards [he] with n hn
     intro Z _ F P W
     simpa only [orientedParametricProductEstimator,dite_eq_right h,ModelWitness.swap_productTarget,
       Parameters.swap] using
       hn Z F.swap P W.swap

 theorem uniform_orientedSubcriticalProductEstimator_risk (A : Parameters) (hθ : A.theta<1/2) :
     ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
       ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
         (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P),
       lpNorm (fun xs=>orientedSubcriticalProductEstimator A F Cv n xs-W.productTarget) 2
         (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤
           C*RoughRegime.UpperSubcritical.rate n A.theta (RoughRegime.Rates.tau A.gminus A.gplus) A.nu := by
   classical
   by_cases h:A.α≤A.β
   · simpa only [orientedSubcriticalProductEstimator,dite_eq_left h] using
       uniform_subcriticalProductEstimator_risk.{u} A h hθ
   · obtain ⟨Cv,C,hCv,hC,he⟩ := uniform_subcriticalProductEstimator_risk.{u} A.swap
       (le_of_lt (lt_of_not_ge h)) (by simpa using hθ)
     refine ⟨Cv,C,hCv,hC,?_⟩
     filter_upwards [he] with n hn
     intro Z _ F P W
     have hh := hn Z F.swap P W.swap
     rw [Parameters.swap_theta,Parameters.swap_nu] at hh
     simpa only [orientedSubcriticalProductEstimator,dite_eq_right h,ModelWitness.swap_productTarget,
       Parameters.swap] using hh

end RoughRegime.Model
