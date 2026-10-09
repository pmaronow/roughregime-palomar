module

public import RoughRegime.ParametricBaselineLower
public import RoughRegime.SourceModel


@[expose] public section
/-! Exact assembly of the parametric and rough source lower bounds in the
original model statement. The rough input here is a theorem interface; this
module does not assert that interface without its source reduction proof. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Model
universe u

 theorem mainLowerClaim_of_rough_lower (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (O : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ)
     (hrough : Nondegenerate A O π → 0 < r → A.theta < 1/2 →
       ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
         ∀ C : Set (ProbabilityMeasure (Observation A Z)), localClass A O π r ⊆ C →
           ∀ n : ℕ, n0 ≤ n →
             ENNReal.ofReal (c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n) ≤
               minimaxRMSE n (target A O) C ∧
             (1/4 : ℝ≥0∞) ≤ minimaxTail n (target A O) C
               (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n)) :
     MainLowerClaim A O π r := by
   intro hnd hr
   by_cases hsub : A.theta < 1/2
   · obtain ⟨c,hc,n0,hn0,hbound⟩ := hrough hnd hr hsub
     refine ⟨c,hc,n0,hn0,?_⟩
     intro C hC _ n hn
     refine ⟨?_,?_⟩
     · intro hge
       exact False.elim ((not_lt_of_ge hge) hsub)
     · intro _
       exact hbound C hC n hn
   · obtain ⟨c,hc,n0,hn0,hbound⟩ := main_parametric_lower A O π hnd r hr
     refine ⟨c,hc,n0,hn0,?_⟩
     intro C hC _ n hn
     refine ⟨fun _ => hbound C hC n hn,?_⟩
     intro hlt
     exact False.elim (hsub hlt.2)

/-- The explicit dimension parameter in a source construction covers every
positive model dimension. No restriction on the response measurable space or
on the order of the two smoothness exponents is imposed. -/
 theorem mainLowerClaim_of_dimension_source
     (hsource : ∀ (A0 : Parameters) (D : ℕ) {Z : Type u} [MeasurableSpace Z]
       (O : Observables Z (A0.withDimension D)) (π : ProbabilityMeasure Z) (r : ℝ),
       MainLowerClaim (A0.withDimension D) O π r)
     (A : Parameters) {Z : Type u} [MeasurableSpace Z]
     (O : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ) : MainLowerClaim A O π r := by
   cases A with
   | mk d alpha beta H delta gminus gplus M0 hd ha hb hH hdelta hgminus hgplus hM0 =>
     cases d with
     | zero => omega
     | succ D =>
       exact hsource
         (Parameters.mk (D+1) alpha beta H delta gminus gplus M0 hd ha hb hH hdelta hgminus hgplus hM0)
         D O π r


 theorem mainLowerClaim_of_dimension_rough_lower
     (hrough : ∀ (A0 : Parameters) (D : ℕ) {Z : Type u} [MeasurableSpace Z]
       (O : Observables Z (A0.withDimension D)) (π : ProbabilityMeasure Z) (r : ℝ),
       Nondegenerate (A0.withDimension D) O π → 0 < r → (A0.withDimension D).theta < 1/2 →
       ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
         ∀ n : ℕ, n0 ≤ n → ∀ C : Set (ProbabilityMeasure (Observation (A0.withDimension D) Z)),
           localClass (A0.withDimension D) O π r ⊆ C →
             ENNReal.ofReal (c*Rates.subcriticalScale n (A0.withDimension D).theta
               (Rates.tau A0.gminus A0.gplus)*Real.log n) ≤
               minimaxRMSE n (target (A0.withDimension D) O) C ∧
             (1/4 : ℝ≥0∞) ≤ minimaxTail n (target (A0.withDimension D) O) C
               (2*c*Rates.subcriticalScale n (A0.withDimension D).theta
                 (Rates.tau A0.gminus A0.gplus)*Real.log n))
     (A : Parameters) {Z : Type u} [MeasurableSpace Z]
     (O : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ) : MainLowerClaim A O π r := by
   apply mainLowerClaim_of_dimension_source (fun A0 D {Z} _ O π r => ?_) A O π r
   apply mainLowerClaim_of_rough_lower (A0.withDimension D) O π r
   intro hnd hr htheta
   obtain ⟨c,hc,n0,hn0,hbounds⟩ := hrough A0 D O π r hnd hr htheta
   exact ⟨c,hc,n0,hn0,fun C hC n hn => hbounds n hn C hC⟩

end RoughRegime.Model
