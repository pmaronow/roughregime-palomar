module

public import RoughRegime.ApplicationTrialClass


@[expose] public section
/-! Literal squared-CATE and CATE-variance targets. The forward and reverse
kernels make the trial and bounded-response experiments equivalent for every
functional of the transformed law. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Trial

def cate (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) :
    Model.Observation A Response → ℝ := fun o =>
  (P : Measure (Model.Observation A Response))[MAR.armOutcome true ∘ Prod.snd |
    Model.covariateInformation A Response] o /
      (P : Measure (Model.Observation A Response))[MAR.armIndicator true ∘ Prod.snd |
        Model.covariateInformation A Response] o -
  (P : Measure (Model.Observation A Response))[MAR.armOutcome false ∘ Prod.snd |
    Model.covariateInformation A Response] o /
      (P : Measure (Model.Observation A Response))[MAR.armIndicator false ∘ Prod.snd |
        Model.covariateInformation A Response] o

def squaredCATE (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) : ℝ :=
  ∫ o, (cate A P o)^2 ∂(P : Measure (Model.Observation A Response))

def cateVariance (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) : ℝ :=
  variance (cate A P) (P : Measure (Model.Observation A Response))

theorem Witness.cate_ae (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Response)) (W : Witness A P) :
    cate A P =ᵐ[(P : Measure (Model.Observation A Response))] W.f ∘ Prod.fst :=
  (transformed_conditional_eq_cate A.d (P : Measure (Model.Observation A Response)) W.fair).symm.trans W.moment

theorem Witness.quadraticTarget_eq (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Response)) (W : Witness A P) :
    quadraticTarget A P = ∫ o, (W.f o.1)^2 ∂(P : Measure (Model.Observation A Response)) := by
  calc
    _ = ∫ o, (W.f o.1)^2 ∂(forwardLaw A P : Measure (Model.Observation A Products.BoundedResponse)) :=
      integral_congr_ae ((W.forward_conditional A P).fun_comp (fun t : ℝ => t^2))
    _ = _ := integral_map (forward_measurable A.d).aemeasurable
      ((W.measurableF.comp measurable_fst).pow_const 2).aestronglyMeasurable

theorem squaredCATE_eq (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Response)) (hP : P ∈ modelClass A) :
    squaredCATE A P = quadraticTarget A P := by
  obtain ⟨W⟩ := hP
  rw [W.quadraticTarget_eq A P]
  exact integral_congr_ae ((W.cate_ae A P).fun_comp (fun t : ℝ => t^2))

/-- The two actual Markov kernels prove equivalence for all transformed-law
functionals, including the two trial targets. -/
theorem transformed_risks_eq (A : Model.Parameters) (hab : A.α = A.β)
    (n : ℕ) (T : ProbabilityMeasure (Model.Observation A Products.BoundedResponse) → ℝ) (t : ℝ) :
    Model.minimaxTail n (fun P => T (forwardLaw A P)) (modelClass A) t =
      Model.minimaxTail n T (Products.quadraticClass A) t ∧
    Model.minimaxRMSE n (fun P => T (forwardLaw A P)) (modelClass A) =
      Model.minimaxRMSE n T (Products.quadraticClass A) := by
  let K := Kernel.deterministic (forward A.d) (forward_measurable A.d)
  have hK : ∀ P, Model.kernelLaw K P = forwardLaw A P := by
    intro P
    apply Subtype.ext
    exact Measure.deterministic_comp_eq_map (forward_measurable A.d)
  have hforward := Model.kernel_reduction n K (fun P => T (forwardLaw A P)) T
    (modelClass A) (Products.quadraticClass A)
    (by intro P hP; rw [hK]; exact forwardLaw_mem A hab P hP)
    (by intro P _; rw [hK]) t
  have hreverse := Model.kernel_reduction n (reverseKernel A.d) T (fun P => T (forwardLaw A P))
    (Products.quadraticClass A) (modelClass A) (reverseLaw_mem A)
    (by intro P _; change T (forwardLaw A (reverseLaw A P)) = T P; rw [forwardLaw_reverseLaw]) t
  exact ⟨le_antisymm hforward.1 hreverse.1,le_antisymm hforward.2 hreverse.2⟩

theorem squaredCATE_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hd : A.δ ≤ 1) (hab : A.α = A.β) :
    Model.UpperBracket (squaredCATE A) (modelClass A) A.bracketParameters (A.nu : ℝ) := by
  obtain ⟨hν,C,hC,n0,hn0,hupper⟩ := Products.quadratic_upperBracket A hM hd
  apply Model.upperBracket_congr_target _ (quadraticTarget A) _ _ _ (squaredCATE_eq A)
  refine ⟨hν,C,hC,n0,hn0,?_⟩
  intro n hn
  unfold quadraticTarget
  rw [(transformed_risks_eq A hab n (Products.quadraticTarget A) 0).2]
  exact hupper n hn

theorem squaredCATE_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (n : ℝ)^(-(1/2 : ℝ))) ≤
        Model.minimaxRMSE n (squaredCATE A) (modelClass A) := by
  obtain ⟨c,hc,he⟩ := Products.quadratic_parametric_lower A hM hlo hhi hab
  refine ⟨c,hc,?_⟩
  filter_upwards [he] with n hn
  rw [Model.minimaxRMSE_congr_target n _ (quadraticTarget A) _ (squaredCATE_eq A)]
  unfold quadraticTarget
  rw [(transformed_risks_eq A hab n (Products.quadraticTarget A) 0).2]
  exact hn

theorem squaredCATE_parametric_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) (htheta : 1/2 ≤ A.theta) :
    Model.Bracket (squaredCATE A) (modelClass A) A.bracketParameters (A.nu : ℝ) :=
  ⟨Products.parametric_lowerBracket A _ _ htheta (squaredCATE_parametric_lower A hM hlo hhi hab),
    squaredCATE_upperBracket A hM ((le_max_left _ _).trans hlo.le) hab⟩

end RoughRegime.Applications.Trial
