module

public import RoughRegime.ProductVarianceUpper


@[expose] public section
/-! Actual excess squared prediction loss and its reduction to a conditional
second moment plus the mean of a known bounded observable. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.Applications.Products

def excessLoss (A : Model.Parameters) (f0 : Model.Covariate A.d → ℝ)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : ℝ :=
  ∫ o, (((P : Measure (Model.Observation A BoundedResponse))[
    (Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd | Model.covariateInformation A BoundedResponse]) o
      - f0 o.1)^2 ∂(P : Measure (Model.Observation A BoundedResponse))

def predictionContrast (A : Model.Parameters) (f0 : Model.Covariate A.d → ℝ) :
    Model.Observation A BoundedResponse → ℝ := fun o => 2*(o.2 : ℝ)*f0 o.1-(f0 o.1)^2

theorem excessLoss_identity (A : Model.Parameters) (f0 : Model.Covariate A.d → ℝ)
    (hf : Measurable f0) (M : ℝ) (hb : ∀ x, |f0 x| ≤ M)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) :
    excessLoss A f0 P = quadraticTarget A P -
      ∫ o, predictionContrast A f0 o ∂(P : Measure (Model.Observation A BoundedResponse)) := by
  let μ := (P : Measure (Model.Observation A BoundedResponse))
  let Y : Model.Observation A BoundedResponse → ℝ := ((Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd)
  let f : Model.Observation A BoundedResponse → ℝ := f0 ∘ Prod.fst
  let mY := μ[Y | Model.covariateInformation A BoundedResponse]
  have hY : MemLp Y 2 μ := Applications.bounded_memLp μ Y
    (measurable_subtype_coe.comp measurable_snd) 1 (fun o => response_bound o.2)
  have hfLp : MemLp f 2 μ := Applications.bounded_memLp μ f (hf.comp measurable_fst) M (fun o => hb o.1)
  have hmY : MemLp mY 2 μ := hY.condExp one_le_two
  have hYf : Integrable (fun o => Y o*f o) μ := memLp_one_iff_integrable.mp (hY.mul hfLp)
  have hmf : Integrable (fun o => mY o*f o) μ := memLp_one_iff_integrable.mp (hmY.mul hfLp)
  have hfs : StronglyMeasurable[Model.covariateInformation A BoundedResponse] f :=
    (hf.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable
  have hcross := Conditional.integral_mul_condExp measurable_fst.comap_le Y f
    (hY.integrable one_le_two) hfs hYf
  have hexp : (fun o => (mY o-f o)^2) =
      (fun o => (mY o)^2-2*(mY o*f o)+(f o)^2) := by funext o; ring
  unfold excessLoss predictionContrast quadraticTarget
  change (∫ o, (mY o-f o)^2 ∂μ) = (∫ o, (mY o)^2 ∂μ) -
    ∫ o, 2*Y o*f o-(f o)^2 ∂μ
  rw [hexp,integral_add (f := fun o => (mY o)^2-2*(mY o*f o)) (g := fun o => (f o)^2)
      (hmY.integrable_sq.sub (hmf.const_mul 2)) hfLp.integrable_sq,
    integral_sub (f := fun o => (mY o)^2) (g := fun o => 2*(mY o*f o))
      hmY.integrable_sq (hmf.const_mul 2),integral_const_mul,
    integral_sub (f := fun o => 2*Y o*f o) (g := fun o => (f o)^2) ((hYf.const_mul 2).congr (Filter.Eventually.of_forall (fun o => by ring))) hfLp.integrable_sq]
  have ht : (∫ o, 2*Y o*f o ∂μ) = 2*(∫ o, Y o*f o ∂μ) := by
    simp only [mul_assoc,integral_const_mul]
  rw [ht,hcross]
  ring

theorem predictionContrast_measurable (A : Model.Parameters) (f0 : Model.Covariate A.d → ℝ)
    (hf : Measurable f0) : Measurable (predictionContrast A f0) :=
  (((measurable_subtype_coe.comp measurable_snd).const_mul 2).mul (hf.comp measurable_fst)).sub
    ((hf.comp measurable_fst).pow_const 2)

theorem predictionContrast_bound (A : Model.Parameters) (f0 : Model.Covariate A.d → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, |f0 x| ≤ M) (o : Model.Observation A BoundedResponse) :
    |predictionContrast A f0 o| ≤ 2*M+M^2 := by
  unfold predictionContrast
  calc
    _ ≤ |2*(o.2 : ℝ)*f0 o.1|+|(f0 o.1)^2| := abs_sub _ _
    _ = 2 * |(o.2 : ℝ)| * |f0 o.1| + |f0 o.1|^2 := by simp only [abs_mul,abs_pow]; norm_num
    _ ≤ 2*1*M+M^2 := add_le_add
      (mul_le_mul (mul_le_mul_of_nonneg_left (response_bound o.2) (by norm_num)) (hb o.1)
        (abs_nonneg _) (by norm_num))
      (sq_le_sq₀ (abs_nonneg _) hM |>.mpr (hb o.1))
    _ = _ := by ring

theorem excessLoss_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (hd : A.δ ≤ 1)
    (f0 : Model.Covariate A.d → ℝ) (hf : Measurable f0)
    (M : ℝ) (hMpos : 0 ≤ M) (hb : ∀ x, |f0 x| ≤ M) :
    Model.UpperBracket (excessLoss A f0) (quadraticClass A) A.bracketParameters (A.nu : ℝ) := by
  apply Model.same_upperBracket_difference _ (quadraticTarget A)
    (fun P => ∫ o, predictionContrast A f0 o ∂(P : Measure (Model.Observation A BoundedResponse)))
    _ _ _ (quadratic_upperBracket A hM hd)
  · exact Model.observableMean_upperBracket _ (predictionContrast_measurable A f0 hf)
      (2*M+M^2) (by positivity) (predictionContrast_bound A f0 M hMpos hb)
      _ _ _ (by exact_mod_cast A.nu_ge_two)
  · intro P _
    exact excessLoss_identity A f0 hf M hb P


theorem quadraticClass_covariate_cube (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) (hP : P ∈ quadraticClass A) :
    ∀ᵐ o ∂(P : Measure (Model.Observation A BoundedResponse)), o.1 ∈ Model.cube A.d := by
  obtain ⟨W⟩ := hP
  apply ae_of_ae_map (f := Prod.fst) (p := fun x => x ∈ Model.cube A.d) measurable_fst.aemeasurable
  rw [W.marginal]
  exact (ae_restrict_mem (Model.isCompact_cube A.d).isClosed.measurableSet).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le

/-- Only the source cube bound on the known predictor is needed. The actual
estimator uses the measurable zero extension off the covariate support. -/
theorem excessLoss_upperBracket_cube (A : Model.Parameters) (hM : 1 ≤ A.M0) (hd : A.δ ≤ 1)
    (f0 : Model.Covariate A.d → ℝ) (hf : Measurable f0)
    (M : ℝ) (hMpos : 0 ≤ M) (hb : ∀ x ∈ Model.cube A.d, |f0 x| ≤ M) :
    Model.UpperBracket (excessLoss A f0) (quadraticClass A) A.bracketParameters (A.nu : ℝ) := by
  let f := (Model.cube A.d).indicator f0
  have hcube : MeasurableSet (Model.cube A.d) := (Model.isCompact_cube A.d).isClosed.measurableSet
  have hfb : ∀ x, |f x| ≤ M := by
    intro x
    by_cases hx : x ∈ Model.cube A.d
    · simpa only [f,indicator_of_mem hx] using hb x hx
    · simpa only [f,indicator_of_notMem hx,abs_zero] using hMpos
  apply Model.upperBracket_congr_target _ (excessLoss A f) _ _ _ _
    (excessLoss_upperBracket A hM hd f (hf.indicator hcube) M hMpos hfb)
  intro P hP
  apply integral_congr_ae
  filter_upwards [quadraticClass_covariate_cube A P hP] with o ho
  simp only [f,indicator_of_mem ho]

end RoughRegime.Applications.Products
