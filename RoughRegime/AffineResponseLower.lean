module

public import RoughRegime.LowerMeasure
public import RoughRegime.Applications
public import RoughRegime.ProductTarget
public import RoughRegime.DiagonalIntegrand


@[expose] public section
/-! Actual affine response probability laws for the local parametric lower bound. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace RoughRegime.AffineResponseLower

set_option backward.isDefEq.respectTransparency false

def clip (ε t : ℝ) : ℝ := max (-ε) (min ε t)

theorem clip_abs_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : |clip ε t| ≤ ε := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clip_eq {ε t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) : clip ε t = t := by
  simp [clip, min_eq_right (le_of_lt ht.2), max_eq_right (le_of_lt ht.1)]

variable {Z : Type*} [MeasurableSpace Z] (π : Measure Z) [IsProbabilityMeasure π]

theorem score_integrable (s : Z → ℝ) (hs : Measurable s) (C : ℝ)
    (hbound : ∀ z, |s z| ≤ C) : Integrable s π := by
  apply Integrable.of_bound hs.aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hbound z

omit [MeasurableSpace Z] in
theorem affine_density_lower (su sv : Z → ℝ) (u ε C t : ℝ)
    (hε : 0 ≤ ε) (_hC : 0 ≤ C) (hu : |u| ≤ ε) (hsmall : ε * C ≤ 1 / 4)
    (hbu : ∀ z, |su z| ≤ C) (hbv : ∀ z, |sv z| ≤ C) (z : Z) :
    1 / 2 ≤ 1 + u * su z + clip ε t * sv z := by
  have hu' : |u * su z| ≤ ε * C := by
    rw [abs_mul]
    exact mul_le_mul hu (hbu z) (abs_nonneg _) hε
  have hv' : |clip ε t * sv z| ≤ ε * C := by
    rw [abs_mul]
    exact mul_le_mul (clip_abs_le hε t) (hbv z) (abs_nonneg _) hε
  nlinarith [neg_le_abs (u * su z), neg_le_abs (clip ε t * sv z)]

/-- The affine response family, extended outside its valid local interval by
clipping only the parameter. Within `(-ε, ε)` it is the paper's exact affine law. -/
def responseDensityLaw (su sv : Z → ℝ) (hsu : Measurable su) (hsv : Measurable sv)
    (u ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hu : |u| ≤ ε)
    (hsmall : ε * C ≤ 1 / 4) (hbu : ∀ z, |su z| ≤ C) (hbv : ∀ z, |sv z| ≤ C)
    (hmu : (∫ z, su z ∂π) = 0) (hmv : (∫ z, sv z ∂π) = 0) (t : ℝ) :
    GeneralTesting.DensityLaw π where
  density z := 1 + u * su z + clip ε t * sv z
  measurable := by fun_prop
  integrable := ((integrable_const 1).add ((score_integrable π su hsu C hbu).const_mul u)).add
    ((score_integrable π sv hsv C hbv).const_mul (clip ε t))
  nonneg := Filter.Eventually.of_forall fun z => le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (affine_density_lower su sv u ε C t hε hC hu hsmall hbu hbv z)
  integral_one := by
    have hiu := score_integrable π su hsu C hbu
    have hiv := score_integrable π sv hsv C hbv
    have hi₁ : Integrable (fun z => 1 + u * su z) π := (integrable_const 1).add (hiu.const_mul u)
    rw [integral_add hi₁ (hiv.const_mul (clip ε t)),
      integral_add (integrable_const 1) (hiu.const_mul u), integral_const_mul, integral_const_mul,
      hmu, hmv]
    simp

def withDesign {X : Type*} [MeasurableSpace X] (η : Measure X) [IsProbabilityMeasure η]
    (L : GeneralTesting.DensityLaw π) : GeneralTesting.DensityLaw (η.prod π) where
  density x := L.density x.2
  measurable := L.measurable.comp measurable_snd
  integrable := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : X => (1 : ℝ)) η).mul_prod L.integrable
  nonneg := by
    filter_upwards [quasiMeasurePreserving_snd.tendsto_ae.eventually L.nonneg] with x hx
    exact hx
  integral_one := by
    rw [integral_fun_snd]
    simp [L.integral_one]

theorem withDesign_measure {X : Type*} [MeasurableSpace X] (η : Measure X)
    [IsProbabilityMeasure η] (L : GeneralTesting.DensityLaw π) :
    (withDesign π η L).measure = η.prod L.measure := by
  unfold withDesign GeneralTesting.DensityLaw.measure
  exact (prod_withDensity_right (ENNReal.measurable_ofReal.comp L.measurable)).symm

omit [IsProbabilityMeasure π] in
/-- Moment identity for actual probability measures induced by affine densities. -/
theorem integral_density_affine (L : GeneralTesting.DensityLaw π)
    (su sv f : Z → ℝ) (u v : ℝ)
    (hL : L.density =ᵐ[π] fun z => 1 + u * su z + v * sv z)
    (hf : Integrable f π) (hfu : Integrable (fun z => f z * su z) π)
    (hfv : Integrable (fun z => f z * sv z) π) :
    (∫ z, f z ∂L.measure) = (∫ z, f z ∂π) +
      u * (∫ z, f z * su z ∂π) + v * (∫ z, f z * sv z ∂π) := by
  unfold GeneralTesting.DensityLaw.measure
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun z => ENNReal.ofReal (L.density z))
    (ENNReal.measurable_ofReal.comp L.measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun z => (ENNReal.ofReal (L.density z)).toReal • f z) =ᵐ[π]
      fun z => f z + u * (f z * su z) + v * (f z * sv z) := by
    filter_upwards [L.nonneg, hL] with z hz hzd
    change 0 ≤ L.density z at hz
    rw [ENNReal.toReal_ofReal hz, smul_eq_mul, hzd]
    ring
  rw [integral_congr_ae he]
  have hi₁ : Integrable (fun z => f z + u * (f z * su z)) π := hf.add (hfu.const_mul u)
  rw [integral_add hi₁ (hfv.const_mul v), integral_add hf (hfu.const_mul u),
    integral_const_mul, integral_const_mul]

omit [IsProbabilityMeasure π] in
theorem densityLaw_integral_eq (L : GeneralTesting.DensityLaw π) (f : Z → ℝ) :
    (∫ z, f z ∂L.measure) = ∫ z, L.density z * f z ∂π := by
  unfold GeneralTesting.DensityLaw.measure
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun z => ENNReal.ofReal (L.density z))
    (ENNReal.measurable_ofReal.comp L.measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [L.nonneg] with z hz
  change 0 ≤ L.density z at hz
  simp [ENNReal.toReal_ofReal hz]

theorem densityLaw_bounded_mean_lower (L : GeneralTesting.DensityLaw π)
    (f : Z → ℝ) (hf : Measurable f) (M cf : ℝ) (_hM : 0 ≤ M)
    (hf0 : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ M)
    (hL : ∀ᵐ z ∂π, cf ≤ L.density z) :
    cf * (∫ z, f z ∂π) ≤ ∫ z, f z ∂L.measure := by
  have hfi : Integrable f π := score_integrable π f hf M
    (fun z => by rw [abs_of_nonneg (hf0 z)]; exact hfb z)
  have hprod : Integrable (fun z => L.density z * f z) π := by
    apply (L.integrable.const_mul M).mono' (L.measurable.mul hf).aestronglyMeasurable
    filter_upwards [L.nonneg] with z hz
    change 0 ≤ L.density z at hz
    change |L.density z * f z| ≤ M * L.density z
    rw [abs_of_nonneg (mul_nonneg hz (hf0 z))]
    nlinarith [mul_le_mul_of_nonneg_left (hfb z) hz]
  have hpoint : (fun z => cf * f z) ≤ᵐ[π] fun z => L.density z * f z := by
    filter_upwards [hL] with z hz
    exact mul_le_mul_of_nonneg_right hz (hf0 z)
  rw [densityLaw_integral_eq π L f]
  have hi := integral_mono_ae (hfi.const_mul cf) hprod hpoint
  simpa [integral_const_mul] using hi

theorem bounded_score_product_integrable (f s : Z → ℝ) (hf : Measurable f)
    (hs : Measurable s) (M K : ℝ) (hM : 0 ≤ M) (_hK : 0 ≤ K)
    (hfb : ∀ z, |f z| ≤ M) (hsb : ∀ z, |s z| ≤ K) :
    Integrable (fun z => f z * s z) π := by
  apply score_integrable π (fun z => f z * s z) (hf.mul hs) (M * K)
  intro z
  rw [abs_mul]
  exact mul_le_mul (hfb z) (hsb z) (abs_nonneg _) hM

omit [IsProbabilityMeasure π] in
theorem residual_score_integral (f g s : Z → ℝ) (a : ℝ)
    (hfs : Integrable (fun z => f z * s z) π) (hgs : Integrable (fun z => g z * s z) π) :
    (∫ z, (f z - a * g z) * s z ∂π) =
      (∫ z, f z * s z ∂π) - a * (∫ z, g z * s z ∂π) := by
  have he : (fun z => (f z - a * g z) * s z) =
      fun z => f z * s z - a * (g z * s z) := by funext z; ring
  rw [he, integral_sub hfs (hgs.const_mul a), integral_const_mul]

omit [IsProbabilityMeasure π] in
/-- Exact residual-score moment bridge, with all moments taken under actual laws.
Choosing `(au,av,bu,bv) = (1,0,0,1)` gives the positive-definite case;
choosing all four equal to one gives the diagonal case. -/
theorem residual_affine_moments (L : GeneralTesting.DensityLaw π)
    (su sv D U V : Z → ℝ) (u v a0 b0 au av bu bv : ℝ)
    (hL : L.density =ᵐ[π] fun z => 1 + u * su z + v * sv z)
    (hD : Integrable D π) (hDu : Integrable (fun z => D z * su z) π)
    (hDv : Integrable (fun z => D z * sv z) π)
    (hU : Integrable U π) (hUu : Integrable (fun z => U z * su z) π)
    (hUv : Integrable (fun z => U z * sv z) π)
    (hV : Integrable V π) (hVu : Integrable (fun z => V z * su z) π)
    (hVv : Integrable (fun z => V z * sv z) π)
    (hU0 : (∫ z, U z ∂π) = a0 * ∫ z, D z ∂π)
    (hV0 : (∫ z, V z ∂π) = b0 * ∫ z, D z ∂π)
    (hRu : (∫ z, U z * su z ∂π) = a0 * (∫ z, D z * su z ∂π) + au)
    (hRv : (∫ z, U z * sv z ∂π) = a0 * (∫ z, D z * sv z ∂π) + av)
    (hSu : (∫ z, V z * su z ∂π) = b0 * (∫ z, D z * su z ∂π) + bu)
    (hSv : (∫ z, V z * sv z ∂π) = b0 * (∫ z, D z * sv z ∂π) + bv) :
    (∫ z, U z ∂L.measure) = a0 * (∫ z, D z ∂L.measure) + au * u + av * v ∧
      (∫ z, V z ∂L.measure) = b0 * (∫ z, D z ∂L.measure) + bu * u + bv * v := by
  rw [integral_density_affine π L su sv D u v hL hD hDu hDv,
    integral_density_affine π L su sv U u v hL hU hUu hUv,
    integral_density_affine π L su sv V u v hL hV hVu hVv,
    hU0, hV0, hRu, hRv, hSu, hSv]
  constructor <;> ring

def responseFunctional (D U V W : Z → ℝ) (lam : ℝ) (ν : Measure Z) : ℝ :=
  (∫ z, W z ∂ν) + lam * ((∫ z, U z ∂ν) * (∫ z, V z ∂ν) / (∫ z, D z ∂ν))

/-- The paper's affine coefficients obtained from actual baseline moments. -/
def embeddedIntegrand (su sv D W : Z → ℝ) (lam a0 b0 u v : ℝ) : ℝ :=
  Applications.localIntegrand
    ((∫ z, W z ∂π) + lam * (a0 * b0 * ∫ z, D z ∂π))
    ((∫ z, W z * su z ∂π) + lam * (a0 * b0 * (∫ z, D z * su z ∂π) + b0))
    ((∫ z, W z * sv z ∂π) + lam * (a0 * b0 * (∫ z, D z * sv z ∂π) + a0))
    lam (∫ z, D z ∂π) (∫ z, D z * su z ∂π) (∫ z, D z * sv z ∂π) u v

omit [IsProbabilityMeasure π] in
/-- The target representation is derived from baseline residual-score moments
under actual probability measures. No target representation is a premise. -/
theorem responseFunctional_eq_embeddedIntegrand (L : GeneralTesting.DensityLaw π)
    (su sv D U V W : Z → ℝ) (u v a0 b0 lam : ℝ)
    (hL : L.density =ᵐ[π] fun z => 1 + u * su z + v * sv z)
    (hD : Integrable D π) (hDu : Integrable (fun z => D z * su z) π)
    (hDv : Integrable (fun z => D z * sv z) π)
    (hU : Integrable U π) (hUu : Integrable (fun z => U z * su z) π)
    (hUv : Integrable (fun z => U z * sv z) π)
    (hV : Integrable V π) (hVu : Integrable (fun z => V z * su z) π)
    (hVv : Integrable (fun z => V z * sv z) π)
    (hW : Integrable W π) (hWu : Integrable (fun z => W z * su z) π)
    (hWv : Integrable (fun z => W z * sv z) π)
    (hU0 : (∫ z, U z ∂π) = a0 * ∫ z, D z ∂π)
    (hV0 : (∫ z, V z ∂π) = b0 * ∫ z, D z ∂π)
    (hRu : (∫ z, U z * su z ∂π) = a0 * (∫ z, D z * su z ∂π) + 1)
    (hRv : (∫ z, U z * sv z ∂π) = a0 * (∫ z, D z * sv z ∂π))
    (hSu : (∫ z, V z * su z ∂π) = b0 * (∫ z, D z * su z ∂π))
    (hSv : (∫ z, V z * sv z ∂π) = b0 * (∫ z, D z * sv z ∂π) + 1)
    (hw : (∫ z, D z ∂π) + u * (∫ z, D z * su z ∂π) + v * (∫ z, D z * sv z ∂π) ≠ 0) :
    responseFunctional D U V W lam L.measure = embeddedIntegrand π su sv D W lam a0 b0 u v := by
  have hu0 : (∫ z, U z ∂L.measure) = a0 * (∫ z, D z ∂L.measure) + u := by
    simpa using (residual_affine_moments π L su sv D U V u v a0 b0 1 0 0 1 hL
      hD hDu hDv hU hUu hUv hV hVu hVv hU0 hV0 hRu (by simpa using hRv)
      (by simpa using hSu) hSv).1
  have hv0 : (∫ z, V z ∂L.measure) = b0 * (∫ z, D z ∂L.measure) + v := by
    simpa using (residual_affine_moments π L su sv D U V u v a0 b0 1 0 0 1 hL
      hD hDu hDv hU hUu hUv hV hVu hVv hU0 hV0 hRu (by simpa using hRv)
      (by simpa using hSu) hSv).2
  unfold responseFunctional embeddedIntegrand Applications.localIntegrand
  rw [hu0, hv0, integral_density_affine π L su sv D u v hL hD hDu hDv,
    integral_density_affine π L su sv W u v hL hW hWu hWv]
  have hw' : (∫ z, D z ∂π) + (∫ z, D z * su z ∂π) * u +
      (∫ z, D z * sv z ∂π) * v ≠ 0 := by simpa [mul_comm] using hw
  field_simp
  ring

theorem model_target_withDesign (A : Model.Parameters) (F : Model.Observables Z A)
    (η : Measure (Model.Covariate A.d)) [IsProbabilityMeasure η]
    (L : GeneralTesting.DensityLaw π) :
    Model.target A F (withDesign π η L).probabilityMeasure =
      responseFunctional F.D F.U F.V F.W F.lam L.measure := by
  have hP : (withDesign π η L).probabilityMeasure =
      (⟨η.prod L.measure, inferInstance⟩ : ProbabilityMeasure (Model.Covariate A.d × Z)) := by
    apply Subtype.ext
    exact withDesign_measure π η L
  rw [hP, Applications.target_product A F η L.measure]
  rfl

/-- Positive-definite score embedding into the actual generic target on product
laws. All integrability and the denominator's positivity are proved from the
observable bounds and the lower density bound. -/
theorem model_target_response_affine (A : Model.Parameters) (F : Model.Observables Z A)
    (η : Measure (Model.Covariate A.d)) [IsProbabilityMeasure η]
    (L : GeneralTesting.DensityLaw π) (su sv : Z → ℝ)
    (hsu : Measurable su) (hsv : Measurable sv) (K : ℝ) (hK : 0 ≤ K)
    (hbu : ∀ z, |su z| ≤ K) (hbv : ∀ z, |sv z| ≤ K)
    (u v a0 b0 : ℝ) (hbase : 0 < ∫ z, F.D z ∂π)
    (hL : L.density =ᵐ[π] fun z => 1 + u * su z + v * sv z)
    (hlower : ∀ᵐ z ∂π, (1 / 2 : ℝ) ≤ L.density z)
    (hU0 : (∫ z, F.U z ∂π) = a0 * ∫ z, F.D z ∂π)
    (hV0 : (∫ z, F.V z ∂π) = b0 * ∫ z, F.D z ∂π)
    (hRu : (∫ z, (F.U z - a0 * F.D z) * su z ∂π) = 1)
    (hRv : (∫ z, (F.U z - a0 * F.D z) * sv z ∂π) = 0)
    (hSu : (∫ z, (F.V z - b0 * F.D z) * su z ∂π) = 0)
    (hSv : (∫ z, (F.V z - b0 * F.D z) * sv z ∂π) = 1) :
    Model.target A F (withDesign π η L).probabilityMeasure =
      embeddedIntegrand π su sv F.D F.W F.lam a0 b0 u v := by
  have hDb (z : Z) : |F.D z| ≤ A.M0 := by
    rw [abs_of_nonneg (F.boundD z).1]
    exact (F.boundD z).2
  have hD := score_integrable π F.D F.measurableD A.M0 hDb
  have hU := score_integrable π F.U F.measurableU A.M0 F.boundU
  have hV := score_integrable π F.V F.measurableV A.M0 F.boundV
  have hDu := bounded_score_product_integrable π F.D su F.measurableD hsu A.M0 K
    (le_of_lt A.hM0) hK hDb hbu
  have hDv := bounded_score_product_integrable π F.D sv F.measurableD hsv A.M0 K
    (le_of_lt A.hM0) hK hDb hbv
  have hUu := bounded_score_product_integrable π F.U su F.measurableU hsu A.M0 K
    (le_of_lt A.hM0) hK F.boundU hbu
  have hUv := bounded_score_product_integrable π F.U sv F.measurableU hsv A.M0 K
    (le_of_lt A.hM0) hK F.boundU hbv
  have hVu := bounded_score_product_integrable π F.V su F.measurableV hsu A.M0 K
    (le_of_lt A.hM0) hK F.boundV hbu
  have hVv := bounded_score_product_integrable π F.V sv F.measurableV hsv A.M0 K
    (le_of_lt A.hM0) hK F.boundV hbv
  obtain ⟨MW, hMW, hWb⟩ := F.boundW
  have hW := score_integrable π F.W F.measurableW MW hWb
  have hWu := bounded_score_product_integrable π F.W su F.measurableW hsu MW K hMW hK hWb hbu
  have hWv := bounded_score_product_integrable π F.W sv F.measurableW hsv MW K hMW hK hWb hbv
  rw [residual_score_integral π F.U F.D su a0 hUu hDu] at hRu
  rw [residual_score_integral π F.U F.D sv a0 hUv hDv] at hRv
  rw [residual_score_integral π F.V F.D su b0 hVu hDu] at hSu
  rw [residual_score_integral π F.V F.D sv b0 hVv hDv] at hSv
  have hmean := densityLaw_bounded_mean_lower π L F.D F.measurableD A.M0 (1 / 2)
    (le_of_lt A.hM0) (fun z => (F.boundD z).1) (fun z => (F.boundD z).2) hlower
  rw [integral_density_affine π L su sv F.D u v hL hD hDu hDv] at hmean
  have hw : (∫ z, F.D z ∂π) + u * (∫ z, F.D z * su z ∂π) +
      v * (∫ z, F.D z * sv z ∂π) ≠ 0 := by linarith
  rw [model_target_withDesign π A F η L]
  exact responseFunctional_eq_embeddedIntegrand π L su sv F.D F.U F.V F.W u v a0 b0 F.lam
    hL hD hDu hDv hU hUu hUv hV hVu hVv hW hWu hWv hU0 hV0
    (by linarith) (by linarith) (by linarith) (by linarith) hw

/-- The parametric statistical conclusion in Proposition 15(b), for the actual
product response laws. The target identity is precisely the proposition's
assumption `T(P_t) = F(u_*, t) + t_*`; it is not a testing or risk assumption. -/
theorem response_parametric_minimax_bound {X : Type*} [MeasurableSpace X]
    (η : Measure X) [IsProbabilityMeasure η]
    (su sv : Z → ℝ) (hsu : Measurable su) (hsv : Measurable sv)
    (u ε K : ℝ) (hε : 0 < ε) (hK : 0 ≤ K) (hu : |u| ≤ ε)
    (hsmall : ε * K ≤ 1 / 4) (hbu : ∀ z, |su z| ≤ K) (hbv : ∀ z, |sv z| ≤ K)
    (hmu : (∫ z, su z ∂π) = 0) (hmv : (∫ z, sv z ∂π) = 0)
    (c0 cu cv lam w0 du dv tstar : ℝ) (hw : w0 + du * u ≠ 0)
    (hD : cv + lam * u / (w0 + du * u) ≠ 0)
    (T : ProbabilityMeasure (X × Z) → ℝ) (C : Set (ProbabilityMeasure (X × Z))) :
    let P := fun t => withDesign π η
      (responseDensityLaw π su sv hsu hsv u ε K (le_of_lt hε) hK hu hsmall hbu hbv hmu hmv t)
    (∀ t ∈ Set.Ioo (-ε) ε, (P t).probabilityMeasure ∈ C) →
    (∀ t ∈ Set.Ioo (-ε) ε, T (P t).probabilityMeasure =
      Applications.localIntegrand c0 cu cv lam w0 du dv u t + tstar) →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Model.minimaxRMSE n T C := by
  classical
  dsimp only
  intro hclass htarget
  let P := fun t => withDesign π η
    (responseDensityLaw π su sv hsu hsv u ε K (le_of_lt hε) hK hu hsmall hbu hbv hmu hmv t)
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by constructor <;> linarith
  have hteq : (fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
      fun t => Applications.localIntegrand c0 cu cv lam w0 du dv u t + tstar := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with t ht
    exact htarget t ht
  have hbase := Applications.localIntegrand_v_hasDerivAt c0 cu cv lam w0 du dv u hw
  have hshift := hbase.add_const tstar
  have hder := hshift.congr_of_eventuallyEq hteq
  have hdens : ∀ t ∈ Set.Ioo (-ε) ε, (P t).density =ᵐ[η.prod π]
      fun x => (1 + u * su x.2) + t * sv x.2 := by
    intro t ht
    exact Filter.Eventually.of_forall fun x => by
      change 1 + u * su x.2 + clip ε t * sv x.2 = _
      rw [clip_eq ht]
  have hpos : ∀ t ∈ Set.Ioo (-ε) ε, ∀ᵐ x ∂η.prod π,
      (1 / 2 : ℝ) ≤ (1 + u * su x.2) + t * sv x.2 := by
    intro t ht
    exact Filter.Eventually.of_forall fun x => by
      simpa [clip_eq ht] using affine_density_lower su sv u ε K t (le_of_lt hε) hK hu hsmall hbu hbv x.2
  have hscore : ∀ᵐ x ∂η.prod π, |sv x.2| ≤ K := Filter.Eventually.of_forall fun x => hbv x.2
  obtain ⟨c, hc, hrisk⟩ := LowerMeasure.parametric_path_minimax_bound P
    (fun x => 1 + u * su x.2) (fun x => sv x.2) T C (-ε) ε 0
    (cv + lam * u / (w0 + du * u)) (1 / 2) K h0 hder hD (by norm_num) hK hdens hpos hscore hclass
  refine ⟨c, hc, ?_⟩
  exact hrisk.mono fun _ hn => hn.1

/-- Arbitrary local class neighborhoods suffice; the response law is the actual
product law and its bounded likelihood score supplies the testing estimate. -/
theorem response_path_minimax_bound {X : Type*} [MeasurableSpace X]
    (η : Measure X) [IsProbabilityMeasure η]
    (su sv : Z → ℝ) (hsu : Measurable su) (hsv : Measurable sv)
    (u ε K : ℝ) (hε : 0 < ε) (hK : 0 ≤ K) (hu : |u| ≤ ε)
    (hsmall : ε * K ≤ 1 / 4) (hbu : ∀ z, |su z| ≤ K) (hbv : ∀ z, |sv z| ≤ K)
    (hmu : (∫ z, su z ∂π) = 0) (hmv : (∫ z, sv z ∂π) = 0)
    (G : ℝ → ℝ) (D tstar : ℝ) (hG : HasDerivAt G D 0) (hD : D ≠ 0)
    (T : ProbabilityMeasure (X × Z) → ℝ) (C : Set (ProbabilityMeasure (X × Z))) :
    let P := fun t => withDesign π η
      (responseDensityLaw π su sv hsu hsv u ε K (le_of_lt hε) hK hu hsmall hbu hbv hmu hmv t)
    (∀ᶠ t in nhds 0, (P t).probabilityMeasure ∈ C) →
    ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0] fun t => G t + tstar) →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Model.minimaxRMSE n T C := by
  classical
  dsimp only
  intro hclass htarget
  let P := fun t => withDesign π η
    (responseDensityLaw π su sv hsu hsv u ε K (le_of_lt hε) hK hu hsmall hbu hbv hmu hmv t)
  have hlocal : ∀ᶠ t : ℝ in nhds 0,
      t ∈ Set.Ioo (-ε) ε ∧ (P t).probabilityMeasure ∈ C := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε, hclass] with t ht htc
    exact ⟨ht, htc⟩
  obtain ⟨l, r, h0, hsub⟩ := hlocal.exists_Ioo_subset
  have hdens : ∀ t ∈ Set.Ioo l r, (P t).density =ᵐ[η.prod π]
      fun x => (1 + u * su x.2) + t * sv x.2 := by
    intro t ht
    exact Filter.Eventually.of_forall fun x => by
      change 1 + u * su x.2 + clip ε t * sv x.2 = _
      rw [clip_eq (hsub ht).1]
  have hpos : ∀ t ∈ Set.Ioo l r, ∀ᵐ x ∂η.prod π,
      (1 / 2 : ℝ) ≤ (1 + u * su x.2) + t * sv x.2 := by
    intro t ht
    exact Filter.Eventually.of_forall fun x => by
      simpa [clip_eq (hsub ht).1] using affine_density_lower su sv u ε K t
        (le_of_lt hε) hK hu hsmall hbu hbv x.2
  have hscore : ∀ᵐ x ∂η.prod π, |sv x.2| ≤ K := Filter.Eventually.of_forall fun x => hbv x.2
  have hder := (hG.add_const tstar).congr_of_eventuallyEq htarget
  obtain ⟨c, hc, hrisk⟩ := LowerMeasure.parametric_path_minimax_bound P
    (fun x => 1 + u * su x.2) (fun x => sv x.2) T C l r 0 D (1 / 2) K
    h0 hder hD (by norm_num) hK hdens hpos hscore (fun t ht => (hsub ht).2)
  exact ⟨c, hc, hrisk.mono fun _ hn => hn.1⟩

/-- Proposition 15(b), positive-definite-score case, for actual product laws.
The class may contain the path on any neighborhood of zero. The only assumption
on the parameter is the paper's fixed additive shift of the actual target. -/
theorem actual_target_rootn_near (A : Model.Parameters) (F : Model.Observables Z A)
    (η : Measure (Model.Covariate A.d)) [IsProbabilityMeasure η]
    (su sv : Z → ℝ) (hsu : Measurable su) (hsv : Measurable sv)
    (ε K : ℝ) (hε : 0 < ε) (hK : 0 ≤ K) (hsmall : ε * K ≤ 1 / 4)
    (hbu : ∀ z, |su z| ≤ K) (hbv : ∀ z, |sv z| ≤ K)
    (hmu : (∫ z, su z ∂π) = 0) (hmv : (∫ z, sv z ∂π) = 0)
    (a0 b0 : ℝ) (hbase : 0 < ∫ z, F.D z ∂π)
    (hU0 : (∫ z, F.U z ∂π) = a0 * ∫ z, F.D z ∂π)
    (hV0 : (∫ z, F.V z ∂π) = b0 * ∫ z, F.D z ∂π)
    (hRu : (∫ z, (F.U z - a0 * F.D z) * su z ∂π) = 1)
    (hRv : (∫ z, (F.U z - a0 * F.D z) * sv z ∂π) = 0)
    (hSu : (∫ z, (F.V z - b0 * F.D z) * su z ∂π) = 0)
    (hSv : (∫ z, (F.V z - b0 * F.D z) * sv z ∂π) = 1) :
    ∀ᶠ u : ℝ in nhds 0, u ≠ 0 → ∃ hu : |u| ≤ ε,
      let P := fun t => withDesign π η
        (responseDensityLaw π su sv hsu hsv u ε K (le_of_lt hε) hK hu hsmall hbu hbv hmu hmv t)
      ∀ (T : ProbabilityMeasure (Model.Covariate A.d × Z) → ℝ)
        (C : Set (ProbabilityMeasure (Model.Covariate A.d × Z))) (tstar : ℝ),
        (∀ᶠ t in nhds 0, (P t).probabilityMeasure ∈ C) →
        ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
          fun t => Model.target A F (P t).probabilityMeasure + tstar) →
        ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
          ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Model.minimaxRMSE n T C := by
  let c0 := (∫ z, F.W z ∂π) + F.lam * (a0 * b0 * ∫ z, F.D z ∂π)
  let cu := (∫ z, F.W z * su z ∂π) +
    F.lam * (a0 * b0 * (∫ z, F.D z * su z ∂π) + b0)
  let cv := (∫ z, F.W z * sv z ∂π) +
    F.lam * (a0 * b0 * (∫ z, F.D z * sv z ∂π) + a0)
  let w0 := ∫ z, F.D z ∂π
  let du := ∫ z, F.D z * su z ∂π
  let dv := ∫ z, F.D z * sv z ∂π
  have hw0 : w0 ≠ 0 := ne_of_gt hbase
  have hden : ∀ᶠ u : ℝ in nhds 0, w0 + du * u ≠ 0 := by
    have hc : ContinuousAt (fun u : ℝ => w0 + du * u) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hw0)
  have hslope := Applications.localIntegrand_nonzero_slope_near c0 cu cv F.lam w0 du dv
    F.hlam hw0
  have hu_near : ∀ᶠ u : ℝ in nhds 0, |u| ≤ ε := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε] with u hu
    exact abs_le.mpr ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  filter_upwards [hden, hslope, hu_near] with u hdu hsu' hu
  intro hune
  refine ⟨hu, ?_⟩
  dsimp only
  intro T C tstar hclass htarget
  let L := fun t => responseDensityLaw π su sv hsu hsv u ε K (le_of_lt hε) hK hu
    hsmall hbu hbv hmu hmv t
  let P := fun t => withDesign π η (L t)
  have hrepr : (fun t => Model.target A F (P t).probabilityMeasure) =ᶠ[nhds 0]
      fun t => Applications.localIntegrand c0 cu cv F.lam w0 du dv u t := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε] with t ht
    have hLd : (L t).density =ᵐ[π] fun z => 1 + u * su z + t * sv z :=
      Filter.Eventually.of_forall fun z => by
        change 1 + u * su z + clip ε t * sv z = _
        rw [clip_eq ht]
    have hLl : ∀ᵐ z ∂π, (1 / 2 : ℝ) ≤ (L t).density z :=
      Filter.Eventually.of_forall fun z =>
        affine_density_lower su sv u ε K t (le_of_lt hε) hK hu hsmall hbu hbv z
    exact model_target_response_affine π A F η (L t) su sv hsu hsv K hK hbu hbv
      u t a0 b0 hbase hLd hLl hU0 hV0 hRu hRv hSu hSv
  have htG : (fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
      fun t => Applications.localIntegrand c0 cu cv F.lam w0 du dv u t + tstar := by
    filter_upwards [htarget, hrepr] with t ht hr
    exact ht.trans (congrArg (fun x => x + tstar) hr)
  have hG := Applications.localIntegrand_v_hasDerivAt c0 cu cv F.lam w0 du dv u hdu
  have hD : cv + F.lam * u / (w0 + du * u) ≠ 0 := by
    rw [← hG.deriv]
    exact hsu' hune
  exact response_path_minimax_bound π η su sv hsu hsv u ε K hε hK hu hsmall hbu hbv hmu hmv
    (fun t => Applications.localIntegrand c0 cu cv F.lam w0 du dv u t)
    (cv + F.lam * u / (w0 + du * u)) tstar hG hD T C hclass htG

def embeddedDiagonalIntegrand (s D W : Z → ℝ) (lam a0 u v : ℝ) : ℝ :=
  Applications.diagonalIntegrand
    ((∫ z, W z ∂π) + lam * (a0 ^ 2 * ∫ z, D z ∂π))
    ((∫ z, W z * s z ∂π) + lam * (a0 ^ 2 * (∫ z, D z * s z ∂π) + 2 * a0))
    ((∫ z, W z * s z ∂π) + lam * (a0 ^ 2 * (∫ z, D z * s z ∂π) + 2 * a0))
    lam (∫ z, D z ∂π) (∫ z, D z * s z ∂π) (∫ z, D z * s z ∂π) u v

/-- The actual target representation for a common diagonal score. -/
theorem model_target_response_diagonal (A : Model.Parameters) (F : Model.Observables Z A)
    (η : Measure (Model.Covariate A.d)) [IsProbabilityMeasure η]
    (L : GeneralTesting.DensityLaw π) (s : Z → ℝ) (hs : Measurable s)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ z, |s z| ≤ K)
    (u v a0 : ℝ) (hbase : 0 < ∫ z, F.D z ∂π)
    (hL : L.density =ᵐ[π] fun z => 1 + u * s z + v * s z)
    (hlower : ∀ᵐ z ∂π, (1 / 2 : ℝ) ≤ L.density z)
    (hUV : F.U = F.V)
    (hU0 : (∫ z, F.U z ∂π) = a0 * ∫ z, F.D z ∂π)
    (hR : (∫ z, (F.U z - a0 * F.D z) * s z ∂π) = 1) :
    Model.target A F (withDesign π η L).probabilityMeasure =
      embeddedDiagonalIntegrand π s F.D F.W F.lam a0 u v := by
  have hDb (z : Z) : |F.D z| ≤ A.M0 := by
    rw [abs_of_nonneg (F.boundD z).1]
    exact (F.boundD z).2
  have hD := score_integrable π F.D F.measurableD A.M0 hDb
  have hU := score_integrable π F.U F.measurableU A.M0 F.boundU
  have hDs := bounded_score_product_integrable π F.D s F.measurableD hs A.M0 K
    (le_of_lt A.hM0) hK hDb hb
  have hUs := bounded_score_product_integrable π F.U s F.measurableU hs A.M0 K
    (le_of_lt A.hM0) hK F.boundU hb
  obtain ⟨MW, hMW, hWb⟩ := F.boundW
  have hW := score_integrable π F.W F.measurableW MW hWb
  have hWs := bounded_score_product_integrable π F.W s F.measurableW hs MW K hMW hK hWb hb
  rw [residual_score_integral π F.U F.D s a0 hUs hDs] at hR
  have hu0 : (∫ z, F.U z ∂L.measure) = a0 * (∫ z, F.D z ∂L.measure) + u + v := by
    rw [integral_density_affine π L s s F.U u v hL hU hUs hUs,
      integral_density_affine π L s s F.D u v hL hD hDs hDs, hU0]
    have hRU : (∫ z, F.U z * s z ∂π) = a0 * (∫ z, F.D z * s z ∂π) + 1 := by linarith
    rw [hRU]
    ring
  have hmean := densityLaw_bounded_mean_lower π L F.D F.measurableD A.M0 (1 / 2)
    (le_of_lt A.hM0) (fun z => (F.boundD z).1) (fun z => (F.boundD z).2) hlower
  rw [integral_density_affine π L s s F.D u v hL hD hDs hDs] at hmean
  have hw : (∫ z, F.D z ∂π) + u * (∫ z, F.D z * s z ∂π) +
      v * (∫ z, F.D z * s z ∂π) ≠ 0 := by linarith
  rw [model_target_withDesign π A F η L]
  unfold responseFunctional embeddedDiagonalIntegrand Applications.diagonalIntegrand
  rw [← hUV, hu0, integral_density_affine π L s s F.D u v hL hD hDs hDs,
    integral_density_affine π L s s F.W u v hL hW hWs hWs]
  have hw' : (∫ z, F.D z ∂π) + (∫ z, F.D z * s z ∂π) * u +
      (∫ z, F.D z * s z ∂π) * v ≠ 0 := by simpa [mul_comm] using hw
  field_simp
  ring

/-- Proposition 15(b), diagonal-score case, including all sufficiently small
nonzero fixed perturbations and every local class neighborhood. -/
theorem actual_diagonal_target_rootn_near (A : Model.Parameters) (F : Model.Observables Z A)
    (η : Measure (Model.Covariate A.d)) [IsProbabilityMeasure η]
    (s : Z → ℝ) (hs : Measurable s) (ε K : ℝ)
    (hε : 0 < ε) (hK : 0 ≤ K) (hsmall : ε * K ≤ 1 / 4)
    (hb : ∀ z, |s z| ≤ K) (hm : (∫ z, s z ∂π) = 0)
    (a0 : ℝ) (hbase : 0 < ∫ z, F.D z ∂π) (hUV : F.U = F.V)
    (hU0 : (∫ z, F.U z ∂π) = a0 * ∫ z, F.D z ∂π)
    (hR : (∫ z, (F.U z - a0 * F.D z) * s z ∂π) = 1) :
    ∀ᶠ u : ℝ in nhds 0, u ≠ 0 → ∃ hu : |u| ≤ ε,
      let P := fun t => withDesign π η
        (responseDensityLaw π s s hs hs u ε K (le_of_lt hε) hK hu hsmall hb hb hm hm t)
      ∀ (T : ProbabilityMeasure (Model.Covariate A.d × Z) → ℝ)
        (C : Set (ProbabilityMeasure (Model.Covariate A.d × Z))) (tstar : ℝ),
        (∀ᶠ t in nhds 0, (P t).probabilityMeasure ∈ C) →
        ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
          fun t => Model.target A F (P t).probabilityMeasure + tstar) →
        ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
          ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Model.minimaxRMSE n T C := by
  let c0 := (∫ z, F.W z ∂π) + F.lam * (a0 ^ 2 * ∫ z, F.D z ∂π)
  let c1 := (∫ z, F.W z * s z ∂π) +
    F.lam * (a0 ^ 2 * (∫ z, F.D z * s z ∂π) + 2 * a0)
  let w0 := ∫ z, F.D z ∂π
  let d1 := ∫ z, F.D z * s z ∂π
  have hw0 : w0 ≠ 0 := ne_of_gt hbase
  have hden : ∀ᶠ u : ℝ in nhds 0, w0 + d1 * u ≠ 0 := by
    have hc : ContinuousAt (fun u : ℝ => w0 + d1 * u) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hw0)
  have hslope := Applications.diagonalIntegrand_nonzero_slope_near c0 c1 c1 F.lam w0 d1 d1
    F.hlam hw0
  have hu_near : ∀ᶠ u : ℝ in nhds 0, |u| ≤ ε := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε] with u hu
    exact abs_le.mpr ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  filter_upwards [hden, hslope, hu_near] with u hdu hsu' hu
  intro hune
  refine ⟨hu, ?_⟩
  dsimp only
  intro T C tstar hclass htarget
  let L := fun t => responseDensityLaw π s s hs hs u ε K (le_of_lt hε) hK hu hsmall hb hb hm hm t
  let P := fun t => withDesign π η (L t)
  have hrepr : (fun t => Model.target A F (P t).probabilityMeasure) =ᶠ[nhds 0]
      fun t => Applications.diagonalIntegrand c0 c1 c1 F.lam w0 d1 d1 u t := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε] with t ht
    have hLd : (L t).density =ᵐ[π] fun z => 1 + u * s z + t * s z :=
      Filter.Eventually.of_forall fun z => by
        change 1 + u * s z + clip ε t * s z = _
        rw [clip_eq ht]
    have hLl : ∀ᵐ z ∂π, (1 / 2 : ℝ) ≤ (L t).density z :=
      Filter.Eventually.of_forall fun z =>
        affine_density_lower s s u ε K t (le_of_lt hε) hK hu hsmall hb hb z
    exact model_target_response_diagonal π A F η (L t) s hs K hK hb
      u t a0 hbase hLd hLl hUV hU0 hR
  have htG : (fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
      fun t => Applications.diagonalIntegrand c0 c1 c1 F.lam w0 d1 d1 u t + tstar := by
    filter_upwards [htarget, hrepr] with t ht hr
    exact ht.trans (congrArg (fun x => x + tstar) hr)
  have hG := Applications.diagonalIntegrand_v_hasDerivAt c0 c1 c1 F.lam w0 d1 d1 u hdu
  have hD : Applications.diagonalSlope c1 F.lam w0 d1 d1 u ≠ 0 := by
    rw [← hG.deriv]
    exact hsu' hune
  exact response_path_minimax_bound π η s s hs hs u ε K hε hK hu hsmall hb hb hm hm
    (fun t => Applications.diagonalIntegrand c0 c1 c1 F.lam w0 d1 d1 u t)
    (Applications.diagonalSlope c1 F.lam w0 d1 d1 u) tstar hG hD T C hclass htG

end RoughRegime.AffineResponseLower
