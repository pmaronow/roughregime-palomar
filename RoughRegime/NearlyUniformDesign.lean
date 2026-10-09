module

public import RoughRegime.ProductSmoothBrackets
public import RoughRegime.RatePolynomialConsequences


@[expose] public section
/-! The smooth, nearly uniform design assertion uses an explicit density
and an actual conditional mean. No bound on any derivative of the density
is part of this class. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff
namespace RoughRegime.Applications.Products

structure SmoothQuadraticWitness (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) where
  p : Model.Covariate A.d → ℝ
  m : Model.Covariate A.d → ℝ
  measurableP : Measurable p
  smoothP : ContDiff ℝ ∞ p
  measurableM : Measurable m
  marginal : (P : Measure (Model.Observation A BoundedResponse)).map Prod.fst =
    (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x))
  moment : (P : Measure (Model.Observation A BoundedResponse))[
    (Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd |
      Model.covariateInformation A BoundedResponse] =ᵐ[
        (P : Measure (Model.Observation A BoundedResponse))] m ∘ Prod.fst
  smoothM : m ∈ Model.holderBall A.α A.H
  densityBounds : ∀ᵐ x ∂Model.cubeVolume A.d, A.gminus ≤ p x ∧ p x ≤ A.gplus

def smoothQuadraticClass (A : Model.Parameters) :
    Set (ProbabilityMeasure (Model.Observation A BoundedResponse)) :=
  {P | Nonempty (SmoothQuadraticWitness A P)}

/-- Smoothness can be required of the same density that obeys the design
bounds: equality of the two marginal measures forces their positive
densities to agree almost everywhere. -/
theorem smoothQuadraticClass_eq (A : Model.Parameters) (hab : A.α = A.β) :
    smoothQuadraticClass A = quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse := by
  ext P
  constructor
  · rintro ⟨W⟩
    refine ⟨⟨{
      p := W.p
      mU := W.m
      mV := W.m
      measurableP := W.measurableP
      measurableU := W.measurableM
      measurableV := W.measurableM
      nonnegativeP := ?_
      marginal := W.marginal
      momentU := W.moment
      momentV := W.moment
      smoothU := W.smoothM
      smoothV := ?_
      densityBounds := W.densityBounds }⟩,
      W.p, W.smoothP, W.marginal⟩
    · filter_upwards [W.densityBounds] with x hx
      exact A.hgminus.le.trans hx.1
    · simpa only [← hab] using W.smoothM
  · rintro ⟨⟨W⟩, q, hq, hqm⟩
    have he : (fun x => ENNReal.ofReal (W.p x)) =ᵐ[Model.cubeVolume A.d]
        (fun x => ENNReal.ofReal (q x)) :=
      (withDensity_eq_iff_of_sigmaFinite
        (ENNReal.measurable_ofReal.comp W.measurableP).aemeasurable
        (ENNReal.measurable_ofReal.comp hq.continuous.measurable).aemeasurable).mp
        (W.marginal.symm.trans hqm)
    have hpq : W.p =ᵐ[Model.cubeVolume A.d] q := by
      filter_upwards [he, W.densityBounds] with x hx hb
      have hp : 0 < W.p x := A.hgminus.trans_le hb.1
      have hqpos : 0 < q x := ENNReal.ofReal_pos.mp
        (hx ▸ ENNReal.ofReal_pos.mpr hp)
      exact (ENNReal.ofReal_eq_ofReal_iff hp.le hqpos.le).mp hx
    refine ⟨{
      p := q
      m := W.mU
      measurableP := hq.continuous.measurable
      smoothP := hq
      measurableM := W.measurableU
      marginal := hqm
      moment := W.momentU
      smoothM := W.smoothU
      densityBounds := ?_ }⟩
    filter_upwards [W.densityBounds, hpq] with x hx heq
    simpa only [heq] using hx

theorem smoothQuadraticClass_eq_generic (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hdelta : A.δ ≤ 1) (hab : A.α = A.β) :
    smoothQuadraticClass A = Model.modelClass A (quadraticObservables A hM) ∩
      Model.smoothDensityClass A.d BoundedResponse := by
  rw [smoothQuadraticClass_eq A hab]
  exact congrArg (fun C => C ∩ Model.smoothDensityClass A.d BoundedResponse)
    (modelClass_eq_generic A (quadraticObservables A hM) rfl hdelta)

/-- In the literal quadratic model the conditional weight is one, so the
bounded quantity `g=w*p` is the design density itself. -/
theorem quadratic_weighted_density_eq {A : Model.Parameters} (hM : 1 ≤ A.M0)
    {P : ProbabilityMeasure (Model.Observation A BoundedResponse)}
    (W : Model.ModelWitness A (quadraticObservables A hM) P) :
    (fun x => W.w x * W.p x) =ᵐ[Model.cubeVolume A.d] W.p := by
  filter_upwards [unit_weight (F := quadraticObservables A hM) rfl W] with x hx
  simp only [hx, one_mul]

/-- The literal interval is `[1-ω,1+ω]`, for every fixed `0<ω<1`. -/
def nearlyUniformParameters (d : ℕ) (s H w : ℝ) (hd : 1 ≤ d) (hs : 0 < s)
    (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1) : Model.Parameters where
  d := d
  α := s
  β := s
  H := H
  δ := 1/2
  gminus := 1-w
  gplus := 1+w
  M0 := 1
  hd := hd
  hα := hs
  hβ := hs
  hH := zero_lt_one.trans hH
  hδ := by norm_num
  hgminus := by linarith
  hgplus := by linarith
  hM0 := zero_lt_one

def nearlyUniformQuadraticClass (d : ℕ) (s H w : ℝ) (hd : 1 ≤ d) (hs : 0 < s)
    (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1) :=
  smoothQuadraticClass (nearlyUniformParameters d s H w hd hs hH hw hw1)

theorem nearlyUniform_density_bound (d : ℕ) (s H w : ℝ)
    (hd : 1 ≤ d) (hs : 0 < s) (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1)
    {P : ProbabilityMeasure (Model.Observation
      (nearlyUniformParameters d s H w hd hs hH hw hw1) BoundedResponse)}
    (W : SmoothQuadraticWitness
      (nearlyUniformParameters d s H w hd hs hH hw hw1) P) :
    ∀ᵐ x ∂Model.cubeVolume d, |W.p x - 1| ≤ w := by
  filter_upwards [W.densityBounds] with x hx
  apply abs_le.mpr
  change 1-w ≤ W.p x ∧ W.p x ≤ 1+w at hx
  constructor <;> linarith [hx.1, hx.2]

/-- The class is nonempty: an independent symmetric bounded response has
constant zero conditional mean and the uniform smooth design density. -/
theorem nearlyUniform_quadratic_nonempty (d : ℕ) (s H w : ℝ)
    (hd : 1 ≤ d) (hs : 0 < s) (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1) :
    (nearlyUniformQuadraticClass d s H w hd hs hH hw hw1).Nonempty := by
  let A := nearlyUniformParameters d s H w hd hs hH hw hw1
  have hm : (∫ z : BoundedResponse, (z:ℝ)
      ∂(boundedDiagonalBaseline : Measure BoundedResponse)) = 0 := by
    rw [boundedDiagonalBaseline_integral _ measurable_subtype_coe]
    norm_num [signPoint, sign]
  refine ⟨Model.productLaw A boundedDiagonalBaseline, ⟨{
    p := fun _ => 1
    m := fun _ => 0
    measurableP := measurable_const
    smoothP := contDiff_const
    measurableM := measurable_const
    marginal := ?_
    moment := ?_
    smoothM := ?_
    densityBounds := ?_ }⟩⟩
  · change ((Model.cubeVolume A.d).prod
      (boundedDiagonalBaseline : Measure BoundedResponse)).map Prod.fst = _
    simp
    rfl
  · have h := Applications.conditional_snd_product (Model.cubeVolume A.d)
      (boundedDiagonalBaseline : Measure BoundedResponse)
      (Subtype.val : BoundedResponse → ℝ) measurable_subtype_coe
    simpa only [hm, Function.comp_def, Model.productLaw, Model.covariateInformation, ProbabilityMeasure.coe_mk, A] using h
  · apply Model.const_mem_holderBall hs
    simp only [abs_zero]
    exact (zero_lt_one.trans hH).le
  · exact ae_of_all _ (fun _ => by
      change 1-w ≤ 1 ∧ 1 ≤ 1+w
      constructor <;> linarith)

@[simp] theorem nearlyUniformParameters_theta (d : ℕ) (s H w : ℝ)
    (hd : 1 ≤ d) (hs : 0 < s) (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1) :
    (nearlyUniformParameters d s H w hd hs hH hw hw1).theta = 2*s/d := by
  dsimp [Model.Parameters.theta, nearlyUniformParameters]
  ring

theorem nearlyUniform_quadratic_bracket (d : ℕ) (s H w : ℝ)
    (hd : 1 ≤ d) (hs : 0 < s) (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1) :
    let A := nearlyUniformParameters d s H w hd hs hH hw hw1
    Model.Bracket (quadraticTarget A)
      (nearlyUniformQuadraticClass d s H w hd hs hH hw hw1)
      A.bracketParameters (A.nu : ℝ) := by
  dsimp only
  let A := nearlyUniformParameters d s H w hd hs hH hw hw1
  have hlo : max A.δ A.gminus < 1 := by
    apply max_lt
    · change (1/2:ℝ) < 1
      norm_num
    · change 1-w < 1
      linarith
  have hhi : 1 < A.gplus := by change 1 < 1+w; linarith
  have h := smooth_quadratic_bracket A le_rfl hlo hhi rfl
  rw [← smoothQuadraticClass_eq A rfl] at h
  exact h

theorem nearlyUniform_quadratic_log_exponent (d : ℕ) (s H w : ℝ)
    (hd : 1 ≤ d) (hs : 0 < s) (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1) :
    let A := nearlyUniformParameters d s H w hd hs hH hw hw1
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n (quadraticTarget A)
      (nearlyUniformQuadraticClass d s H w hd hs hH hw hw1)).toReal / Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) (2*s/d))) := by
  simpa only [Model.Parameters.bracketParameters, nearlyUniformParameters_theta] using
    (nearlyUniform_quadratic_bracket d s H w hd hs hH hw hw1).log_polynomial_exponent

theorem nearlyUniform_quadratic_rough_exponent (d : ℕ) (s H w : ℝ)
    (hd : 1 ≤ d) (hs : 0 < s) (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1)
    (hrough : 2*s/d < 1/2) :
    let A := nearlyUniformParameters d s H w hd hs hH hw hw1
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n (quadraticTarget A)
      (nearlyUniformQuadraticClass d s H w hd hs hH hw hw1)).toReal / Real.log n)
      atTop (𝓝 (-(2*s/d))) := by
  simpa only [min_eq_right hrough.le] using
    nearlyUniform_quadratic_log_exponent d s H w hd hs hH hw hw1

/-- The interval width enters the subpolynomial correction through the
explicit `tau(1-w,1+w)`, while the polynomial exponent is unchanged. -/
theorem nearlyUniform_quadratic_log_refinement (d : ℕ) (s H w : ℝ)
    (hd : 1 ≤ d) (hs : 0 < s) (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1)
    (hrough : 2*s/d < 1/2) :
    let A := nearlyUniformParameters d s H w hd hs hH hw hw1
    (fun n : ℕ => Real.log (Model.minimaxRMSE n (quadraticTarget A)
      (nearlyUniformQuadraticClass d s H w hd hs hH hw hw1)).toReal +
      (2*s/d)*Real.log n + Rates.kappa (2*s/d) (Rates.tau (1-w) (1+w)) *
        Real.sqrt (Real.log n)) =O[atTop] (fun n : ℕ => Real.log (Real.log n)) := by
  have htheta := nearlyUniformParameters_theta d s H w hd hs hH hw hw1
  have hlo : (nearlyUniformParameters d s H w hd hs hH hw hw1).gminus = 1-w := rfl
  have hhi : (nearlyUniformParameters d s H w hd hs hH hw hw1).gplus = 1+w := rfl
  have h := (nearlyUniform_quadratic_bracket d s H w hd hs hH hw hw1).log_refinement
    (by simpa only [Model.Parameters.bracketParameters, htheta] using hrough)
  simpa only [Model.Parameters.bracketParameters, htheta, hlo, hhi] using h

theorem nearlyUniform_quadratic_not_hoif (d : ℕ) (s H w : ℝ)
    (hd : 1 ≤ d) (hs : 0 < s) (hH : 1 < H) (hw : 0 < w) (hw1 : w < 1)
    (hrough : 2*s/d < 1/2) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (K : ℝ) (hK : 0 < K) :
    let A := nearlyUniformParameters d s H w hd hs hH hw hw1
    ¬∀ᶠ n : ℕ in atTop, Model.minimaxRMSE n (quadraticTarget A)
      (nearlyUniformQuadraticClass d s H w hd hs hH hw hw1) ≤
        ENNReal.ofReal (K * (n : ℝ) ^ (-(4*s/(4*s+d)) + e n)) := by
  have hdR : 0 < (d:ℝ) := by exact_mod_cast (by omega : 0<d)
  simpa only [Model.Parameters.bracketParameters, nearlyUniformParameters_theta,
    Model.hoifExponent_eq_source s d hs hdR] using
    (nearlyUniform_quadratic_bracket d s H w hd hs hH hw hw1).not_hoif_upper
      (by simpa only [Model.Parameters.bracketParameters, nearlyUniformParameters_theta] using hrough)
      e he K hK

end RoughRegime.Applications.Products
