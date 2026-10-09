module

public import RoughRegime.CanonicalPartitionPPP
public import RoughRegime.GlobalAffine
public import RoughRegime.GridBoundary
public import RoughRegime.RectangleTransport
public import RoughRegime.PartitionPoisson


@[expose] public section
/-! The actual local two-cell mark law and its affine map to a conditional
component of the canonical observation law. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open RoughRegime.LatticeFourier
open scoped ENNReal BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

 theorem map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (g : Y → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity (fun x => g (f x))).map f = (μ.map f).withDensity g := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hs.preimage hf),
    withDensity_apply _ hs, Measure.restrict_map hf hs, lintegral_map hg hf]

 theorem gridEmbed_map_cubeVolume {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N)
    (hell : 0 < ell) :
    (Model.cubeVolume (D+1)).map (gridEmbed offset ell b) =
      ENNReal.ofReal (1 / ell^(D+1)) • volume.restrict (gridBlockClosed offset ell b) := by
  have he : gridEmbed offset ell b = Model.rectangleEmbed (gridOrigin offset ell b) (fun _ => ell) := by
    funext x
    ext q
    simp [gridEmbed, Model.rectangleEmbed]
  have hr : Model.rectangle (gridOrigin offset ell b) (fun _ => ell) =
      gridBlockClosed offset ell b := by
    ext x
    rw [gridBlockClosed_iff offset ell b hell]
    simp only [Model.rectangle, gridOrigin, Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · intro h q
      have hh := h q
      change offset + ell * (gridCell b q : ℝ) ≤ x q ∧
        x q ≤ offset + ell * (gridCell b q : ℝ) + ell at hh
      constructor <;> nlinarith [hh.1, hh.2]
    · intro h q
      have hh := h q
      change offset + ell * (gridCell b q : ℝ) ≤ x q ∧
        x q ≤ offset + ell * (gridCell b q : ℝ) + ell
      constructor <;> nlinarith [hh.1, hh.2]
  rw [he, Model.rectangleEmbed_map_cubeVolume _ _ (fun _ => hell), hr]
  simp

 theorem bool_count_eq_diracs : (Measure.count : Measure Bool) = Measure.dirac false + Measure.dirac true := by
  rw [Measure.count, Measure.sum_fintype]
  simp only [Fintype.sum_bool, add_comm]

 theorem prod_bool_count {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ] :
    μ.prod (Measure.count : Measure Bool) =
      (μ.map (fun x => (x,false))) + (μ.map (fun x => (x,true))) := by
  rw [bool_count_eq_diracs, Measure.prod_add, Measure.prod_dirac, Measure.prod_dirac]

 def uniformBlockLabel : Measure Bool := (1/2 : ℝ≥0∞) • Measure.count

 instance uniformBlockLabel_isProbabilityMeasure : IsProbabilityMeasure uniformBlockLabel where
  measure_univ := by
    have hc : (Measure.count : Measure Bool) univ = 2 := by
      rw [Measure.count, Measure.sum_fintype, Fintype.sum_bool]
      simp
      norm_num
    rw [uniformBlockLabel, Measure.smul_apply, hc]
    simpa only [one_div, smul_eq_mul] using
      ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)

 theorem uniformBlockLabel_integral (f : Bool → ℝ) :
    (∫ b, f b ∂uniformBlockLabel) = (f true + f false)/2 := by
  rw [uniformBlockLabel, integral_smul_measure, integral_count, Fintype.sum_bool]
  norm_num [smul_eq_mul]
  ring

 theorem map_prod_uniformBlockLabel {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Z) [SFinite μ] [SFinite ν]
    (f : (X × Bool) × Z → Y) (hf : Measurable f) :
    ((μ.prod uniformBlockLabel).prod ν).map f =
      (1/2 : ℝ≥0∞) • ((μ.prod ν).map (fun o => f ((o.1,false),o.2)) +
        (μ.prod ν).map (fun o => f ((o.1,true),o.2))) := by
  rw [uniformBlockLabel, Measure.prod_smul_right, Measure.prod_smul_left,
    Measure.map_smul _ hf.aemeasurable, prod_bool_count, Measure.add_prod,
    Measure.map_add _ _ hf]
  congr 1
  have h (b : Bool) : ((μ.map (fun x => (x,b))).prod ν).map f =
      (μ.prod ν).map (fun o => f ((o.1,b),o.2)) := by
    have he := Measure.map_prod_map μ ν (measurable_prodMk_right (y := b)) measurable_id
    rw [Measure.map_id] at he
    rw [he, Measure.map_map hf ((measurable_prodMk_right (y := b)).prodMap measurable_id)]
    rfl
  rw [h false, h true]

 namespace CanonicalFrame
 variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

 def localPairBase (_F : CanonicalFrame D N ι) {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z) :
    Measure ((Model.Covariate (D+1) × Bool) × Z) :=
  ((Model.cubeVolume (D+1)).prod uniformBlockLabel).prod (π : Measure Z)

 instance localPairBase_isProbabilityMeasure {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) : IsProbabilityMeasure (F.localPairBase π) := by
  unfold localPairBase
  infer_instance

 def localBlockDensity (w : PairState ι) (b : Bool) (x : Model.Covariate (D+1)) : ℝ :=
  blockDensity F.p0 ((F.rminus+F.rplus)/2) ((F.rplus-F.rminus)/2-F.delta)
    w.2.1 (blockPhase F.U F.M F.a F.q F.gamma w.1) F.outer (RoughRegime.Lower.sign b) x

 theorem localBlockDensity_bounds (w : PairState ι) (b : Bool) (x : Model.Covariate (D+1)) :
    F.rminus ≤ F.localBlockDensity w b x ∧ F.localBlockDensity w b x ≤ F.rplus := by
  have hm := source_margin_parameters F.rminus F.rplus F.p0 F.delta F.delta_pos
    F.interval F.delta_r F.delta_p0 F.delta_p1
  have hs : |RoughRegime.Lower.sign b| ≤ 1 := by cases b <;> norm_num [RoughRegime.Lower.sign]
  have hb := blockDensity_bounds F.p0 ((F.rminus+F.rplus)/2) ((F.rplus-F.rminus)/2-F.delta)
    w.2.1 (RoughRegime.Lower.sign b) (F.rminus+F.delta) (F.rplus-F.delta)
    (blockPhase F.U F.M F.a F.q F.gamma w.1) F.outer hs
    ⟨hm.2.1, hm.2.2.1⟩ hm.2.2.2 F.outer_bound x
  dsimp [localBlockDensity]
  constructor <;> linarith [hb.1, hb.2, F.delta_pos]

 theorem localBlockDensity_ne (w : PairState ι) (b : Bool) (x : Model.Covariate (D+1)) :
    F.localBlockDensity w b x ≠ 0 :=
  (F.rminus_pos.trans_le (F.localBlockDensity_bounds w b x).1).ne'

 theorem localBlockDensity_measurable (w : PairState ι) :
    Measurable (fun o : Model.Covariate (D+1) × Bool => F.localBlockDensity w o.2 o.1) := by
  have hp := (blockPhase_smooth F.U F.M F.a F.q F.gamma w.1 F.gamma_pos F.gamma_le).continuous.measurable
  have ho := F.outer_smooth.continuous.measurable
  have hs : Measurable RoughRegime.Lower.sign := measurable_of_countable _
  unfold localBlockDensity blockDensity blockOscillatingDensity
  fun_prop

 theorem localSignal_bound (A : ℝ) (hA : 0 ≤ A) (w : PairState ι) (b : Bool)
    (x : Model.Covariate (D+1)) :
    |A * RoughRegime.Lower.sign b * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner x| ≤ A := by
  have hg := jointGate_bounds F.Q F.M F.eta F.lambda w.1
  have hs : |RoughRegime.Lower.sign b| = 1 := by cases b <;> norm_num [RoughRegime.Lower.sign]
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hA, hs, mul_one, abs_of_nonneg hg.1]
  calc
    _ ≤ A * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hg.2 hA)
      (F.inner_bound x) (abs_nonneg _) (by positivity)
    _ = A := by ring

 def localUnsignedProfile (A : ℝ) (w : PairState ι) (b : Bool) (x : Model.Covariate (D+1)) : ℝ :=
  A * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner x / F.localBlockDensity w b x

 theorem localUnsignedProfile_bound (A : ℝ) (hA : 0 ≤ A) (w : PairState ι) (b : Bool)
    (x : Model.Covariate (D+1)) : |F.localUnsignedProfile A w b x| ≤ A/F.rminus := by
  have hn := F.localSignal_bound A hA w true x
  simp only [RoughRegime.Lower.sign, ite_true, mul_one] at hn
  unfold localUnsignedProfile
  rw [abs_div, abs_of_pos (F.rminus_pos.trans_le (F.localBlockDensity_bounds w b x).1)]
  exact div_le_div₀ hA hn F.rminus_pos (F.localBlockDensity_bounds w b x).1

 theorem localPairDensity_measurable {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z)) (w : PairState ι) :
    Measurable (F.localPairDensity π S w) := by
  have hp : Measurable (fun o : (Model.Covariate (D+1) × Bool) × Z => F.localBlockDensity w o.1.2 o.1.1) :=
    (F.localBlockDensity_measurable w).comp measurable_fst
  have hi : Measurable (fun o : (Model.Covariate (D+1) × Bool) × Z => F.inner o.1.1) :=
    F.inner_smooth.continuous.measurable.comp measurable_fst.fst
  have hu : Measurable (fun o : (Model.Covariate (D+1) × Bool) × Z => S.su o.2) := S.measurableU.comp measurable_snd
  have hv : Measurable (fun o : (Model.Covariate (D+1) × Bool) × Z => S.sv o.2) := S.measurableV.comp measurable_snd
  change Measurable (fun o : (Model.Covariate (D+1) × Bool) × Z => (F.localBlockDensity w o.1.2 o.1.1 + _ + _) / _)
  fun_prop

 theorem localPairDensity_joint_measurable {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z)) :
    Measurable (fun q : PairState ι × ((Model.Covariate (D+1) × Bool) × Z) =>
      F.localPairDensity π S q.1 q.2) := by
  have hs (i : ι) : Measurable (softDigit F.U (F.gamma i)) :=
    (softDigit_smooth F.U _ (F.gamma_pos i) (F.gamma_le i)).continuous.measurable
  have hz : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  have hg : Measurable (jointGate F.Q F.M F.eta F.lambda) := jointGate_measurable _ _ _ _
  have hsign : Measurable RoughRegime.Lower.sign := measurable_of_countable _
  have ho := F.outer_smooth.continuous.measurable
  have hi := F.inner_smooth.continuous.measurable
  have hu := S.measurableU
  have hv := S.measurableV
  unfold localPairDensity blockDensity blockOscillatingDensity blockPhase coordinateSoftDigit
  fun_prop

 theorem localPairDensity_bound {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z)) (w : PairState ι)
    (o : (Model.Covariate (D+1) × Bool) × Z) :
    |F.localPairDensity π S w o| ≤ (F.rplus+(F.Au+F.Av)*S.C)/F.pairBarDensity := by
  have hd := F.localBlockDensity_bounds w o.1.2 o.1.1
  have hu := mul_le_mul (F.localSignal_bound F.Au F.Au_nonneg w w.2.2.1 o.1.1)
    (S.boundU o.2) (abs_nonneg _) F.Au_nonneg
  have hv := mul_le_mul (F.localSignal_bound F.Av F.Av_nonneg w w.2.2.2 o.1.1)
    (S.boundV o.2) (abs_nonneg _) F.Av_nonneg
  rw [← abs_mul] at hu hv
  change |(F.localBlockDensity w o.1.2 o.1.1 + _ + _)/F.pairBarDensity| ≤ _
  rw [abs_div, abs_of_pos F.pairBarDensity_positive]
  apply div_le_div_of_nonneg_right _ F.pairBarDensity_positive.le
  have hdn : 0 ≤ F.localBlockDensity w o.1.2 o.1.1 := F.rminus_pos.le.trans hd.1
  have hab := (abs_add_le (F.localBlockDensity w o.1.2 o.1.1)
    (F.Au * RoughRegime.Lower.sign w.2.2.1 * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner o.1.1 * S.su o.2))
  have hac := abs_add_le
    (F.localBlockDensity w o.1.2 o.1.1 + F.Au * RoughRegime.Lower.sign w.2.2.1 *
      jointGate F.Q F.M F.eta F.lambda w.1 * F.inner o.1.1 * S.su o.2)
    (F.Av * RoughRegime.Lower.sign w.2.2.2 * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner o.1.1 * S.sv o.2)
  rw [abs_of_nonneg hdn] at hab
  nlinarith

 theorem localPairDensity_nonnegative {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (w : PairState ι)
    (o : (Model.Covariate (D+1) × Bool) × Z) : 0 ≤ F.localPairDensity π S w o := by
  have hu := mul_le_mul (F.localSignal_bound F.Au F.Au_nonneg w w.2.2.1 o.1.1)
    (S.boundU o.2) (abs_nonneg _) F.Au_nonneg
  have hv := mul_le_mul (F.localSignal_bound F.Av F.Av_nonneg w w.2.2.2 o.1.1)
    (S.boundV o.2) (abs_nonneg _) F.Av_nonneg
  rw [← abs_mul, abs_le] at hu hv
  have hs : ((F.Au+F.Av)*S.C)/F.rminus ≤ 1/4 := by
    simpa only [div_mul_eq_mul_div] using hsmall
  have hb := (div_le_iff₀ F.rminus_pos).mp hs
  change 0 ≤ (F.localBlockDensity w o.1.2 o.1.1 + _ + _) / F.pairBarDensity
  apply div_nonneg _ F.pairBarDensity_positive.le
  have hd := (F.localBlockDensity_bounds w o.1.2 o.1.1).1
  nlinarith [F.rminus_pos]

 theorem localPairDensity_integrable {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z)) (w : PairState ι) :
    Integrable (F.localPairDensity π S w) (F.localPairBase π) := by
  apply Integrable.of_bound (F.localPairDensity_measurable π S w).aestronglyMeasurable
    ((F.rplus+(F.Au+F.Av)*S.C)/F.pairBarDensity)
  exact Filter.Eventually.of_forall (fun o => F.localPairDensity_bound π S w o)

 theorem localPairDensity_integral {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z)) (w : PairState ι) :
    (∫ o, F.localPairDensity π S w o ∂F.localPairBase π) = 1 := by
  have hu := AffineResponseLower.score_integrable (π : Measure Z) S.su S.measurableU S.C S.boundU
  have hv := AffineResponseLower.score_integrable (π : Measure Z) S.sv S.measurableV S.C S.boundV
  unfold localPairBase
  rw [integral_prod _ (F.localPairDensity_integrable π S w)]
  have he (xb : Model.Covariate (D+1) × Bool) :
      (∫ z, F.localPairDensity π S w (xb,z) ∂(π : Measure Z)) =
        F.localBlockDensity w xb.2 xb.1 / F.pairBarDensity := by
    change (∫ z, (F.localBlockDensity w xb.2 xb.1 +
      F.Au * RoughRegime.Lower.sign w.2.2.1 * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner xb.1 * S.su z +
      F.Av * RoughRegime.Lower.sign w.2.2.2 * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner xb.1 * S.sv z) /
      F.pairBarDensity ∂(π : Measure Z)) = _
    let cu := F.Au * RoughRegime.Lower.sign w.2.2.1 * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner xb.1
    let cv := F.Av * RoughRegime.Lower.sign w.2.2.2 * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner xb.1
    have h1 := integral_add (integrable_const (F.localBlockDensity w xb.2 xb.1)) (hu.const_mul cu)
    have h2 := integral_add ((integrable_const (F.localBlockDensity w xb.2 xb.1)).add (hu.const_mul cu)) (hv.const_mul cv)
    simp only [Pi.add_apply] at h1 h2
    rw [integral_div, h2, h1, integral_const_mul, integral_const_mul, S.meanU, S.meanV]
    simp
  simp_rw [he]
  have hi : Integrable (fun o : Model.Covariate (D+1) × Bool => F.localBlockDensity w o.2 o.1)
      ((Model.cubeVolume (D+1)).prod uniformBlockLabel) := by
    apply Integrable.of_bound (F.localBlockDensity_measurable w).aestronglyMeasurable F.rplus
    filter_upwards [] with o
    rw [Real.norm_eq_abs, abs_of_pos (F.rminus_pos.trans_le (F.localBlockDensity_bounds w o.2 o.1).1)]
    exact (F.localBlockDensity_bounds w o.2 o.1).2
  rw [integral_div, integral_prod _ hi]
  simp_rw [uniformBlockLabel_integral]
  have hc (x : Model.Covariate (D+1)) :
      (F.localBlockDensity w true x + F.localBlockDensity w false x)/2 =
        F.p0 + F.outer x * ((F.rminus+F.rplus)/2-F.p0) := by
    unfold localBlockDensity
    simp only [RoughRegime.Lower.sign, Bool.false_eq_true, ite_false, ite_true]
    rw [blockDensity_pair_cancellation]
    ring
  simp_rw [hc]
  rw [integral_add (integrable_const _) ((continuous_cube_integrable _ F.outer_smooth.continuous).mul_const _),
    integral_mul_const]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  change F.pairBarDensity / F.pairBarDensity = 1
  exact div_self F.pairBarDensity_positive.ne'

 def localPairLaw {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (w : PairState ι) :
    GeneralTesting.DensityLaw (F.localPairBase π) where
  density := F.localPairDensity π S w
  measurable := F.localPairDensity_measurable π S w
  integrable := F.localPairDensity_integrable π S w
  nonneg := Filter.Eventually.of_forall (F.localPairDensity_nonnegative π S hsmall w)
  integral_one := F.localPairDensity_integral π S w

 def localPairKernel {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) :
    ProbabilityTheory.Kernel (PairState ι) ((Model.Covariate (D+1) × Bool) × Z) where
  toFun w := (F.localPairLaw π S hsmall w).measure
  measurable' := by
    apply measurable_withDensity
    exact (F.localPairDensity_joint_measurable π S).ennreal_ofReal

 instance localPairKernel_markov {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) :
    ProbabilityTheory.IsMarkovKernel (F.localPairKernel π S hsmall) where
  isProbabilityMeasure w := (F.localPairLaw π S hsmall w).isProbabilityMeasure

 theorem localPairDensity_eq_observationDensity {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
    (z : GridPair D N → PairState ι) (k : GridPair D N)
    (o : (Model.Covariate (D+1) × Bool) × Z) (hx : o.1.1 ∈ Model.cube (D+1)) :
    F.localPairDensity π S (z k) o =
      (SpatialAffine.law S (F.field z) hsmall).density (F.localPairEmbedding k o) / F.pairBarDensity := by
  let x := gridEmbed F.offset F.ell (k,o.1.2) o.1.1
  have hxc : x ∈ gridBlockClosed F.offset F.ell (k,o.1.2) := by
    change gridCoords F.offset F.ell (k,o.1.2) x ∈ Model.cube (D+1)
    rw [gridCoords_embed _ _ _ F.ell_pos.ne']
    exact hx
  have hpx : F.p z x ≠ 0 := by
    have hb := (F.realization z).margins x
    exact (show 0 < F.p z x by linarith [F.rminus_pos, F.delta_pos]).ne'
  have hd : F.localBlockDensity (z k) o.1.2 o.1.1 = F.p z x := by
    have he := globalDensity_eq_local_closed F.offset F.ell F.p0 ((F.rminus+F.rplus)/2)
      ((F.rplus-F.rminus)/2-F.delta) F.ell_pos F.outer F.outer_zero
      (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z) (k,o.1.2) x hxc
    simpa [p, localBlockDensity, stateAngles, statePhases, x, gridCoords_embed _ _ _ F.ell_pos.ne'] using he.symm
  have hu : F.p z x * F.u z x =
      F.Au * RoughRegime.Lower.sign (z k).2.2.1 * jointGate F.Q F.M F.eta F.lambda (z k).1 * F.inner o.1.1 := by
    have he := globalProfile_local_density_product F.offset F.ell F.p0 ((F.rminus+F.rplus)/2)
      ((F.rplus-F.rminus)/2-F.delta) F.Au F.ell_pos F.inner F.outer F.inner_zero
      (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z) (stateSignU z)
      (stateGates F.Q F.M F.eta F.lambda z) (k,o.1.2) x hxc hpx
    simpa [p,u,stateSignU,stateGates,x,gridCoords_embed _ _ _ F.ell_pos.ne'] using he
  have hv : F.p z x * F.v z x =
      F.Av * RoughRegime.Lower.sign (z k).2.2.2 * jointGate F.Q F.M F.eta F.lambda (z k).1 * F.inner o.1.1 := by
    have he := globalProfile_local_density_product F.offset F.ell F.p0 ((F.rminus+F.rplus)/2)
      ((F.rplus-F.rminus)/2-F.delta) F.Av F.ell_pos F.inner F.outer F.inner_zero
      (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z) (stateSignV z)
      (stateGates F.Q F.M F.eta F.lambda z) (k,o.1.2) x hxc hpx
    simpa [p,v,stateSignV,stateGates,x,gridCoords_embed _ _ _ F.ell_pos.ne'] using he
  change (F.localBlockDensity (z k) o.1.2 o.1.1 + _ + _) / F.pairBarDensity =
    (F.p z x * (1 + F.u z x * S.su o.2 + F.v z x * S.sv o.2)) / F.pairBarDensity
  rw [hd, ← hu, ← hv]
  ring

 theorem localPairEmbedding_base_map {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (k : GridPair D N) :
    (F.localPairBase π).map (F.localPairEmbedding k) =
      ENNReal.ofReal (1/(2*F.ell^(D+1))) •
        (((Model.cubeVolume (D+1)).prod (π : Measure Z)).restrict (F.observedPairSet k)) := by
  rw [localPairBase, map_prod_uniformBlockLabel _ _ _ (F.localPairEmbedding_measurable k)]
  have h (b : Bool) :
      (((Model.cubeVolume (D+1)).prod (π : Measure Z)).map
        (fun o => F.localPairEmbedding k ((o.1,b),o.2))) =
      ENNReal.ofReal (1/F.ell^(D+1)) •
        (((Model.cubeVolume (D+1)).prod (π : Measure Z)).restrict
          (Prod.fst ⁻¹' gridBlockOpen F.offset F.ell (k,b))) := by
    have he := Measure.map_prod_map (Model.cubeVolume (D+1)) (π : Measure Z)
      (gridEmbed_smooth F.offset F.ell (k,b)).continuous.measurable measurable_id
    rw [Measure.map_id] at he
    change (((Model.cubeVolume (D+1)).prod (π : Measure Z)).map
      (Prod.map (gridEmbed F.offset F.ell (k,b)) id)) = _
    rw [← he, gridEmbed_map_cubeVolume _ _ _ F.ell_pos, Measure.prod_smul_left]
    rw [Measure.restrict_congr_set (gridBlockClosed_ae_eq_open F.offset F.ell F.ell_pos (k,b))]
    have hs : gridBlockOpen F.offset F.ell (k,b) ⊆ Model.cube (D+1) :=
      gridBlockOpen_subset_cube F.offset F.ell (k,b) F.ell_pos F.offset_nonneg F.size_bound
    have hr : volume.restrict (gridBlockOpen F.offset F.ell (k,b)) =
        (Model.cubeVolume (D+1)).restrict (gridBlockOpen F.offset F.ell (k,b)) := by
      change _ = (volume.restrict (Model.cube (D+1))).restrict _
      rw [Measure.restrict_restrict (gridBlockOpen_measurable F.offset F.ell F.ell_pos (k,b)), inter_eq_left.mpr hs]
    rw [hr, Measure.restrict_prod_eq_prod_univ]
    have ht : gridBlockOpen F.offset F.ell (k,b) ×ˢ (univ : Set Z) =
        Prod.fst ⁻¹' gridBlockOpen F.offset F.ell (k,b) := by ext o; simp
    rw [ht]
  rw [h false, h true, ← smul_add, smul_smul]
  have hd : Disjoint (Prod.fst ⁻¹' gridBlockOpen F.offset F.ell (k,false) : Set (Model.Covariate (D+1) × Z))
      (Prod.fst ⁻¹' gridBlockOpen F.offset F.ell (k,true)) :=
    (gridBlockOpen_pairwiseDisjoint D N F.offset F.ell F.ell_pos (by simp)).preimage _
  rw [← Measure.restrict_union hd
    ((gridBlockOpen_measurable F.offset F.ell F.ell_pos (k,true)).preimage measurable_fst)]
  have hs : Prod.fst ⁻¹' gridBlockOpen F.offset F.ell (k,false) ∪
      Prod.fst ⁻¹' gridBlockOpen F.offset F.ell (k,true) = F.observedPairSet (Z := Z) k := rfl
  rw [hs]
  congr 1
  have hh : (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hh, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
  congr 1
  field_simp

 theorem localPairBase_covariate_ae {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) :
    ∀ᵐ o ∂F.localPairBase π, o.1.1 ∈ Model.cube (D+1) := by
  have hx : ∀ᵐ x ∂Model.cubeVolume (D+1), x ∈ Model.cube (D+1) :=
    ae_restrict_mem (Model.measurableSet_cube _)
  have hxb : ∀ᵐ xb ∂(Model.cubeVolume (D+1)).prod uniformBlockLabel,
      xb.1 ∈ Model.cube (D+1) := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact hx
  have hmap : ∀ᵐ xb ∂(F.localPairBase π).map Prod.fst, xb.1 ∈ Model.cube (D+1) := by
    rw [localPairBase, Measure.map_fst_prod, measure_univ, one_smul]
    exact hxb
  exact ae_of_ae_map measurable_fst.aemeasurable hmap

 theorem localPairLaw_map {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
    (z : GridPair D N → PairState ι) (k : GridPair D N) :
    (F.localPairLaw π S hsmall (z k)).measure.map (F.localPairEmbedding k) =
      (ENNReal.ofReal F.pairMass)⁻¹ •
        (F.observationProbability π S hsmall z : Measure (Model.Covariate (D+1) × Z)).restrict
          (F.observedPairSet k) := by
  let L := SpatialAffine.law S (F.field z) hsmall
  let g : Model.Covariate (D+1) × Z → ℝ≥0∞ :=
    (ENNReal.ofReal F.pairBarDensity)⁻¹ • (fun o => ENNReal.ofReal (L.density o))
  have hg : Measurable g := measurable_const.mul L.measurable.ennreal_ofReal
  have he : (fun o => ENNReal.ofReal (F.localPairDensity π S (z k) o)) =ᵐ[F.localPairBase π]
      (fun o => g (F.localPairEmbedding k o)) := by
    filter_upwards [F.localPairBase_covariate_ae π] with o ho
    rw [F.localPairDensity_eq_observationDensity π S hsmall z k o ho,
      ENNReal.ofReal_div_of_pos F.pairBarDensity_positive]
    change ENNReal.ofReal (L.density (F.localPairEmbedding k o)) /
      ENNReal.ofReal F.pairBarDensity = _
    simp only [g, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  change ((F.localPairBase π).withDensity (fun o => ENNReal.ofReal (F.localPairDensity π S (z k) o))).map
    (F.localPairEmbedding k) = _
  rw [withDensity_congr_ae he, map_withDensity_comp _ _ _
    (F.localPairEmbedding_measurable k) hg, F.localPairEmbedding_base_map π k,
    withDensity_smul_measure]
  dsimp only [g]
  rw [withDensity_smul _ L.measurable.ennreal_ofReal, smul_smul,
    ← restrict_withDensity (F.observedPairSet_measurable k)]
  have hc : ENNReal.ofReal (1/(2*F.ell^(D+1))) * (ENNReal.ofReal F.pairBarDensity)⁻¹ =
      (ENNReal.ofReal F.pairMass)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos F.pairBarDensity_positive,
      ← ENNReal.ofReal_mul (div_nonneg zero_le_one (mul_nonneg (by norm_num) (pow_nonneg F.ell_pos.le _))),
      ← ENNReal.ofReal_inv_of_pos F.pairMass_positive]
    congr 1
    unfold pairMass
    field_simp
  rw [hc]
  rfl

 theorem observationProbability_pairMass_ennreal {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
    (z : GridPair D N → PairState ι) (k : GridPair D N) :
    (F.observationProbability π S hsmall z : Measure (Model.Covariate (D+1) × Z)) (F.observedPairSet k) =
      ENNReal.ofReal F.pairMass := by
  rw [← F.observationProbability_pairMass π S hsmall z k]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

 theorem localPairLaw_map_componentLaw {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
    (z : GridPair D N → PairState ι) (k : GridPair D N) :
    (F.localPairLaw π S hsmall (z k)).measure.map (F.localPairEmbedding k) =
      (PartitionPoisson.componentLaw (F.observationProbability π S hsmall z) (F.observedPairSet k) :
        Measure (Model.Covariate (D+1) × Z)) := by
  have hm := F.observationProbability_pairMass_ennreal π S hsmall z k
  have hn : (F.observationProbability π S hsmall z : Measure (Model.Covariate (D+1) × Z))
      (F.observedPairSet k) ≠ 0 := by
    rw [hm]
    exact ENNReal.ofReal_ne_zero_iff.mpr F.pairMass_positive
  rw [PartitionPoisson.componentLaw, dite_eq_right hn]
  change _ = ProbabilityTheory.cond _ _
  rw [ProbabilityTheory.cond, hm]
  exact F.localPairLaw_map π S hsmall z k

 end CanonicalFrame

end RoughRegime.LatticePriors
