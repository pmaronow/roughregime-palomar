module

public import RoughRegime.CanonicalPairMarks
public import RoughRegime.PoissonKernels
public import RoughRegime.PoissonNormalization
public import RoughRegime.CubeTransport
public import RoughRegime.LatticePhaseField
public import RoughRegime.PhaseFieldTransport


@[expose] public section
/-! The literal canonical pair density is exactly the normalized affine-phase
likelihood used in the physical marked-Poisson comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ContDiff
namespace RoughRegime.LatticePriors.CanonicalFrame
open RoughRegime.PoissonMeasure RoughRegime.LatticeFourier
set_option backward.isDefEq.respectTransparency false
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

def phaseStateEquiv (_F : CanonicalFrame D N ι) : PhaseParameter (ι → ℤ) ≃ᵐ PairState ι :=
  MeasurableEquiv.prodAssoc

def canonicalPhaseField : AffinePhaseField (ι → ℤ) (Model.Covariate (D+1) × Bool) where
  c _ x := (F.outer x.1 - ∫ y, F.outer y ∂Model.cubeVolume (D+1)) * ((F.rminus+F.rplus)/2-F.p0)
  a ξ x := RoughRegime.Lower.sign x.2 * ((F.rplus-F.rminus)/2-F.delta) * F.outer x.1 *
    Real.cos (blockPhase F.U F.M F.a F.q F.gamma ξ x.1)
  b ξ x := -(RoughRegime.Lower.sign x.2 * ((F.rplus-F.rminus)/2-F.delta) * F.outer x.1 *
    Real.sin (blockPhase F.U F.M F.a F.q F.gamma ξ x.1))
  hu ξ x := jointGate F.Q F.M F.eta F.lambda ξ * F.inner x.1
  hv ξ x := jointGate F.Q F.M F.eta F.lambda ξ * F.inner x.1

 theorem canonicalPhaseField_measurable : F.canonicalPhaseField.IsMeasurable := by
  have hs (i : ι) : Measurable (softDigit F.U (F.gamma i)) :=
    (softDigit_smooth F.U _ (F.gamma_pos i) (F.gamma_le i)).continuous.measurable
  have hz : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  have hg : Measurable (jointGate F.Q F.M F.eta F.lambda) := jointGate_measurable _ _ _ _
  have hsign : Measurable RoughRegime.Lower.sign := measurable_of_countable _
  have ho := F.outer_smooth.continuous.measurable
  have hi := F.inner_smooth.continuous.measurable
  constructor
  all_goals unfold Function.uncurry canonicalPhaseField blockPhase coordinateSoftDigit; fun_prop

 def phaseScores (_F : CanonicalFrame D N ι) {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z)) (l : Fin 3) (z : Z) : ℝ :=
  if l=0 then 1 else if l=1 then S.su z else S.sv z

 theorem phaseScores_measurable {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z)) (l : Fin 3) : Measurable (F.phaseScores π S l) := by
  unfold phaseScores
  split_ifs <;> first | exact measurable_const | exact S.measurableU | exact S.measurableV

 theorem phaseScores_bound {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z)) (l : Fin 3) (z : Z) :
    |F.phaseScores π S l z| ≤ max 1 S.C := by
  unfold phaseScores
  split_ifs
  · simp only [abs_one]; exact le_max_left (1 : ℝ) S.C
  · exact (S.boundU z).trans (le_max_right _ _)
  · exact (S.boundV z).trans (le_max_right _ _)

 theorem canonicalPhaseField_density_raw (q : PhaseParameter (ι → ℤ))
    (x : Model.Covariate (D+1) × Bool) :
    F.canonicalPhaseField.unsigned F.Au F.Av 0 q.1 x =
      F.localBlockDensity (F.phaseStateEquiv q) x.2 x.1 - F.pairBarDensity := by
  simp only [AffinePhaseField.unsigned, ite_true]
  unfold canonicalPhaseField localBlockDensity blockDensity blockOscillatingDensity pairBarDensity
    phaseStateEquiv MeasurableEquiv.prodAssoc Equiv.prodAssoc
  dsimp
  simp only [Real.cos_add]
  ring

 theorem canonicalPhaseField_markedFactor {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (q : PhaseParameter (ι → ℤ)) (o : (Model.Covariate (D+1) × Bool) × Z) :
    F.canonicalPhaseField.markedFactor F.Au F.Av (F.phaseScores π S) q o =
      F.localBlockDensity (F.phaseStateEquiv q) o.1.2 o.1.1 - F.pairBarDensity +
      F.Au * RoughRegime.Lower.sign q.2.1 * jointGate F.Q F.M F.eta F.lambda q.1.1 * F.inner o.1.1 * S.su o.2 +
      F.Av * RoughRegime.Lower.sign q.2.2 * jointGate F.Q F.M F.eta F.lambda q.1.1 * F.inner o.1.1 * S.sv o.2 := by
  unfold AffinePhaseField.markedFactor
  rw [Fin.sum_univ_three]
  have h0 : F.canonicalPhaseField.feature F.Au F.Av 0 q o.1 * F.phaseScores π S 0 o.2 =
      F.localBlockDensity (F.phaseStateEquiv q) o.1.2 o.1.1 - F.pairBarDensity := by
    simp [AffinePhaseField.feature, phaseScores, F.canonicalPhaseField_density_raw]
  have h1 : F.canonicalPhaseField.feature F.Au F.Av 1 q o.1 * F.phaseScores π S 1 o.2 =
      F.Au * RoughRegime.Lower.sign q.2.1 * jointGate F.Q F.M F.eta F.lambda q.1.1 * F.inner o.1.1 * S.su o.2 := by
    change (RoughRegime.Lower.sign q.2.1 * 1 * (F.Au *
      (jointGate F.Q F.M F.eta F.lambda q.1.1 * F.inner o.1.1))) * S.su o.2 = _
    ring
  have h2 : F.canonicalPhaseField.feature F.Au F.Av 2 q o.1 * F.phaseScores π S 2 o.2 =
      F.Av * RoughRegime.Lower.sign q.2.2 * jointGate F.Q F.M F.eta F.lambda q.1.1 * F.inner o.1.1 * S.sv o.2 := by
    change (1 * RoughRegime.Lower.sign q.2.2 * (F.Av *
      (jointGate F.Q F.M F.eta F.lambda q.1.1 * F.inner o.1.1))) * S.sv o.2 = _
    ring
  rw [h0, h1, h2]

 theorem canonicalPhaseField_normalized_density {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (q : PhaseParameter (ι → ℤ)) (o : (Model.Covariate (D+1) × Bool) × Z) :
    1 + (F.canonicalPhaseField.scale (1/F.pairBarDensity)).markedFactor F.Au F.Av (F.phaseScores π S) q o =
      F.localPairDensity π S (F.phaseStateEquiv q) o := by
  have he : (F.canonicalPhaseField.scale (1/F.pairBarDensity)).markedFactor F.Au F.Av (F.phaseScores π S) q o =
      (1/F.pairBarDensity) * F.canonicalPhaseField.markedFactor F.Au F.Av (F.phaseScores π S) q o := by
    simp only [AffinePhaseField.markedFactor, AffinePhaseField.feature_scale, mul_assoc, Finset.mul_sum]
  rw [he, F.canonicalPhaseField_markedFactor π S]
  change 1 + (1/F.pairBarDensity) *
    (F.localBlockDensity (q.1.1, q.1.2, q.2) o.1.2 o.1.1 - F.pairBarDensity + _ + _) = _
  change 1 + (1/F.pairBarDensity) * (_ - F.pairBarDensity + _ + _) = (_+_+_)/F.pairBarDensity
  dsimp [localBlockDensity, localPairDensity, phaseStateEquiv, MeasurableEquiv.prodAssoc, Equiv.prodAssoc]
  field_simp [F.pairBarDensity_positive.ne']
  ring

/-- The physical pair likelihood in the affine-phase experiment. -/
def canonicalLikelihood {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (q : PhaseParameter (ι → ℤ)) (o : (Model.Covariate (D+1) × Bool) × Z) : ℝ :=
  1 + (F.canonicalPhaseField.scale (1/F.pairBarDensity)).markedFactor
    F.Au F.Av (F.phaseScores π S) q o

theorem canonicalLikelihood_eq {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z)) (q : PhaseParameter (ι → ℤ))
    (o : (Model.Covariate (D+1) × Bool) × Z) :
    F.canonicalLikelihood π S q o = F.localPairDensity π S (F.phaseStateEquiv q) o :=
  F.canonicalPhaseField_normalized_density π S q o

theorem canonicalLikelihood_measurable {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z)) :
    Measurable (Function.uncurry (F.canonicalLikelihood π S)) := by
  have hm := (F.canonicalPhaseField.scale (1/F.pairBarDensity)).markedFactor_measurable
    (F.canonicalPhaseField.scale_isMeasurable F.canonicalPhaseField_measurable _)
    F.Au F.Av (F.phaseScores π S) (F.phaseScores_measurable π S)
  exact measurable_const.add hm

theorem canonicalLikelihood_bound {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (q : PhaseParameter (ι → ℤ)) (o : (Model.Covariate (D+1) × Bool) × Z) :
    |F.canonicalLikelihood π S q o| ≤ (F.rplus+(F.Au+F.Av)*S.C)/F.pairBarDensity := by
  rw [F.canonicalLikelihood_eq π S]
  exact F.localPairDensity_bound π S _ _

theorem canonicalLikelihood_nonnegative {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
    (q : PhaseParameter (ι → ℤ)) (o : (Model.Covariate (D+1) × Bool) × Z) :
    0 ≤ F.canonicalLikelihood π S q o := by
  rw [F.canonicalLikelihood_eq π S]
  exact F.localPairDensity_nonnegative π S hsmall _ _

theorem canonicalLikelihood_integral {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (q : PhaseParameter (ι → ℤ)) :
    (∫ o, F.canonicalLikelihood π S q o ∂F.localPairBase π) = 1 := by
  simp_rw [F.canonicalLikelihood_eq π S]
  exact F.localPairDensity_integral π S _

/-- A literal instance of the density-law constructor used in the comparison
theorem, with all normalization and positivity obligations proved. -/
def canonicalPointLaw {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (q : PhaseParameter (ι → ℤ)) :
    GeneralTesting.DensityLaw (F.localPairBase π) :=
  pointLaw (F.localPairBase π) (F.canonicalLikelihood π S)
    (F.canonicalLikelihood_measurable π S) ((F.rplus+(F.Au+F.Av)*S.C)/F.pairBarDensity)
    (F.canonicalLikelihood_bound π S) (F.canonicalLikelihood_nonnegative π S hsmall)
    (F.canonicalLikelihood_integral π S) q

theorem canonicalPointLaw_measure {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (q : PhaseParameter (ι → ℤ)) :
    (F.canonicalPointLaw π S hsmall q).measure =
      (F.localPairLaw π S hsmall (F.phaseStateEquiv q)).measure := by
  change (F.localPairBase π).withDensity (fun o => ENNReal.ofReal (F.canonicalLikelihood π S q o)) =
    (F.localPairBase π).withDensity (fun o => ENNReal.ofReal (F.localPairDensity π S (F.phaseStateEquiv q) o))
  congr 1
  funext o
  rw [F.canonicalLikelihood_eq π S]

def canonicalPoissonKernel {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z)) (rate : ℝ≥0) :
    Kernel (PhaseParameter (ι → ℤ)) (PointConfiguration ((Model.Covariate (D+1) × Bool) × Z)) :=
  PoissonMeasure.observationKernel (F.localPairBase π) (F.canonicalLikelihood π S)
    (F.canonicalLikelihood_measurable π S) rate

theorem canonicalPoissonKernel_isMarkov {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (rate : ℝ≥0) :
    IsMarkovKernel (F.canonicalPoissonKernel π S rate) :=
  observationKernel_isMarkov (F.localPairBase π) (F.canonicalLikelihood π S)
    (F.canonicalLikelihood_measurable π S) ((F.rplus+(F.Au+F.Av)*S.C)/F.pairBarDensity)
    (F.canonicalLikelihood_bound π S) (F.canonicalLikelihood_nonnegative π S hsmall)
    (F.canonicalLikelihood_integral π S) rate

/-- The actual affine-phase observation experiment is the canonical physical
pair process, rather than merely a process with a comparable likelihood. -/
theorem canonicalPoissonKernel_apply {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (rate : ℝ≥0)
    (q : PhaseParameter (ι → ℤ)) :
    F.canonicalPoissonKernel π S rate q =
      referenceProcess (F.localPairLaw π S hsmall (F.phaseStateEquiv q)).measure rate := by
  unfold canonicalPoissonKernel
  rw [observationKernel_apply (F.localPairBase π) (F.canonicalLikelihood π S)
    (F.canonicalLikelihood_measurable π S) ((F.rplus+(F.Au+F.Av)*S.C)/F.pairBarDensity)
    (F.canonicalLikelihood_bound π S) (F.canonicalLikelihood_nonnegative π S hsmall)
    (F.canonicalLikelihood_integral π S)]
  simp_rw [LowerMeasure.iidDensityLaw_measure]
  change (Measure.sum fun n => ENNReal.ofReal (RoughRegime.Lower.poissonMass rate n) •
    (Measure.pi fun _ : Fin n => (F.canonicalPointLaw π S hsmall q).measure).map
      (@Sigma.mk ℕ (fun k => Fin k → ((Model.Covariate (D+1) × Bool) × Z)) n)) = _
  simp_rw [F.canonicalPointLaw_measure π S hsmall]
  rfl

/-- The same genuine marked-Poisson kernel in the native state coordinates
of the canonical independent block prior. -/
def physicalPairKernel {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (_hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (rate : ℝ≥0) :
    Kernel (PairState ι) (PointConfiguration ((Model.Covariate (D+1) × Bool) × Z)) :=
  (F.canonicalPoissonKernel π S rate).comap F.phaseStateEquiv.symm F.phaseStateEquiv.symm.measurable

instance physicalPairKernel_markov {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (rate : ℝ≥0) :
    IsMarkovKernel (F.physicalPairKernel π S hsmall rate) := by
  have := F.canonicalPoissonKernel_isMarkov π S hsmall rate
  unfold physicalPairKernel
  infer_instance

theorem physicalPairKernel_apply {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (rate : ℝ≥0) (w : PairState ι) :
    F.physicalPairKernel π S hsmall rate w = referenceProcess (F.localPairLaw π S hsmall w).measure rate := by
  rw [physicalPairKernel,Kernel.comap_apply,F.canonicalPoissonKernel_apply π S hsmall]
  simp only [MeasurableEquiv.apply_symm_apply]

/-- A bound depending only on the fixed density upper margin, uniformly over
all coefficient draws, angles, resolution levels, and smoothing widths. -/
theorem canonicalPhaseField_bounded : F.canonicalPhaseField.Bounded (1+2*F.rplus) := by
  have hL : 0 < F.rplus := F.rminus_pos.trans F.interval
  have hp0 : 0 ≤ F.p0 := by linarith [F.delta_p0,F.delta_pos,F.rminus_pos]
  have hp1 : F.p0 ≤ F.rplus := by linarith [F.delta_p1,F.delta_pos]
  have hr0 : 0 ≤ (F.rminus+F.rplus)/2 := by linarith [F.rminus_pos]
  have hr1 : (F.rminus+F.rplus)/2 ≤ F.rplus := by linarith [F.interval]
  have hh0 : 0 ≤ (F.rplus-F.rminus)/2-F.delta := by linarith [F.delta_r,F.interval]
  have hh1 : (F.rplus-F.rminus)/2-F.delta ≤ F.rplus := by linarith [F.delta_pos,F.rminus_pos]
  have hI0 : 0 ≤ ∫ x, F.outer x ∂Model.cubeVolume (D+1) :=
    integral_nonneg fun x => (F.outer_bound x).1
  have hI1 : (∫ x, F.outer x ∂Model.cubeVolume (D+1)) ≤ 1 := by
    have hi := continuous_cube_integrable F.outer F.outer_smooth.continuous
    have he := integral_mono hi (integrable_const (1:ℝ)) fun x => (F.outer_bound x).2
    simpa using he
  have hcenter (x : Model.Covariate (D+1)) :
      |F.outer x-(∫ y, F.outer y ∂Model.cubeVolume (D+1))| ≤ 1 := by
    rw [abs_le]
    have ho := F.outer_bound x
    constructor <;> linarith
  have hdif : |(F.rminus+F.rplus)/2-F.p0| ≤ F.rplus := by
    rw [abs_le]
    constructor <;> linarith
  have hsign (b : Bool) : |RoughRegime.Lower.sign b|=1 := by cases b <;> norm_num [RoughRegime.Lower.sign]
  have hwave (x : Model.Covariate (D+1) × Bool) :
      |RoughRegime.Lower.sign x.2*((F.rplus-F.rminus)/2-F.delta)*F.outer x.1| ≤ F.rplus := by
    rw [abs_mul,abs_mul,hsign,one_mul,abs_of_nonneg hh0,abs_of_nonneg (F.outer_bound x.1).1]
    calc
      _ ≤ ((F.rplus-F.rminus)/2-F.delta)*1 :=
        mul_le_mul_of_nonneg_left (F.outer_bound x.1).2 hh0
      _ ≤ _ := by simpa using hh1
  have hg (ξ : ι→ℤ) (x : Model.Covariate (D+1)) :
      |jointGate F.Q F.M F.eta F.lambda ξ*F.inner x| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg (jointGate_bounds _ _ _ _ ξ).1]
    exact (mul_le_mul (jointGate_bounds _ _ _ _ ξ).2 (F.inner_bound x)
      (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
  constructor
  · intro ξ x
    change |(F.outer x.1-∫ y,F.outer y ∂Model.cubeVolume (D+1))*((F.rminus+F.rplus)/2-F.p0)| ≤ _
    rw [abs_mul]
    have he := mul_le_mul (hcenter x.1) hdif (abs_nonneg _) zero_le_one
    nlinarith
  · intro ξ x
    change |(_)*Real.cos (blockPhase F.U F.M F.a F.q F.gamma ξ x.1)| ≤ _
    rw [abs_mul]
    have he := mul_le_mul (hwave x)
      (Real.abs_cos_le_one (blockPhase F.U F.M F.a F.q F.gamma ξ x.1)) (abs_nonneg _) hL.le
    nlinarith
  · intro ξ x
    change |-(_*Real.sin (blockPhase F.U F.M F.a F.q F.gamma ξ x.1))| ≤ _
    rw [abs_neg,abs_mul]
    have he := mul_le_mul (hwave x)
      (Real.abs_sin_le_one (blockPhase F.U F.M F.a F.q F.gamma ξ x.1)) (abs_nonneg _) hL.le
    nlinarith
  all_goals intro ξ x; exact (hg ξ x.1).trans (by linarith)

/-- The literal coordinate map between the two ordinary spatial mark domains. -/
def cubeMarkEquiv (d : ℕ) : ((Fin d → ℝ) × Bool) ≃ᵐ (Model.Covariate d × Bool) :=
  MeasurableEquiv.prodCongr (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).toMeasurableEquiv.symm
    (MeasurableEquiv.refl Bool)

theorem cubeMarkEquiv_preserving (d : ℕ) :
    MeasurePreserving (cubeMarkEquiv d) ((DyadicDigits.cubeUniform d).prod uniformBlockLabel)
      ((Model.cubeVolume d).prod uniformBlockLabel) := by
  have hc : MeasurePreserving (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).toMeasurableEquiv.symm
      (DyadicDigits.cubeUniform d) (Model.cubeVolume d) :=
    MeasurePreserving.symm (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).toMeasurableEquiv
      (cubeVolume_ofLp_preserving d)
  exact hc.prod (MeasurePreserving.id uniformBlockLabel)

def canonicalCoordinatePhaseField : AffinePhaseField (ι→ℤ) ((Fin (D+1)→ℝ)×Bool) :=
  F.canonicalPhaseField.pullback (cubeMarkEquiv (D+1))

/-- The Γ norm in the Euclidean canonical experiment is exactly the ordinary
coordinate product-domain norm used by the Fourier counting argument. -/
theorem canonicalPhaseField_gammaNorm_coordinate (ν : Measure (ι→ℤ)) (j : ℕ) :
    F.canonicalCoordinatePhaseField.gammaNorm ν
      ((DyadicDigits.cubeUniform (D+1)).prod uniformBlockLabel) F.Au F.Av F.M j =
    F.canonicalPhaseField.gammaNorm ν ((Model.cubeVolume (D+1)).prod uniformBlockLabel)
      F.Au F.Av F.M j :=
  F.canonicalPhaseField.gammaNorm_pullback ν _ _ (cubeMarkEquiv (D+1))
    (cubeMarkEquiv_preserving (D+1)) F.Au F.Av F.M j

theorem pairBarDensity_bounds : F.rminus ≤ F.pairBarDensity ∧ F.pairBarDensity ≤ F.rplus := by
  have hp0 : F.rminus ≤ F.p0 := by linarith [F.delta_p0,F.delta_pos]
  have hp1 : F.p0 ≤ F.rplus := by linarith [F.delta_p1,F.delta_pos]
  have hr0 : F.rminus ≤ (F.rminus+F.rplus)/2 := by linarith [F.interval]
  have hr1 : (F.rminus+F.rplus)/2 ≤ F.rplus := by linarith [F.interval]
  have hI0 : 0 ≤ ∫ x,F.outer x ∂Model.cubeVolume (D+1) := integral_nonneg fun x => (F.outer_bound x).1
  have hI1 : (∫ x,F.outer x ∂Model.cubeVolume (D+1)) ≤ 1 := by
    have he := integral_mono (continuous_cube_integrable F.outer F.outer_smooth.continuous)
      (integrable_const (1:ℝ)) fun x => (F.outer_bound x).2
    simpa using he
  unfold pairBarDensity
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr hI1),
      mul_nonneg (sub_nonneg.mpr hr0) hI0]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hI1),
      mul_nonneg (sub_nonneg.mpr hr1) hI0]

theorem canonicalPhaseField_scale_bound :
    |1/F.pairBarDensity| * (1+2*F.rplus) ≤ (1+2*F.rplus)/F.rminus := by
  rw [abs_of_pos (one_div_pos.mpr F.pairBarDensity_positive),div_mul_eq_mul_div,one_mul]
  exact div_le_div_of_nonneg_left (by linarith [F.rminus_pos,F.interval])
    F.rminus_pos F.pairBarDensity_bounds.1

/-- The response perturbation leaves a fixed positive lower likelihood bound
that depends only on the density margins. -/
theorem localPairDensity_lower {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (w : PairState ι)
    (o : (Model.Covariate (D+1) × Bool) × Z) :
    3*F.rminus/(4*F.rplus) ≤ F.localPairDensity π S w o := by
  have hu := mul_le_mul (F.localSignal_bound F.Au F.Au_nonneg w w.2.2.1 o.1.1)
    (S.boundU o.2) (abs_nonneg _) F.Au_nonneg
  have hv := mul_le_mul (F.localSignal_bound F.Av F.Av_nonneg w w.2.2.2 o.1.1)
    (S.boundV o.2) (abs_nonneg _) F.Av_nonneg
  rw [← abs_mul,abs_le] at hu hv
  have hs : ((F.Au+F.Av)*S.C)/F.rminus ≤ 1/4 := by
    simpa only [div_mul_eq_mul_div] using hsmall
  have hb := (div_le_iff₀ F.rminus_pos).mp hs
  have hnum : 3*F.rminus/4 ≤ F.localBlockDensity w o.1.2 o.1.1 +
      F.Au*RoughRegime.Lower.sign w.2.2.1*jointGate F.Q F.M F.eta F.lambda w.1*F.inner o.1.1*S.su o.2 +
      F.Av*RoughRegime.Lower.sign w.2.2.2*jointGate F.Q F.M F.eta F.lambda w.1*F.inner o.1.1*S.sv o.2 := by
    have hd := (F.localBlockDensity_bounds w o.1.2 o.1.1).1
    nlinarith
  change _ ≤ (_+_+_)/F.pairBarDensity
  calc
    _ = (3*F.rminus/4)/F.rplus := by ring
    _ ≤ (3*F.rminus/4)/F.pairBarDensity :=
      div_le_div_of_nonneg_left (div_nonneg (mul_nonneg (by norm_num) F.rminus_pos.le) (by norm_num))
        F.pairBarDensity_positive F.pairBarDensity_bounds.2
    _ ≤ _ := div_le_div_of_nonneg_right hnum F.pairBarDensity_positive.le

theorem canonicalLikelihood_lower {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
    (q : PhaseParameter (ι→ℤ)) (o : (Model.Covariate (D+1)×Bool)×Z) :
    3*F.rminus/(4*F.rplus) ≤ F.canonicalLikelihood π S q o := by
  rw [F.canonicalLikelihood_eq π S]
  exact F.localPairDensity_lower π S hsmall _ _

theorem canonicalPhaseField_markedFactor_integral_zero {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (q : PhaseParameter (ι→ℤ)) :
    (∫ o,(F.canonicalPhaseField.scale (1/F.pairBarDensity)).markedFactor F.Au F.Av
      (F.phaseScores π S) q o ∂F.localPairBase π)=0 := by
  have hi : Integrable (F.canonicalLikelihood π S q) (F.localPairBase π) := by
    change Integrable (fun o => F.canonicalLikelihood π S q o) (F.localPairBase π)
    simp_rw [F.canonicalLikelihood_eq π S]
    exact F.localPairDensity_integrable π S _
  have he : (fun o=>(F.canonicalPhaseField.scale (1/F.pairBarDensity)).markedFactor F.Au F.Av
      (F.phaseScores π S) q o) = fun o=>F.canonicalLikelihood π S q o-1 := by
    funext o
    unfold canonicalLikelihood
    ring
  rw [he,integral_sub hi (integrable_const 1),F.canonicalLikelihood_integral π S]
  simp

end RoughRegime.LatticePriors.CanonicalFrame
