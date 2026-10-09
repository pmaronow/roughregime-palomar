module

public import RoughRegime.CanonicalPairMarks
public import RoughRegime.GlobalNonlinearTarget
public import RoughRegime.GlobalTargetTaylor
public import RoughRegime.SpatialTargetMeasurability
public import RoughRegime.SourceModel


@[expose] public section
/-! Actual centered nonlinear targets for every canonical source realization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors.CanonicalFrame
open RoughRegime.LatticeFourier
set_option backward.isDefEq.respectTransparency false
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

def centeredBlockIntegrand (Phi : (ℝ × ℝ) → ℝ) (label : Bool)
    (q : PairState ι × Model.Covariate (D+1)) : ℝ :=
  F.localBlockDensity q.1 label q.2*
    (Phi (Lower.sign q.1.2.2.1*F.localUnsignedProfile F.Au q.1 label q.2,
          Lower.sign q.1.2.2.2*F.localUnsignedProfile F.Av q.1 label q.2)-Phi 0)

def centeredBlockTarget (Phi : (ℝ × ℝ) → ℝ) (label : Bool) (w : PairState ι) : ℝ :=
  ∫ y, F.centeredBlockIntegrand Phi label (w,y) ∂Model.cubeVolume (D+1)

theorem localBlockDensity_joint_measurable (label : Bool) :
    Measurable (fun q : PairState ι × Model.Covariate (D+1) => F.localBlockDensity q.1 label q.2) := by
  have hs (i : ι) : Measurable (softDigit F.U (F.gamma i)) :=
    (softDigit_smooth F.U (F.gamma i) (F.gamma_pos i) (F.gamma_le i)).continuous.measurable
  have hz : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  have ho := F.outer_smooth.continuous.measurable
  unfold localBlockDensity blockDensity blockOscillatingDensity blockPhase coordinateSoftDigit
  fun_prop

theorem localUnsignedProfile_joint_measurable (A : ℝ) (label : Bool) :
    Measurable (fun q : PairState ι × Model.Covariate (D+1) => F.localUnsignedProfile A q.1 label q.2) := by
  have hg : Measurable (jointGate F.Q F.M F.eta F.lambda) := jointGate_measurable _ _ _ _
  have hi := F.inner_smooth.continuous.measurable
  have hp := F.localBlockDensity_joint_measurable label
  unfold localUnsignedProfile
  fun_prop

theorem centeredBlockIntegrand_measurable (Phi : (ℝ × ℝ) → ℝ) (hPhi : Measurable Phi) (label : Bool) :
    Measurable (F.centeredBlockIntegrand Phi label) := by
  have hp := F.localBlockDensity_joint_measurable label
  have hu := F.localUnsignedProfile_joint_measurable F.Au label
  have hv := F.localUnsignedProfile_joint_measurable F.Av label
  have hs : Measurable Lower.sign := measurable_of_countable _
  unfold centeredBlockIntegrand
  fun_prop

theorem centeredBlockTarget_measurable (Phi : (ℝ × ℝ) → ℝ) (hPhi : Measurable Phi) (label : Bool) :
    Measurable (F.centeredBlockTarget Phi label) :=
  (F.centeredBlockIntegrand_measurable Phi hPhi label).stronglyMeasurable.integral_prod_right'.measurable

theorem centeredBlockIntegrand_bound (Phi : (ℝ × ℝ) → ℝ) (B : ℝ)
    (hbound : ∀ u v : ℝ, |u|≤F.Au/F.rminus → |v|≤F.Av/F.rminus → |Phi (u,v)-Phi 0|≤B)
    (label : Bool) (q : PairState ι × Model.Covariate (D+1)) :
    |F.centeredBlockIntegrand Phi label q|≤F.rplus*B := by
  have hs (s : Bool) (x : ℝ) : |Lower.sign s*x|=|x| := by cases s <;> simp [Lower.sign]
  have hfb := hbound (Lower.sign q.1.2.2.1*F.localUnsignedProfile F.Au q.1 label q.2)
    (Lower.sign q.1.2.2.2*F.localUnsignedProfile F.Av q.1 label q.2)
    (by rw [hs]; exact F.localUnsignedProfile_bound F.Au F.Au_nonneg q.1 label q.2)
    (by rw [hs]; exact F.localUnsignedProfile_bound F.Av F.Av_nonneg q.1 label q.2)
  unfold centeredBlockIntegrand
  rw [abs_mul,abs_of_pos (F.rminus_pos.trans_le (F.localBlockDensity_bounds q.1 label q.2).1)]
  exact mul_le_mul (F.localBlockDensity_bounds q.1 label q.2).2 hfb (abs_nonneg _)
    (F.rminus_pos.le.trans F.interval.le)

theorem centeredBlockTarget_bound (Phi : (ℝ × ℝ) → ℝ) (B : ℝ)
    (hbound : ∀ u v : ℝ, |u|≤F.Au/F.rminus → |v|≤F.Av/F.rminus → |Phi (u,v)-Phi 0|≤B)
    (label : Bool) (w : PairState ι) : |F.centeredBlockTarget Phi label w|≤F.rplus*B := by
  have hh := norm_integral_le_of_norm_le_const (μ := Model.cubeVolume (D+1))
    (f := fun y => F.centeredBlockIntegrand Phi label (w,y)) (C := F.rplus*B)
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs]
      exact F.centeredBlockIntegrand_bound Phi B hbound label (w,y)))
  simpa only [centeredBlockTarget,Real.norm_eq_abs,probReal_univ,mul_one] using hh

theorem localCenteredResponse_eq (Phi : (ℝ × ℝ) → ℝ)
    (z : GridPair D N → PairState ι) (b : GridBlock D N) (y : Model.Covariate (D+1)) :
    localCenteredResponse Phi F.p0 ((F.rminus+F.rplus)/2) ((F.rplus-F.rminus)/2-F.delta)
      F.Au F.Av F.inner F.outer (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
      (stateSignU z) (stateSignV z) (stateGates F.Q F.M F.eta F.lambda z) b y =
    F.centeredBlockIntegrand Phi b.2 (z b.1,y) := by
  have he (A sigma gate : ℝ) (inner den : Model.Covariate (D+1) → ℝ) :
      blockProfile A sigma gate inner den y=sigma*(A*gate*inner y/den y) := by
    unfold blockProfile
    ring
  unfold localCenteredResponse centeredBlockIntegrand localUnsignedProfile localBlockDensity
    stateAngles statePhases stateSignU stateSignV stateGates
  simp only [he]

/-- The actual canonical global nonlinear target equals its baseline plus a
literal independent-pair target, for every source realization. -/
theorem global_response_centered_decomposition (Phi : (ℝ × ℝ) → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hbound : ∀ u v : ℝ, |u|≤F.Au/F.rminus → |v|≤F.Av/F.rminus → |Phi (u,v)-Phi 0|≤B)
    (z : GridPair D N → PairState ι) :
    (∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1)) =
      Phi 0+independentPairTarget F.ell (F.centeredBlockTarget Phi) z := by
  have hp : Integrable (F.p z) (Model.cubeVolume (D+1)) :=
    continuous_cube_integrable _ (F.realization z).density_smooth.continuous
  have hm (b : GridBlock D N) : Measurable
      (localCenteredResponse Phi F.p0 ((F.rminus+F.rplus)/2) ((F.rplus-F.rminus)/2-F.delta)
        F.Au F.Av F.inner F.outer (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
        (stateSignU z) (stateSignV z) (stateGates F.Q F.M F.eta F.lambda z) b) :=
    localCenteredResponse_measurable Phi hPhi _ _ _ _ _ _ _ F.inner_smooth.continuous.measurable
      F.outer_smooth.continuous.measurable _ _
      (fun k => (blockPhase_smooth F.U F.M F.a F.q F.gamma (z k).1 F.gamma_pos F.gamma_le).continuous.measurable)
      _ _ _ b
  have hb (b : GridBlock D N) (y : Model.Covariate (D+1)) :
      |localCenteredResponse Phi F.p0 ((F.rminus+F.rplus)/2) ((F.rplus-F.rminus)/2-F.delta)
        F.Au F.Av F.inner F.outer (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
        (stateSignU z) (stateSignV z) (stateGates F.Q F.M F.eta F.lambda z) b y|≤F.rplus*B := by
    rw [F.localCenteredResponse_eq]
    exact F.centeredBlockIntegrand_bound Phi B hbound b.2 (z b.1,y)
  have hh := globalNonlinearTarget_integral Phi F.offset F.ell F.p0
    ((F.rminus+F.rplus)/2) ((F.rplus-F.rminus)/2-F.delta) F.Au F.Av F.ell_pos
    F.offset_nonneg F.size_bound F.inner F.outer F.inner_zero F.outer_zero
    (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
    (stateSignU z) (stateSignV z) (stateGates F.Q F.M F.eta F.lambda z)
    hp (F.realization z).normalized hm (F.rplus*B) hb
  change (∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1)) =
    Phi 0+F.ell^(D+1)*∑ b : GridBlock D N, F.centeredBlockTarget Phi b.2 (z b.1)
  simpa only [globalNonlinearTarget,p,u,v,F.localCenteredResponse_eq,centeredBlockTarget] using hh

/-- The actual model target of the normalized hard observation law has this
centered independent-pair representation. -/
theorem model_target_centered_decomposition (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (O : Model.Observables Z (A.withDimension D)) (pi : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (pi : Measure Z)) (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4)
    (hbase : 0<Model.baselineW (A.withDimension D) O pi) (B : ℝ)
    (hbound : ∀ u v : ℝ, |u|≤F.Au/F.rminus → |v|≤F.Av/F.rminus →
      |SpatialAffine.affineIntegrand (A.withDimension D) O pi S u v-
        SpatialAffine.affineIntegrand (A.withDimension D) O pi S 0 0|≤B)
    (z : GridPair D N → PairState ι) :
    Model.target (A.withDimension D) O (F.observationProbability pi S hsmall z) =
      SpatialAffine.affineIntegrand (A.withDimension D) O pi S 0 0+
        independentPairTarget F.ell
          (F.centeredBlockTarget (fun uv => SpatialAffine.affineIntegrand (A.withDimension D) O pi S uv.1 uv.2)) z := by
  exact (SpatialAffine.model_target_integral (A.withDimension D) O pi S (F.field z) hsmall hbase).trans
    (F.global_response_centered_decomposition _
      (SpatialAffine.affineIntegrand_measurable (A.withDimension D) O pi S) B hbound z)

end RoughRegime.LatticePriors.CanonicalFrame
