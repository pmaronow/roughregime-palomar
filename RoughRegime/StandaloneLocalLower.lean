module

public import RoughRegime.LocalLowerData
public import RoughRegime.SourceStandaloneExtras
public import RoughRegime.SourceGermUniform
public import RoughRegime.SourceFixedOffsetLower
public import RoughRegime.AffineResponseUniform
public import RoughRegime.UniformCube


@[expose] public section
/-! Standalone original Proposition15 and Lemma16. The inputs are the actual
finite response baseline and the supplied bounded dual scores. An enclosing
model is constructed from those inputs; its nondegeneracy is proved from the
score identities. All finite smooth-germ restrictions and target offsets are
retained. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace RoughRegime.LocalLower
open RoughRegime.LatticePriors RoughRegime.Localization

structure StandingData {Z : Type*} [MeasurableSpace Z]
    (O : ResponseData Z) (π : ProbabilityMeasure Z) where
  dimensionPred : ℕ
  alpha : ℝ
  beta : ℝ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  rminus : ℝ
  rplus : ℝ
  rminus_pos : 0 < rminus
  rminus_lt_one : rminus < 1
  one_lt_rplus : 1 < rplus
  baseline_pos : 0 < O.w0 π
  finite_support : ∃ s : Finset Z, (π : Measure Z) (s : Set Z)=1
  scores : SpatialAffine.Scores (π : Measure Z)
  score_identity : O.scoreIdentity π scores alpha beta

namespace StandingData
set_option backward.isDefEq.respectTransparency false
variable {Z : Type*} [MeasurableSpace Z] {O : ResponseData Z} {π : ProbabilityMeasure Z}
    (S : StandingData O π)

def parameters : Model.Parameters :=
  O.parameters π S.dimensionPred S.alpha S.beta S.rminus S.rplus
    S.alpha_pos S.beta_pos S.rminus_pos S.rminus_lt_one S.one_lt_rplus S.baseline_pos

def observables : Model.Observables Z (S.parameters.withDimension S.dimensionPred) :=
  O.observables (S.parameters.withDimension S.dimensionPred) le_rfl

abbrev SourceFamily := SourceModelFamily S.parameters S.dimensionPred S.observables π

def SelectedExtras {ι : Type*} [Fintype ι]
    (F : S.SourceFamily) (e : ι→SourceExtraCondition S.alpha S.beta) : Prop :=
  ∀ (θ τ c0 r : ℝ), 0 < θ → θ < 1/2 → 0 < τ → 0 < r →
    ∀ᶠ n in atTop, ∃ V : F.SelectedValidity θ τ c0 n,
      let B := F.selectedFrame θ τ c0 n V
      ∃ hsmall : (B.Au+B.Av)/F.rminus*F.scores.C ≤ 1/4,
        ∀ z : GridPair S.dimensionPred
            (selectedGridPairs θ τ c0
              (selectedSourceVolume S.parameters (S.dimensionPred+1) θ τ) (S.dimensionPred+1) n)→
            PairState (Fin (selectedSourceLevel S.parameters (S.dimensionPred+1) θ τ n)×
              Fin (S.dimensionPred+1)),
          (SpatialAffine.law F.scores (B.field z) hsmall).probabilityMeasure∈
            Model.localClass (S.parameters.withDimension S.dimensionPred) S.observables π r ∧
          ∀ i, (e i).condition.Holds (B.field z).p (B.field z).u (B.field z).v

/-- Original supplied-score inputs construct the actual hard family at every
requested positive epsilon, with all finite H/I/W restrictions. -/
theorem proposition15_lemma16_hard_family (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {ι : Type*} [Fintype ι] (e : ι→SourceExtraCondition S.alpha S.beta)
    (hbase : ∀ i, (e i).condition.baselineAdmissible S.rminus S.rplus) :
    ∃ F : S.SourceFamily, F.Localized ∧ F.scores=S.scores ∧
      F.rminus=S.rminus ∧ F.rplus=S.rplus ∧ F.epsilonU+F.epsilonV ≤ epsilon ∧
      S.SelectedExtras F e := by
  obtain ⟨F,hF,hS,hrm,hrp⟩ := O.exists_prescribed_score_family π S.dimensionPred
    S.alpha S.beta S.rminus S.rplus S.alpha_pos S.beta_pos S.rminus_pos S.rminus_lt_one
    S.one_lt_rplus S.baseline_pos S.finite_support S.scores S.score_identity
  obtain ⟨G,hG,hcap,hSG,_,_⟩ := hF.capped_all epsilon hepsilon
  have hbaseG : ∀ i, (e i).condition.baselineAdmissible G.rminus G.rplus := by
    intro i
    change (e i).condition.baselineAdmissible F.rminus F.rplus
    rw [hrm,hrp]
    exact hbase i
  obtain ⟨H,hH,hweights,hSH,_,_,hextras⟩ :=
    G.exists_universal_selected_extra_family_bounded hG e hbaseG
  refine ⟨H,hH,hSH.trans (hSG.trans hS),?_,?_,hweights.trans hcap,hextras⟩
  · exact hrm
  · exact hrp

/-- Lemma16's parametric clause uses the actual constant Holder norm, and
holds regardless of the rough/smooth regime. -/
theorem lemma16_constant_path {ι : Type*} [Fintype ι]
    (e : ι→SourceExtraCondition S.alpha S.beta)
    (hbase : ∀ i, (e i).condition.baselineAdmissible S.rminus S.rplus) :
    ∃ r : ℝ, 0 < r ∧ ∀ a : ℝ×ℝ, |a.1|≤r → |a.2|≤r →
      ∀ i, (e i).condition.Holds (fun _ : Model.Covariate (S.dimensionPred+1) => 1)
        (fun _ => a.1) (fun _ => a.2) :=
  finite_constant_neighborhood (fun i => (e i).condition) S.rminus S.rplus
    S.rminus_lt_one S.one_lt_rplus hbase

/-- Proposition15(a), including arbitrary supplied scores, original density
endpoints, every finite restriction, and every containing statistical class
with a fixed additive target offset. -/
theorem proposition15_rough (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {ι : Type*} [Fintype ι] (e : ι→SourceExtraCondition S.alpha S.beta)
    (hbase : ∀ i, (e i).condition.baselineAdmissible S.rminus S.rplus)
    (hrough : (S.parameters.withDimension S.dimensionPred).theta < 1/2) :
    ∃ F : S.SourceFamily, F.Localized ∧ F.scores=S.scores ∧
      F.rminus=S.rminus ∧ F.rplus=S.rplus ∧ F.epsilonU+F.epsilonV ≤ epsilon ∧
      S.SelectedExtras F e ∧
      ∃ c0 c : ℝ, 0 < c ∧
        ∀ (Cn : ℕ→Set (ProbabilityMeasure
            (Model.Observation (S.parameters.withDimension S.dimensionPred) Z)))
          (T : ProbabilityMeasure
            (Model.Observation (S.parameters.withDimension S.dimensionPred) Z)→ℝ) (tstar : ℝ),
        F.SelectedClassSequenceClaim (S.parameters.withDimension S.dimensionPred).theta
          (Rates.tau S.rminus S.rplus) c0 Cn →
        F.SelectedTargetOffsetClaim (S.parameters.withDimension S.dimensionPred).theta
          (Rates.tau S.rminus S.rplus) c0 T tstar →
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal (Real.sqrt (3/8)*c*Rates.subcriticalScale n
            (S.parameters.withDimension S.dimensionPred).theta
            (Rates.tau S.rminus S.rplus)*Real.log n) ≤ Model.minimaxRMSE n T (Cn n) ∧
          (3/8 : ℝ≥0∞) ≤ Model.minimaxTail n T (Cn n)
            (c*Rates.subcriticalScale n (S.parameters.withDimension S.dimensionPred).theta
              (Rates.tau S.rminus S.rplus)*Real.log n) := by
  obtain ⟨F,hF,hS,hrm,hrp,hweight,hextras⟩ :=
    S.proposition15_lemma16_hard_family epsilon hepsilon e hbase
  refine ⟨F,hF,hS,hrm,hrp,hweight,hextras,?_⟩
  obtain ⟨c0,c,hc,hbound⟩ := F.exists_fixed_offset_shift_rough_lower hF hrough
  refine ⟨c0,c,hc,?_⟩
  intro Cn T tstar hclass htarget
  have hclass' : F.SelectedClassSequenceClaim (S.parameters.withDimension S.dimensionPred).theta
      (Rates.tau F.rminus F.rplus) c0 Cn := by simpa only [hrm,hrp] using hclass
  have htau : Rates.tau S.parameters.gminus S.parameters.gplus=Rates.tau S.rminus S.rplus := by
    rw [←F.normalized_tau,hrm,hrp]
  have htarget' : F.SelectedTargetOffsetClaim (S.parameters.withDimension S.dimensionPred).theta
      (Rates.tau F.rminus F.rplus) c0 T tstar := by simpa only [hrm,hrp] using htarget
  simpa only [htau] using hbound Cn T tstar hclass' htarget' 

def parametricRadius : ℝ := 1/(4*(S.scores.C+1))

theorem parametricRadius_pos : 0 < S.parametricRadius := by
  unfold parametricRadius
  positivity [S.scores.nonnegativeC]

theorem parametricRadius_small : S.parametricRadius*S.scores.C ≤ 1/4 := by
  have hc : 0 < S.scores.C+1 := by linarith [S.scores.nonnegativeC]
  have he : S.parametricRadius*(S.scores.C+1)=1/4 := by
    unfold parametricRadius
    field_simp
  nlinarith [S.parametricRadius_pos]

/-- Proposition15(b) for exactly the supplied scores, including every
sufficiently small nonzero fixed u and every class containing an arbitrary
neighborhood of the true affine response path. -/
theorem proposition15_parametric :
    ∀ᶠ u : ℝ in nhds 0, u ≠ 0 → ∃ hu : |u| ≤ S.parametricRadius,
      let P := fun t => AffineResponseLower.withDesign (π : Measure Z)
        (Model.cubeVolume (S.dimensionPred+1))
        (AffineResponseLower.responseDensityLaw (π : Measure Z) S.scores.su S.scores.sv
          S.scores.measurableU S.scores.measurableV u S.parametricRadius S.scores.C
          S.parametricRadius_pos.le S.scores.nonnegativeC hu S.parametricRadius_small
          S.scores.boundU S.scores.boundV S.scores.meanU S.scores.meanV t)
      ∃ c : ℝ, 0 < c ∧
      ∀ (T : ProbabilityMeasure (Model.Covariate (S.dimensionPred+1)×Z)→ℝ)
        (C : Set (ProbabilityMeasure (Model.Covariate (S.dimensionPred+1)×Z))) (tstar : ℝ),
        (∀ᶠ t in nhds 0, (P t).probabilityMeasure∈C) →
        ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
          fun t => Model.target (S.parameters.withDimension S.dimensionPred)
            S.observables (P t).probabilityMeasure+tstar) →
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤ Model.minimaxRMSE n T C := by
  have hU0 : (∫z,S.observables.U z ∂(π : Measure Z))=
      O.a0 π*(∫z,S.observables.D z ∂(π : Measure Z)) := by
    change (∫z,O.U z ∂(π : Measure Z))=((∫z,O.U z ∂(π : Measure Z))/O.w0 π)*O.w0 π
    field_simp [S.baseline_pos.ne']
  have hV0 : (∫z,S.observables.V z ∂(π : Measure Z))=
      O.b0 π*(∫z,S.observables.D z ∂(π : Measure Z)) := by
    change (∫z,O.V z ∂(π : Measure Z))=((∫z,O.V z ∂(π : Measure Z))/O.w0 π)*O.w0 π
    field_simp [S.baseline_pos.ne']
  rcases S.score_identity with hpos|hdiag
  · exact AffineResponseLower.actual_target_rootn_near_uniform (π : Measure Z)
      (S.parameters.withDimension S.dimensionPred) S.observables
      (Model.cubeVolume (S.dimensionPred+1)) S.scores.su S.scores.sv
      S.scores.measurableU S.scores.measurableV S.parametricRadius S.scores.C
      S.parametricRadius_pos S.scores.nonnegativeC S.parametricRadius_small
      S.scores.boundU S.scores.boundV S.scores.meanU S.scores.meanV
      (O.a0 π) (O.b0 π) S.baseline_pos hU0 hV0
      hpos.1 hpos.2.1 hpos.2.2.1 hpos.2.2.2
  · have hd := AffineResponseLower.actual_diagonal_target_rootn_near_uniform (π : Measure Z)
      (S.parameters.withDimension S.dimensionPred) S.observables
      (Model.cubeVolume (S.dimensionPred+1)) S.scores.su S.scores.measurableU
      S.parametricRadius S.scores.C S.parametricRadius_pos S.scores.nonnegativeC
      S.parametricRadius_small S.scores.boundU S.scores.meanU (O.a0 π) S.baseline_pos
      hdiag.1 hU0 hdiag.2.2.2
    simpa only [←hdiag.2.2.1,Model.Parameters.withDimension] using hd

end StandingData
end RoughRegime.LocalLower
