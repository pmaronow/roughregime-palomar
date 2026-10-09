module

public import RoughRegime.ApplicationSeparatedTreatment
public import RoughRegime.CubeAE
public import RoughRegime.ApplicationTreatmentUpper


@[expose] public section
/-! Separated treatment moment identities via genuine finite Hölder reciprocal
calculus. Auxiliary inverse radii are chosen uniformly and do not restrict the
literal separated class. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.SeparatedTreatment
set_option maxHeartbeats 700000

structure InverseSetup (A : Model.Parameters) where
  Q : ℝ
  hQ : 0<Q
  inverseHolder : ∀ w : Model.Covariate A.d→ℝ,
    w ∈ Model.holderBall A.α (A.H+1) →
    (∀ x ∈ Model.cube A.d,A.δ≤w x) →
    (fun x => (w x)⁻¹) ∈ Model.holderBall A.α Q

theorem exists_inverseSetup (A : Model.Parameters) : Nonempty (InverseSetup A) := by
  obtain ⟨Q,hQ,hquot⟩ := Model.uniform_holder_quotient A.d A.α 1 (A.H+1) A.δ
    A.hα zero_le_one (by linarith [A.hH]) A.hδ
  refine ⟨⟨Q,hQ,?_⟩⟩
  intro w hw hl
  have h := hquot (fun _ => 1) w (Model.const_mem_holderBall A.hα (by norm_num)) hw hl
  simpa only [one_div] using h

def inverseParameters (A : Model.Parameters) (S : InverseSetup A)
    (hδ : A.δ≤1/2) (β : ℝ) (hβ : 0<β) : Model.Parameters :=
  { A with
    β := β
    hβ := hβ
    H := max (A.H+1) S.Q
    hH := by
      have h : 0<A.H+1 := by linarith [A.hH]
      exact h.trans_le (le_max_left _ _)
    gminus := A.δ*A.gminus
    hgminus := mul_pos A.hδ A.hgminus
    hgplus := by
      have hd : A.δ≤1 := by linarith
      exact (mul_le_mul_of_nonneg_right hd A.hgminus.le).trans_lt (by simpa using A.hgplus) }

def ArmWitness.toMAR (A : Model.Parameters) (S : InverseSetup A) (hδ : A.δ≤1/2)
    (β : ℝ) (hβ : 0<β) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse))
    (W : ArmWitness (armParameters A β hβ) j P) :
    MAR.ArmWitness (inverseParameters A S hδ β hβ) j P where
  p := W.p
  w := W.w
  b := W.b
  measurableP := W.measurableP
  measurableW := W.measurableW
  measurableB := W.measurableB
  nonnegativeP := W.nonnegativeP
  marginal := W.marginal
  momentD := W.momentD
  momentV := W.momentV
  overlap := W.overlap
  smoothInverse := by
    have hp := Model.holderBall_ae_mem_Icc_cube W.w A.α (A.H+1) A.δ (1-A.δ)
      W.smoothW W.overlap
    have h := S.inverseHolder W.w W.smoothW (fun x hx => (hp x hx).1)
    exact h.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  smoothB := W.smoothB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  densityBounds := by
    change ∀ᵐ x ∂Model.cubeVolume A.d,
      A.δ*A.gminus≤W.w x*W.p x ∧ W.w x*W.p x≤A.gplus
    filter_upwards [W.overlap,W.densityBounds] with x hw hp
    change A.δ≤W.w x ∧ W.w x≤1-A.δ at hw
    change A.gminus≤W.p x ∧ W.p x≤A.gplus at hp
    have hwp : 0≤W.w x := A.hδ.le.trans hw.1
    have hpp : 0≤W.p x := A.hgminus.le.trans hp.1
    constructor
    · exact mul_le_mul hw.1 hp.1 A.hgminus.le hwp
    · calc
        W.w x*W.p x ≤ 1*W.p x := mul_le_mul_of_nonneg_right (by linarith [hw.2,A.hδ]) hpp
        _ ≤ A.gplus := by simpa only [one_mul] using hp.2

theorem Witness.att_observable_identity (A : Model.Parameters) (S : InverseSetup A)
    (hδ : A.δ≤1/2) (β1 : ℝ) (hβ1 : 0<β1)
    (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse))
    (W : Witness A β1 hβ1 P) :
    MAR.att A.d P=(MAR.treatmentOutcomeMean A.d P-MAR.armMean A.d false P)/
      MAR.armProbability A.d true P :=
  MAR.att_observable_identity (inverseParameters A S hδ A.β A.hβ) P
    ((W.controlArm A β1 hβ1 P).toMAR A S hδ A.β A.hβ false P)
    ((W.treatedArm A β1 hβ1 P).toMAR A S hδ β1 hβ1 true P)

theorem Witness.atu_observable_identity (A : Model.Parameters) (S : InverseSetup A)
    (hδ : A.δ≤1/2) (β1 : ℝ) (hβ1 : 0<β1)
    (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse))
    (W : Witness A β1 hβ1 P) :
    MAR.atu A.d P=(MAR.armMean A.d true P-MAR.treatmentOutcomeMean A.d P)/
      (1-MAR.armProbability A.d true P) :=
  MAR.atu_observable_identity (inverseParameters A S hδ A.β A.hβ) P
    ((W.controlArm A β1 hβ1 P).toMAR A S hδ A.β A.hβ false P)
    ((W.treatedArm A β1 hβ1 P).toMAR A S hδ β1 hβ1 true P)

end RoughRegime.Applications.SeparatedTreatment
