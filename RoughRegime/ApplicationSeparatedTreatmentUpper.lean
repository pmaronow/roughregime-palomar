module

public import RoughRegime.ApplicationSeparatedTreatment
public import RoughRegime.ApplicationSeparatedUpper
public import RoughRegime.ApplicationTreatmentUpper
public import RoughRegime.SeparatedTreatmentMoments


@[expose] public section
/-! The literal qualified upper brackets for all three treatment effects on
the separated-density class. The keep-arm maps use the proved finite Holder
complement bound, and the design interval is exactly the source `I_zeta`. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace RoughRegime.Applications.SeparatedTreatment
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

theorem armMean_upperBracket (A : Model.Parameters) (j : Bool) (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    Model.UpperBracket (MAR.armMean A.d j) (armClass A j)
      (SeparatedMAR.enlargedBracketParameters A ζ hζ hζ1) (A.nu : ℝ) := by
  obtain ⟨hν,C,hC,n0,hn0,he⟩ := SeparatedMAR.separated_upperBracket A ζ hζ hζ1
  exact ⟨hν,C,hC,n0,hn0,fun n hn => ((keepArm_risk_transfer A j n 0).2).trans (he n hn)⟩

theorem treatment_arm_upperBrackets (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    Model.UpperBracket (MAR.armMean A.d false) (modelClass A β1 hβ1)
      (SeparatedMAR.enlargedBracketParameters A ζ hζ hζ1) (A.nu : ℝ) ∧
    Model.UpperBracket (MAR.armMean A.d true) (modelClass A β1 hβ1)
      (SeparatedMAR.enlargedBracketParameters (MAR.parametersWithBeta A β1 hβ1) ζ hζ hζ1)
      ((MAR.parametersWithBeta A β1 hβ1).nu : ℝ) := by
  constructor
  · exact Model.upperBracket_mono_class _ _ _ (modelClass_subset_control A β1 hβ1)
      (armMean_upperBracket (armParameters A A.β A.hβ) false ζ hζ hζ1)
  · exact Model.upperBracket_mono_class _ _ _ (modelClass_subset_treated A β1 hβ1)
      (armMean_upperBracket (armParameters A β1 hβ1) true ζ hζ hζ1)

theorem ate_upperBracket (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    Model.UpperBracket (MAR.ate A.d) (modelClass A β1 hβ1)
      (SeparatedMAR.enlargedBracketParameters (MAR.treatmentParameters A β1 hβ1) ζ hζ hζ1)
      ((MAR.treatmentParameters A β1 hβ1).nu : ℝ) := by
  let A1 := MAR.parametersWithBeta A β1 hβ1
  let As := MAR.treatmentParameters A β1 hβ1
  let C := modelClass A β1 hβ1
  let Ti : Fin 2 → ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse) → ℝ :=
    ![MAR.armMean A.d false,MAR.armMean A.d true]
  let Si : Fin 2 → Model.BracketParameters :=
    ![SeparatedMAR.enlargedBracketParameters A ζ hζ hζ1,SeparatedMAR.enlargedBracketParameters A1 ζ hζ hζ1]
  let νi : Fin 2 → ℝ := ![(A.nu : ℝ),(A1.nu : ℝ)]
  obtain ⟨h0,h1⟩ := treatment_arm_upperBrackets A β1 hβ1 ζ hζ hζ1
  apply Model.finite_upperBracket_transfer _ Ti C Si νi
    (SeparatedMAR.enlargedBracketParameters As ζ hζ hζ1) (As.nu : ℝ) 1
    (by exact_mod_cast As.nu_ge_two) zero_lt_one
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i
    · exact MAR.treatmentParameters_theta_le_left A β1 hβ1
    · exact MAR.treatmentParameters_theta_le_right A β1 hβ1
  · intro i; fin_cases i
    · exact MAR.treatmentParameters_nu_tie_left A β1 hβ1
    · exact MAR.treatmentParameters_nu_tie_right A β1 hβ1
  · intro i; fin_cases i
    · exact h0
    · exact h1
  · intro n
    simpa only [Ti,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,ENNReal.ofReal_one,one_mul,add_comm] using
      Model.difference_minimax n (MAR.ate A.d) (MAR.armMean A.d true) (MAR.armMean A.d false) C (fun _ _ => rfl)

theorem modelClass_empty_of_large_delta (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (hδ : ¬A.δ ≤ 1/2) : modelClass A β1 hβ1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro P ⟨W⟩
  obtain ⟨x,hx⟩ := W.overlap.exists
  apply hδ
  linarith [hx.1,hx.2]

theorem att_upperBracket (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    Model.UpperBracket (MAR.att A.d) (modelClass A β1 hβ1)
      (SeparatedMAR.enlargedBracketParameters A ζ hζ hζ1) (A.nu : ℝ) := by
  by_cases hδ : A.δ ≤ 1/2
  · obtain ⟨S⟩ := exists_inverseSetup A
    let C := modelClass A β1 hβ1
    let BS := SeparatedMAR.enlargedBracketParameters A ζ hζ hζ1
    let N := fun P => MAR.treatmentOutcomeMean A.d P-MAR.armMean A.d false P
    have hν : 2 ≤ (A.nu : ℝ) := by exact_mod_cast A.nu_ge_two
    have hnum := Model.same_upperBracket_difference N _ _ C BS (A.nu : ℝ)
      (MAR.treatmentOutcomeMean_upperBracket A C BS _ hν)
      (treatment_arm_upperBrackets A β1 hβ1 ζ hζ hζ1).1 (fun _ _ => rfl)
    have hratio := Model.ratio_upperBracket N (MAR.armProbability A.d true) C BS (A.nu : ℝ)
      hnum (MAR.armProbability_upperBracket A true C BS _ hν) 1 A.δ (1+A.δ)
      zero_le_one A.hδ (by linarith)
      (by
        rintro P ⟨W⟩
        have WM := (W.controlArm A β1 hβ1 P).toMAR A S hδ A.β A.hβ false P
        obtain ⟨hy0,hy1⟩ := MAR.treatmentOutcomeMean_range A.d P
        obtain ⟨hb0,hb1⟩ := MAR.armMean_range (inverseParameters A S hδ A.β A.hβ) false P WM
        change 0 ≤ MAR.armMean A.d false P at hb0
        change MAR.armMean A.d false P ≤ 1 at hb1
        exact ⟨by dsimp only [N]; linarith,by dsimp only [N]; linarith⟩)
      (by
        rintro P ⟨W⟩
        have WM := (W.treatedArm A β1 hβ1 P).toMAR A S hδ β1 hβ1 true P
        have hp := MAR.armProbability_range (inverseParameters A S hδ β1 hβ1) true P WM
        change MAR.armProbability A.d true P ∈ Icc A.δ (1-A.δ) at hp
        exact ⟨hp.1,by linarith [hp.2,A.hδ]⟩)
    apply Model.upperBracket_congr_target _ _ C BS _ _ hratio
    rintro P ⟨W⟩
    exact W.att_observable_identity A S hδ β1 hβ1 P
  · refine ⟨by exact_mod_cast A.nu_ge_two,1,zero_lt_one,3,le_rfl,?_⟩
    intro n _
    rw [modelClass_empty_of_large_delta A β1 hβ1 hδ,Model.minimaxRMSE_empty]
    exact bot_le

theorem atu_upperBracket (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    Model.UpperBracket (MAR.atu A.d) (modelClass A β1 hβ1)
      (SeparatedMAR.enlargedBracketParameters (MAR.parametersWithBeta A β1 hβ1) ζ hζ hζ1)
      ((MAR.parametersWithBeta A β1 hβ1).nu : ℝ) := by
  let A1 := MAR.parametersWithBeta A β1 hβ1
  by_cases hδ : A.δ ≤ 1/2
  · obtain ⟨S⟩ := exists_inverseSetup A
    let C := modelClass A β1 hβ1
    let BS := SeparatedMAR.enlargedBracketParameters A1 ζ hζ hζ1
    let N := fun P => MAR.armMean A.d true P-MAR.treatmentOutcomeMean A.d P
    have hν : 2 ≤ (A1.nu : ℝ) := by exact_mod_cast A1.nu_ge_two
    have hnum := Model.same_upperBracket_difference N _ _ C BS (A1.nu : ℝ)
      (treatment_arm_upperBrackets A β1 hβ1 ζ hζ hζ1).2
      (MAR.treatmentOutcomeMean_upperBracket A C BS _ hν) (fun _ _ => rfl)
    have hratio := Model.ratio_upperBracket N (MAR.armProbability A.d false) C BS (A1.nu : ℝ)
      hnum (MAR.armProbability_upperBracket A false C BS _ hν) 1 A.δ (1+A.δ)
      zero_le_one A.hδ (by linarith)
      (by
        rintro P ⟨W⟩
        have WM := (W.treatedArm A β1 hβ1 P).toMAR A S hδ β1 hβ1 true P
        obtain ⟨hy0,hy1⟩ := MAR.treatmentOutcomeMean_range A.d P
        obtain ⟨hb0,hb1⟩ := MAR.armMean_range (inverseParameters A S hδ β1 hβ1) true P WM
        change 0 ≤ MAR.armMean A.d true P at hb0
        change MAR.armMean A.d true P ≤ 1 at hb1
        exact ⟨by dsimp only [N]; linarith,by dsimp only [N]; linarith⟩)
      (by
        rintro P ⟨W⟩
        have WM := (W.controlArm A β1 hβ1 P).toMAR A S hδ A.β A.hβ false P
        have hp := MAR.armProbability_range (inverseParameters A S hδ A.β A.hβ) false P WM
        change MAR.armProbability A.d false P ∈ Icc A.δ (1-A.δ) at hp
        exact ⟨hp.1,by linarith [hp.2,A.hδ]⟩)
    apply Model.upperBracket_congr_target _ _ C BS _ _ hratio
    rintro P ⟨W⟩
    dsimp only [N]
    rw [MAR.armProbability_complement]
    exact W.atu_observable_identity A S hδ β1 hβ1 P
  · refine ⟨by exact_mod_cast A1.nu_ge_two,1,zero_lt_one,3,le_rfl,?_⟩
    intro n _
    rw [modelClass_empty_of_large_delta A β1 hβ1 hδ,Model.minimaxRMSE_empty]
    exact bot_le

theorem treatment_upperBrackets (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    let C := modelClass A β1 hβ1
    Model.UpperBracket (MAR.ate A.d) C
      (SeparatedMAR.enlargedBracketParameters (MAR.treatmentParameters A β1 hβ1) ζ hζ hζ1)
      ((MAR.treatmentParameters A β1 hβ1).nu : ℝ) ∧
    Model.UpperBracket (MAR.att A.d) C
      (SeparatedMAR.enlargedBracketParameters A ζ hζ hζ1) (A.nu : ℝ) ∧
    Model.UpperBracket (MAR.atu A.d) C
      (SeparatedMAR.enlargedBracketParameters (MAR.parametersWithBeta A β1 hβ1) ζ hζ hζ1)
      ((MAR.parametersWithBeta A β1 hβ1).nu : ℝ) :=
  ⟨ate_upperBracket A β1 hβ1 ζ hζ hζ1,att_upperBracket A β1 hβ1 ζ hζ hζ1,atu_upperBracket A β1 hβ1 ζ hζ hζ1⟩

end RoughRegime.Applications.SeparatedTreatment
