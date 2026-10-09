module

public import RoughRegime.ApplicationEffectTransfers
public import RoughRegime.ObservableMeanUpper
public import RoughRegime.RatioBracket


@[expose] public section
/-! Full treatment-effect upper brackets on the literal two-arm class. The
ATE selects the smaller regression smoothness; ATT and ATU select the control
and treated regressions respectively. The construction uses actual keep-arm
kernels, bounded observable sample means, and positive projected ratios. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1000000

abbrev treatmentParameters (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1) : Model.Parameters :=
  parametersWithBeta A (min A.β β1) (lt_min A.hβ hβ1)

theorem treatmentParameters_theta_le_left (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1) :
    (treatmentParameters A β1 hβ1).theta ≤ A.theta := by
  change (A.α + min A.β β1)/(A.d : ℝ) ≤ (A.α+A.β)/(A.d : ℝ)
  exact div_le_div_of_nonneg_right (add_le_add le_rfl (min_le_left A.β β1))
    (Nat.cast_nonneg A.d)

theorem treatmentParameters_theta_le_right (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1) :
    (treatmentParameters A β1 hβ1).theta ≤ (parametersWithBeta A β1 hβ1).theta := by
  change (A.α + min A.β β1)/(A.d : ℝ) ≤ (A.α+β1)/(A.d : ℝ)
  exact div_le_div_of_nonneg_right (add_le_add le_rfl (min_le_right A.β β1))
    (Nat.cast_nonneg A.d)

theorem treatmentParameters_nu_tie_left (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (h : (treatmentParameters A β1 hβ1).theta = A.theta) :
    (A.nu : ℝ) ≤ (treatmentParameters A β1 hβ1).nu := by
  have hd : (A.d : ℝ) ≠ 0 := by
    have hh := A.hd
    exact_mod_cast (show A.d ≠ 0 by omega)
  have hb : min A.β β1 = A.β :=
    add_left_cancel ((div_left_inj' hd).mp h)
  simp only [Model.Parameters.nu, hb]
  exact le_rfl

theorem treatmentParameters_nu_tie_right (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (h : (treatmentParameters A β1 hβ1).theta = (parametersWithBeta A β1 hβ1).theta) :
    ((parametersWithBeta A β1 hβ1).nu : ℝ) ≤ (treatmentParameters A β1 hβ1).nu := by
  have hd : (A.d : ℝ) ≠ 0 := by
    have hh := A.hd
    exact_mod_cast (show A.d ≠ 0 by omega)
  have hb : min A.β β1 = β1 :=
    add_left_cancel ((div_left_inj' hd).mp h)
  simp only [Model.Parameters.nu, hb]
  exact le_rfl

theorem armMean_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (j : Bool) :
    Model.UpperBracket (armMean A.d j) (armClass A j) A.bracketParameters (A.nu : ℝ) := by
  obtain ⟨hν,C,hC,n0,hn0,hupper⟩ := Model.model_upperBracket A (observables A hM)
  exact ⟨hν,C,hC,n0,hn0,fun n hn =>
    ((keepArm_risk_transfer A hM j n 0).2).trans (hupper n hn)⟩

theorem treatment_arm_upperBrackets (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1) :
    Model.UpperBracket (armMean A.d false) (treatmentClass A β1 hβ1)
      A.bracketParameters (A.nu : ℝ) ∧
    Model.UpperBracket (armMean A.d true) (treatmentClass A β1 hβ1)
      (parametersWithBeta A β1 hβ1).bracketParameters ((parametersWithBeta A β1 hβ1).nu : ℝ) :=
  ⟨Model.upperBracket_mono_class _ _ _ (fun _ h => h.1) (armMean_upperBracket A hM false),
   Model.upperBracket_mono_class _ _ _ (fun _ h => h.2)
     (armMean_upperBracket (parametersWithBeta A β1 hβ1) hM true)⟩

def treatmentOutcomeMean (d : ℕ)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) : ℝ :=
  ∫ o, (o.2.2 : ℝ) ∂(P : Measure (Model.Covariate d × TreatmentResponse))

theorem treatmentOutcomeMean_range (d : ℕ)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) :
    treatmentOutcomeMean d P ∈ Icc (0 : ℝ) 1 := by
  have hi : Integrable (fun o : Model.Covariate d × TreatmentResponse => (o.2.2 : ℝ))
      (P : Measure (Model.Covariate d × TreatmentResponse)) :=
    Integrable.of_mem_Icc 0 1
      ((measurable_subtype_coe.comp measurable_snd).comp measurable_snd).aemeasurable
      (Filter.Eventually.of_forall (fun o => o.2.2.property))
  have h0 := integral_mono_ae (integrable_const (0 : ℝ)) hi
    (Filter.Eventually.of_forall (fun o => o.2.2.property.1))
  have h1 := integral_mono_ae hi (integrable_const (1 : ℝ))
    (Filter.Eventually.of_forall (fun o => o.2.2.property.2))
  exact ⟨by simpa only [treatmentOutcomeMean,integral_const,probReal_univ,one_smul] using h0,
    by simpa only [treatmentOutcomeMean,integral_const,probReal_univ,one_smul] using h1⟩

theorem treatmentOutcomeMean_upperBracket (A : Model.Parameters)
    (C : Set (ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)))
    (S : Model.BracketParameters) (ν : ℝ) (hν : 2 ≤ ν) :
    Model.UpperBracket (treatmentOutcomeMean A.d) C S ν :=
  Model.observableMean_upperBracket (fun o : Model.Covariate A.d × TreatmentResponse => (o.2.2 : ℝ))
    ((measurable_subtype_coe.comp measurable_snd).comp measurable_snd)
    1 zero_le_one (fun o => by rw [abs_of_nonneg o.2.2.property.1]; exact o.2.2.property.2) C S ν hν

theorem armProbability_upperBracket (A : Model.Parameters) (j : Bool)
    (C : Set (ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)))
    (S : Model.BracketParameters) (ν : ℝ) (hν : 2 ≤ ν) :
    Model.UpperBracket (armProbability A.d j) C S ν :=
  Model.observableMean_upperBracket (fun o : Model.Covariate A.d × TreatmentResponse => armIndicator j o.2)
    ((armIndicator_measurable j).comp measurable_snd)
    1 zero_le_one (fun o => by
      rw [abs_of_nonneg (armIndicator_range j o.2).1]
      exact (armIndicator_range j o.2).2) C S ν hν

theorem ate_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1) :
    Model.UpperBracket (ate A.d) (treatmentClass A β1 hβ1)
      (treatmentParameters A β1 hβ1).bracketParameters ((treatmentParameters A β1 hβ1).nu : ℝ) := by
  let A1 := parametersWithBeta A β1 hβ1
  let As := treatmentParameters A β1 hβ1
  let C := treatmentClass A β1 hβ1
  let Ti : Fin 2 → ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse) → ℝ :=
    ![armMean A.d false,armMean A.d true]
  let Si : Fin 2 → Model.BracketParameters := ![A.bracketParameters,A1.bracketParameters]
  let νi : Fin 2 → ℝ := ![(A.nu : ℝ),(A1.nu : ℝ)]
  obtain ⟨h0,h1⟩ := treatment_arm_upperBrackets A hM β1 hβ1
  apply Model.finite_upperBracket_transfer _ Ti C Si νi As.bracketParameters (As.nu : ℝ) 1
    (by exact_mod_cast As.nu_ge_two) zero_lt_one
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i
    · exact treatmentParameters_theta_le_left A β1 hβ1
    · exact treatmentParameters_theta_le_right A β1 hβ1
  · intro i; fin_cases i
    · exact treatmentParameters_nu_tie_left A β1 hβ1
    · exact treatmentParameters_nu_tie_right A β1 hβ1
  · intro i; fin_cases i
    · exact h0
    · exact h1
  · intro n
    simpa only [Ti,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      ENNReal.ofReal_one,one_mul,add_comm] using
      Model.difference_minimax n (ate A.d) (armMean A.d true) (armMean A.d false) C (fun _ _ => rfl)

theorem att_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1) :
    Model.UpperBracket (att A.d) (treatmentClass A β1 hβ1) A.bracketParameters (A.nu : ℝ) := by
  let C := treatmentClass A β1 hβ1
  let N := fun P => treatmentOutcomeMean A.d P - armMean A.d false P
  have hν : 2 ≤ (A.nu : ℝ) := by exact_mod_cast A.nu_ge_two
  have hnum := Model.same_upperBracket_difference N _ _ C A.bracketParameters (A.nu : ℝ)
    (treatmentOutcomeMean_upperBracket A C _ _ hν) (treatment_arm_upperBrackets A hM β1 hβ1).1
    (fun _ _ => rfl)
  have hratio := Model.ratio_upperBracket N (armProbability A.d true) C A.bracketParameters (A.nu : ℝ)
    hnum (armProbability_upperBracket A true C _ _ hν) 1 A.δ (1+A.δ) zero_le_one A.hδ (by linarith)
    (by
      rintro P ⟨⟨h0⟩,⟨_h1⟩⟩
      obtain ⟨hy0,hy1⟩ := treatmentOutcomeMean_range A.d P
      obtain ⟨hb0,hb1⟩ := armMean_range A false P h0
      exact ⟨by dsimp only [N]; linarith,by dsimp only [N]; linarith⟩)
    (by
      rintro P ⟨⟨_h0⟩,⟨h1⟩⟩
      have hp := armProbability_range (parametersWithBeta A β1 hβ1) true P h1
      change armProbability A.d true P ∈ Icc A.δ (1-A.δ) at hp
      exact ⟨hp.1,by linarith [hp.2,A.hδ]⟩)
  apply Model.upperBracket_congr_target _ _ C _ _ _ hratio
  rintro P ⟨⟨h0⟩,⟨h1⟩⟩
  exact att_observable_identity A P h0 h1

theorem atu_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1) :
    Model.UpperBracket (atu A.d) (treatmentClass A β1 hβ1)
      (parametersWithBeta A β1 hβ1).bracketParameters ((parametersWithBeta A β1 hβ1).nu : ℝ) := by
  let A1 := parametersWithBeta A β1 hβ1
  let C := treatmentClass A β1 hβ1
  let N := fun P => armMean A.d true P - treatmentOutcomeMean A.d P
  have hν : 2 ≤ (A1.nu : ℝ) := by exact_mod_cast A1.nu_ge_two
  have hnum := Model.same_upperBracket_difference N _ _ C A1.bracketParameters (A1.nu : ℝ)
    (treatment_arm_upperBrackets A hM β1 hβ1).2 (treatmentOutcomeMean_upperBracket A C _ _ hν)
    (fun _ _ => rfl)
  have hratio := Model.ratio_upperBracket N (armProbability A.d false) C A1.bracketParameters (A1.nu : ℝ)
    hnum (armProbability_upperBracket A false C _ _ hν) 1 A.δ (1+A.δ) zero_le_one A.hδ (by linarith)
    (by
      rintro P ⟨⟨_h0⟩,⟨h1⟩⟩
      obtain ⟨hy0,hy1⟩ := treatmentOutcomeMean_range A.d P
      have hb := armMean_range A1 true P h1
      change armMean A.d true P ∈ Icc (0 : ℝ) 1 at hb
      obtain ⟨hb0,hb1⟩ := hb
      exact ⟨by dsimp only [N]; linarith,by dsimp only [N]; linarith⟩)
    (by
      rintro P ⟨⟨h0⟩,⟨_h1⟩⟩
      have hp := armProbability_range A false P h0
      exact ⟨hp.1,by linarith [hp.2,A.hδ]⟩)
  apply Model.upperBracket_congr_target _ _ C _ _ _ hratio
  rintro P ⟨⟨h0⟩,⟨h1⟩⟩
  dsimp only [N,treatmentOutcomeMean]
  rw [armProbability_complement]
  exact atu_observable_identity A P h0 h1

/-- The original eta application constants, with the source response bound
one and the literal interval [eta,eta inverse]. -/
def etaParameters (d : ℕ) (α β H η : ℝ) (hd : 1 ≤ d)
    (hα : 0 < α) (hβ : 0 < β) (hH : 0 < H) (hη : 0 < η) (hηquarter : η < 1/4) :
    Model.Parameters where
  d := d
  α := α
  β := β
  H := H
  δ := η
  gminus := η
  gplus := η⁻¹
  M0 := 1
  hd := hd
  hα := hα
  hβ := hβ
  hH := hH
  hδ := hη
  hgminus := hη
  hgplus := by
    rw [← one_div]
    apply (lt_div_iff₀ hη).mpr
    nlinarith
  hM0 := zero_lt_one

/-- The actual T_eta class in the applications table. No restrictions on the
conditional outcome distribution beyond the bounded response are added. -/
abbrev etaTreatmentClass (d : ℕ) (α β0 β1 H η : ℝ) (hd : 1 ≤ d)
    (hα : 0 < α) (hβ0 : 0 < β0) (hβ1 : 0 < β1) (hH : 0 < H)
    (hη : 0 < η) (hηquarter : η < 1/4) :=
  treatmentClass (etaParameters d α β0 H η hd hα hβ0 hH hη hηquarter) β1 hβ1

/-- All three original T_eta upper-bracket rows, using only the fixed class
parameters. The selected smoothness is min(beta0,beta1), beta0, and beta1. -/
theorem eta_treatment_upperBrackets (d : ℕ) (α β0 β1 H η : ℝ) (hd : 1 ≤ d)
    (hα : 0 < α) (hβ0 : 0 < β0) (hβ1 : 0 < β1) (hH : 0 < H)
    (hη : 0 < η) (hηquarter : η < 1/4) :
    let A := etaParameters d α β0 H η hd hα hβ0 hH hη hηquarter
    let A1 := parametersWithBeta A β1 hβ1
    let As := treatmentParameters A β1 hβ1
    let C := etaTreatmentClass d α β0 β1 H η hd hα hβ0 hβ1 hH hη hηquarter
    Model.UpperBracket (ate d) C As.bracketParameters (As.nu : ℝ) ∧
      Model.UpperBracket (att d) C A.bracketParameters (A.nu : ℝ) ∧
      Model.UpperBracket (atu d) C A1.bracketParameters (A1.nu : ℝ) := by
  dsimp only
  let A := etaParameters d α β0 H η hd hα hβ0 hH hη hηquarter
  exact ⟨ate_upperBracket A le_rfl β1 hβ1,att_upperBracket A le_rfl β1 hβ1,
    atu_upperBracket A le_rfl β1 hβ1⟩

end RoughRegime.Applications.MAR
