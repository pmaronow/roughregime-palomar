module

public import RoughRegime.ApplicationsRisk
public import RoughRegime.KernelSeedBridge
public import RoughRegime.ModelUpperConsequences
public import RoughRegime.RateCombination


@[expose] public section
/-! Actual Lipschitz risk composition in the model's uniform-seed convention.
No independent or hypothetical estimators are assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RoughRegime.Model

/-- The zero-moment part of source Lemma19(a), directly on the actual iid
experiment. Each coordinate estimator is projected onto its true interval. -/
theorem lipschitz_minimax_combination {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (n : ℕ) (T : ProbabilityMeasure Ω → ℝ) (Ti : Fin m → ProbabilityMeasure Ω → ℝ)
    (C : Set (ProbabilityMeasure Ω)) (lo hi : Fin m → ℝ) (hlohi : ∀ i, lo i ≤ hi i)
    (Φ : ((i : Fin m) → Icc (lo i) (hi i)) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ a b, |Φ a - Φ b| ≤ L * ∑ i, |(a i : ℝ) - b i|)
    (hmem : ∀ P ∈ C, ∀ i, Ti i P ∈ Icc (lo i) (hi i))
    (hrelation : ∀ P ∈ C, T P = Φ (fun i => projIcc (lo i) (hi i) (hlohi i) (Ti i P))) :
    minimaxRMSE n T C ≤ ENNReal.ofReal L * ∑ i, minimaxRMSE n (Ti i) C := by
  haveI : ∀ P : ProbabilityMeasure Ω, IsProbabilityMeasure (randomizedExperiment n P) := fun P => by
    change IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => (P : Measure Ω))).prod KernelSeedBridge.seedLaw)
    infer_instance
  let Ψ : ((i : Fin m) → Icc (lo i) (hi i)) → Unit → ℝ := fun a _ => Φ a
  have hLipΨ : ∀ a b q r, |Ψ a q - Ψ b r| ≤
      L * ((∑ i, |(a i : ℝ) - b i|) + dist q r) := by
    intro a b q r
    simpa only [Ψ,dist_self,Subsingleton.elim q r,add_zero] using hLip a b
  have h := Applications.lipschitz_combination_minimax (randomizedExperiment n) T Ti C
    lo hi hlohi Ψ (Applications.lipschitz_combination_measurable lo hi Ψ L hL hLipΨ)
    (fun _ => ()) measurable_const (fun _ => ()) L 0 0 hL le_rfl hLipΨ hmem
    (by intro P hP; simp only [Ψ,hrelation P hP,sub_self,abs_zero,le_refl])
    (by intro P _; simp)
  simp only [mul_zero,ENNReal.ofReal_zero,add_zero] at h
  simpa only [← minimaxRMSE_eq_squaredRisk] using h

/-- A common one-dimensional interval is a special case of the exact finite
composition result; the target identity is required only on the class. -/
theorem difference_minimax {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T U V : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (hrelation : ∀ P ∈ C, T P = U P - V P) :
    minimaxRMSE n T C ≤ minimaxRMSE n U C + minimaxRMSE n V C := by
  let Ti : Fin 2 → ProbabilityMeasure Ω → ℝ := ![U,V]
  let combine : (Fin 2 → Applications.Estimator ((Fin n → Ω) × ℝ)) →
      Applications.Estimator ((Fin n → Ω) × ℝ) := fun E =>
    ⟨fun x => (E 0).val x - (E 1).val x, (E 0).property.sub (E 1).property⟩
  haveI : ∀ P : ProbabilityMeasure Ω, IsProbabilityMeasure (randomizedExperiment n P) := fun P => by
    change IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => (P : Measure Ω))).prod KernelSeedBridge.seedLaw)
    infer_instance
  have h := Applications.combination_minimax (randomizedExperiment n) T Ti C combine
    (fun _ _ => 0) 1 0 0 zero_le_one le_rfl
    (by
      intro E P hP x
      simp only [combine,Ti,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
        one_mul,add_zero,hrelation P hP]
      calc
        _ = |((E 0).val x - U P) - ((E 1).val x - V P)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _)
    (by intro P _; simp)
  simpa only [Ti,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    ENNReal.ofReal_one,ENNReal.ofReal_zero,one_mul,mul_zero,add_zero,
    ← minimaxRMSE_eq_squaredRisk] using h

end RoughRegime.Model
