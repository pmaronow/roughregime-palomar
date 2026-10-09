module

public import RoughRegime.RatioBracket


@[expose] public section
/-! Actual projected-estimator square transformation on a bounded interval. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem square_upperBracket {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (ν : ℝ) (hT : UpperBracket T C S ν)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ P ∈ C, |T P| ≤ M) :
    UpperBracket (fun P => (T P)^2) C S ν := by
  let Ti : Fin 1 → ProbabilityMeasure Ω → ℝ := fun _ => T
  let lo : Fin 1 → ℝ := fun _ => -M
  let hi : Fin 1 → ℝ := fun _ => M
  have hlohi : ∀ i, lo i ≤ hi i := fun _ => neg_le_self hM
  let Φ : ((i : Fin 1) → Icc (lo i) (hi i)) → ℝ := fun a => (a 0 : ℝ)^2
  have hL : 0 < 2*M+1 := by linarith
  have hLip : ∀ a b, |Φ a - Φ b| ≤ (2*M+1) * ∑ i, |(a i : ℝ)-b i| := by
    intro a b
    have hab : |(a 0 : ℝ)+(b 0 : ℝ)| ≤ 2*M :=
      by
      have h := (abs_add_le (a 0 : ℝ) (b 0 : ℝ)).trans
        (add_le_add (abs_le.mpr (a 0).property) (abs_le.mpr (b 0).property))
      simpa only [two_mul] using h
    simp only [Fin.sum_univ_one,Φ]
    calc
      _ = |((a 0 : ℝ)-(b 0 : ℝ))*((a 0 : ℝ)+(b 0 : ℝ))| := by congr 1; ring
      _ = |(a 0 : ℝ)-(b 0 : ℝ)| * |(a 0 : ℝ)+(b 0 : ℝ)| := abs_mul _ _
      _ ≤ |(a 0 : ℝ)-(b 0 : ℝ)| * (2*M) := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
      _ ≤ _ := by nlinarith only [abs_nonneg ((a 0 : ℝ)-(b 0 : ℝ))]
  apply finite_upperBracket_transfer _ Ti C (fun _ => S) (fun _ => ν) S ν (2*M+1)
    hT.1 hL (fun _ => rfl) (fun _ => rfl) (fun _ => le_rfl) (fun _ _ => le_rfl) (fun _ => hT)
  intro n
  exact lipschitz_minimax_combination n _ Ti C lo hi hlohi Φ (2*M+1) hL.le hLip
    (fun P hP _ => abs_le.mp (hb P hP))
    (by
      intro P hP
      have hp := congrArg Subtype.val (projIcc_of_mem (hlohi 0) (abs_le.mp (hb P hP)))
      change (T P)^2 = (projIcc (lo 0) (hi 0) (hlohi 0) (Ti 0 P) : ℝ)^2
      rw [hp])

end RoughRegime.Model
