module

public import RoughRegime.RiskBridge


@[expose] public section
/-! Exact bracket and hardness predicates (Definitions 2 and 17), and the
lower-bracket consequence in Lemma 18, on the actual randomized iid experiment.
The predicates do not assume the main theorem or any application bracket. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace RoughRegime.Model

/-- The domain of the bracket definition: a positive index and nondegenerate
positive interval. The upper-bracket exponent is separately required to be ≥2. -/
structure BracketParameters where
  theta : ℝ
  lo : ℝ
  hi : ℝ
  htheta : 0 < theta
  hlo : 0 < lo
  hinterval : lo < hi

/-- Equation (15), including the parametric regime. -/
def lowerBracketScale (S : BracketParameters) (n : ℕ) : ℝ :=
  if S.theta < 1 / 2 then
    Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi) * Real.log n
  else (n : ℝ) ^ (-(1 / 2 : ℝ))

/-- Equation (15), including the parametric regime. -/
def upperBracketScale (S : BracketParameters) (ν : ℝ) (n : ℕ) : ℝ :=
  if S.theta < 1 / 2 then
    Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi) *
      (Real.log n) ^ (ν / 2 + 1 / 4)
  else (n : ℝ) ^ (-(1 / 2 : ℝ))

/-- Definition 2's lower bracket, including its probability clause. -/
def LowerBracket {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
    ENNReal.ofReal (c * lowerBracketScale S n) ≤ minimaxRMSE n T C ∧
    (S.theta < 1 / 2 →
      (1 / 4 : ℝ≥0∞) ≤ minimaxTail n T C (2 * c * lowerBracketScale S n))

/-- Definition 2's upper bracket. -/
def UpperBracket {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (ν : ℝ) : Prop :=
  2 ≤ ν ∧ ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
    minimaxRMSE n T C ≤ ENNReal.ofReal (c * upperBracketScale S ν n)

/-- Definition 2's simultaneous bracket. -/
def Bracket {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (ν : ℝ) : Prop :=
  LowerBracket T C S ∧ UpperBracket T C S ν

/-- Definition 17. Every estimator in the infimum has an independent uniform
seed and n independent observations, as in `Model.minimaxTail`. -/
def HardAtScale {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω → ℝ) (Cn : ℕ → Set (ProbabilityMeasure Ω))
    (tn : ℕ → ℝ) : Prop :=
  (∀ n, 0 < tn n) ∧ (3 / 8 : ℝ≥0∞) ≤
    Filter.liminf (fun n => minimaxTail n T (Cn n) (tn n)) atTop

/-- Full principal implication of Lemma 18 in the source hardness notation. -/
theorem HardAtScale.eventually_risk {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω → ℝ} {Cn : ℕ → Set (ProbabilityMeasure Ω)}
    {tn : ℕ → ℝ} (hhard : HardAtScale T Cn tn)
    (C : Set (ProbabilityMeasure Ω)) (hC : ∀ᶠ n in atTop, Cn n ⊆ C) :
    ∀ᶠ n in atTop,
      (1 / 4 : ℝ≥0∞) ≤ minimaxTail n T C (tn n) ∧
      ENNReal.ofReal (tn n / 2) ≤ minimaxRMSE n T C :=
  hardness_to_risk T Cn C tn (fun n => (hhard.1 n).le) hC hhard.2

/-- Lemma 18's 'in particular' clause. The scale identity may hold eventually:
changing finitely many initial scale values does not affect hardness or brackets. -/
theorem HardAtScale.lowerBracket {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω → ℝ} {Cn : ℕ → Set (ProbabilityMeasure Ω)}
    {tn : ℕ → ℝ} (hhard : HardAtScale T Cn tn)
    (C : Set (ProbabilityMeasure Ω)) (hC : ∀ᶠ n in atTop, Cn n ⊆ C)
    (S : BracketParameters) (_hsub : S.theta < 1 / 2)
    (c1 : ℝ) (hc1 : 0 < c1)
    (hscale : ∀ᶠ n in atTop, tn n = c1 * lowerBracketScale S n) :
    LowerBracket T C S := by
  have he := hhard.eventually_risk C hC
  have hp : ∀ᶠ n in atTop,
      ENNReal.ofReal ((c1 / 2) * lowerBracketScale S n) ≤ minimaxRMSE n T C ∧
      (S.theta < 1 / 2 → (1 / 4 : ℝ≥0∞) ≤
        minimaxTail n T C (2 * (c1 / 2) * lowerBracketScale S n)) := by
    filter_upwards [he, hscale] with n hn hs
    rw [hs] at hn
    have hr : c1 * lowerBracketScale S n / 2 = (c1 / 2) * lowerBracketScale S n := by ring
    have ht : 2 * (c1 / 2) * lowerBracketScale S n = c1 * lowerBracketScale S n := by ring
    exact ⟨by simpa only [hr] using hn.2, fun _ => by simpa only [ht] using hn.1⟩
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 hp
  refine ⟨c1 / 2, by positivity, max 3 n0, le_max_left _ _, ?_⟩
  intro n hn
  exact hn0 n (le_trans (le_max_right _ _) hn)

end RoughRegime.Model
