module

public import RoughRegime.PoissonComparison
public import RoughRegime.ProductTesting


@[expose] public section
/-! Uniform constants in the actual marked-Poisson comparison. The constant
depends on the field and score bounds, the lower density bound, and a fixed
upper bound on the Poisson rate; it is independent of the frequency and amplitudes. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

 def comparisonConstant (C S c R : ℝ) : ℝ :=
   let k₁ := 9 * S ^ 2 * c⁻¹
   let k₂ := 81 * S ^ 2 * C ^ 2 * c⁻¹
   2 + k₁ + k₂ + Real.exp (R * |c⁻¹ - 1|) * (k₁ ^ 2 + k₂ ^ 4 * Real.exp (k₂ * R))

 theorem comparisonConstant_bounds (C S c R : ℝ) (hc : 0 < c) :
    1 ≤ comparisonConstant C S c R ∧
    9 * S ^ 2 * c⁻¹ ≤ comparisonConstant C S c R ∧
    81 * S ^ 2 * C ^ 2 * c⁻¹ ≤ comparisonConstant C S c R ∧
    Real.exp (R * |c⁻¹ - 1|) * (9 * S ^ 2 * c⁻¹) ^ 2 ≤ comparisonConstant C S c R ∧
    Real.exp (R * |c⁻¹ - 1|) * (81 * S ^ 2 * C ^ 2 * c⁻¹) ^ 4 *
      Real.exp ((81 * S ^ 2 * C ^ 2 * c⁻¹) * R) ≤ comparisonConstant C S c R := by
  unfold comparisonConstant
  have hk1 : 0 ≤ 9 * S ^ 2 * c⁻¹ := by positivity
  have hk2 : 0 ≤ 81 * S ^ 2 * C ^ 2 * c⁻¹ := by positivity
  have hp1 : 0 ≤ Real.exp (R * |c⁻¹ - 1|) * (9 * S ^ 2 * c⁻¹) ^ 2 := by positivity
  have hp2 : 0 ≤ Real.exp (R * |c⁻¹ - 1|) * (81 * S ^ 2 * C ^ 2 * c⁻¹) ^ 4 *
      Real.exp ((81 * S ^ 2 * C ^ 2 * c⁻¹) * R) := by positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

variable {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
variable (ν : Measure H) (μ : Measure X) (κ : Measure Z)
variable [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] [IsProbabilityMeasure κ]

/-- Lemma11's full leading-series plus fourth-order remainder for a genuine
single-pair affine-phase experiment, with one constant independent of M and Au,Av. -/
 theorem AffinePhaseField.poisson_hellinger_uniform (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C S : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hS : 0 ≤ S) (hb : F.Bounded C)
    (s : Fin 3 → Z → ℝ) (hs : ∀ l, Measurable (s l)) (hbs : ∀ l z, |s l z| ≤ S)
    (hzero : ∀ q, (∫ y, F.markedFactor Au Av s q y ∂μ.prod κ) = 0)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ q y, c ≤ 1 + F.markedFactor Au Av s q y)
    (M : ℕ) (rate : ℝ≥0) (R : ℝ) (hRate : (rate : ℝ) ≤ R) :
    let K := comparisonConstant C S c R
    GeneralTesting.hellingerSquared
      (F.poissonLaw ν μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs hzero c hc hlow M rate true)
      (F.poissonLaw ν μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs hzero c hc hlow M rate false) ≤
      K * (rate : ℝ) ^ 2 * (∑' j, if M ≤ j then
        (K * (rate : ℝ)) ^ j / j.factorial * F.gammaNorm ν μ Au Av M j else 0) +
      K * (rate : ℝ) ^ 4 * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 *
        ((K * (rate : ℝ)) ^ M / M.factorial) := by
  let rrate := (rate : ℝ)
  let k₁ := 9 * S ^ 2 * c⁻¹
  let k₂ := 81 * S ^ 2 * C ^ 2 * c⁻¹
  let K := comparisonConstant C S c R
  let P := Real.exp (R * |c⁻¹ - 1|)
  let D := Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2
  have hrrate : 0 ≤ rrate := rate.coe_nonneg
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := by positivity
  have hD : 0 ≤ D := by positivity
  have hKb := comparisonConstant_bounds C S c R hc
  have hK : 0 ≤ K := le_trans zero_le_one hKb.1
  have hP : 0 ≤ P := le_of_lt (Real.exp_pos _)
  have hp : Real.exp (rrate * (c⁻¹ - 1)) ≤ P := by
    apply Real.exp_le_exp.mpr
    calc
      rrate * (c⁻¹ - 1) ≤ rrate * |c⁻¹ - 1| := mul_le_mul_of_nonneg_left (le_abs_self _) hrrate
      _ ≤ R * |c⁻¹ - 1| := mul_le_mul_of_nonneg_right hRate (abs_nonneg _)
  have hkp1 : k₁ * rrate ≤ K * rrate := mul_le_mul_of_nonneg_right hKb.2.1 hrrate
  have hkp2 : k₂ * rrate ≤ K * rrate := mul_le_mul_of_nonneg_right hKb.2.2.1 hrrate
  let T₁ := ∑' j : ℕ, if M ≤ j then (k₁ * rrate) ^ j / j.factorial * F.gammaNorm ν μ Au Av M j else 0
  let T := ∑' j : ℕ, if M ≤ j then (K * rrate) ^ j / j.factorial * F.gammaNorm ν μ Au Av M j else 0
  have hT₁ : 0 ≤ T₁ := tsum_nonneg fun j => by
    split_ifs
    · exact mul_nonneg (by positivity) (F.gammaNorm_nonneg ν μ Au Av M j)
    · positivity
  have hT : 0 ≤ T := tsum_nonneg fun j => by
    split_ifs
    · exact mul_nonneg (by positivity) (F.gammaNorm_nonneg ν μ Au Av M j)
    · positivity
  have hseries1 := PoissonSeriesBounds.summable_cutoff _
    (F.gammaSeries_summable ν μ Au Av C hAu hAv hC hb M (k₁ * rrate) (by positivity)) M
  have hseries := PoissonSeriesBounds.summable_cutoff _
    (F.gammaSeries_summable ν μ Au Av C hAu hAv hC hb M (K * rrate) (by positivity)) M
  have hTT : T₁ ≤ T := hseries1.tsum_le_tsum (fun j => by
    split_ifs
    · exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hkp1 j) (by positivity))
        (F.gammaNorm_nonneg ν μ Au Av M j)
    · exact le_rfl) hseries
  have hcoef1 : (1 / 4) * Real.exp (rrate * (c⁻¹ - 1)) * k₁ ^ 2 ≤ K := by
    have hi := mul_le_mul_of_nonneg_right hp (sq_nonneg k₁)
    have hj : (1 / 4) * (Real.exp (rrate * (c⁻¹ - 1)) * k₁ ^ 2) ≤ P * k₁ ^ 2 := by
      nlinarith [Real.exp_pos (rrate * (c⁻¹ - 1)), sq_nonneg k₁]
    have hj' : (1 / 4) * Real.exp (rrate * (c⁻¹ - 1)) * k₁ ^ 2 ≤ P * k₁ ^ 2 := by
      simpa only [mul_assoc] using hj
    exact hj'.trans hKb.2.2.2.1
  have hexp : Real.exp (k₂ * rrate) ≤ Real.exp (k₂ * R) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hRate hk₂)
  have hcoef2 : Real.exp (rrate * (c⁻¹ - 1)) * k₂ ^ 4 * Real.exp (k₂ * rrate) ≤ K := by
    have hi := mul_le_mul (mul_le_mul_of_nonneg_right hp (pow_nonneg hk₂ 4)) hexp
      (le_of_lt (Real.exp_pos _)) (by positivity : 0 ≤ P * k₂ ^ 4)
    exact hi.trans hKb.2.2.2.2
  have hhead : (1 / 4) * Real.exp (rrate * (c⁻¹ - 1)) * ((k₁ * rrate) ^ 2 * T₁) ≤ K * rrate ^ 2 * T := by
    have hi := mul_le_mul (mul_le_mul_of_nonneg_right hcoef1 (sq_nonneg rrate)) hTT hT₁
      (mul_nonneg hK (sq_nonneg rrate))
    convert hi using 1
    ring
  have htail : (1 / 4) * Real.exp (rrate * (c⁻¹ - 1)) *
      (4 * D * (k₂ * rrate) ^ 4 * ((k₂ * rrate) ^ M / M.factorial) * Real.exp (k₂ * rrate)) ≤
      K * rrate ^ 4 * D * ((K * rrate) ^ M / M.factorial) := by
    have hm := div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hkp2 M)
      (by positivity : (0 : ℝ) ≤ M.factorial)
    have hi := mul_le_mul
      (mul_le_mul_of_nonneg_right hcoef2 (mul_nonneg (pow_nonneg hrrate 4) hD)) hm (by positivity)
      (by positivity : 0 ≤ K * (rrate ^ 4 * D))
    convert hi using 1 <;> ring
  have hh := F.poisson_hellinger_bound ν μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb
    s hs hbs hzero c hc hlow M rate
  have hz1 : 9 * S ^ 2 * ((rate : ℝ) * c⁻¹) = k₁ * rrate := by dsimp [k₁, rrate]; ring
  have hz2 : 81 * S ^ 2 * C ^ 2 * ((rate : ℝ) * c⁻¹) = k₂ * rrate := by dsimp [k₂, rrate]; ring
  rw [hz1, hz2, mul_add] at hh
  exact hh.trans (by simpa only [T₁, T, D, K, rrate, mul_assoc] using add_le_add hhead htail)

end RoughRegime.PoissonMeasure
