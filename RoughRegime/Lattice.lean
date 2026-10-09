module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic


@[expose] public section
/-!
# Checked ingredients of the lattice construction

This file formalizes the pointwise sinc gate estimates and the finite
combinatorics used in Lemmas 13 and 14 of the supplied paper. It does **not**
claim that the lattice sampling identity, compact Fourier support, smoothness
bounds, or the complete prior lemma have been formalized.
-/

namespace RoughRegime.Lattice

open scoped BigOperators

noncomputable def gate (Q : ℕ) (scale x : ℝ) : ℝ :=
  Real.sinc (x / scale) ^ (2 * Q)

theorem gate_nonneg (Q : ℕ) (scale x : ℝ) : 0 ≤ gate Q scale x := by
  unfold gate
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem gate_le_one (Q : ℕ) (scale x : ℝ) : gate Q scale x ≤ 1 := by
  unfold gate
  rw [pow_mul, ← sq_abs]
  exact pow_le_one₀ (sq_nonneg _)
    (pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _))

theorem gate_zero (Q : ℕ) (scale : ℝ) : gate Q scale 0 = 1 := by
  simp [gate]

theorem sinc_mul_abs_le_one (x : ℝ) : |Real.sinc x| * |x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.sinc_of_ne_zero hx, abs_div, div_mul_cancel₀ _ (abs_ne_zero.mpr hx)]
  exact Real.abs_sin_le_one x

/-- The paper's gate power estimate, for every integer power through `2Q`.
The paper only needs the smaller range through `2Q - 2`. -/
theorem gate_weighted_power (Q r : ℕ) (hr : r ≤ 2 * Q)
    (scale x : ℝ) (hscale : 0 < scale) :
    gate Q scale x * |x| ^ r ≤ scale ^ r := by
  have hs : |Real.sinc (x / scale)| ≤ 1 := Real.abs_sinc_le_one _
  have hm : |Real.sinc (x / scale)| * |x| ≤ scale := by
    have h := sinc_mul_abs_le_one (x / scale)
    rw [abs_div, abs_of_pos hscale] at h
    have h' := (mul_le_mul_of_nonneg_right h hscale.le)
    simpa [div_eq_mul_inv, mul_assoc, hscale.ne'] using h'
  have heven : Real.sinc (x / scale) ^ (2 * Q) =
      |Real.sinc (x / scale)| ^ (2 * Q) := by
    rw [pow_mul, pow_mul, sq_abs]
  unfold gate
  rw [heven, ← Nat.sub_add_cancel hr, pow_add]
  calc
    |Real.sinc (x / scale)| ^ (2 * Q - r) *
        |Real.sinc (x / scale)| ^ r * |x| ^ r
        = |Real.sinc (x / scale)| ^ (2 * Q - r) *
            (|Real.sinc (x / scale)| * |x|) ^ r := by rw [mul_pow]; ring
    _ ≤ 1 * scale ^ r := mul_le_mul
      (pow_le_one₀ (abs_nonneg _) hs) (pow_le_pow_left₀ (by positivity) hm _)
      (by positivity) zero_le_one
    _ = scale ^ r := one_mul _

theorem one_sub_pow_le (Q : ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z ^ Q ≤ (Q : ℝ) * (1 - z) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hpow : 0 ≤ z ^ Q := pow_nonneg hz0 _
    have hprod : 0 ≤ (1 - z) * (1 - z ^ Q) :=
      mul_nonneg (by linarith) (by have := pow_le_one₀ (n := Q) hz0 hz1; linarith)
    nlinarith

theorem sinc_sq_lower_nonneg (x : ℝ) (hx : 0 ≤ x) :
    1 - x ^ 2 / 3 ≤ Real.sinc x ^ 2 := by
  by_cases hlarge : 3 ≤ x ^ 2
  · nlinarith [sq_nonneg (Real.sinc x)]
  by_cases hzero : x = 0
  · simp [hzero]
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  have hsin := Real.sin_ge_sub_cube hx
  have hprod : Real.sinc x * x = Real.sin x := by
    rw [Real.sinc_of_ne_zero hzero, div_mul_cancel₀ _ hzero]
  have hlow : 1 - x ^ 2 / 6 ≤ Real.sinc x := by
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith
  have hlow0 : 0 ≤ 1 - x ^ 2 / 6 := by nlinarith
  have hsquare := mul_self_le_mul_self hlow0 hlow
  nlinarith [sq_nonneg (x ^ 2)]

theorem sinc_sq_lower (x : ℝ) : 1 - x ^ 2 / 3 ≤ Real.sinc x ^ 2 := by
  by_cases hx : 0 ≤ x
  · exact sinc_sq_lower_nonneg x hx
  have h := sinc_sq_lower_nonneg (-x) (by linarith)
  simpa only [Real.sinc_neg, neg_sq] using h

/-- The pointwise deficit bound underlying the expectation estimate. -/
theorem gate_deficit (Q : ℕ) (scale x : ℝ) :
    1 - gate Q scale x ≤ (Q : ℝ) * (x / scale) ^ 2 / 3 := by
  have hz : Real.sinc (x / scale) ^ 2 ≤ 1 := by
    have h := pow_le_one₀ (n := 2) (abs_nonneg _) (Real.abs_sinc_le_one (x / scale))
    simpa only [sq_abs] using h
  have hp := one_sub_pow_le Q (Real.sinc (x / scale) ^ 2) (sq_nonneg _) hz
  have hl := sinc_sq_lower (x / scale)
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  unfold gate
  rw [pow_mul]
  nlinarith

/-- Gate expectations obey the second-moment bound for any probability law.
This establishes the analytic implication used in Lemma 13; identifying the
lattice expectation with the continuous integral still needs sampling. -/
theorem gate_expected_deficit (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] (Q : ℕ) (scale : ℝ) (hscale : 0 < scale)
    (hmoment : MeasureTheory.Integrable (fun x : ℝ => x ^ 2) μ) :
    1 - (∫ x, gate Q scale x ∂μ) ≤
      (Q : ℝ) * (∫ x : ℝ, x ^ 2 ∂μ) / (3 * scale ^ 2) := by
  have hgate : MeasureTheory.Integrable (gate Q scale) μ := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
      ?_ (MeasureTheory.ae_of_all _ fun x => ?_)
    · apply Continuous.aestronglyMeasurable
      unfold gate
      fun_prop
    · rw [Real.norm_eq_abs, abs_of_nonneg (gate_nonneg _ _ _)]
      exact gate_le_one _ _ _
  have hint := MeasureTheory.integral_mono
    ((MeasureTheory.integrable_const (1 : ℝ)).sub hgate)
    (hmoment.const_mul ((Q : ℝ) / (3 * scale ^ 2)))
    (fun x : ℝ => show 1 - gate Q scale x ≤ (Q : ℝ) / (3 * scale ^ 2) * x ^ 2 from by
      convert gate_deficit Q scale x using 1
      field_simp)
  change (∫ x, 1 - gate Q scale x ∂μ) ≤
    (∫ x : ℝ, (Q : ℝ) / (3 * scale ^ 2) * x ^ 2 ∂μ) at hint
  rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const (1 : ℝ)) hgate,
    MeasureTheory.integral_const_mul] at hint
  simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ,
    smul_eq_mul, one_mul] at hint
  convert hint using 1
  ring

/-- Product gates control simultaneous coefficient powers. The exponent is
allowed to be zero, so a subset of coefficients is covered by the same result. -/
theorem product_gate_weighted_power {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Q : ℕ) (r : ι → ℕ) (scale x : ι → ℝ)
    (hr : ∀ i ∈ s, r i ≤ 2 * Q) (hscale : ∀ i ∈ s, 0 < scale i) :
    (∏ i ∈ s, gate Q (scale i) (x i)) * (∏ i ∈ s, |x i| ^ r i)
      ≤ ∏ i ∈ s, scale i ^ r i := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun i hi => mul_nonneg (gate_nonneg _ _ _) (by positivity))
    (fun i hi => gate_weighted_power Q (r i) (hr i hi) (scale i) (x i) (hscale i hi))

/-- Finite product version of the union bound used to control the gate loss. -/
theorem one_sub_product_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    1 - ∏ i ∈ s, g i ≤ ∑ i ∈ s, (1 - g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have h0 := hg0 i (Finset.mem_insert_self _ _)
    have h1 := hg1 i (Finset.mem_insert_self _ _)
    have hs0 : ∀ j ∈ s, 0 ≤ g j := fun j hj => hg0 j (Finset.mem_insert_of_mem hj)
    have hs1 : ∀ j ∈ s, g j ≤ 1 := fun j hj => hg1 j (Finset.mem_insert_of_mem hj)
    have hb := ih hs0 hs1
    have hp : ∏ j ∈ s, g j ≤ 1 := Finset.prod_le_one₀ hs0 hs1
    rw [Finset.prod_insert his, Finset.sum_insert his]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hp)]

/-- Alias bands near a frequency multiple can reach only multiples 0 and 1
in the range used in the coefficient proof. -/
theorem alias_zero_or_one (M k K X : ℝ) (l : ℤ)
    (hM : 0 < M) (_hk0 : 0 ≤ k) (hk : 2 * k < M)
    (hK : 4 * K ≤ M) (hX0 : -k ≤ X) (hX1 : X ≤ M + k)
    (halias : |X - (l : ℝ) * M| ≤ K) : l = 0 ∨ l = 1 := by
  by_contra hn
  have hl : l ≤ -1 ∨ 2 ≤ l := by omega
  rcases abs_le.mp halias with ⟨ha0, ha1⟩
  rcases hl with hl | hl
  · have hlR : (l : ℝ) ≤ -1 := by exact_mod_cast hl
    have hp := mul_le_mul_of_nonneg_right hlR hM.le
    nlinarith
  · have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
    have hp := mul_le_mul_of_nonneg_right hlR hM.le
    nlinarith

noncomputable def mismatch {ι : Type*} (n p : Finset ι) (s : ι → ℝ) (digit : Bool) : ℝ :=
  if digit then (∑ i ∈ n, |s i - 1|) + ∑ i ∈ p, |s i|
  else (∑ i ∈ n, |s i|) + ∑ i ∈ p, |s i - 1|

theorem mismatch_false {ι : Type*} (n p : Finset ι) (s : ι → ℝ) (k : ℕ)
    (hp : p.card = k) (hn0 : ∀ i ∈ n, 0 ≤ s i) (hp1 : ∀ i ∈ p, s i ≤ 1) :
    mismatch n p s false = (∑ i ∈ n, s i) - (∑ i ∈ p, s i) + k := by
  have hn : (∑ i ∈ n, |s i|) = ∑ i ∈ n, s i :=
    Finset.sum_congr rfl (fun i hi => abs_of_nonneg (hn0 i hi))
  have hp' : (∑ i ∈ p, |s i - 1|) = ∑ i ∈ p, (1 - s i) :=
    Finset.sum_congr rfl (fun i hi => by rw [abs_of_nonpos (by linarith [hp1 i hi])]; ring)
  simp only [mismatch, Bool.false_eq_true, ↓reduceIte]
  rw [hn, hp', Finset.sum_sub_distrib]
  simp [hp]
  ring

theorem mismatch_true {ι : Type*} (n p : Finset ι) (s : ι → ℝ) (M k : ℕ)
    (hn : n.card = M + k) (hn1 : ∀ i ∈ n, s i ≤ 1) (hp0 : ∀ i ∈ p, 0 ≤ s i) :
    mismatch n p s true = M + k - ((∑ i ∈ n, s i) - ∑ i ∈ p, s i) := by
  have hn' : (∑ i ∈ n, |s i - 1|) = ∑ i ∈ n, (1 - s i) :=
    Finset.sum_congr rfl (fun i hi => by rw [abs_of_nonpos (by linarith [hn1 i hi])]; ring)
  have hp' : (∑ i ∈ p, |s i|) = ∑ i ∈ p, s i :=
    Finset.sum_congr rfl (fun i hi => abs_of_nonneg (hp0 i hi))
  simp only [mismatch, ↓reduceIte]
  rw [hn', hp', Finset.sum_sub_distrib]
  simp [hn]
  ring

/-- The precise digit mismatch conclusion used in `lat:mismatch`. Only the
Fourier alias condition is an input; the mismatch conclusion is proved here. -/
theorem alias_implies_mismatch {ι : Type*} (n p : Finset ι) (s : ι → ℝ)
    (M k : ℕ) (K : ℝ) (l : ℤ) (hM : 0 < M) (hk : 2 * (k : ℝ) < M)
    (hK : 4 * K ≤ M) (hn : n.card = M + k) (hp : p.card = k)
    (hn0 : ∀ i ∈ n, 0 ≤ s i) (hn1 : ∀ i ∈ n, s i ≤ 1)
    (hp0 : ∀ i ∈ p, 0 ≤ s i) (hp1 : ∀ i ∈ p, s i ≤ 1)
    (halias : |((∑ i ∈ n, s i) - ∑ i ∈ p, s i) - (l : ℝ) * M| ≤ K) :
    ∃ digit : Bool, mismatch n p s digit ≤ (k : ℝ) + K := by
  have hnlo : 0 ≤ ∑ i ∈ n, s i := Finset.sum_nonneg hn0
  have hplo : 0 ≤ ∑ i ∈ p, s i := Finset.sum_nonneg hp0
  have hnhi : (∑ i ∈ n, s i) ≤ (M : ℝ) + k := by
    calc
      (∑ i ∈ n, s i) ≤ ∑ i ∈ n, (1 : ℝ) := Finset.sum_le_sum hn1
      _ = (M : ℝ) + k := by simp [hn]
  have hphi : (∑ i ∈ p, s i) ≤ (k : ℝ) := by
    calc
      (∑ i ∈ p, s i) ≤ ∑ i ∈ p, (1 : ℝ) := Finset.sum_le_sum hp1
      _ = (k : ℝ) := by simp [hp]
  have hclass := alias_zero_or_one (M : ℝ) k K
    ((∑ i ∈ n, s i) - ∑ i ∈ p, s i) l
    (by exact_mod_cast hM) (Nat.cast_nonneg _) hk hK (by linarith) (by linarith) halias
  rcases hclass with rfl | rfl
  · refine ⟨false, ?_⟩
    rw [mismatch_false n p s k hp hn0 hp1]
    simp only [Int.cast_zero, zero_mul, sub_zero] at halias
    have := (abs_le.mp halias).2
    linarith
  · refine ⟨true, ?_⟩
    rw [mismatch_true n p s M k hn hn1 hp0]
    simp only [Int.cast_one, one_mul] at halias
    have := (abs_le.mp halias).1
    linarith
/-- A wrong hard digit incurs the paper's soft mismatch cost. -/
theorem soft_digit_mismatch (s : ℝ) (hard target : Bool)
    (hzero : hard = false → s ≤ 1 / 2)
    (hone : hard = true → 1 / 2 ≤ s) (hne : hard ≠ target) :
    (1 / 2 : ℝ) ≤ |s - if target then 1 else 0| := by
  cases hard <;> cases target <;> simp_all
  · have hs := hzero
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hs := hone
    rw [abs_of_nonneg (by linarith)]
    exact hs

/-- Exact factorization for averaging a product over independent uniform bits.
This is the finite combinatorial identity behind the digit integration step. -/
theorem sum_bit_penalties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (target : ι → Bool) :
    (∑ e : ι → Bool, ∏ i, if e i = target i then (1 : ℝ) else a i)
      = ∏ i, (1 + a i) := by
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) => if b = target i then (1 : ℝ) else a i)]
  apply Finset.prod_congr rfl
  intro i hi
  cases target i <;> simp [add_comm]

/-- Division by the exact number of bit strings gives the uniform average. -/
theorem average_bit_penalties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (target : ι → Bool) :
    (∑ e : ι → Bool, ∏ i, if e i = target i then (1 : ℝ) else a i) /
        (2 : ℝ) ^ Fintype.card ι
      = ∏ i, ((1 + a i) / 2) := by
  rw [sum_bit_penalties, Finset.prod_div_distrib]
  simp

/-- A product of `j` Fourier modes from `{-1, 0, 1}` has frequency at most `j`. -/
theorem mode_sum_bound {ι : Type*} (s : Finset ι) (mode : ι → ℤ)
    (hmode : ∀ i ∈ s, |mode i| ≤ 1) : |∑ i ∈ s, mode i| ≤ s.card := by
  calc
    |∑ i ∈ s, mode i| ≤ ∑ i ∈ s, |mode i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (1 : ℤ) := Finset.sum_le_sum hmode
    _ = s.card := by simp

/-- Therefore the likelihood coefficient cannot contain frequency `M` before
degree `M`. This is the combinatorial part of `Gamma_j = 0` for `j < M`. -/
theorem mode_sum_ne_frequency {ι : Type*} (s : Finset ι) (mode : ι → ℤ)
    (M : ℕ) (hmode : ∀ i ∈ s, |mode i| ≤ 1) (hdegree : s.card < M) :
    (∑ i ∈ s, mode i) ≠ (M : ℤ) ∧ (∑ i ∈ s, mode i) ≠ -(M : ℤ) := by
  have hb := mode_sum_bound s mode hmode
  have hc : (s.card : ℤ) < M := by exact_mod_cast hdegree
  constructor <;> intro h <;> rw [h] at hb <;> simp at hb <;> omega

/-- Lattice phases retain the separation cosine exactly. -/
theorem lattice_coherence (M : ℝ) (hM : M ≠ 0) (z : ℤ) :
    Real.cos (M * ((2 * Real.pi / M) * z)) = 1 := by
  convert Real.cos_int_mul_two_pi z using 1
  congr 1
  field_simp

theorem sum_lattice_coefficients {ι : Type*} (s : Finset ι) (M : ℝ)
    (z : ι → ℤ) (digit : ι → Bool) :
    (∑ i ∈ s, (2 * Real.pi / M) * (z i : ℝ) * if digit i then 1 else 0)
      = (2 * Real.pi / M) * ((∑ i ∈ s, if digit i then z i else 0 : ℤ) : ℝ) := by
  rw [Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases digit i <;> simp

theorem finite_lattice_coherence {ι : Type*} (s : Finset ι) (M : ℝ) (hM : M ≠ 0)
    (z : ι → ℤ) (digit : ι → Bool) :
    Real.cos (M * ∑ i ∈ s, (2 * Real.pi / M) * (z i : ℝ) *
      if digit i then 1 else 0) = 1 := by
  rw [sum_lattice_coefficients]
  exact lattice_coherence M hM _

/-- Coherence outside a small collar preserves the weighted separation
integral even when the cosine is arbitrary on the collar. -/
theorem weighted_coherence_lower {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (collar : Set X) (hcollar : MeasurableSet collar) (w c : X → ℝ)
    (hw : MeasureTheory.Integrable w μ) (hc : MeasureTheory.AEStronglyMeasurable c μ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) (hc1 : ∀ x, |c x| ≤ 1)
    (hcoherence : ∀ x ∉ collar, c x = 1) :
    (∫ x, w x ∂μ) - 2 * μ.real collar ≤ ∫ x, w x * c x ∂μ := by
  have hind : MeasureTheory.Integrable (collar.indicator (fun _ : X => (1 : ℝ))) μ :=
    (MeasureTheory.integrable_const (1 : ℝ)).indicator hcollar
  have hprod : MeasureTheory.Integrable (fun x => w x * c x) μ :=
    hw.mul_bdd hc (MeasureTheory.ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hc1 x)
  have hp : ∀ x, w x - 2 * collar.indicator (fun _ : X => (1 : ℝ)) x ≤ w x * c x := by
    intro x
    by_cases hx : x ∈ collar
    · simp only [Set.indicator_of_mem hx]
      have hlo := (abs_le.mp (hc1 x)).1
      nlinarith [hw0 x, hw1 x, mul_nonneg (hw0 x) (show 0 ≤ c x + 1 by linarith)]
    · simp only [Set.indicator_of_notMem hx, hcoherence x hx, mul_zero, sub_zero, mul_one]
      exact le_rfl
  have hi := MeasureTheory.integral_mono (hw.sub (hind.const_mul 2)) hprod hp
  change (∫ x, w x - 2 * collar.indicator (fun _ : X => (1 : ℝ)) x ∂μ) ≤ _ at hi
  rw [MeasureTheory.integral_sub hw (hind.const_mul 2), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_indicator_const 1 hcollar] at hi
  simpa only [smul_eq_mul, mul_one] using hi

theorem weighted_coherence_half {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (collar : Set X) (hcollar : MeasurableSet collar) (w c : X → ℝ)
    (hw : MeasureTheory.Integrable w μ) (hc : MeasureTheory.AEStronglyMeasurable c μ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) (hc1 : ∀ x, |c x| ≤ 1)
    (hcoherence : ∀ x ∉ collar, c x = 1)
    (hsmall : μ.real collar ≤ (∫ x, w x ∂μ) / 4) :
    (∫ x, w x ∂μ) / 2 ≤ ∫ x, w x * c x ∂μ := by
  have h := weighted_coherence_lower μ collar hcollar w c hw hc hw0 hw1 hc1 hcoherence
  linarith

/-- The elementary variance argument used for the gate's second moment. -/
theorem expected_square_ge_square {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (g : X → ℝ) (hg : MeasureTheory.Integrable g μ)
    (hg2 : MeasureTheory.Integrable (fun x => g x ^ 2) μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  let m : ℝ := ∫ x, g x ∂μ
  have hvar : 0 ≤ ∫ x, (g x - m) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have heq : (∫ x, (g x - m) ^ 2 ∂μ) = (∫ x, g x ^ 2 ∂μ) - m ^ 2 := by
    calc
      (∫ x, (g x - m) ^ 2 ∂μ) =
          ∫ x, (g x ^ 2 - (2 * m) * g x) + m ^ 2 ∂μ := by
        apply MeasureTheory.integral_congr_ae
        exact MeasureTheory.ae_of_all _ (fun x => by ring)
      _ = (∫ x, g x ^ 2 ∂μ) - (2 * m) * (∫ x, g x ∂μ) + m ^ 2 := by
        have hmul : MeasureTheory.Integrable (fun x => (2 * m) * g x) μ := hg.const_mul _
        have hsub : MeasureTheory.Integrable (fun x => g x ^ 2 - (2 * m) * g x) μ :=
          hg2.sub hmul
        rw [MeasureTheory.integral_add hsub
          (MeasureTheory.integrable_const (m ^ 2)),
          MeasureTheory.integral_sub hg2 hmul,
          MeasureTheory.integral_const_mul]
        simp
      _ = (∫ x, g x ^ 2 ∂μ) - m ^ 2 := by dsimp [m]; ring
  rw [heq] at hvar
  change m ^ 2 ≤ _
  linarith

theorem expected_square_ge_nine_sixteenths {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (g : X → ℝ) (hg : MeasureTheory.Integrable g μ)
    (hg2 : MeasureTheory.Integrable (fun x => g x ^ 2) μ)
    (hmean : (3 / 4 : ℝ) ≤ ∫ x, g x ∂μ) :
    (9 / 16 : ℝ) ≤ ∫ x, g x ^ 2 ∂μ := by
  have h := expected_square_ge_square μ g hg hg2
  nlinarith

/-- A uniform lower bound survives multiplication by a dependent random gate;
the argument does not require independence of the phase and the gate. -/
theorem dependent_gate_separation {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (S H : X → ℝ) (I : ℝ) (hI : 0 ≤ I)
    (hsquare : MeasureTheory.Integrable (fun x => S x ^ 2) μ)
    (hprod : MeasureTheory.Integrable (fun x => S x ^ 2 * H x) μ)
    (hH : ∀ x, I / 2 ≤ H x) (hES : (9 / 16 : ℝ) ≤ ∫ x, S x ^ 2 ∂μ) :
    9 * I / 32 ≤ ∫ x, S x ^ 2 * H x ∂μ := by
  have h := MeasureTheory.integral_mono (hsquare.const_mul (I / 2)) hprod
    (fun x => show I / 2 * S x ^ 2 ≤ S x ^ 2 * H x from by
      nlinarith [mul_nonneg (sq_nonneg (S x)) (show 0 ≤ H x - I / 2 by linarith [hH x])])
  rw [MeasureTheory.integral_const_mul] at h
  nlinarith [mul_nonneg hI (show 0 ≤ (∫ x, S x ^ 2 ∂μ) - 9 / 16 by linarith)]

end RoughRegime.Lattice
