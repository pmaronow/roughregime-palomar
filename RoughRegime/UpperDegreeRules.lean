module

public import RoughRegime.UpperTuning
public import RoughRegime.Window
public import RoughRegime.Rates


@[expose] public section
/-! Explicit numerical degree rules used in the upper-bound construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.UpperDegreeRules

def approximationWeight (K θ τ : ℝ) (ν m : ℕ) : ℝ :=
  K ^ (-θ) * ((m + 1 : ℕ) : ℝ) ^ ν * Real.exp (-τ * m)

def biasDegree (A : ℝ) (l : ℕ) : ℕ := Nat.ceil (A * l)

def cappedDegree (B x : ℝ) (ν : ℕ) : ℕ := Nat.floor (B / x) - ν - 2

/-- The floor rule stays positive under exactly the paper's large-sample condition. -/
lemma cappedDegree_properties (B x : ℝ) (ν : ℕ) (_hx : 0 < x)
    (hlarge : (ν : ℝ) + 3 ≤ B / x) :
    1 ≤ cappedDegree B x ν ∧
      (cappedDegree B x ν : ℝ) + ν + 2 ≤ B / x ∧
      B / x - ν - 3 < (cappedDegree B x ν : ℝ) := by
  have hfloor : ν + 3 ≤ Nat.floor (B / x) := Nat.le_floor (by exact_mod_cast hlarge)
  have hcast : (cappedDegree B x ν : ℝ) = (Nat.floor (B / x) : ℝ) - ν - 2 := by
    unfold cappedDegree
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  have hpos : 1 ≤ cappedDegree B x ν := by unfold cappedDegree; omega
  have hB : 0 ≤ B / x := by linarith [show (0 : ℝ) ≤ (ν : ℝ) from Nat.cast_nonneg ν]
  constructor
  · exact hpos
  constructor
  · rw [hcast]
    linarith [Nat.floor_le hB]
  · rw [hcast]
    linarith [Nat.lt_floor_add_one (B / x)]

lemma biasDegree_bounds (A : ℝ) (l : ℕ) (hA : 0 ≤ A) :
    A * l ≤ (biasDegree A l : ℝ) ∧ (biasDegree A l : ℝ) + 1 ≤ A * l + 2 := by
  unfold biasDegree
  exact ⟨Nat.le_ceil _, by linarith [Nat.ceil_lt_add_one (mul_nonneg hA (Nat.cast_nonneg l))]⟩

/-- The bias degree gives a geometrically decreasing error away from the terminal level. -/
theorem biasDegree_weight_bound (K Kstar θ τ A : ℝ) (ν l : ℕ)
    (hKstar : 0 < Kstar) (hθ : 0 ≤ θ) (hτ : 0 ≤ τ) (hA : 0 ≤ A)
    (hK : Kstar * Real.exp (-(l : ℝ) * Real.log 2) ≤ K)
    (hdecay : θ * Real.log 2 + 1 ≤ τ * A) :
    approximationWeight K θ τ ν (biasDegree A l) ≤
      Kstar ^ (-θ) * (A * l + 2) ^ ν * Real.exp (-(l : ℝ)) := by
  have hbase : 0 < Kstar * Real.exp (-(l : ℝ) * Real.log 2) := by positivity
  have hKpos : 0 < K := hbase.trans_le hK
  have hresolution : K ^ (-θ) ≤ Kstar ^ (-θ) * Real.exp (θ * l * Real.log 2) := by
    have h := Real.rpow_le_rpow_of_nonpos hbase hK (neg_nonpos.mpr hθ)
    rw [Real.mul_rpow hKstar.le (Real.exp_nonneg _), ← Real.exp_mul] at h
    have he : (-(l : ℝ) * Real.log 2) * (-θ) = θ * l * Real.log 2 := by ring
    rw [he] at h
    exact h
  have hd := biasDegree_bounds A l hA
  have hpoly : (((biasDegree A l + 1 : ℕ) : ℝ) ^ ν) ≤ (A * l + 2) ^ ν := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ ν
    simpa only [Nat.cast_add, Nat.cast_one] using hd.2
  have hexp : Real.exp (-τ * biasDegree A l) ≤ Real.exp (-τ * A * l) := by
    apply Real.exp_monotone
    nlinarith [mul_le_mul_of_nonneg_left hd.1 hτ]
  have hlast : Real.exp (θ * l * Real.log 2) * Real.exp (-τ * A * l) ≤ Real.exp (-(l : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_monotone
    nlinarith [mul_le_mul_of_nonneg_right hdecay (Nat.cast_nonneg l)]
  unfold approximationWeight
  calc
    _ ≤ (Kstar ^ (-θ) * Real.exp (θ * l * Real.log 2)) * (A * l + 2) ^ ν *
        Real.exp (-τ * A * l) := by
      exact mul_le_mul (mul_le_mul hresolution hpoly (by positivity) (by positivity))
        hexp (by positivity) (by positivity)
    _ = Kstar ^ (-θ) * (A * l + 2) ^ ν *
        (Real.exp (θ * l * Real.log 2) * Real.exp (-τ * A * l)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlast (by positivity)

def biasRuleConstant (A : ℝ) (ν : ℕ) : ℝ :=
  (A + 2) ^ ν * ∑' l : ℕ, (l : ℝ) ^ ν * Real.exp (-(l : ℝ))

/-- The full finite-level bias-rule sum, with an explicit finite constant. -/
theorem biasDegree_sum_bound {ι : Type*} [Fintype ι] (K : ι → ℝ) (l : ι → ℕ)
    (hl : ∀ j, 1 ≤ l j) (hinj : Function.Injective l)
    (Kstar θ τ A : ℝ) (ν : ℕ) (hKstar : 0 < Kstar)
    (hθ : 0 ≤ θ) (hτ : 0 ≤ τ) (hA : 0 ≤ A)
    (hK : ∀ j, Kstar * Real.exp (-(l j : ℝ) * Real.log 2) ≤ K j)
    (hdecay : θ * Real.log 2 + 1 ≤ τ * A) :
    (∑ j, approximationWeight (K j) θ τ ν (biasDegree A (l j))) ≤
      biasRuleConstant A ν * Kstar ^ (-θ) := by
  classical
  have hs : Summable (fun l : ℕ => (l : ℝ) ^ ν * Real.exp (-(l : ℝ))) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul ν (by norm_num : (0 : ℝ) < 1)
  have hsum : (∑ j, (l j : ℝ) ^ ν * Real.exp (-(l j : ℝ))) ≤
      ∑' l : ℕ, (l : ℝ) ^ ν * Real.exp (-(l : ℝ)) := by
    have himage := Finset.sum_image (s := Finset.univ) (g := l)
      (f := fun t : ℕ => (t : ℝ) ^ ν * Real.exp (-(t : ℝ)))
      (fun i _ j _ hij => hinj hij)
    rw [← himage]
    exact hs.sum_le_tsum _ (fun i _ => by positivity)
  calc
    _ ≤ ∑ j, Kstar ^ (-θ) * (A + 2) ^ ν * ((l j : ℝ) ^ ν * Real.exp (-(l j : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hpoly : (A * l j + 2) ^ ν ≤ ((A + 2) * l j) ^ ν := by
        apply pow_le_pow_left₀ (by positivity) _ ν
        have hlj : (1 : ℝ) ≤ l j := by exact_mod_cast hl j
        nlinarith
      have h := biasDegree_weight_bound (K j) Kstar θ τ A ν (l j) hKstar hθ hτ hA (hK j) hdecay
      calc
        _ ≤ Kstar ^ (-θ) * (((A + 2) * l j) ^ ν) * Real.exp (-(l j : ℝ)) :=
          h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by positivity)) (by positivity))
        _ = _ := by rw [mul_pow]; ring
    _ = Kstar ^ (-θ) * (A + 2) ^ ν * ∑ j, ((l j : ℝ) ^ ν * Real.exp (-(l j : ℝ))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Kstar ^ (-θ) * (A + 2) ^ ν * ∑' l : ℕ, (l : ℝ) ^ ν * Real.exp (-(l : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by unfold biasRuleConstant; ring

def levelDistance (J : ℕ) (j : Fin (J + 1)) : ℕ := J - j.val + 1

def parentCells (J : ℕ) (j : Fin (J + 1)) : ℕ := if j.val = 0 then 1 else 2 ^ (j.val - 1)

lemma levelDistance_positive (J : ℕ) (j : Fin (J + 1)) : 1 ≤ levelDistance J j := by
  unfold levelDistance
  omega

lemma levelDistance_injective (J : ℕ) : Function.Injective (levelDistance J) := by
  intro i j hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  unfold levelDistance at hij
  omega

/-- Exact relation between the terminal resolution, the level distance, and
parent-cell count, including the repeated base level `K₀=K₁=1`. -/
lemma parentCells_terminal_lower (J : ℕ) (j : Fin (J + 1)) :
    (2 : ℝ) ^ J * Real.exp (-(levelDistance J j : ℝ) * Real.log 2) ≤ parentCells J j := by
  have hexp : Real.exp (-(levelDistance J j : ℝ) * Real.log 2) = ((2 : ℝ) ^ levelDistance J j)⁻¹ := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hexp]
  unfold parentCells levelDistance
  split_ifs with hj0
  · simp only [hj0, Nat.sub_zero, Nat.cast_one, pow_succ]
    have hpow : (2 : ℝ) ^ J ≠ 0 := by positivity
    field_simp
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) J]
  · have hJ : j.val - 1 + (J - j.val + 1) = J := by have := j.isLt; omega
    have hpow : (2 : ℝ) ^ J = (2 : ℝ) ^ (j.val - 1) * (2 : ℝ) ^ (J - j.val + 1) := by
      rw [← pow_add, hJ]
    rw [hpow]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    have hnonzero : (2 : ℝ) ^ (J - j.val + 1) ≠ 0 := by positivity
    rw [mul_assoc, mul_inv_cancel₀ hnonzero, mul_one]

/-- `eq:bias-rule-sum`, for the exact dyadic cell counts and actual ceiling rule. -/
theorem dyadic_biasDegree_sum_bound (J : ℕ) (θ τ A : ℝ) (ν : ℕ)
    (hθ : 0 ≤ θ) (hτ : 0 ≤ τ) (hA : 0 ≤ A)
    (hdecay : θ * Real.log 2 + 1 ≤ τ * A) :
    (∑ j : Fin (J + 1), approximationWeight (parentCells J j) θ τ ν (biasDegree A (levelDistance J j))) ≤
      biasRuleConstant A ν * ((2 : ℝ) ^ J) ^ (-θ) := by
  exact biasDegree_sum_bound (fun j => parentCells J j) (levelDistance J)
    (levelDistance_positive J) (levelDistance_injective J) _ θ τ A ν (by positivity)
    hθ hτ hA (parentCells_terminal_lower J) hdecay

/-- The variance floor rule bounds the high-level geometric power by `exp B`. -/
theorem capped_variance_power_bound (B x y : ℝ) (ν R : ℕ) (hx : 0 < x)
    (_hy : 0 ≤ y) (hyx : y ≤ Real.exp x) (_hB : 0 ≤ B)
    (hR : R ≤ cappedDegree B x ν + ν + 2)
    (hlarge : (ν : ℝ) + 3 ≤ B / x) :
    max 1 y ^ (R - 1) ≤ Real.exp B := by
  have hc := (cappedDegree_properties B x ν hx hlarge).2.1
  have hRcast : (R : ℝ) ≤ B / x := by
    have hr : (R : ℝ) ≤ (cappedDegree B x ν : ℝ) + ν + 2 := by exact_mod_cast hR
    exact hr.trans hc
  have hRx : (R : ℝ) * x ≤ B := (le_div_iff₀ hx).mp hRcast
  have hmax : max 1 y ≤ Real.exp x := max_le (Real.one_le_exp hx.le) hyx
  calc
    _ ≤ Real.exp x ^ (R - 1) := pow_le_pow_left₀ (by positivity) hmax _
    _ = Real.exp (((R - 1 : ℕ) : ℝ) * x) := (Real.exp_nat_mul x _).symm
    _ ≤ Real.exp B := by
      apply Real.exp_monotone
      have hsub : ((R - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast Nat.sub_le R 1
      exact (mul_le_mul_of_nonneg_right hsub hx.le).trans hRx

lemma sqrt_difference_le (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    Real.sqrt a - Real.sqrt b ≤ (a - b) / Real.sqrt a := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have hsle : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hba
  apply (le_div_iff₀ hsa).mpr
  nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt hb,
    mul_nonneg hsb (sub_nonneg.mpr hsle)]

/-- The exact bounded loss in the window exponent used below the threshold. -/
theorem window_phase_correction (θ τ Δ L : ℝ)
    (hθ : 0 < θ) (hτ : 0 < τ) (hΔ : 0 < Δ) (hL : 0 < L)
    (hB : 0 ≤ Δ * L - 2 * (2 * Real.sqrt (θ * Δ * τ)) * Real.sqrt L) :
    (2 * Real.sqrt (θ * Δ * τ)) * Real.sqrt L -
        2 * Real.sqrt (θ * τ * (Δ * L - 2 * (2 * Real.sqrt (θ * Δ * τ)) * Real.sqrt L)) ≤
      8 * θ * τ := by
  let κ : ℝ := 2 * Real.sqrt (θ * Δ * τ)
  let B : ℝ := Δ * L - 2 * κ * Real.sqrt L
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hb : 0 ≤ B := hB
  have hBL : B ≤ Δ * L := by dsimp [B]; nlinarith [Real.sqrt_nonneg L]
  have hdiff := sqrt_difference_le (Δ * L) B (mul_pos hΔ hL) hb hBL
  have hrootκ : κ = 2 * Real.sqrt (θ * τ) * Real.sqrt Δ := by
    dsimp [κ]
    have halg : θ * Δ * τ = (θ * τ) * Δ := by ring
    rw [halg, Real.sqrt_mul (mul_pos hθ hτ).le]
    ring
  have hrootL : Real.sqrt (Δ * L) = Real.sqrt Δ * Real.sqrt L := Real.sqrt_mul hΔ.le L
  have hphase : κ * Real.sqrt L - 2 * Real.sqrt (θ * τ * B) =
      2 * Real.sqrt (θ * τ) * (Real.sqrt (Δ * L) - Real.sqrt B) := by
    rw [Real.sqrt_mul (mul_pos hθ hτ).le, hrootκ, hrootL]
    ring
  change κ * Real.sqrt L - 2 * Real.sqrt (θ * τ * B) ≤ _
  rw [hphase]
  calc
    _ ≤ 2 * Real.sqrt (θ * τ) * ((Δ * L - B) / Real.sqrt (Δ * L)) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = 8 * θ * τ := by
      dsimp [B]
      rw [hrootκ, hrootL]
      have hD : Real.sqrt Δ ≠ 0 := (Real.sqrt_pos.mpr hΔ).ne'
      have hSL : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
      field_simp
      have hs := Real.sq_sqrt (mul_pos hθ hτ).le
      linear_combination 8 * Real.sqrt Δ * Real.sqrt L * hs

/-- Exponential version of the subcritical window correction. -/
theorem window_exponential_correction (θ τ Δ L : ℝ)
    (hθ : 0 < θ) (hτ : 0 < τ) (hΔ : 0 < Δ) (hL : 0 < L)
    (hB : 0 ≤ Δ * L - 2 * (2 * Real.sqrt (θ * Δ * τ)) * Real.sqrt L) :
    Real.exp (-2 * Real.sqrt (θ * τ * (Δ * L - 2 * (2 * Real.sqrt (θ * Δ * τ)) * Real.sqrt L))) ≤
      Real.exp (8 * θ * τ) * Real.exp (-(2 * Real.sqrt (θ * Δ * τ)) * Real.sqrt L) := by
  rw [← Real.exp_add]
  apply Real.exp_monotone
  linarith [window_phase_correction θ τ Δ L hθ hτ hΔ hL hB]

/-- At the floor degree, the approximation error is the window summand times
explicit powers of the degree envelope and normalization. -/
theorem cappedDegree_weight_bound (n Q Rbar θ τ B x : ℝ) (ν : ℕ)
    (hn : 0 < n) (hQ : 0 < Q) (hx : 0 < x) (hτ : 0 ≤ τ)
    (hlarge : (ν : ℝ) + 3 ≤ B / x)
    (hdegree : (cappedDegree B x ν : ℝ) + 1 ≤ Rbar) :
    approximationWeight (n * Real.exp x / Q) θ τ ν (cappedDegree B x ν) ≤
      n ^ (-θ) * Q ^ θ * Rbar ^ ν * Real.exp (τ * (ν + 3)) *
        Real.exp (-θ * x - τ * B / x) := by
  have hpoly : (((cappedDegree B x ν + 1 : ℕ) : ℝ) ^ ν) ≤ Rbar ^ ν := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ ν
    simpa only [Nat.cast_add, Nat.cast_one] using hdegree
  have hc := (cappedDegree_properties B x ν hx hlarge).2.2
  have hexp : Real.exp (-τ * cappedDegree B x ν) ≤
      Real.exp (τ * (ν + 3) - τ * B / x) := by
    apply Real.exp_monotone
    have hh := mul_le_mul_of_nonneg_left hc.le hτ
    rw [mul_sub, mul_sub, ← mul_div_assoc] at hh
    linarith
  have hresolution : (n * Real.exp x / Q) ^ (-θ) = n ^ (-θ) * Q ^ θ * Real.exp (-θ * x) := by
    rw [Real.div_rpow (mul_pos hn (Real.exp_pos x)).le hQ.le,
      Real.mul_rpow hn.le (Real.exp_nonneg x), ← Real.exp_mul, Real.rpow_neg hQ.le, div_inv_eq_mul]
    rw [show x * (-θ) = -θ * x by ring]
    ring
  have hRbar : 0 ≤ Rbar := by linarith [show (0 : ℝ) ≤ (cappedDegree B x ν : ℝ) from Nat.cast_nonneg _]
  unfold approximationWeight
  rw [hresolution]
  calc
    _ ≤ (n ^ (-θ) * Q ^ θ * Real.exp (-θ * x)) * Rbar ^ ν *
        Real.exp (τ * (ν + 3) - τ * B / x) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity)) hexp (by positivity) (by positivity)
    _ = _ := by rw [Real.exp_sub, Real.exp_sub]; ring

/-- Exact finite-window bias bound for the actual variance floor rule. -/
theorem cappedDegree_window_sum_bound (S : Finset ℝ) (n Q Rbar θ τ B Xbar : ℝ) (ν : ℕ)
    (hn : 0 < n) (hQ : 0 < Q) (hRbar : 0 ≤ Rbar)
    (hθ : 0 < θ) (hτ : 0 < τ) (hB : 0 < B) (hXbar : 0 < Xbar)
    (hS : ∀ x ∈ S, 0 < x ∧ x ≤ Xbar)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Real.log 2 ≤ |x - y|)
    (hlarge : ∀ x ∈ S, (ν : ℝ) + 3 ≤ B / x)
    (hdegree : ∀ x ∈ S, (cappedDegree B x ν : ℝ) + 1 ≤ Rbar) :
    (∑ x ∈ S, approximationWeight (n * Real.exp x / Q) θ τ ν (cappedDegree B x ν)) ≤
      n ^ (-θ) * Q ^ θ * Rbar ^ ν * Real.exp (τ * (ν + 3)) *
        (2 + Real.sqrt (Real.pi * Xbar / θ) / Real.log 2) * Real.exp (-2 * Real.sqrt (θ * τ * B)) := by
  let A := n ^ (-θ) * Q ^ θ * Rbar ^ ν * Real.exp (τ * (ν + 3))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ x ∈ S, A * Real.exp (-θ * x - τ * B / x) := by
      apply Finset.sum_le_sum
      intro x hx
      exact cappedDegree_weight_bound n Q Rbar θ τ B x ν hn hQ (hS x hx).1 hτ.le
        (hlarge x hx) (hdegree x hx)
    _ = A * ∑ x ∈ S, Real.exp (-θ * x - τ * B / x) := (Finset.mul_sum _ _ _).symm
    _ ≤ A * ((2 + Real.sqrt (Real.pi * Xbar / θ) / Real.log 2) * Real.exp (-2 * Real.sqrt (θ * τ * B))) :=
      mul_le_mul_of_nonneg_left
        (RoughRegime.Window.window_sum S θ τ B Xbar hθ hτ hB hXbar hS hsep) hA
    _ = _ := by dsimp [A]; ring

def selectedDegree (A : ℝ) (l : ℕ) (B x : ℝ) (ν : ℕ) : ℕ :=
  min (biasDegree A l) (if 0 < x then cappedDegree B x ν else biasDegree A l)

def cappedLevels (J : ℕ) (A B : ℝ) (x : Fin (J + 1) → ℝ) (ν : ℕ) : Finset (Fin (J + 1)) := by
  classical
  exact Finset.univ.filter (fun j => 0 < x j ∧ cappedDegree B (x j) ν < biasDegree A (levelDistance J j))

lemma approximationWeight_nonneg (K θ τ : ℝ) (ν m : ℕ) (hK : 0 ≤ K) :
    0 ≤ approximationWeight K θ τ ν m := by unfold approximationWeight; positivity

lemma selectedDegree_degree_bound (A : ℝ) (l : ℕ) (B x : ℝ) (ν : ℕ) (hA : 0 ≤ A) :
    (selectedDegree A l B x ν : ℝ) + ν + 2 ≤ A * l + ν + 3 := by
  have hm : (selectedDegree A l B x ν : ℝ) ≤ (biasDegree A l : ℝ) := by
    exact_mod_cast (Nat.min_le_left (biasDegree A l) (if 0 < x then cappedDegree B x ν else biasDegree A l))
  linarith [(biasDegree_bounds A l hA).2]

lemma selectedDegree_cap_bound (A : ℝ) (l : ℕ) (B x : ℝ) (ν : ℕ) (hx : 0 < x) :
    selectedDegree A l B x ν + ν + 2 ≤ cappedDegree B x ν + ν + 2 := by
  unfold selectedDegree
  rw [ite_eq_left hx]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.min_le_right _ _) ν) 2

/-- `eq:bias-two-rules` for the exact two-rule selected degrees. -/
theorem selectedDegree_weight_sum_bound (J : ℕ) (θ τ A B : ℝ)
    (x : Fin (J + 1) → ℝ) (ν : ℕ) (hθ : 0 ≤ θ) (hτ : 0 ≤ τ) (hA : 0 ≤ A)
    (hdecay : θ * Real.log 2 + 1 ≤ τ * A) :
    (∑ j : Fin (J + 1), approximationWeight (parentCells J j) θ τ ν
      (selectedDegree A (levelDistance J j) B (x j) ν)) ≤
      biasRuleConstant A ν * ((2 : ℝ) ^ J) ^ (-θ) +
        ∑ j ∈ cappedLevels J A B x ν,
          approximationWeight (parentCells J j) θ τ ν (cappedDegree B (x j) ν) := by
  classical
  have hnonneg (j : Fin (J + 1)) (m : ℕ) : 0 ≤ approximationWeight (parentCells J j) θ τ ν m :=
    approximationWeight_nonneg _ _ _ _ _ (Nat.cast_nonneg _)
  have hpoint (j : Fin (J + 1)) :
      approximationWeight (parentCells J j) θ τ ν (selectedDegree A (levelDistance J j) B (x j) ν) ≤
        approximationWeight (parentCells J j) θ τ ν (biasDegree A (levelDistance J j)) +
          if j ∈ cappedLevels J A B x ν then
            approximationWeight (parentCells J j) θ τ ν (cappedDegree B (x j) ν) else 0 := by
    by_cases hx : 0 < x j
    · by_cases hc : cappedDegree B (x j) ν < biasDegree A (levelDistance J j)
      · have hm : j ∈ cappedLevels J A B x ν := by simp [cappedLevels, hx, hc]
        simp only [selectedDegree, ite_eq_left hx, min_eq_right hc.le, ite_eq_left hm]
        exact le_add_of_nonneg_left (hnonneg j _)
      · have hm : j ∉ cappedLevels J A B x ν := by simp [cappedLevels, hc]
        simp only [selectedDegree, ite_eq_left hx, min_eq_left (le_of_not_gt hc), ite_eq_right hm, add_zero]
        exact le_rfl
    · have hm : j ∉ cappedLevels J A B x ν := by simp [cappedLevels, hx]
      simp only [selectedDegree, ite_eq_right hx, min_self, ite_eq_right hm, add_zero]
      exact le_rfl
  calc
    _ ≤ ∑ j : Fin (J + 1),
        (approximationWeight (parentCells J j) θ τ ν (biasDegree A (levelDistance J j)) +
          if j ∈ cappedLevels J A B x ν then
            approximationWeight (parentCells J j) θ τ ν (cappedDegree B (x j) ν) else 0) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = (∑ j : Fin (J + 1), approximationWeight (parentCells J j) θ τ ν (biasDegree A (levelDistance J j))) +
        ∑ j ∈ cappedLevels J A B x ν, approximationWeight (parentCells J j) θ τ ν (cappedDegree B (x j) ν) := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_ite_mem_eq _ _
    _ ≤ _ := add_le_add (dyadic_biasDegree_sum_bound J θ τ A ν hθ hτ hA hdecay) le_rfl

end RoughRegime.UpperDegreeRules
