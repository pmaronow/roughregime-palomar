module

public import RoughRegime.UpperSubcriticalGeometry


@[expose] public section
/-! Variance sums for the actual subcritical minimum degree rule. -/
noncomputable section
namespace RoughRegime.UpperSubcritical
open RoughRegime.UpperDegreeRules RoughRegime.UpperParametric RoughRegime.UpperTuning

def globalDegreeConstant (θ τ A : ℝ) (ν : ℕ) : ℝ := A * levelCountConstant θ τ + ν + 3

def budget (n θ τ : ℝ) : ℝ :=
  (1 - 2 * θ) * Real.log n - 2 * RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)

def chosenOrder (n θ τ A Cv : ℝ) (ν : ℕ) (j : Fin (terminal n θ τ + 1)) : ℕ :=
  selectedDegree A (levelDistance (terminal n θ τ) j) (budget n θ τ)
    (levelLog (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n j) ν

def chosenDegree (n θ τ A Cv : ℝ) (ν : ℕ) (j : Fin (terminal n θ τ + 1)) : ℕ :=
  chosenOrder n θ τ A Cv ν j + ν + 2

lemma chosenDegree_positive (n θ τ A Cv : ℝ) (ν : ℕ) (j : Fin (terminal n θ τ + 1)) :
    0 < chosenDegree n θ τ A Cv ν j := by unfold chosenDegree; omega

lemma chosenDegree_global_bound (n θ τ A Cv : ℝ) (ν : ℕ) (hL : 1 ≤ Real.log n)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hA : 0 ≤ A)
    (j : Fin (terminal n θ τ + 1)) :
    (chosenDegree n θ τ A Cv ν j : ℝ) ≤ globalDegreeConstant θ τ A ν * Real.log n := by
  have hb := selectedDegree_global_bound (terminal n θ τ) A (budget n θ τ)
    (levelLog (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n) ν hA j
  have hc := mul_le_mul_of_nonneg_left (terminal_level_count_bound n θ τ hL hθ hθhalf hτ) hA
  have hν : (ν : ℝ) + 3 ≤ ((ν : ℝ) + 3) * Real.log n := by nlinarith [Nat.cast_nonneg (α := ℝ) ν]
  unfold globalDegreeConstant
  unfold chosenDegree chosenOrder
  have hcomb : A * ((terminal n θ τ : ℝ) + 1) + ν + 3 ≤ globalDegreeConstant θ τ A ν * Real.log n := by
    unfold globalDegreeConstant
    convert add_le_add hc hν using 1 <;> ring
  exact hb.trans hcomb

lemma parentCells_one_le (J : ℕ) (j : Fin (J + 1)) : 1 ≤ (parentCells J j : ℝ) := by
  unfold parentCells
  split_ifs
  · simp
  · simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact one_le_pow₀ (by norm_num)

lemma parentCells_smoothness_le_one (J : ℕ) (q : ℝ) (hq : 0 ≤ q) (j : Fin (J + 1)) :
    (parentCells J j : ℝ) ^ (-2 * q) ≤ 1 := by
  have h := Real.rpow_le_rpow_of_exponent_le (parentCells_one_le J j) (show -2 * q ≤ (0 : ℝ) by nlinarith)
  simpa only [Real.rpow_zero] using h

/-- Every level variance obeys the genuine coarse geometric bound derived from
Lemma 8, before applying either resolution rule. -/
lemma chosen_variance_geometric (n θ τ A Cv q : ℝ) (ν : ℕ) (hn : 0 < n) (hCv : 0 ≤ Cv) (hq : 0 ≤ q)
    (v : Fin (terminal n θ τ + 1) → ℝ)
    (hv : ∀ j, v j ≤ Cv * (parentCells (terminal n θ τ) j : ℝ) ^ (-2 * q) / n +
      ∑ k ∈ Finset.range (chosenDegree n θ τ A Cv ν j - 1),
        RoughRegime.LiftVariance.varianceTerm Cv (parentCells (terminal n θ τ) j) n (k + 2))
    (j : Fin (terminal n θ τ + 1)) :
    v j ≤ Cv * chosenDegree n θ τ A Cv ν j / n *
      max 1 (Cv * chosenDegree n θ τ A Cv ν j * parentCells (terminal n θ τ) j / n) ^ (chosenDegree n θ τ A Cv ν j - 1) := by
  have h := variance_levels_of_variance_bound (v j) Cv (parentCells (terminal n θ τ) j) n
    ((parentCells (terminal n θ τ) j : ℝ) ^ (-2 * q)) hCv (parentCells_positive _ j).le hn
    (chosenDegree n θ τ A Cv ν j) (hv j)
  exact h.trans (geometric_variance_bound Cv n _ _ hCv hn (parentCells_smoothness_le_one _ q hq j)
    (by positivity) _ (chosenDegree_positive n θ τ A Cv ν j))

/-- On a low level, the actual chosen variance has the source `O(L/n)` bound. -/
theorem chosen_variance_low_bound (n θ τ A Cv q : ℝ) (ν : ℕ)
    (hn : 0 < n) (hL : 1 ≤ Real.log n) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (hA : 0 ≤ A) (hCv : 0 ≤ Cv) (hq : 0 ≤ q)
    (hlarge : Cv * globalDegreeConstant θ τ A ν ≤ Real.log n)
    (v : Fin (terminal n θ τ + 1) → ℝ)
    (hv : ∀ j, v j ≤ Cv * (parentCells (terminal n θ τ) j : ℝ) ^ (-2 * q) / n +
      ∑ k ∈ Finset.range (chosenDegree n θ τ A Cv ν j - 1),
        RoughRegime.LiftVariance.varianceTerm Cv (parentCells (terminal n θ τ) j) n (k + 2))
    (j : Fin (terminal n θ τ + 1))
    (hjlow : (parentCells (terminal n θ τ) j : ℝ) ≤ n / (Real.log n) ^ 2) :
    v j ≤ Cv * globalDegreeConstant θ τ A ν * Real.log n / n := by
  have hLp : 0 < Real.log n := zero_lt_one.trans_le hL
  have hdegree := chosenDegree_global_bound n θ τ A Cv ν hL hθ hθhalf hτ hA j
  have hC : 0 ≤ globalDegreeConstant θ τ A ν := by unfold globalDegreeConstant levelCountConstant; have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ; positivity
  have hy : Cv * chosenDegree n θ τ A Cv ν j * parentCells (terminal n θ τ) j / n ≤ 1 := by
    calc
      _ ≤ Cv * (globalDegreeConstant θ τ A ν * Real.log n) * (n / (Real.log n) ^ 2) / n := by gcongr
      _ = Cv * globalDegreeConstant θ τ A ν / Real.log n := by field_simp
      _ ≤ 1 := (div_le_one hLp).mpr hlarge
  have hgeo := chosen_variance_geometric n θ τ A Cv q ν hn hCv hq v hv j
  rw [max_eq_left hy, one_pow, mul_one] at hgeo
  have hm := mul_le_mul_of_nonneg_left hdegree hCv
  exact hgeo.trans ((div_le_div_of_nonneg_right hm hn.le).trans_eq (by ring))

/-- On a high level, the actual cap rule bounds the variance by `Cv Rbar e^B/n`. -/
theorem chosen_variance_high_bound (n θ τ A Cv q : ℝ) (ν : ℕ)
    (hn : 0 < n) (hL : 1 ≤ Real.log n) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (hA : 0 ≤ A) (hCv : 0 < Cv) (hq : 0 ≤ q)
    (hnlarge : (Real.log n) ^ 2 ≤ n) (hB : 0 ≤ budget n θ τ)
    (hfloor : (ν : ℝ) + 3 ≤ budget n θ τ / windowEndpoint (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n)
    (v : Fin (terminal n θ τ + 1) → ℝ)
    (hv : ∀ j, v j ≤ Cv * (parentCells (terminal n θ τ) j : ℝ) ^ (-2 * q) / n +
      ∑ k ∈ Finset.range (chosenDegree n θ τ A Cv ν j - 1),
        RoughRegime.LiftVariance.varianceTerm Cv (parentCells (terminal n θ τ) j) n (k + 2))
    (j : Fin (terminal n θ τ + 1))
    (hjhigh : n / (Real.log n) ^ 2 < (parentCells (terminal n θ τ) j : ℝ)) :
    v j ≤ Cv * highDegreeEnvelope n θ τ A ν / n * Real.exp (budget n θ τ) := by
  let J := terminal n θ τ
  let Rbar := highDegreeEnvelope n θ τ A ν
  let x := levelLog J Cv Rbar n j
  let y := Cv * chosenDegree n θ τ A Cv ν j * parentCells J j / n
  have hRp : 0 < Rbar := by
    have hr := highDegreeEnvelope_positive n θ τ A ν hL hθ hθhalf hτ hA
    have := Nat.cast_nonneg (α := ℝ) ν
    dsimp [Rbar]
    linarith
  have hdegree : (chosenDegree n θ τ A Cv ν j : ℝ) ≤ Rbar :=
    selectedDegree_high_bound n θ τ A (budget n θ τ) ν hA hn hL hnlarge
      (levelLog J Cv Rbar n) j hjhigh
  have hy : y ≤ Real.exp x := by
    rw [exp_levelLog J Cv Rbar n hCv hRp hn j]
    dsimp [y]
    gcongr
  have hpower : max 1 y ^ (chosenDegree n θ τ A Cv ν j - 1) ≤ Real.exp (budget n θ τ) := by
    by_cases hx : 0 < x
    · have hxe : x ≤ windowEndpoint J Cv Rbar n := levelLog_le_endpoint J Cv Rbar n hn j
      have hfloorx : (ν : ℝ) + 3 ≤ budget n θ τ / x :=
        hfloor.trans (div_le_div_of_nonneg_left hB hx hxe)
      apply capped_variance_power_bound (budget n θ τ) x y ν _ hx (by dsimp [y]; positivity) hy hB
      · exact selectedDegree_cap_bound A (levelDistance J j) (budget n θ τ) x ν hx
      · exact hfloorx
    · have hy1 : y ≤ 1 := hy.trans (Real.exp_le_one_iff.mpr (le_of_not_gt hx))
      rw [max_eq_left hy1, one_pow]
      exact Real.one_le_exp hB
  have hgeo := chosen_variance_geometric n θ τ A Cv q ν hn hCv.le hq v hv j
  change v j ≤ Cv * chosenDegree n θ τ A Cv ν j / n * max 1 y ^ (chosenDegree n θ τ A Cv ν j - 1) at hgeo
  exact hgeo.trans (mul_le_mul (by gcongr) hpower (by positivity) (by positivity))

lemma sqrt_rpow_nonnegative (x s : ℝ) (hx : 0 ≤ x) : Real.sqrt (x ^ s) = x ^ (s / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

lemma sqrt_exp (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

lemma budget_exp_div_sample (n θ τ : ℝ) (hn : 0 < n) :
    Real.exp (budget n θ τ) / n = n ^ (-2 * θ) *
      Real.exp (-2 * RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) := by
  rw [Real.rpow_def_of_pos hn, ← Real.exp_add, ← Real.exp_log hn, ← Real.exp_sub]
  unfold budget
  simp only [Real.log_exp]
  congr 1
  ring

/-- The true selected-level standard deviations sum to two explicit terms.
The high-level term here uses the valid coarse count `J+1=O(L)`; since `ν≥2`
it still fits the logarithmic power in the claimed upper rate. -/
theorem chosen_standard_deviation_sum_bound (n θ τ A Cv q : ℝ) (ν : ℕ)
    (hn : 0 < n) (hL : 1 ≤ Real.log n) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (hA : 0 ≤ A) (hCv : 0 < Cv) (hq : 0 ≤ q)
    (hnlarge : (Real.log n) ^ 2 ≤ n) (hB : 0 ≤ budget n θ τ)
    (hlarge : Cv * globalDegreeConstant θ τ A ν ≤ Real.log n)
    (hfloor : (ν : ℝ) + 3 ≤ budget n θ τ / windowEndpoint (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n)
    (v : Fin (terminal n θ τ + 1) → ℝ)
    (hv : ∀ j, v j ≤ Cv * (parentCells (terminal n θ τ) j : ℝ) ^ (-2 * q) / n +
      ∑ k ∈ Finset.range (chosenDegree n θ τ A Cv ν j - 1),
        RoughRegime.LiftVariance.varianceTerm Cv (parentCells (terminal n θ τ) j) n (k + 2)) :
    (∑ j : Fin (terminal n θ τ + 1), Real.sqrt (v j)) ≤
      (levelCountConstant θ τ * Real.sqrt (Cv * globalDegreeConstant θ τ A ν)) *
        (Real.log n) ^ (3 / 2 : ℝ) / Real.sqrt n +
      (levelCountConstant θ τ * Real.sqrt (Cv * highDegreeConstant θ τ A ν)) *
        n ^ (-θ) * (Real.log n) ^ (5 / 4 : ℝ) *
          Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) := by
  classical
  let L := Real.log n
  let CJ := levelCountConstant θ τ
  let Cg := globalDegreeConstant θ τ A ν
  let CR := highDegreeConstant θ τ A ν
  let low := Cv * Cg * L / n
  let high := Cv * CR * Real.sqrt L / n * Real.exp (budget n θ τ)
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCJ : 0 ≤ CJ := by unfold CJ levelCountConstant; positivity
  have hCg : 0 ≤ Cg := by unfold Cg globalDegreeConstant levelCountConstant; positivity
  have hCR : 0 ≤ CR := by unfold CR highDegreeConstant; positivity
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlo : 0 ≤ low := by dsimp [low]; positivity
  have hhi : 0 ≤ high := by dsimp [high]; positivity
  have hpoint (j : Fin (terminal n θ τ + 1)) : Real.sqrt (v j) ≤ Real.sqrt low + Real.sqrt high := by
    by_cases hj : (parentCells (terminal n θ τ) j : ℝ) ≤ n / (Real.log n) ^ 2
    · exact (Real.sqrt_le_sqrt (chosen_variance_low_bound n θ τ A Cv q ν hn hL hθ hθhalf hτ hA hCv.le hq hlarge v hv j hj)).trans
        (le_add_of_nonneg_right (Real.sqrt_nonneg high))
    · have hh := chosen_variance_high_bound n θ τ A Cv q ν hn hL hθ hθhalf hτ hA hCv hq hnlarge hB hfloor v hv j (lt_of_not_ge hj)
      have henv := highDegreeEnvelope_bound n θ τ A ν hL hθ hθhalf hτ hA
      have hm := mul_le_mul_of_nonneg_left henv hCv.le
      have ht := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hm hn.le) (Real.exp_pos (budget n θ τ)).le
      have hb : v j ≤ high := by
        convert hh.trans ht using 1; ring
      exact (Real.sqrt_le_sqrt hb).trans (le_add_of_nonneg_left (Real.sqrt_nonneg low))
  have hsum : (∑ j : Fin (terminal n θ τ + 1), Real.sqrt (v j)) ≤ CJ * L * (Real.sqrt low + Real.sqrt high) := by
    calc
      _ ≤ ∑ _j : Fin (terminal n θ τ + 1), (Real.sqrt low + Real.sqrt high) := Finset.sum_le_sum (fun j _ => hpoint j)
      _ = ((terminal n θ τ : ℝ) + 1) * (Real.sqrt low + Real.sqrt high) := by simp; ring
      _ ≤ CJ * L * (Real.sqrt low + Real.sqrt high) := mul_le_mul_of_nonneg_right
        (terminal_level_count_bound n θ τ hL hθ hθhalf hτ) (by positivity)
  have hlRoot : Real.sqrt low = Real.sqrt (Cv * Cg) * L ^ (1 / 2 : ℝ) / Real.sqrt n := by
    dsimp [low]
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow L]
  have hhRoot : Real.sqrt high = Real.sqrt (Cv * CR) * L ^ (1 / 4 : ℝ) * n ^ (-θ) *
      Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt L) := by
    have hid : high = (Cv * CR) * Real.sqrt L * n ^ (-2 * θ) *
        Real.exp (-2 * RoughRegime.Rates.kappa θ τ * Real.sqrt L) := by
      dsimp [high, L]
      rw [show Cv * CR * Real.sqrt (Real.log n) / n * Real.exp (budget n θ τ) =
        Cv * CR * Real.sqrt (Real.log n) * (Real.exp (budget n θ τ) / n) by ring, budget_exp_div_sample n θ τ hn]
      ring
    have hquarter : Real.sqrt (Real.sqrt L) = L ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow L, sqrt_rpow_nonnegative L (1 / 2) hLp.le]
      congr 1
      norm_num
    rw [hid, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      sqrt_rpow_nonnegative n (-2 * θ) hn.le, sqrt_exp, hquarter]
    have hnexp : -2 * θ / 2 = -θ := by ring
    have heexp : -2 * RoughRegime.Rates.kappa θ τ * Real.sqrt L / 2 = -RoughRegime.Rates.kappa θ τ * Real.sqrt L := by ring
    rw [hnexp, heexp]
  rw [hlRoot, hhRoot] at hsum
  have hLhalf : L * L ^ (1 / 2 : ℝ) = L ^ (3 / 2 : ℝ) := by
    convert (Real.rpow_add hLp (1 : ℝ) (1 / 2)).symm using 1 <;> norm_num
  have hLquarter : L * L ^ (1 / 4 : ℝ) = L ^ (5 / 4 : ℝ) := by
    convert (Real.rpow_add hLp (1 : ℝ) (1 / 4)).symm using 1 <;> norm_num
  refine hsum.trans_eq ?_
  calc
    CJ * L * (Real.sqrt (Cv * Cg) * L ^ (1 / 2 : ℝ) / Real.sqrt n +
      Real.sqrt (Cv * CR) * L ^ (1 / 4 : ℝ) * n ^ (-θ) * Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt L)) =
      (CJ * Real.sqrt (Cv * Cg)) * (L * L ^ (1 / 2 : ℝ)) / Real.sqrt n +
      (CJ * Real.sqrt (Cv * CR)) * n ^ (-θ) * (L * L ^ (1 / 4 : ℝ)) *
        Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt L) := by ring
    _ = _ := by rw [hLhalf, hLquarter]

end RoughRegime.UpperSubcritical
