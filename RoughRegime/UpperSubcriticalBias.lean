module

public import RoughRegime.UpperSubcriticalVariance


@[expose] public section
/-! The true finite capped-level window sum for the chosen subcritical degrees. -/
noncomputable section
namespace RoughRegime.UpperSubcritical
open RoughRegime.UpperDegreeRules RoughRegime.UpperParametric RoughRegime.UpperRates

def rate (n θ τ : ℝ) (ν : ℕ) : ℝ :=
  n ^ (-θ) * (Real.log n) ^ (θ / 2 + (ν : ℝ) / 2 + 1 / 4) *
    Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n))

def capConstant (θ τ A Cv : ℝ) (ν : ℕ) : ℝ :=
  cappedBiasConstant Cv (highDegreeConstant θ τ A ν)
    (windowConstant θ τ Cv (highDegreeConstant θ τ A ν)) θ τ ν

/-- Exact finite sum over the actual capped dyadic levels; separation, degree
envelopes, and window membership are proved from the chosen rules. -/
theorem chosen_capped_bias_bound (n θ τ A Cv : ℝ) (ν : ℕ)
    (hn : 0 < n) (hL : 1 ≤ Real.log n) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (hA : 0 ≤ A) (hCv : 1 ≤ Cv) (hnlarge : (Real.log n) ^ 2 ≤ n)
    (hRsmall : Cv * highDegreeEnvelope n θ τ A ν ≤ (Real.log n) ^ 2)
    (hB : 0 < budget n θ τ)
    (hfloor : (ν : ℝ) + 3 ≤ budget n θ τ / windowEndpoint (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n) :
    (∑ j ∈ cappedLevels (terminal n θ τ) A (budget n θ τ)
      (levelLog (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n) ν,
      approximationWeight (parentCells (terminal n θ τ) j) θ τ ν
        (cappedDegree (budget n θ τ) (levelLog (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n j) ν)) ≤
      capConstant θ τ A Cv ν * rate n θ τ ν := by
  classical
  let J := terminal n θ τ
  let Rbar := highDegreeEnvelope n θ τ A ν
  let x := levelLog J Cv Rbar n
  let Γ := cappedLevels J A (budget n θ τ) x ν
  let S := Γ.image x
  let CR := highDegreeConstant θ τ A ν
  let CX := windowConstant θ τ Cv CR
  let Xbar := windowEndpoint J Cv Rbar n
  have hCvp : 0 < Cv := zero_lt_one.trans_le hCv
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hRp : 0 < Rbar := by
    have hr := highDegreeEnvelope_positive n θ τ A ν hL hθ hθhalf hτ hA
    have := Nat.cast_nonneg (α := ℝ) ν
    dsimp [Rbar]
    linarith
  have hCRp : 0 < CR := by unfold CR highDegreeConstant; positivity
  have hCX : 0 ≤ CX := by unfold CX windowConstant; positivity
  have hXp : 0 < Xbar := windowEndpoint_positive n θ τ A Cv ν hL hθ hθhalf hτ hA hCv
  have hcap (j : Fin (J + 1)) (hj : j ∈ Γ) : 0 < x j ∧ cappedDegree (budget n θ τ) (x j) ν < biasDegree A (levelDistance J j) := by
    simpa only [Γ, cappedLevels, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  have hhigh (j : Fin (J + 1)) (hj : j ∈ Γ) : n / (Real.log n) ^ 2 < (parentCells J j : ℝ) :=
    levelLog_positive_is_high J Cv Rbar n hCvp hRp hn (zero_lt_one.trans_le hL) hRsmall j (hcap j hj).1
  have hj0 (j : Fin (J + 1)) (hj : j ∈ Γ) : j.val ≠ 0 := by
    intro he
    have hone : (parentCells J j : ℝ) = 1 := by simp [parentCells, he]
    have hratio : 1 ≤ n / (Real.log n) ^ 2 := (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hL) 2)).mpr (by simpa using hnlarge)
    have hh := hhigh j hj
    rw [hone] at hh
    linarith
  have hsepΓ (i : Fin (J + 1)) (hi : i ∈ Γ) (j : Fin (J + 1)) (hj : j ∈ Γ) (hij : i ≠ j) : Real.log 2 ≤ |x i - x j| :=
    levelLog_separated J Cv Rbar n hn i j (hj0 i hi) (hj0 j hj) hij
  have hinj : Set.InjOn x Γ := by
    intro i hi j hj he
    by_contra hij
    have hs := hsepΓ i hi j hj hij
    rw [he, sub_self, abs_zero] at hs
    linarith
  have hS : ∀ z ∈ S, 0 < z ∧ z ≤ Xbar := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    exact ⟨(hcap j hj).1, levelLog_le_endpoint J Cv Rbar n hn j⟩
  have hsepS : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → Real.log 2 ≤ |z - w| := by
    intro z hz w hw hzw
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
    exact hsepΓ i hi j hj (fun hij => hzw (congrArg x hij))
  have hlarge : ∀ z ∈ S, (ν : ℝ) + 3 ≤ budget n θ τ / z := by
    intro z hz
    exact hfloor.trans (div_le_div_of_nonneg_left hB.le (hS z hz).1 (hS z hz).2)
  have hdegree : ∀ z ∈ S, (cappedDegree (budget n θ τ) z ν : ℝ) + 1 ≤ Rbar := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    have hs := selectedDegree_high_bound n θ τ A (budget n θ τ) ν hA hn hL hnlarge x j (hhigh j hj)
    have hm : selectedDegree A (levelDistance J j) (budget n θ τ) (x j) ν = cappedDegree (budget n θ τ) (x j) ν := by
      simp only [selectedDegree, ite_eq_left (hcap j hj).1, min_eq_right (hcap j hj).2.le]
    rw [hm] at hs
    simp only [Nat.cast_add, Nat.cast_ofNat] at hs
    have := Nat.cast_nonneg (α := ℝ) ν
    linarith
  have hraw := cappedDegree_subcritical_bound S n Cv CR CX Rbar Xbar θ τ (Real.log n) ν
    hn hCvp hCRp.le hCX hRp hXp hθ hθhalf hτ hL
    (highDegreeEnvelope_bound n θ τ A ν hL hθ hθhalf hτ hA)
    (windowEndpoint_bound n θ τ A Cv ν hL hθ hθhalf hτ hA hCvp)
    hB hS hsepS hlarge hdegree
  have hK (j : Fin (J + 1)) : n * Real.exp (x j) / (Cv * Rbar) = (parentCells J j : ℝ) := by
    rw [exp_levelLog J Cv Rbar n hCvp hRp hn j]
    field_simp
  rw [Finset.sum_image hinj] at hraw
  simp_rw [hK] at hraw
  simpa only [Γ, J, x, CR, CX, Rbar, Xbar, capConstant, rate, budget, mul_assoc] using hraw

/-- The whole two-rule approximation error, including uncapped levels, obeys
the paper's subcritical rate. -/
theorem chosen_bias_sum_bound (n θ τ A Cv : ℝ) (ν : ℕ)
    (hn : 0 < n) (hL : 1 ≤ Real.log n) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (hA : 0 ≤ A) (hCv : 1 ≤ Cv) (hdecay : θ * Real.log 2 + 1 ≤ τ * A)
    (hnlarge : (Real.log n) ^ 2 ≤ n) (hRsmall : Cv * highDegreeEnvelope n θ τ A ν ≤ (Real.log n) ^ 2)
    (hB : 0 < budget n θ τ)
    (hfloor : (ν : ℝ) + 3 ≤ budget n θ τ / windowEndpoint (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n) :
    (∑ j : Fin (terminal n θ τ + 1), approximationWeight (parentCells (terminal n θ τ) j) θ τ ν (chosenOrder n θ τ A Cv ν j)) ≤
      (biasRuleConstant A ν + capConstant θ τ A Cv ν) * rate n θ τ ν := by
  have hs := selectedDegree_weight_sum_bound (terminal n θ τ) θ τ A (budget n θ τ)
    (levelLog (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n) ν hθ.le hτ.le hA hdecay
  have hc := chosen_capped_bias_bound n θ τ A Cv ν hn hL hθ hθhalf hτ hA hCv hnlarge hRsmall hB hfloor
  have ht := terminal_bias_bound n θ τ hL hn hθ hθhalf hτ
  have hpower : 1 ≤ (Real.log n) ^ (θ / 2 + (ν : ℝ) / 2 + 1 / 4) :=
    Real.one_le_rpow hL (by positivity)
  have hbase : n ^ (-θ) * Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) ≤ rate n θ τ ν := by
    unfold rate
    convert mul_le_mul_of_nonneg_left hpower (show 0 ≤ n ^ (-θ) * Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) by positivity) using 1 <;> ring
  have htRate := ht.trans hbase
  have hconst := biasRuleConstant_nonneg A ν hA
  unfold chosenOrder
  exact hs.trans (by convert add_le_add (mul_le_mul_of_nonneg_left htRate hconst) hc using 1; ring)

end RoughRegime.UpperSubcritical
