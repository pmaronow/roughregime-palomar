module

public import RoughRegime.ReductionHardness
public import RoughRegime.ReductionSeparation


@[expose] public section
/-! Actual amplitude identities and the remainder loss in Proposition 12. -/
noncomputable section
open Filter

namespace RoughRegime.ReductionScales

def amplitude (ε B R a m : ℝ) : ℝ := ε * (B * R) ^ (-a) * m

lemma amplitude_positive (ε B R a m : ℝ) (hε : 0 < ε) (hB : 0 < B) (hR : 0 < R) (hm : 0 < m) :
    0 < amplitude ε B R a m := by unfold amplitude; positivity

lemma amplitude_le_block (ε B R a m : ℝ) (hε : 0 ≤ ε) (hB : 0 < B) (hR : 0 < R)
    (hm : m ≤ R ^ a) : amplitude ε B R a m ≤ ε * B ^ (-a) := by
  unfold amplitude
  rw [Real.mul_rpow hB.le hR.le]
  have hRp : 0 < R ^ (-a) := Real.rpow_pos_of_pos hR _
  have hmul : R ^ (-a) * m ≤ 1 := by
    calc
      R ^ (-a) * m ≤ R ^ (-a) * R ^ a := mul_le_mul_of_nonneg_left hm hRp.le
      _ = 1 := by rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  calc
    ε * (B ^ (-a) * R ^ (-a)) * m = (ε * B ^ (-a)) * (R ^ (-a) * m) := by ring
    _ ≤ (ε * B ^ (-a)) * 1 := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = ε * B ^ (-a) := mul_one _

lemma amplitude_le_sample (ε B R a m n : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hn : 0 < n) (hBn : n ≤ B) (hR : 0 < R) (ha : 0 ≤ a) (hm : m ≤ R ^ a) :
    amplitude ε B R a m ≤ n ^ (-a) := by
  have hB : 0 < B := hn.trans_le hBn
  have h1 := amplitude_le_block ε B R a m hε hB hR hm
  have hpow : B ^ (-a) ≤ n ^ (-a) := Real.rpow_le_rpow_of_nonpos hn hBn (neg_nonpos.mpr ha)
  calc
    amplitude ε B R a m ≤ ε * B ^ (-a) := h1
    _ ≤ 1 * B ^ (-a) := mul_le_mul_of_nonneg_right hε1 (by positivity)
    _ ≤ n ^ (-a) := by simpa using hpow

lemma amplitude_product (εu εv B R a b m : ℝ) (hB : 0 < B) (hR : 0 < R) :
    amplitude εu B R a m * amplitude εv B R b m = εu * εv * m ^ 2 * (B * R) ^ (-(a + b)) := by
  unfold amplitude
  rw [neg_add, Real.rpow_add (mul_pos hB hR)]
  ring

lemma selected_amplitude_product (εu εv θ τ c0 a b : ℝ) (hab : a + b = θ)
    (R m : ℝ → ℝ) (d : ℕ) (n : ℝ) (hn : 0 < n) (hR : 0 < R n) :
    amplitude εu (selectedBlockCount θ τ c0 R d n) (R n) a (m n) *
      amplitude εv (selectedBlockCount θ τ c0 R d n) (R n) b (m n) * Real.exp (-τ * frequency n θ τ) =
        εu * εv * (m n) ^ 2 * separationScale θ τ c0 R d n := by
  have hB : 0 < (selectedBlockCount θ τ c0 R d n : ℝ) := by
    unfold selectedBlockCount
    exact_mod_cast blockCount_positive n (R n) _ d hn hR
  rw [amplitude_product εu εv _ _ a b _ hB hR, hab]
  have hx : n * resolutionRatio θ τ c0 R d n = (selectedBlockCount θ τ c0 R d n : ℝ) * R n := by
    unfold resolutionRatio
    field_simp
  unfold separationScale
  rw [hx]
  ring

lemma frequency_logR_div_log_tendsto_zero (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ))) :
    Tendsto (fun n : ℝ => frequency n θ τ * Real.log (R n) / Real.log n) atTop (nhds 0) := by
  have hlittle : (fun n : ℝ => (frequency n θ τ : ℝ) * Real.log (frequency n θ τ)) =o[atTop] (fun n => Real.log n) := by
    apply Asymptotics.isLittleO_of_tendsto' _ (frequency_log_div_log_tendsto_zero θ τ hθ hθhalf hτ)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    exact fun h0 => False.elim ((Real.log_pos hn).ne' h0)
  have hbound := (Asymptotics.isBigO_refl (fun n : ℝ => (frequency n θ τ : ℝ)) atTop).mul hR
  exact (hbound.trans_isLittleO hlittle).tendsto_div_nhds_zero

/-- The actual resolution power in the remainder is defeated by every fixed
negative sample-size power. This proves the paper's `exp(O(M log M))` step. -/
theorem resolution_exponential_loss_tendsto_zero (θ τ a : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (ha : 0 < a)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ))) :
    Tendsto (fun n : ℝ => n ^ (-a) * (R n) ^ frequency n θ τ) atTop (nhds 0) := by
  have hsmall := frequency_logR_div_log_tendsto_zero θ τ hθ hθhalf hτ R hR
  have hratio := hsmall.sub_const a
  simp only [zero_sub] at hratio
  have hprod := hratio.neg_mul_atTop (neg_neg_of_pos ha) Real.tendsto_log_atTop
  have hbot : Tendsto (fun n : ℝ => -a * Real.log n + frequency n θ τ * Real.log (R n)) atTop atBot := by
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    have hLn : Real.log n ≠ 0 := (Real.log_pos hn).ne'
    field_simp
    ring
  have he := Real.tendsto_exp_atBot.comp hbot
  apply Filter.Tendsto.congr' _ he
  filter_upwards [hRpos, eventually_gt_atTop (0 : ℝ)] with n hRn hn
  have hRp : 0 < R n := zero_lt_one.trans_le hRn
  rw [Function.comp_apply, Real.exp_add, Real.rpow_def_of_pos hn, ← Real.log_pow,
    Real.exp_log (pow_pos hRp _)]
  congr 1
  congr 1
  ring

/-- The amplitude bounds follow from the actual source constraints and the
constructed block count. -/
theorem selected_amplitude_eventually_le_sample (θ τ c0 ε a : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a)
    (R m : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (hm : ∀ᶠ n in atTop, m n ≤ (R n) ^ a) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ n in atTop, amplitude ε (selectedBlockCount θ τ c0 R d n) (R n) a (m n) ≤ n ^ (-a) := by
  have hB := blockInflation_div_logPower_tendsto θ τ c0 0 hθ hθhalf hτ R hRpos hR d hd
  simp only [Real.rpow_zero, div_one] at hB
  filter_upwards [hB.eventually_ge_atTop 1, hRpos, hm, eventually_gt_atTop (0 : ℝ)] with n hnB hnR hnm hn
  have hBn : n ≤ (selectedBlockCount θ τ c0 R d n : ℝ) := by
    simpa only [one_mul, blockInflation] using (le_div_iff₀ hn).mp hnB
  exact amplitude_le_sample ε _ _ a _ n hε hε1 hn hBn (zero_lt_one.trans_le hnR) ha hnm

/-- The actual product of the two amplitudes has the stated lower-rate scale. -/
theorem selected_amplitude_product_eventually_lower (θ τ c0 εu εv a b : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hεu : 0 ≤ εu) (hεv : 0 ≤ εv) (hab : a + b = θ)
    (R m : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    ∀ᶠ n in atTop, (εu * εv * separationConstant θ τ c0 / 2) * (m n) ^ 2 * RoughRegime.Rates.subcriticalScale n θ τ ≤
      amplitude εu (selectedBlockCount θ τ c0 R d n) (R n) a (m n) *
        amplitude εv (selectedBlockCount θ τ c0 R d n) (R n) b (m n) * Real.exp (-τ * frequency n θ τ) := by
  filter_upwards [separationScale_eventually_lower θ τ c0 hθ hθhalf hτ R hRpos hR d hd,
    hRpos, eventually_gt_atTop (0 : ℝ)] with n hn hnR hnp
  rw [selected_amplitude_product εu εv θ τ c0 a b hab R m d n hnp (zero_lt_one.trans_le hnR)]
  convert mul_le_mul_of_nonneg_left hn (show 0 ≤ εu * εv * (m n) ^ 2 by positivity) using 1; ring

def remainderRatio (C Λ Au Av R CE CΓ : ℝ) (M : ℕ) : ℝ :=
  C * Λ ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 * R ^ (M - 1) * Real.exp (-CE * M) / CΓ ^ M

lemma remainderRatio_nonnegative (C Λ Au Av R CE CΓ : ℝ) (M : ℕ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hCΓ : 0 ≤ CΓ) : 0 ≤ remainderRatio C Λ Au Av R CE CΓ M := by
  unfold remainderRatio
  positivity

lemma remainderRatio_le (C Λ Au Av R CE CΓ V z : ℝ) (M : ℕ)
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) (hΛV : Λ ≤ V) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av)
    (hAuz : Au ≤ z) (hAvz : Av ≤ z) (hR : 1 ≤ R) (hCE : 0 ≤ CE) (hCΓ : 1 ≤ CΓ) :
    remainderRatio C Λ Au Av R CE CΓ M ≤ 4 * C * V ^ 2 * z ^ 4 * R ^ M := by
  have hz : 0 ≤ z := hAu.trans hAuz
  have hV : 0 ≤ V := hΛ.trans hΛV
  have he : Real.exp (-CE * M) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hMn : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    nlinarith
  have hcp : 1 ≤ CΓ ^ M := one_le_pow₀ hCΓ
  have hRp : 0 ≤ R := zero_le_one.trans hR
  have hpow : R ^ (M - 1) ≤ R ^ M := pow_le_pow_right₀ hR (Nat.sub_le M 1)
  have hsum : Au ^ 2 + Av ^ 2 ≤ 2 * z ^ 2 := by
    nlinarith [sq_nonneg (z - Au), sq_nonneg (z - Av), mul_nonneg hAu (sub_nonneg.mpr hAuz), mul_nonneg hAv (sub_nonneg.mpr hAvz)]
  unfold remainderRatio
  calc
    _ ≤ C * V ^ 2 * (2 * z ^ 2) ^ 2 * R ^ M * 1 / 1 := by
      gcongr
    _ = 4 * C * V ^ 2 * z ^ 4 * R ^ M := by ring

/-- The exact numeric second-to-leading-term ratio tends to zero for the
actual amplitudes and constructed blocks. -/
theorem selected_remainderRatio_tendsto_zero (θ τ c0 εu εv a b C v0 CE CΓ : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (ha : 0 < a) (hb : 0 < b)
    (hεu : 0 < εu) (hεu1 : εu ≤ 1) (hεv : 0 < εv) (hεv1 : εv ≤ 1)
    (hC : 0 ≤ C) (hv : 0 < v0) (hCE : 0 ≤ CE) (hCΓ : 1 ≤ CΓ)
    (R m : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n) (hmpos : ∀ᶠ n in atTop, 1 ≤ m n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (hma : ∀ᶠ n in atTop, m n ≤ (R n) ^ a) (hmb : ∀ᶠ n in atTop, m n ≤ (R n) ^ b)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => remainderRatio C (2 * v0 / blockInflation θ τ c0 R d n)
      (amplitude εu (selectedBlockCount θ τ c0 R d n) (R n) a (m n))
      (amplitude εv (selectedBlockCount θ τ c0 R d n) (R n) b (m n))
      (R n) CE CΓ (frequency n θ τ)) atTop (nhds 0) := by
  have hs : 0 < min a b := lt_min ha hb
  have hAu := selected_amplitude_eventually_le_sample θ τ c0 εu a hθ hθhalf hτ hεu.le hεu1 ha.le R m hRpos hR hma d hd
  have hAv := selected_amplitude_eventually_le_sample θ τ c0 εv b hθ hθhalf hτ hεv.le hεv1 hb.le R m hRpos hR hmb d hd
  have hB := blockInflation_div_logPower_tendsto θ τ c0 0 hθ hθhalf hτ R hRpos hR d hd
  simp only [Real.rpow_zero, div_one] at hB
  have hlim := (resolution_exponential_loss_tendsto_zero θ τ (4 * min a b) hθ hθhalf hτ (by positivity) R hRpos hR).const_mul (16 * C * v0 ^ 2)
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hRpos] with n hnR
    exact remainderRatio_nonnegative C _ _ _ _ CE CΓ _ hC (zero_le_one.trans hnR) (zero_le_one.trans hCΓ)
  · filter_upwards [hAu, hAv, hRpos, hmpos, hB.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)] with n hnAu hnAv hnR hnm hnB hn
    have hnp : 0 < n := zero_lt_one.trans_le hn
    have hRp : 0 < R n := zero_lt_one.trans_le hnR
    have hBp : 0 < (selectedBlockCount θ τ c0 R d n : ℝ) := by
      unfold selectedBlockCount
      exact_mod_cast blockCount_positive n (R n) _ d hnp hRp
    have hLambda : 0 ≤ 2 * v0 / blockInflation θ τ c0 R d n := by positivity
    have hLambdaV : 2 * v0 / blockInflation θ τ c0 R d n ≤ 2 * v0 := by
      exact (div_le_self (by positivity : 0 ≤ 2 * v0) hnB)
    have hu := (amplitude_positive εu _ _ a _ hεu hBp hRp (zero_lt_one.trans_le hnm)).le
    have hvv := (amplitude_positive εv _ _ b _ hεv hBp hRp (zero_lt_one.trans_le hnm)).le
    have hna : n ^ (-a) ≤ n ^ (-min a b) := Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg (min_le_left a b))
    have hnb : n ^ (-b) ≤ n ^ (-min a b) := Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg (min_le_right a b))
    have hbound := remainderRatio_le C _ _ _ (R n) CE CΓ (2 * v0) (n ^ (-min a b)) (frequency n θ τ) hC hLambda hLambdaV hu hvv
      (hnAu.trans hna) (hnAv.trans hnb) hnR hCE hCΓ
    have heq : (n ^ (-min a b)) ^ (4 : ℕ) = n ^ (-(4 * min a b)) := by
      rw [← Real.rpow_natCast (n ^ (-min a b)) 4, ← Real.rpow_mul hnp.le]
      congr 1
      ring
    rw [heq] at hbound
    convert hbound using 1; ring

end RoughRegime.ReductionScales
