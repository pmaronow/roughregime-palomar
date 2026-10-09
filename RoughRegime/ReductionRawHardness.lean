module

public import RoughRegime.ReductionAmplitudes


@[expose] public section
/-! Exact identification of the physical Poisson leading term with the
rounded numerical hardness expression in Proposition 12. -/
noncomputable section
open Filter
namespace RoughRegime.ReductionScales
set_option maxHeartbeats 800000

 def rawLeadingHardness (n B θ v0 ε R m CE C1 : ℝ) (M : ℕ) : ℝ :=
  B * (2 * v0 * n / B) ^ 2 * (ε * m ^ 2 * (B * R) ^ (-θ)) ^ 2 *
    R ^ (1 - (M : ℝ)) * Real.exp (CE * M) * (C1 * n / B) ^ M / M.factorial

 theorem rawLeadingHardness_eq (n B θ v0 ε R m CE C1 : ℝ) (M : ℕ)
    (hn : 0 < n) (hB : 0 < B) (hR : 0 < R) :
    rawLeadingHardness n B θ v0 ε R m CE C1 M =
      leadingHardness n θ v0 ε R m CE C1 (B * R / n) M := by
  let x := B * R / n
  have hx : 0 < x := div_pos (mul_pos hB hR) hn
  have hBR : B * R = n * x := by dsimp [x]; field_simp
  have hpow : ((B * R) ^ (-θ)) ^ 2 = n ^ (-2 * θ) * x ^ (-2 * θ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (mul_pos hB hR).le,hBR,
      Real.mul_rpow hn.le hx.le]
    congr 1 <;> ring_nf
  have hRp : R ^ (1 - (M : ℝ)) * R ^ M = R := by
    rw [← Real.rpow_natCast,← Real.rpow_add hR]
    simp
  have hnp : n * n ^ (-2 * θ) = n ^ (1 - 2 * θ) := by
    calc
      _ = n ^ (1 : ℝ) * n ^ (-2 * θ) := by rw [Real.rpow_one]
      _ = n ^ (1 + (-2 * θ)) := (Real.rpow_add hn _ _).symm
      _ = _ := by congr 1; ring_nf
  have hxp : x ^ ((M : ℝ) + 1 + 2 * θ) = x ^ (M + 1) * x ^ (2 * θ) := by
    rw [Real.rpow_add hx,← Nat.cast_add_one,Real.rpow_natCast]
  have hxneg : x ^ (-2 * θ) * x ^ (2 * θ) = 1 := by
    rw [← Real.rpow_add hx]
    convert Real.rpow_zero x using 1; ring_nf
  have hLambda : B * (2 * v0 * n / B) ^ 2 = 4 * v0 ^ 2 * n * R / x := by
    dsimp [x]
    field_simp
    ring_nf
  have hy : C1 * n / B = C1 * R / x := by
    dsimp [x]
    field_simp
  change rawLeadingHardness n B θ v0 ε R m CE C1 M = leadingHardness n θ v0 ε R m CE C1 x M
  unfold rawLeadingHardness leadingHardness
  rw [mul_pow,mul_pow,hpow,hLambda,hy,div_pow,mul_pow,hxp,pow_succ]
  field_simp
  have hfac : n * n ^ (-2 * θ) * x ^ (-2 * θ) * x ^ (2 * θ) * R ^ (1 - (M : ℝ)) * R ^ M =
      n ^ (1 - 2 * θ) * R := by
    calc
      _ = (n * n ^ (-2 * θ)) * (x ^ (-2 * θ) * x ^ (2 * θ)) * (R ^ (1 - (M : ℝ)) * R ^ M) := by ring_nf
      _ = _ := by rw [hnp,hxneg,hRp]; ring_nf
  convert congrArg (fun y : ℝ => v0 ^ 2 * ε ^ 2 * m ^ 4 * C1 ^ M * x ^ (M + 1) * y) hfac using 1 <;> ring_nf

 theorem rawLeadingHardness_amplitudes_eq (n B a b θ v0 εu εv R m CE C1 : ℝ) (M : ℕ)
    (hn : 0 < n) (hB : 0 < B) (hR : 0 < R) (hab : a + b = θ) :
    B * (2 * v0 * n / B) ^ 2 * (amplitude εu B R a m * amplitude εv B R b m) ^ 2 *
      R ^ (1 - (M : ℝ)) * Real.exp (CE * M) * (C1 * n / B) ^ M / M.factorial =
        leadingHardness n θ v0 (εu * εv) R m CE C1 (B * R / n) M := by
  rw [amplitude_product εu εv B R a b m hB hR,hab]
  exact rawLeadingHardness_eq n B θ v0 (εu * εv) R m CE C1 M hn hB hR

 theorem selected_rawLeadingHardness_tendsto_zero (θ τ c0 v0 ε CE C1 c : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hv : 0 < v0)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC1 : 0 < C1) (hc : 0 < c)
    (hmargin : 1 + Real.log C1 + CE < c0)
    (R m : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n) (hmpos : ∀ᶠ n in atTop, 1 ≤ m n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (hmM : ∀ᶠ n in atTop, m n ≤ c * frequency n θ τ)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => rawLeadingHardness n (selectedBlockCount θ τ c0 R d n)
      θ v0 ε (R n) (m n) CE C1 (frequency n θ τ)) atTop (nhds 0) := by
  apply Filter.Tendsto.congr' _
    (leadingHardness_tendsto_zero θ τ c0 v0 ε CE C1 c hθ hθhalf hτ hv hε hε1 hC1 hc hmargin
      R m hRpos hmpos hR hmM d hd)
  filter_upwards [hRpos,eventually_gt_atTop (0 : ℝ)] with n hnR hn
  have hRp : 0 < R n := zero_lt_one.trans_le hnR
  have hBp : 0 < (selectedBlockCount θ τ c0 R d n : ℝ) := by
    exact_mod_cast blockCount_positive n (R n) _ d hn hRp
  exact (rawLeadingHardness_eq n _ θ v0 ε _ _ CE C1 _ hn hBp hRp).symm

end RoughRegime.ReductionScales
