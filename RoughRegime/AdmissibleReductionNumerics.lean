module

public import RoughRegime.ReductionNaturalScales
public import RoughRegime.SourceSelectedPoisson


@[expose] public section
/-! Exact physical-majorant and pair-rate limits for the arbitrary natural
resolution/multiplier choices of Proposition 12. -/
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace RoughRegime.ReductionScales.NaturalScaleChoice
set_option backward.isDefEq.respectTransparency false
variable {A : AbstractScaleParameters} (S : NaturalScaleChoice A)

 theorem Lambda_tendsto_zero : Tendsto S.Lambda atTop (nhds 0) := by
  have hB:=S.block_superlog 0
  simp only [Real.rpow_zero,mul_one] at hB
  have he:=(tendsto_inv_atTop_zero.comp hB).const_mul (2*A.v0)
  simp only [mul_zero] at he
  apply Filter.Tendsto.congr' _ he
  exact Eventually.of_forall (fun n=>by rw [S.Lambda_eq]; simp only [Function.comp_apply,inv_div]; ring)

 theorem Lambda_nonnegative (n : ℕ) : 0 ≤ S.Lambda n := by
  rw [S.Lambda_eq]
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) A.hv.le) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

 theorem block_canonicalPoissonMajorant_eq (n : ℕ) (hn : 0<n) (hR : 0<S.R n)
    (hM : 0<frequency n A.theta A.tau) :
    (S.B n:ℝ)*LatticePriors.canonicalPoissonMajorant A.Cstar A.CΓ A.CE (S.R n)
      (S.Lambda n) (S.Au n) (S.Av n) (frequency n A.theta A.tau)=S.poissonMajorant n := by
  rw [LatticePriors.block_mul_canonicalPoissonMajorant _ _ _ _ _ _ _ _ _ hR
    (zero_lt_one.trans_le A.hCΓ) hM]
  rw [← S.rawI_eq_physical n hn hR]
  exact (S.poissonMajorant_eq n).symm

 theorem eventually_large_block : ∀ᶠ n : ℕ in atTop,n ≤ S.B n := by
  have hb:=(S.block_superlog 0).eventually_ge_atTop 1
  simp only [Real.rpow_zero,mul_one] at hb
  filter_upwards [hb,eventually_gt_atTop (0:ℕ)] with n hn hnp
  have hnp' : (0:ℝ)<n := by exact_mod_cast hnp
  exact_mod_cast (show (n:ℝ) ≤ (S.B n:ℝ) by simpa only [one_mul] using (le_div_iff₀ hnp').mp hn)

 theorem eventually_even_power : ∀ᶠ n : ℕ in atTop,
    ∃ k : ℕ,0<k ∧ Even k ∧ S.B n=k^A.d := by
  filter_upwards [S.hRpos,eventually_gt_atTop (0:ℕ)] with n hR hn
  rw [S.B_eq_selected]
  unfold blockCount
  let z:=idealSideLength n (S.R n) (logResolution n A.theta A.tau A.c0) A.d
  refine ⟨evenCeiling z,?_,evenCeiling_even z,rfl⟩
  have hz : 0<z:=idealSideLength_positive n (S.R n) _ A.d (by exact_mod_cast hn) (zero_lt_one.trans_le hR)
  exact_mod_cast hz.trans_le (evenCeiling_bounds z hz.le).1

end RoughRegime.ReductionScales.NaturalScaleChoice
