module

public import RoughRegime.ModelPredicates


@[expose] public section
/-! Exact unnumbered rate identities: positive common interval scaling leaves
the reciprocal ratio unchanged, and the gap between the two paper scales is
the stated power of log n. These do not identify that gap with the risk. -/
noncomputable section
namespace RoughRegime.Rates

 theorem rho_mul_interval (c lo hi : ℝ) (hc : 0<c) :
     rho (c*lo) (c*hi)=rho lo hi := by
   unfold rho
   rw [Real.sqrt_mul hc.le,Real.sqrt_mul hc.le,←mul_sub,←mul_add]
   exact mul_div_mul_left _ _ (Real.sqrt_pos.mpr hc).ne'

 theorem tau_mul_interval (c lo hi : ℝ) (hc : 0<c) :
     tau (c*lo) (c*hi)=tau lo hi := by
   unfold tau
   rw [rho_mul_interval c lo hi hc]

 theorem kappa_mul_interval (c lo hi θ : ℝ) (hc : 0<c) :
     kappa θ (tau (c*lo) (c*hi))=kappa θ (tau lo hi) := by
   rw [tau_mul_interval c lo hi hc]

end RoughRegime.Rates
namespace RoughRegime.Model

 theorem bracketScale_gap (S : BracketParameters) (ν : ℝ) (n : ℕ)
     (hrough : S.theta<1/2) (hn : 1<n) :
     upperBracketScale S ν n/lowerBracketScale S n=(Real.log n)^(ν/2-3/4) := by
   have hnR : 1<(n:ℝ) := by exact_mod_cast hn
   have hp := Rates.scale_pos n S.theta (Rates.tau S.lo S.hi) hnR
   have hl := Real.log_pos hnR
   unfold upperBracketScale lowerBracketScale
   rw [ite_eq_left hrough,ite_eq_left hrough,mul_div_mul_left _ _ hp.ne']
   have he : ν/2-3/4=(ν/2+1/4)-1 := by ring
   rw [he,Real.rpow_sub_one hl.ne']

 theorem bracketScale_gap_nu_two (S : BracketParameters) (n : ℕ)
     (hrough : S.theta<1/2) (hn : 1<n) :
     upperBracketScale S 2 n/lowerBracketScale S n=(Real.log n)^(1/4:ℝ) := by
   simpa only [show (2:ℝ)/2-3/4=1/4 by norm_num] using bracketScale_gap S 2 n hrough hn

end RoughRegime.Model
