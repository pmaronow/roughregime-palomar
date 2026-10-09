module

public import RoughRegime.CompactUpperNumerics


@[expose] public section
/-! Common uncapped tuning on every density interval whose tau is bounded
below by the same positive number. -/
noncomputable section
open Filter
open scoped BigOperators
namespace RoughRegime.UpperParametric
open RoughRegime.UpperDegreeRules RoughRegime.LiftVariance
set_option maxHeartbeats 800000

theorem uncapped_total_error_bound_eventually_uniform
    (θ τlo A Cv C0 Cproj q : ℝ) (ν : ℕ)
    (hθ : 1/2≤θ) (hτlo : 0<τlo) (hA : 0≤A) (hCv : 1≤Cv)
    (hC0 : 0≤C0) (hCproj : 0≤Cproj) (hq : 0<q)
    (hdecay : θ*Real.log 2+1≤τlo*A) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀τ,τlo≤τ→
      let cK:=terminalConstant A Cv ν
      let J:=terminalLevel cK n
      let m:Fin (J+1)→ℕ:=fun j=>biasDegree A (levelDistance J j)
      (∀j,2*(m j+ν+2)≤n) ∧
      ∀v:Fin (J+1)→ℝ,
      (∀j,v j≤Cv*(parentCells J j:ℝ)^(-2*q)/n+
        ∑k∈Finset.range (m j+ν+2-1),varianceTerm Cv (parentCells J j) n (k+2))→
      Cproj*((2:ℝ)^J)^(-θ)+C0*(∑j,approximationWeight (parentCells J j) θ τ ν (m j))+
        (∑j,Real.sqrt (v j))≤C/Real.sqrt n := by
  let cK:=terminalConstant A Cv ν
  let B:=(Cproj+C0*biasRuleConstant A ν)*(2/cK)^θ
  let S:=Real.sqrt Cv*(1+(1-(2:ℝ)^(-q))⁻¹)+2*Cv*sqrtResolutionConstant*Real.sqrt cK
  have hCvp:0<Cv:=zero_lt_one.trans_le hCv
  have hcK:0<cK:=by dsimp [cK,terminalConstant];positivity
  have hB:0≤B:=by
    dsimp [B]
    exact mul_nonneg (add_nonneg hCproj (mul_nonneg hC0 (biasRuleConstant_nonneg A ν hA)))
      (Real.rpow_nonneg (by positivity) _)
  refine ⟨|B+S|+1,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (uncappedThreshold A Cv ν),eventually_ge_atTop (3:ℕ)] with n hn hn3
  intro τ hτ
  dsimp only
  let J:=terminalLevel cK n
  let m:Fin (J+1)→ℕ:=fun j=>biasDegree A (levelDistance J j)
  have ht:=uncapped_tuning_valid A Cv ν n hA hCvp hn
  have ht' : 0<cK ∧ cK≤1 ∧ cK*n/2<(2:ℝ)^J ∧ (2:ℝ)^J≤cK*n ∧
      ∀j:Fin (J+1),2*(m j+ν+2)≤n ∧ Cv*(m j+ν+2:ℕ)*parentCells J j/n≤1/2 := ht
  refine ⟨fun j=>(ht'.2.2.2.2 j).1,?_⟩
  intro v hv
  have hnr:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hn1:1≤(n:ℝ):=by exact_mod_cast (show 1≤n by omega)
  have hcn:1≤cK*n:=(one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans ht'.2.2.2.1
  have hv' (j:Fin (J+1)) : v j≤Cv*(parentCells J j:ℝ)^(-2*q)/n+
      4*Cv^2*parentCells J j/(n:ℝ)^2 :=
    (hv j).trans (add_le_add le_rfl (variance_tail_small_resolution Cv (parentCells J j) n
      (m j+ν+2) hCvp.le (Nat.cast_nonneg _) hnr (ht'.2.2.2.2 j).2))
  have hdecayτ:=hdecay.trans (mul_le_mul_of_nonneg_right hτ hA)
  have hb:=uncapped_total_error_bound A Cv C0 Cproj cK n θ τ q ν hA hCvp.le hC0 hCproj
    hcK hnr (by linarith) (hτlo.trans_le hτ).le hq hdecayτ hcn v hv'
  have hnum:=parametric_rate_comparison n θ B S hn1 hθ hB
  exact hb.trans (hnum.trans (div_le_div_of_nonneg_right
    ((le_abs_self (B+S)).trans (by linarith)) (Real.sqrt_nonneg _)))

theorem uncapped_basic_total_error_bound_eventually_uniform
    (θ τlo A Cv C0 Cproj q : ℝ) (ν : ℕ)
    (hθ : 0<θ) (hτlo : 0<τlo) (hA : 0≤A) (hCv : 1≤Cv)
    (hC0 : 0≤C0) (hCproj : 0≤Cproj) (hq : 0<q)
    (hdecay : θ*Real.log 2+1≤τlo*A) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀τ,τlo≤τ→
      let cK:=terminalConstant A Cv ν
      let J:=terminalLevel cK n
      let m:Fin (J+1)→ℕ:=fun j=>biasDegree A (levelDistance J j)
      (∀j,2*(m j+ν+2)≤n) ∧
      ∀v:Fin (J+1)→ℝ,
      (∀j,v j≤Cv*(parentCells J j:ℝ)^(-2*q)/n+
        ∑k∈Finset.range (m j+ν+2-1),varianceTerm Cv (parentCells J j) n (k+2))→
      Cproj*((2:ℝ)^J)^(-θ)+C0*(∑j,approximationWeight (parentCells J j) θ τ ν (m j))+
        (∑j,Real.sqrt (v j))≤C*((n:ℝ)^(-θ)+(n:ℝ)^(-(1/2:ℝ))) := by
  let cK:=terminalConstant A Cv ν
  let B:=(Cproj+C0*biasRuleConstant A ν)*(2/cK)^θ
  let S:=Real.sqrt Cv*(1+(1-(2:ℝ)^(-q))⁻¹)+2*Cv*sqrtResolutionConstant*Real.sqrt cK
  have hCvp:0<Cv:=zero_lt_one.trans_le hCv
  have hcK:0<cK:=by dsimp [cK,terminalConstant];positivity
  have hB:0≤B:=by
    dsimp [B]
    exact mul_nonneg (add_nonneg hCproj (mul_nonneg hC0 (biasRuleConstant_nonneg A ν hA)))
      (Real.rpow_nonneg (by positivity) _)
  let C:=|B|+|S|+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_ge_atTop (uncappedThreshold A Cv ν),eventually_ge_atTop (3:ℕ)] with n hn hn3
  intro τ hτ
  dsimp only
  let J:=terminalLevel cK n
  let m:Fin (J+1)→ℕ:=fun j=>biasDegree A (levelDistance J j)
  have ht:=uncapped_tuning_valid A Cv ν n hA hCvp hn
  have ht' : 0<cK ∧ cK≤1 ∧ cK*n/2<(2:ℝ)^J ∧ (2:ℝ)^J≤cK*n ∧
      ∀j:Fin (J+1),2*(m j+ν+2)≤n ∧ Cv*(m j+ν+2:ℕ)*parentCells J j/n≤1/2 := ht
  refine ⟨fun j=>(ht'.2.2.2.2 j).1,?_⟩
  intro v hv
  have hnr:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hn1:1≤(n:ℝ):=by exact_mod_cast (show 1≤n by omega)
  have hcn:1≤cK*n:=(one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans ht'.2.2.2.1
  have hv' (j:Fin (J+1)) : v j≤Cv*(parentCells J j:ℝ)^(-2*q)/n+
      4*Cv^2*parentCells J j/(n:ℝ)^2 :=
    (hv j).trans (add_le_add le_rfl (variance_tail_small_resolution Cv (parentCells J j) n
      (m j+ν+2) hCvp.le (Nat.cast_nonneg _) hnr (ht'.2.2.2.2 j).2))
  have hdecayτ:=hdecay.trans (mul_le_mul_of_nonneg_right hτ hA)
  have hb:=uncapped_total_error_bound A Cv C0 Cproj cK n θ τ q ν hA hCvp.le hC0 hCproj
    hcK hnr (by linarith) (hτlo.trans_le hτ).le hq hdecayτ hcn v hv'
  apply hb.trans
  have hBC:B≤C:=by dsimp [C];linarith [le_abs_self B,abs_nonneg S]
  have hSC:S≤C:=by dsimp [C];linarith [le_abs_self S,abs_nonneg B]
  have heq:C/Real.sqrt (n:ℝ)=C*(n:ℝ)^(-(1/2:ℝ)):=by
    rw [Real.rpow_neg hnr.le (1/2),←Real.sqrt_eq_rpow]
    rfl
  calc
    _≤C*(n:ℝ)^(-θ)+C/Real.sqrt n:=add_le_add
      (mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg hnr.le _))
      (div_le_div_of_nonneg_right hSC (Real.sqrt_nonneg _))
    _=C*((n:ℝ)^(-θ)+(n:ℝ)^(-(1/2:ℝ))):=by rw [heq];ring

end RoughRegime.UpperParametric
