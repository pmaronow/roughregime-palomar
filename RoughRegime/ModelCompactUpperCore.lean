module

public import RoughRegime.ModelCompactProductRates
public import RoughRegime.ModelUpper


@[expose] public section
/-! Statistical and numerical compact-family assembly for the actual
randomized experiment. The finite polynomial population/variance bounds
are supplied by the model's concrete approximation lemmas. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def CompactUniformUpperClaim (A:Parameters)(G:Set (ℝ×ℝ))
    (hdom:G⊆densityIntervalDomain)(L MW:ℝ) : Prop :=
  ∃C:ℝ,0<C ∧ ∃n0:ℕ,3≤n0 ∧ ∀I(hI:I∈G),
    let B:=densityParameters A I (hdom hI)
    ∀(Z:Type u)(mZ:MeasurableSpace Z)(F:@Observables Z mZ B),
      |F.lam|=L→(∀z,|F.W z|≤MW)→UpperBoundAt B F C n0

theorem compact_uniformUpperClaim_ordered_parametric_of_finite
    (A:Parameters)(hαβ:A.α≤A.β)(hθ:1/2≤A.theta)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain)
    (Cb Cv Cproj:ℝ)(hCb:1≤Cb)(hCv:1≤Cv)(hCproj:0<Cproj)
    (hfinite:CompactProductRisk.{u} A hαβ G hdom Cb Cv Cproj)(L MW:ℝ) :
    CompactUniformUpperClaim.{u} A G hdom L MW := by
  obtain ⟨D,Cp,hD,hCp,hprod⟩:=compact_parametricProductEstimator_risk_from_finite.{u}
    A hαβ hθ G hG hdom Cb Cv Cproj hCb hCv hCproj hfinite
  obtain ⟨n0,hn0⟩:=eventually_atTop.mp hprod
  let C:=|MW|+|L| *Cp+1
  refine ⟨C,by dsimp [C];positivity,max 3 n0,le_max_left _ _,?_⟩
  intro I hI
  dsimp only
  intro Z mZ F hL hMW n hn _
  let B:=densityParameters A I (hdom hI)
  have hn3:3≤n:=(le_max_left _ _).trans hn
  have hnN:n0≤n:=(le_max_right _ _).trans hn
  have hnp:0<n:=by omega
  refine ⟨fun _=>?_,fun hsub=>False.elim (by
    change 0<A.theta ∧ A.theta<1/2 at hsub
    linarith [hsub.2])⟩
  let E:=compactParametricProductEstimator B hαβ F D Cv n
  have hE:Measurable E:=by
    dsimp [E,compactParametricProductEstimator]
    exact productEstimator_measurable _ _ _ _ _ _
  apply minimaxRMSE_le_fixed_estimator n (target B F) (modelClass B F) (combinedEstimator B F n E hE)
  intro P hP
  obtain ⟨W⟩:=hP
  have hmem:MemLp E 2 (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z)))):=by
    dsimp [E,compactParametricProductEstimator]
    exact productEstimator_memLp _ _ _ _ _ _ _
  have hc:=combinedEstimator_eLpNorm_error B F P W n hnp E hE hmem MW hMW
  have hp:=hn0 n hnN I hI Z F P W
  have hlam:|F.lam|≤|L|:=by rw [hL];exact le_abs_self _
  apply hc.trans
  apply ENNReal.ofReal_le_ofReal
  have hm:=mul_le_mul_of_nonneg_left hp (abs_nonneg F.lam)
  have hmul:=mul_le_mul_of_nonneg_right hlam (div_nonneg hCp.le (Real.sqrt_nonneg (n:ℝ)))
  have hnum:|MW| /Real.sqrt (n:ℝ)+|F.lam| *lpNorm (fun xs=>E xs-W.productTarget) 2
      (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z))))≤(|MW|+|L| *Cp)/Real.sqrt n := by
    calc
      _≤|MW| /Real.sqrt n+|L| *(Cp/Real.sqrt n):=add_le_add le_rfl (hm.trans hmul)
      _=_:=by ring
  have ht:=div_le_div_of_nonneg_right (show |MW|+|L| *Cp≤C by dsimp [C];linarith)
    (Real.sqrt_nonneg (n:ℝ))
  have heq:C/Real.sqrt (n:ℝ)=C*(n:ℝ)^(-(1/2:ℝ)):=by
    rw [Real.rpow_neg (Nat.cast_nonneg _) (1/2),←Real.sqrt_eq_rpow]
    rfl
  exact hnum.trans (ht.trans_eq heq)

theorem compact_rootN_le_subcriticalRate_eventually (A:Parameters)(hθ:A.theta<1/2)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain) :
    ∀ᶠn:ℕ in atTop,∀I∈G,1/Real.sqrt (n:ℝ)≤
      UpperSubcritical.rate n A.theta (Rates.tau I.1 I.2) A.nu := by
  obtain ⟨τlo,τhi,_,_,hτ⟩:=compact_density_tau_bounds G hG hdom
  have he:=tendsto_natCast_atTop_atTop.eventually
    (UpperSubcritical.lowVariance_relative_rate_uniform A.theta τhi A.nu A.theta_pos hθ)
  have hlog:=tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  filter_upwards [he,hlog] with n hn hL
  intro I hI
  have hpow:1≤(Real.log (n:ℝ))^(3/2:ℝ):=Real.one_le_rpow hL (by norm_num)
  exact (div_le_div_of_nonneg_right hpow (Real.sqrt_nonneg _)).trans (hn _ (hτ I hI).2)

theorem compact_uniformUpperClaim_ordered_subcritical_of_finite
    (A:Parameters)(hαβ:A.α≤A.β)(hθ:A.theta<1/2)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain)
    (Cb Cv Cproj:ℝ)(hCb:1≤Cb)(hCv:1≤Cv)(hCproj:0<Cproj)
    (hfinite:CompactProductRisk.{u} A hαβ G hdom Cb Cv Cproj)(L MW:ℝ) :
    CompactUniformUpperClaim.{u} A G hdom L MW := by
  obtain ⟨D,Cp,hD,hCp,hprod⟩:=compact_subcriticalProductEstimator_risk_from_finite.{u}
    A hαβ hθ G hG hdom Cb Cv Cproj hCb hCv hCproj hfinite
  obtain ⟨n0,hn0⟩:=eventually_atTop.mp
    (hprod.and (compact_rootN_le_subcriticalRate_eventually A hθ G hG hdom))
  let C:=|MW|+|L| *Cp+1
  refine ⟨C,by dsimp [C];positivity,max 3 n0,le_max_left _ _,?_⟩
  intro I hI
  dsimp only
  intro Z mZ F hL hMW n hn _
  let B:=densityParameters A I (hdom hI)
  have hn3:3≤n:=(le_max_left _ _).trans hn
  have hnN:n0≤n:=(le_max_right _ _).trans hn
  have hnp:0<n:=by omega
  let τ:=Rates.tau I.1 I.2
  let r:=UpperSubcritical.rate n A.theta τ A.nu
  have hrp:0<r:=UpperSubcritical.rate_positive n A.theta τ A.nu
    (by exact_mod_cast (show 1<n by omega))
  refine ⟨fun hcrit=>False.elim (by
    change 1/2≤A.theta at hcrit
    linarith),fun _=>?_⟩
  let E:=compactSubcriticalProductEstimator B hαβ F D Cv n
  have hE:Measurable E:=by
    dsimp [E,compactSubcriticalProductEstimator]
    exact productEstimator_measurable _ _ _ _ _ _
  apply minimaxRMSE_le_fixed_estimator n (target B F) (modelClass B F) (combinedEstimator B F n E hE)
  intro P hP
  obtain ⟨W⟩:=hP
  have hmem:MemLp E 2 (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z)))):=by
    dsimp [E,compactSubcriticalProductEstimator]
    exact productEstimator_memLp _ _ _ _ _ _ _
  have hc:=combinedEstimator_eLpNorm_error B F P W n hnp E hE hmem MW hMW
  have hp:=(hn0 n hnN).1 I hI Z F P W
  have hroot:=(hn0 n hnN).2 I hI
  have hlam:|F.lam|≤|L|:=by rw [hL];exact le_abs_self _
  apply hc.trans
  apply ENNReal.ofReal_le_ofReal
  have hw:|MW| /Real.sqrt (n:ℝ)≤|MW| *r:=by
    convert mul_le_mul_of_nonneg_left hroot (abs_nonneg MW) using 1
    ring
  have hm:=mul_le_mul_of_nonneg_left hp (abs_nonneg F.lam)
  have hmul:=mul_le_mul_of_nonneg_right hlam (mul_nonneg hCp.le hrp.le)
  have hnum:|MW| /Real.sqrt (n:ℝ)+|F.lam| *lpNorm (fun xs=>E xs-W.productTarget) 2
      (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z))))≤C*r := by
    calc
      _≤|MW| *r+|L| *(Cp*r):=add_le_add hw (hm.trans hmul)
      _=(|MW|+|L| *Cp)*r:=by ring
      _≤C*r:=mul_le_mul_of_nonneg_right (by dsimp [C];linarith) hrp.le
  have heq:=UpperSubcritical.rate_eq_paper_scale n A.theta τ A.nu
    (by exact_mod_cast (show 1<n by omega))
  dsimp only [r] at hnum
  rw [heq] at hnum
  simpa only [mul_assoc,densityParameters_theta,densityParameters_nu,
    densityParameters_lo,densityParameters_hi] using hnum

theorem compact_uniformUpperClaim_ordered_of_finite
    (A:Parameters)(hαβ:A.α≤A.β)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain)
    (Cb Cv Cproj:ℝ)(hCb:1≤Cb)(hCv:1≤Cv)(hCproj:0<Cproj)
    (hfinite:CompactProductRisk.{u} A hαβ G hdom Cb Cv Cproj)(L MW:ℝ) :
    CompactUniformUpperClaim.{u} A G hdom L MW := by
  by_cases hθ:1/2≤A.theta
  · exact compact_uniformUpperClaim_ordered_parametric_of_finite A hαβ hθ G hG hdom
      Cb Cv Cproj hCb hCv hCproj hfinite L MW
  · exact compact_uniformUpperClaim_ordered_subcritical_of_finite A hαβ (lt_of_not_ge hθ) G hG hdom
      Cb Cv Cproj hCb hCv hCproj hfinite L MW

theorem compact_uniformUpperClaim_of_swap (A:Parameters)(G:Set (ℝ×ℝ))
    (hdom:G⊆densityIntervalDomain)(L MW:ℝ)
    (h:CompactUniformUpperClaim.{u} A.swap G hdom L MW) :
    CompactUniformUpperClaim.{u} A G hdom L MW := by
  obtain ⟨C,hC,n0,hn0,hu⟩:=h
  refine ⟨C,hC,n0,hn0,?_⟩
  intro I hI
  dsimp only
  intro Z mZ F hL hMW
  exact (upperBoundAt_swap F C n0).mp (hu I hI Z mZ F.swap hL hMW)


theorem compact_eventual_basic_minimax_of_finite
    (A:Parameters)(hαβ:A.α≤A.β)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain)
    (Cb Cv Cproj:ℝ)(hCb:1≤Cb)(hCv:1≤Cv)(hCproj:0<Cproj)
    (hfinite:CompactProductRisk.{u} A hαβ G hdom Cb Cv Cproj)(L MW:ℝ) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀I(hI:I∈G),
      let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z B),
      |F.lam|=L→(∀z,|F.W z|≤MW)→
      minimaxRMSE n (target B F) (modelClass B F)≤
        ENNReal.ofReal (C*((n:ℝ)^(-(1/2:ℝ))+(n:ℝ)^(-A.theta))) := by
  obtain ⟨D,Cp,hD,hCp,hprod⟩:=compact_basicProductEstimator_risk_from_finite.{u}
    A hαβ G hG hdom Cb Cv Cproj hCb hCv hCproj hfinite
  let C:=|MW|+|L| *Cp+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [hprod,eventually_ge_atTop (3:ℕ)] with n hn hn3
  intro I hI
  dsimp only
  intro Z mZ F hL hMW
  let B:=densityParameters A I (hdom hI)
  have hnp:0<n:=by omega
  let r:=(n:ℝ)^(-A.theta)+(n:ℝ)^(-(1/2:ℝ))
  have hr:0≤r:=by dsimp [r];positivity
  let E:=compactParametricProductEstimator B hαβ F D Cv n
  have hE:Measurable E:=by
    dsimp [E,compactParametricProductEstimator]
    exact productEstimator_measurable _ _ _ _ _ _
  apply minimaxRMSE_le_fixed_estimator n (target B F) (modelClass B F) (combinedEstimator B F n E hE)
  intro P hP
  obtain ⟨W⟩:=hP
  have hmem:MemLp E 2 (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z)))):=by
    dsimp [E,compactParametricProductEstimator]
    exact productEstimator_memLp _ _ _ _ _ _ _
  have hc:=combinedEstimator_eLpNorm_error B F P W n hnp E hE hmem MW hMW
  have hp:=hn I hI Z F P W
  have hlam:|F.lam|≤|L|:=by rw [hL];exact le_abs_self _
  apply hc.trans
  apply ENNReal.ofReal_le_ofReal
  have hroot:|MW| /Real.sqrt (n:ℝ)=|MW| *(n:ℝ)^(-(1/2:ℝ)):=by
    rw [Real.rpow_neg (Nat.cast_nonneg _) (1/2),←Real.sqrt_eq_rpow]
    rfl
  have hw:|MW| /Real.sqrt (n:ℝ)≤|MW| *r:=by
    rw [hroot]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (abs_nonneg _)
  have hm:=mul_le_mul_of_nonneg_left hp (abs_nonneg F.lam)
  have hmul:=mul_le_mul_of_nonneg_right hlam (mul_nonneg hCp.le hr)
  calc
    _≤|MW| *r+|L| *(Cp*r):=add_le_add hw (hm.trans hmul)
    _=(|MW|+|L| *Cp)*r:=by ring
    _≤C*r:=mul_le_mul_of_nonneg_right (by dsimp [C];linarith) hr
    _=C*((n:ℝ)^(-(1/2:ℝ))+(n:ℝ)^(-A.theta)):=by dsimp [r];ring

end RoughRegime.Model
