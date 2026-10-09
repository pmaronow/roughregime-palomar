module

public import RoughRegime.ModelUpper
public import RoughRegime.HolderGeometry
public import RoughRegime.PolynomialDimensionOne


@[expose] public section
/-! The all-sample basic upper bound stated before the sharp upper proof.
The constants remain uniform over all response spaces and all observables
with fixed numerical parameters. For the finite initial sample sizes a
bounded constant estimate suffices; the proved sharp construction supplies
the eventually smaller error. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace RoughRegime.Model
universe u
set_option backward.isDefEq.respectTransparency false

 def basicUpperScale (A : Parameters) (n : ℕ) : ℝ :=
   (n:ℝ)^(-(1/2:ℝ))+(n:ℝ)^(-A.theta)

 theorem basicUpperScale_nonneg (A : Parameters) (n : ℕ) : 0≤basicUpperScale A n := by
   unfold basicUpperScale
   positivity

 theorem basicUpperScale_pos (A : Parameters) (n : ℕ) (hn : 0<n) : 0<basicUpperScale A n := by
   unfold basicUpperScale
   exact add_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

 theorem target_uniform_bound (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
     (MW : ℝ) (hMW : ∀z,|F.W z|≤MW) :
     |target A F P|≤|MW|+|F.lam| *A.H^2*A.gplus := by
   have hmean : |∫ o,F.W o.2 ∂(P:Measure (Observation A Z))|≤|MW| := by
     have he := norm_integral_le_of_norm_le_const (μ:=(P:Measure (Observation A Z)))
       (f:=fun o=>F.W o.2) (C:=|MW|) (ae_of_all _ (fun o=>by
         simpa only [Real.norm_eq_abs] using (hMW o.2).trans (le_abs_self MW)))
     simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using he
   have hpoint : ∀ᵐx ∂cubeVolume A.d,‖W.a x*W.b x*(W.w x*W.p x)‖≤A.H^2*A.gplus := by
     filter_upwards [ae_restrict_mem (isCompact_cube A.d).isClosed.measurableSet,W.densityBounds] with x hx hg
     have ha := holderNorm_bounds_values W.a A.α A.H A.hH.le W.smoothA x hx
     have hb := holderNorm_bounds_values W.b A.β A.H A.hH.le W.smoothB x hx
     rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (A.hgminus.trans_le hg.1).le]
     have hh := mul_le_mul (mul_le_mul ha hb (abs_nonneg _) A.hH.le) hg.2
       (A.hgminus.trans_le hg.1).le (mul_nonneg A.hH.le A.hH.le)
     simpa only [pow_two] using hh
   have hprod : |∫x,W.a x*W.b x*(W.w x*W.p x) ∂cubeVolume A.d|≤A.H^2*A.gplus := by
     simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hpoint
   rw [target_weighted_representation A F P W]
   calc
     _ ≤ |∫ o,F.W o.2 ∂(P:Measure (Observation A Z))|+|F.lam| *
       |∫x,W.a x*W.b x*(W.w x*W.p x) ∂cubeVolume A.d| := by rw [←abs_mul]; exact abs_add_le _ _
     _ ≤ |MW|+|F.lam| *(A.H^2*A.gplus) := add_le_add hmean (mul_le_mul_of_nonneg_left hprod (abs_nonneg _))
     _ = _ := by ring

 theorem subcritical_upper_relative_basic_tendsto (A : Parameters) (hrough : A.theta<1/2) :
     Tendsto (fun n:ℕ => RoughRegime.UpperSubcritical.rate n A.theta
       (Rates.tau A.gminus A.gplus) A.nu/(n:ℝ)^(-A.theta)) atTop (𝓝 0) := by
   let p : ℝ := A.theta/2+(A.nu:ℝ)/2+1/4
   let kap : ℝ := Rates.kappa A.theta (Rates.tau A.gminus A.gplus)
   have hkap : 0<kap := Rates.kappa_pos A.theta (Rates.tau A.gminus A.gplus)
     A.theta_pos hrough A.tau_pos
   have he := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*p) kap hkap).comp
     (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
   apply he.congr'
   filter_upwards [eventually_gt_atTop (1:ℕ)] with n hn
   have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
   have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
   have hs : (Real.sqrt (Real.log (n:ℝ)))^(2*p)=(Real.log (n:ℝ))^p := by
     rw [Real.sqrt_eq_rpow,←Real.rpow_mul hl.le]
     congr 1
     ring
   simp only [Function.comp_apply]
   rw [hs]
   unfold RoughRegime.UpperSubcritical.rate
   dsimp only [p,kap]
   field_simp [(Real.rpow_pos_of_pos hn0 (-A.theta)).ne']

 theorem uniform_eventual_basic_upper (A : Parameters) (L MW : ℝ) :
     ∃C:ℝ,0<C ∧ ∃N:ℕ,3≤N ∧
       ∀(Z:Type u)(mZ:MeasurableSpace Z)(F:@Observables Z mZ A),
       |F.lam|=L → (∀z,|F.W z|≤MW) → ∀n:ℕ,N≤n →
       minimaxRMSE n (target A F) (modelClass A F)≤ENNReal.ofReal (C*basicUpperScale A n) := by
   obtain ⟨C,hC,N,hN,hupper⟩ := uniformUpperClaim.{u} A L MW
   by_cases hrough : A.theta<1/2
   · have he := (subcritical_upper_relative_basic_tendsto A hrough).eventually
       (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))
     obtain ⟨N1,hN1⟩ := eventually_atTop.mp he
     refine ⟨C,hC,max N N1,hN.trans (le_max_left _ _),?_⟩
     intro Z mZ F hL hMW n hn
     by_cases hnonempty : (modelClass A F).Nonempty
     · have hu := (hupper Z mZ F hL hMW n ((le_max_left _ _).trans hn) hnonempty).2 ⟨A.theta_pos,hrough⟩
       apply hu.trans
       apply ENNReal.ofReal_le_ofReal
       have hnp : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
       have hb := (div_lt_one (Real.rpow_pos_of_pos hnp (-A.theta))).mp (hN1 n ((le_max_right _ _).trans hn))
       have hn1 : 1<(n:ℝ) := by exact_mod_cast (show 1<n by omega)
       rw [mul_assoc,←RoughRegime.UpperSubcritical.rate_eq_paper_scale n A.theta (Rates.tau A.gminus A.gplus) A.nu hn1]
       apply mul_le_mul_of_nonneg_left _ hC.le
       exact hb.le.trans (le_add_of_nonneg_left (by positivity))
     · have hc : modelClass A F=∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
       simp [hc,minimaxRMSE]
   · refine ⟨C,hC,N,hN,?_⟩
     intro Z mZ F hL hMW n hn
     by_cases hnonempty : (modelClass A F).Nonempty
     · have hu := (hupper Z mZ F hL hMW n hn hnonempty).1 (le_of_not_gt hrough)
       exact hu.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
         (le_add_of_nonneg_right (by positivity : 0≤(n:ℝ)^(-A.theta))) hC.le))
     · have hc : modelClass A F=∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
       simp [hc,minimaxRMSE]

 theorem uniform_basic_upper (A : Parameters) (L MW : ℝ) :
     ∃C:ℝ,0<C ∧
       ∀(Z:Type u)(mZ:MeasurableSpace Z)(F:@Observables Z mZ A),
       |F.lam|=L → (∀z,|F.W z|≤MW) → ∀n:ℕ,3≤n →
       ∃E:Estimator (Observation A Z) n,
       ∀P∈modelClass A F,eLpNorm (fun o=>E.val o-target A F P) 2 (randomizedExperiment n P)≤
         ENNReal.ofReal (C*basicUpperScale A n) := by
   obtain ⟨C,hC,N,hN,hupper⟩ := uniform_eventual_basic_upper.{u} A L MW
   have hgp : 0<A.gplus := A.hgminus.trans A.hgplus
   let B := |MW|+|L| *A.H^2*A.gplus
   have hB : 0≤B := by dsimp [B]; positivity
   let C0 := C+1+∑k∈Finset.range N,B/basicUpperScale A k
   have hsum : 0≤∑k∈Finset.range N,B/basicUpperScale A k :=
     Finset.sum_nonneg (fun k _=>div_nonneg hB (basicUpperScale_nonneg A k))
   have hC0 : 0<C0 := by dsimp [C0]; linarith
   refine ⟨2*C0,by positivity,?_⟩
   intro Z mZ F hL hMW n hn
   have hr := basicUpperScale_pos A n (by omega)
   have hb : minimaxRMSE n (target A F) (modelClass A F)≤ENNReal.ofReal (C0*basicUpperScale A n) := by
     by_cases hNn : N≤n
     · exact (hupper Z mZ F hL hMW n hNn).trans (ENNReal.ofReal_le_ofReal
         (mul_le_mul_of_nonneg_right (by dsimp [C0]; linarith) hr.le))
     · let E : Estimator (Observation A Z) n := ⟨fun _=>0,measurable_const⟩
       apply minimaxRMSE_le_fixed_estimator n _ _ E
       intro P hP
       obtain ⟨W⟩ := hP
       have ht := target_uniform_bound A F P W MW hMW
       have hLabs : |L|=L := by rw [←hL,abs_abs]
       have htB : |target A F P|≤B := by simpa only [hL,hLabs,B] using ht
       have hquot : B/basicUpperScale A n≤C0 := by
         have ht := Finset.single_le_sum (s:=Finset.range N)
           (fun k _=>div_nonneg hB (basicUpperScale_nonneg A k)) (Finset.mem_range.mpr (lt_of_not_ge hNn))
         dsimp [C0]
         linarith
       have hscale : B≤C0*basicUpperScale A n := (div_le_iff₀ hr).mp hquot
       let : IsProbabilityMeasure (randomizedExperiment n P) := by
         change IsProbabilityMeasure ((Measure.pi (fun _ :Fin n=>(P:Measure (Observation A Z)))).prod KernelSeedBridge.seedLaw)
         infer_instance
       have he := eLpNorm_le_of_ae_bound (μ:=randomizedExperiment n P) (p:=(2:ℝ≥0∞))
         (f:=fun o=>E.val o-target A F P) (by change AEStronglyMeasurable (fun _=>0-target A F P) _;exact aestronglyMeasurable_const)
         (ae_of_all _ (fun _=>by simpa [E,Real.norm_eq_abs] using htB.trans hscale))
       simpa only [measure_univ,ENNReal.one_rpow,one_mul] using he
   have hlt : minimaxRMSE n (target A F) (modelClass A F)<ENNReal.ofReal ((2*C0)*basicUpperScale A n) :=
     hb.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0<(2*C0)*basicUpperScale A n)).mpr
       (by nlinarith [mul_pos hC0 hr]))
   change (⨅E:Estimator (Observation A Z) n,⨆P,⨆hP:P∈modelClass A F,
     eLpNorm (fun o=>E.val o-target A F P) 2 (randomizedExperiment n P))<_ at hlt
   obtain ⟨E,hE⟩ := iInf_lt_iff.mp hlt
   refine ⟨E,fun P hP=>?_⟩
   apply le_trans _ hE.le
   exact le_iSup_of_le P (le_iSup_of_le hP le_rfl)

end RoughRegime.Model
