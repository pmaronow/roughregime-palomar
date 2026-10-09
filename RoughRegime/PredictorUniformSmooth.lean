module

public import RoughRegime.PredictorUniformConstants
public import RoughRegime.ProductDerivedSmoothLower


@[expose] public section
/-! The predictor-uniform constants of Corollary 3(b) persist on the true
C-infinity design-density subclass. The same two fixed sine anchors and
one smooth quadratic hard family work before every bounded predictor. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace RoughRegime.Applications.Products
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
 theorem uniform_smooth_excessLoss_parametric_lower (A : Model.Parameters)
     (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus) (M : ℝ) :
     ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
       ∀(f0 : Model.Covariate A.d→ℝ),Measurable f0→(∀x,|f0 x|≤M)→
       ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
         Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) := by
   let S:=sineSetup A
   obtain ⟨a,ha,hsmall⟩ := Lower.exists_small_parametric_amplitude (1/2) S.eta
   let h : ℕ→ℝ := fun n=>a/Real.sqrt (n:ℝ)
   let Dmin := S.eta^2/4
   let c := Dmin*a/4
   have hη : 0<S.eta := S.positive
   have hc : 0<c := by dsimp [c,Dmin]; positivity
   have hhzero : Tendsto h atTop (nhds 0) := by
     have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
       (tendsto_natCast_atTop_atTop : Tendsto (fun n:ℕ=>(n:ℝ)) atTop atTop))
     simpa only [h,div_eq_mul_inv,mul_zero,Function.comp_apply] using hi.const_mul a
   refine ⟨c,hc,?_⟩
   filter_upwards [hhzero.eventually_le_const (by norm_num : (0:ℝ)<1/8),eventually_gt_atTop 0]
     with n hnb hn
   intro f0 hf hb
   let B:=∫x,S.phi x*f0 x ∂Model.cubeVolume A.d
   have htchoice : ∃t0:ℝ,(t0=1/4 ∨ t0=1/2) ∧ S.eta^2/8≤|t0*S.eta^2-2*B| := by
     by_cases ht : S.eta^2/8≤|(1/4)*S.eta^2-2*B|
     · exact ⟨1/4,Or.inl rfl,ht⟩
     · refine ⟨1/2,Or.inr rfl,?_⟩
       have he : (1/2)*S.eta^2-2*B-((1/4)*S.eta^2-2*B)=S.eta^2/4 := by ring_nf
       have ht' := abs_add_le ((1/2)*S.eta^2-2*B) (-((1/4)*S.eta^2-2*B))
       simp only [←sub_eq_add_neg,abs_neg] at ht'
       rw [he,abs_of_nonneg (by positivity : 0≤S.eta^2/4)] at ht'
       linarith
   obtain ⟨t0,ht0,hD⟩ := htchoice
   have hnR : 0<(n:ℝ) := by exact_mod_cast hn
   have hnp : 0<h n := div_pos ha (Real.sqrt_pos.mpr hnR)
   have htplus : t0+h n∈Ioo (-1) 1 := by rcases ht0 with rfl | rfl <;> constructor <;> linarith
   have htminus : t0-h n∈Ioo (-1) 1 := by rcases ht0 with rfl | rfl <;> constructor <;> linarith
   have hH : (n:ℝ)*S.eta^2*(h n)^2/(1/2) ≤ 1/4 := by
     have he : (n:ℝ)*S.eta^2*(h n)^2/(1/2)=S.eta^2*a^2/(1/2) := by
       dsimp [h]
       rw [div_pow,Real.sq_sqrt hnR.le]
       field_simp
     rw [he]
     exact hsmall
   have he : excessLoss A f0 (S.probabilityLaw (t0+h n))-
       excessLoss A f0 (S.probabilityLaw (t0-h n))=2*h n*(t0*S.eta^2-2*B) := by
     rw [S.excessLoss_value f0 hf M hb,S.excessLoss_value f0 hf M hb,
       clampedParameter_eq _ ⟨htplus.1.le,htplus.2.le⟩,
       clampedParameter_eq _ ⟨htminus.1.le,htminus.2.le⟩]
     dsimp only [B]
     ring_nf
   have hsep : Dmin*h n ≤ |excessLoss A f0 (S.probabilityLaw (t0+h n))-
       excessLoss A f0 (S.probabilityLaw (t0-h n))| := by
     rw [he,abs_mul,abs_of_pos (by positivity : 0<2*h n)]
     dsimp [Dmin]
     nlinarith [mul_le_mul_of_nonneg_left hD hnp.le]
   have ht := LowerMeasure.affine_two_point_minimax S.densityLaw (fun _=>1)
     (fun o:Model.Observation A BoundedResponse=>(o.2:ℝ)*S.phi o.1)
     (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) (-1) 1 t0 (h n) Dmin (1/2) S.eta n
     (by dsimp [Dmin]; positivity) hnp (by norm_num) hη.le htplus htminus
     S.affine_density (fun t ht=>ae_of_all _ (S.affine_positive t ht))
     (ae_of_all _ S.affine_score_bound) hH
     ⟨S.quadraticClass_member hab hlo hhi _,S.probabilityLaw_mem_smoothDensityClass _⟩
     ⟨S.quadraticClass_member hab hlo hhi _,S.probabilityLaw_mem_smoothDensityClass _⟩ hsep
   have hscale : c*(n:ℝ)^(-(1/2:ℝ))=Dmin*h n/4 := by
     rw [Real.rpow_neg hnR.le,←Real.sqrt_eq_rpow]
     dsimp [c,h]
     ring_nf
   rw [hscale]
   exact ht.1


theorem uniform_smooth_excessLoss_rough_lower (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (hrough : A.theta<1/2) (M : ℝ) (hM0 : 0≤M) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ∀f0 : Model.Covariate A.d→ℝ,Measurable f0→(∀x,|f0 x|≤M)→
        ENNReal.ofReal (c*Model.lowerBracketScale A.bracketParameters n)≤
          Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) ∧
        (1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)
          (2*c*Model.lowerBracketScale A.bracketParameters n) := by
  obtain ⟨c,hc,hQ⟩ := smooth_quadratic_rough_hardness A hM hlo hhi hab hrough
  let B := 2*M+M^2
  have hB : 0≤B := by dsimp [B];positivity
  let t : ℕ→ℝ := fun n=>2*c*Model.lowerBracketScale A.bracketParameters n
  have herror := (Applications.transfer_error_tendsto_zero 1 B t
    (Model.rough_lowerBracket_squared_sample_tendsto A.bracketParameters hrough (2*c) (by positivity))).eventually_le_const
      (by norm_num : (0:ℝ≥0∞)<1/8)
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [hQ,herror,eventually_gt_atTop (1:ℕ)] with n hn herror hn1
  intro f0 hf hb
  let f := predictionContrast A f0
  have hf' : Measurable f := predictionContrast_measurable A f0 hf
  have hb' : ∀o,|f o|≤B := predictionContrast_bound A f0 M hM0 hb
  let h := scalarPilot f
  let lo : Fin 1→ℝ := fun _=>-B
  let hi : Fin 1→ℝ := fun _=>B
  let Phi : Icc (-B) (1+B)→Applications.momentRectangle lo hi→ℝ := fun a q=>(a:ℝ)+q.val 0
  have hm : ∀P : ProbabilityMeasure (Model.Observation A BoundedResponse),
      (∫o,f o ∂(P:Measure _))∈Icc (-B) B := fun P=>abs_le.mp (bounded_mean_abs P f B hb')
  have htarget : ∀P : ProbabilityMeasure (Model.Observation A BoundedResponse),
      excessLoss A f0 P∈Icc (-B) (1+B) := by
    intro P
    rw [excessLoss_identity A f0 hf M hb]
    have hq := quadraticTarget_range A P
    have hm' := hm P
    dsimp only [f] at hm'
    constructor <;> linarith [hq.1,hq.2,hm'.1,hm'.2]
  have hLip : ∀a b q r,|Phi a q-Phi b r|≤1*(|(a:ℝ)-b|+dist q r) := by
    intro a b q r
    calc
      _ ≤ |(a:ℝ)-b|+|q.val 0-r.val 0| := by
        dsimp [Phi]
        convert abs_add_le ((a:ℝ)-b) (q.val 0-r.val 0) using 1
        ring_nf
      _ ≤ |(a:ℝ)-b|+dist q r := add_le_add le_rfl (pilot_coordinate_dist q r)
      _ = _ := by ring_nf
  have ht : 0<t n := by
    have hnR : 1<(n:ℝ) := by exact_mod_cast hn1
    dsimp [t,Model.lowerBracketScale,Model.Parameters.bracketParameters]
    rw [ite_eq_left hrough]
    simpa [mul_assoc] using mul_pos (mul_pos (by positivity : 0<2*c) (Rates.scale_pos n A.theta (Rates.tau A.gminus A.gplus) hnR))
      (Real.log_pos hnR)
  have htransfer := Applications.reverse_transfer_iid_randomized KernelSeedBridge.seedLaw (by omega : n≠0)
    (fun P : ProbabilityMeasure (Model.Observation A BoundedResponse)=>(P:Measure _))
    (excessLoss A f0) (quadraticTarget A) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) h (fun _=>hf')
    (by intro P j;change MemLp f 2 (P:Measure _);exact Applications.bounded_memLp (P:Measure _) f hf' B hb')
    lo hi (fun _=>by dsimp [lo,hi];linarith) (fun P _=>hm P)
    (-B) (1+B) (by linarith) Phi
    (Applications.lipschitz_reverse_measurable _ _ Phi 1 zero_le_one hLip)
    1 (t n) 0 B zero_lt_one ht (by positivity) hLip (fun P _=>htarget P)
    (by
      intro P _
      rw [projIcc_of_mem (by linarith : -B≤1+B) (htarget P)]
      change |quadraticTarget A P-(excessLoss A f0 P+∫o,f o ∂(P:Measure _))|≤0
      rw [excessLoss_identity A f0 hf M hb]
      dsimp only [f]
      ring_nf
      simp)
    (fun P _=>scalarPilot_variance P f hf' B hb')
  change Model.minimaxTail n (quadraticTarget A) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) (t n)≤
    Model.minimaxTail n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) (t n/(4*1))+
      ENNReal.ofReal (16*1^2*B^2/((n:ℝ)*(t n)^2)) at htransfer
  have htail : (1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) (t n/(4*1)) := by
    apply ENNReal.le_of_add_le_add_right (by norm_num : (1/8:ℝ≥0∞)≠⊤)
    rw [show (1/4:ℝ≥0∞)+1/8=3/8 by
      have he := congrArg ENNReal.ofReal (show (1/4:ℝ)+1/8=3/8 by norm_num)
      rw [ENNReal.ofReal_add (by norm_num) (by norm_num)] at he
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4),
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8),
        ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using he]
    exact hn.trans (htransfer.trans (add_le_add le_rfl herror))
  have hr := Model.minimaxRMSE_lower_of_quarter_tail n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)
    (t n/(4*1)) (by positivity) htail
  constructor
  · convert hr using 1
    dsimp [t]
    congr 1
    ring_nf
  · convert htail using 1
    dsimp [t]
    congr 1
    ring_nf


theorem uniform_smooth_excessLoss_constants (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (M : ℝ) (hM0 : 0≤M) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃n0:ℕ,3≤n0 ∧
      ∀f0 : Model.Covariate A.d→ℝ,Measurable f0→(∀x,|f0 x|≤M)→
      ∀n:ℕ,n0≤n→
        ENNReal.ofReal (c*Model.lowerBracketScale A.bracketParameters n)≤
          Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) ∧
        Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)≤
          ENNReal.ofReal (C*Model.upperBracketScale A.bracketParameters (A.nu:ℝ) n) ∧
        (A.theta<1/2→(1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)
          (2*c*Model.lowerBracketScale A.bracketParameters n)) := by
  obtain ⟨C,hC,hupper⟩:=uniform_excessLoss_upper A hM
    ((le_max_left _ _).trans hlo.le) M hM0
  have hupper : ∀ᶠn:ℕ in atTop,
      ∀f0:Model.Covariate A.d→ℝ,Measurable f0→(∀x,|f0 x|≤M)→
        Model.minimaxRMSE n (excessLoss A f0)
          (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)≤
          ENNReal.ofReal (C*Model.upperBracketScale A.bracketParameters (A.nu:ℝ) n) :=
    hupper.mono (fun n hn f hf hb=>
    (Model.minimaxRMSE_mono_class n (excessLoss A f) (inter_subset_left)).trans (hn f hf hb))
  have hlower : ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ∀f0 : Model.Covariate A.d→ℝ,Measurable f0→(∀x,|f0 x|≤M)→
        ENNReal.ofReal (c*Model.lowerBracketScale A.bracketParameters n)≤
          Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) ∧
        (A.theta<1/2→(1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)
          (2*c*Model.lowerBracketScale A.bracketParameters n)) := by
    by_cases hrough:A.theta<1/2
    · obtain ⟨c,hc,he⟩:=uniform_smooth_excessLoss_rough_lower A hM hlo hhi hab hrough M hM0
      exact ⟨c,hc,he.mono (fun n hn f hf hb=>⟨(hn f hf hb).1,fun _=>(hn f hf hb).2⟩)⟩
    · obtain ⟨c,hc,he⟩:=uniform_smooth_excessLoss_parametric_lower A hab
        ((le_max_right _ _).trans hlo.le) hhi.le M
      refine ⟨c,hc,he.mono ?_⟩
      intro n hn f hf hb
      refine ⟨?_,fun h=>False.elim (hrough h)⟩
      simpa only [Model.lowerBracketScale,Model.Parameters.bracketParameters,ite_eq_right hrough]
        using hn f hf hb
  obtain ⟨c,hc,hlower⟩:=hlower
  obtain ⟨n0,hn0⟩:=eventually_atTop.mp (hlower.and hupper)
  refine ⟨c,C,hc,hC,max 3 n0,le_max_left _ _,?_⟩
  intro f hf hb n hn
  have he:=hn0 n ((le_max_right _ _).trans hn)
  exact ⟨(he.1 f hf hb).1,he.2 f hf hb,(he.1 f hf hb).2⟩

/-- The common constants need only the predictor's bound on the source cube;
values outside the cube do not alter any model target. -/
theorem uniform_smooth_excessLoss_constants_cube (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (M : ℝ) (hM0 : 0≤M) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃n0:ℕ,3≤n0 ∧
      ∀f0 : Model.Covariate A.d→ℝ,Measurable f0→(∀x∈Model.cube A.d,|f0 x|≤M)→
      ∀n:ℕ,n0≤n→
        ENNReal.ofReal (c*Model.lowerBracketScale A.bracketParameters n)≤
          Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) ∧
        Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)≤
          ENNReal.ofReal (C*Model.upperBracketScale A.bracketParameters (A.nu:ℝ) n) ∧
        (A.theta<1/2→(1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)
          (2*c*Model.lowerBracketScale A.bracketParameters n)) := by
  obtain ⟨c,C,hc,hC,n0,hn0,he⟩:=uniform_smooth_excessLoss_constants A hM hlo hhi hab M hM0
  refine ⟨c,C,hc,hC,n0,hn0,?_⟩
  intro f0 hf hb n hn
  let f:=(Model.cube A.d).indicator f0
  have hcube:MeasurableSet (Model.cube A.d):=(Model.isCompact_cube A.d).isClosed.measurableSet
  have hfb:∀x,|f x|≤M := by
    intro x
    by_cases hx:x∈Model.cube A.d
    · simpa only [f,indicator_of_mem hx] using hb x hx
    · simpa only [f,indicator_of_notMem hx,abs_zero] using hM0
  have htarget:∀P∈(quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse),excessLoss A f0 P=excessLoss A f P := by
    intro P hP
    apply integral_congr_ae
    filter_upwards [quadraticClass_covariate_cube A P hP.1] with o ho
    simp only [f,indicator_of_mem ho]
  rw [Model.minimaxRMSE_congr_target n (excessLoss A f0) (excessLoss A f) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) htarget,
    Model.minimaxTail_congr_target n (excessLoss A f0) (excessLoss A f) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) _ htarget]
  exact he f (hf.indicator hcube) hfb n hn

end RoughRegime.Applications.Products
