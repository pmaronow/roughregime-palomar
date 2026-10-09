module

public import RoughRegime.ProductDerivedLower


@[expose] public section
/-! Common excess-loss bracket constants, chosen before every measurable
predictor satisfying the same numerical bound. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace RoughRegime.Model

theorem minimaxRMSE_lower_of_quarter_tail {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (t : ℝ) (ht : 0≤t) (hp : (1/4:ℝ≥0∞)≤ minimaxTail n T C t) :
    ENNReal.ofReal (t/2)≤ minimaxRMSE n T C := by
  rw [minimaxRMSE_eq_squaredRisk]
  have hm : ENNReal.ofReal ((t/2)^2)≤Applications.minimaxMSE (randomizedExperiment n) T C := by
    calc
      _ = ENNReal.ofReal (t^2)*(1/4:ℝ≥0∞) := by
        rw [show (t/2)^2=t^2*(1/4:ℝ) by ring,ENNReal.ofReal_mul (sq_nonneg _)]
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
        norm_num
      _ ≤ ENNReal.ofReal (t^2)*minimaxTail n T C t := by gcongr
      _ ≤ _ := Applications.minimaxMSE_lower_of_tail (randomizedExperiment n) T C t ht
  unfold Applications.minimaxRMSE
  have hh := (ENNReal.le_rpow_inv_iff (x:=ENNReal.ofReal (t/2))
    (y:=Applications.minimaxMSE (randomizedExperiment n) T C) (by norm_num : (0:ℝ)<2)).mpr
  have hh' : ENNReal.ofReal (t/2)^(2:ℝ) ≤ Applications.minimaxMSE (randomizedExperiment n) T C := by
    rw [ENNReal.rpow_two]
    rw [ENNReal.ofReal_pow (by positivity : 0≤t/2) 2] at hm
    exact hm
  simpa only [one_div] using hh hh' 

end RoughRegime.Model

namespace RoughRegime.Applications.Products

theorem uniform_excessLoss_upper (A : Model.Parameters) (hM : 1≤A.M0) (hd : A.δ≤1)
    (M : ℝ) (hM0 : 0≤M) :
    ∃K:ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      ∀f0 : Model.Covariate A.d→ℝ,Measurable f0→(∀x,|f0 x|≤M)→
        Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A)≤
          ENNReal.ofReal (K*Model.upperBracketScale A.bracketParameters (A.nu:ℝ) n) := by
  obtain ⟨_,K,hK,n0,_,hQ⟩ := quadratic_upperBracket A hM hd
  let B := 2*M+M^2
  have hB : 0≤B := by dsimp [B];positivity
  have hroot : ∀ᶠ n : ℕ in atTop,(n:ℝ)^(-(1/2:ℝ))≤
      Model.upperBracketScale A.bracketParameters (A.nu:ℝ) n :=
    tendsto_natCast_atTop_atTop.eventually (RateCombination.rootN_eventually_le
      A.theta (Rates.tau A.gminus A.gplus) (A.nu:ℝ))
  refine ⟨K+B,by linarith,?_⟩
  filter_upwards [eventually_ge_atTop n0,hroot,eventually_gt_atTop (1:ℕ)] with n hn hroot hn1
  intro f0 hf hb
  have hdiff := Model.difference_minimax n (excessLoss A f0) (quadraticTarget A)
    (fun P=>∫o,predictionContrast A f0 o ∂(P:Measure (Model.Observation A BoundedResponse)))
    (quadraticClass A) (fun P _=>excessLoss_identity A f0 hf M hb P)
  have hmean := Model.observableMean_minimax n (by omega) (predictionContrast A f0)
    (predictionContrast_measurable A f0 hf) B hB (predictionContrast_bound A f0 M hM0 hb)
    (quadraticClass A)
  have hrate : 0≤Model.upperBracketScale A.bracketParameters (A.nu:ℝ) n :=
    (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hroot
  apply hdiff.trans ((add_le_add (hQ n hn) hmean).trans _)
  rw [←ENNReal.ofReal_add (mul_nonneg hK.le hrate) (div_nonneg hB (Real.sqrt_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  have hBroot : B/Real.sqrt (n:ℝ)≤B*Model.upperBracketScale A.bracketParameters (A.nu:ℝ) n := by
    rw [div_eq_mul_inv,Real.sqrt_eq_rpow,←Real.rpow_neg (Nat.cast_nonneg n)]
    exact mul_le_mul_of_nonneg_left hroot hB
  nlinarith

theorem uniform_excessLoss_rough_lower (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (hrough : A.theta<1/2) (M : ℝ) (hM0 : 0≤M) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ∀f0 : Model.Covariate A.d→ℝ,Measurable f0→(∀x,|f0 x|≤M)→
        ENNReal.ofReal (c*Model.lowerBracketScale A.bracketParameters n)≤
          Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A) ∧
        (1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A)
          (2*c*Model.lowerBracketScale A.bracketParameters n) := by
  obtain ⟨c,hc,hQ⟩ := quadratic_rough_hardness A hM hlo hhi hab hrough
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
        dsimp [Phi];convert abs_add_le ((a:ℝ)-b) (q.val 0-r.val 0) using 1 <;> ring
      _ ≤ |(a:ℝ)-b|+dist q r := add_le_add le_rfl (pilot_coordinate_dist q r)
      _ = _ := by ring
  have ht : 0<t n := by
    have hnR : 1<(n:ℝ) := by exact_mod_cast hn1
    dsimp [t,Model.lowerBracketScale,Model.Parameters.bracketParameters]
    rw [ite_eq_left hrough]
    simpa [mul_assoc] using mul_pos (mul_pos (by positivity : 0<2*c) (Rates.scale_pos n A.theta (Rates.tau A.gminus A.gplus) hnR))
      (Real.log_pos hnR)
  have htransfer := Applications.reverse_transfer_iid_randomized KernelSeedBridge.seedLaw (by omega : n≠0)
    (fun P : ProbabilityMeasure (Model.Observation A BoundedResponse)=>(P:Measure _))
    (excessLoss A f0) (quadraticTarget A) (quadraticClass A) h (fun _=>hf')
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
  change Model.minimaxTail n (quadraticTarget A) (quadraticClass A) (t n)≤
    Model.minimaxTail n (excessLoss A f0) (quadraticClass A) (t n/(4*1))+
      ENNReal.ofReal (16*1^2*B^2/((n:ℝ)*(t n)^2)) at htransfer
  have htail : (1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A) (t n/(4*1)) := by
    apply ENNReal.le_of_add_le_add_right (by norm_num : (1/8:ℝ≥0∞)≠⊤)
    rw [show (1/4:ℝ≥0∞)+1/8=3/8 by
      have he := congrArg ENNReal.ofReal (show (1/4:ℝ)+1/8=3/8 by norm_num)
      rw [ENNReal.ofReal_add (by norm_num) (by norm_num)] at he
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4),
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8),
        ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using he]
    exact hn.trans (htransfer.trans (add_le_add le_rfl herror))
  have hr := Model.minimaxRMSE_lower_of_quarter_tail n (excessLoss A f0) (quadraticClass A)
    (t n/(4*1)) (by positivity) htail
  constructor
  · convert hr using 1 <;> dsimp [t] <;> congr 1 <;> ring
  · convert htail using 1 <;> dsimp [t] <;> congr 1 <;> ring

end RoughRegime.Applications.Products
