module

public import RoughRegime.SmoothDensityLower
public import RoughRegime.ApplicationOverlapSelected
public import RoughRegime.ApplicationOverlapReduction
public import RoughRegime.ApplicationOverlapUpper
public import RoughRegime.ApplicationOverlapScale
public import RoughRegime.SourceRoughSequence
public import RoughRegime.ModelEventualHardness


@[expose] public section
/-! The actual independent-wave source laws give the rough lower overlap
bracket. Their cubic ratio error vanishes relative to the true hard scale. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Overlap
open RoughRegime.LatticePriors RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

 def smoothIndependentHardClass (A : Model.Parameters) (ε r : ℝ) (n : ℕ) :=
  {P | P∈(modelClass A ε ∩ Model.smoothDensityClass A.d Response) ∧ |numerator A.d P-effect A.d P/4|≤ independentErrorEnvelope A.α A.β r A.d n}
 theorem smooth_independent_rough_lower (A0 : Model.Parameters) (D : ℕ) (ε : ℝ)
    (hε : 0<ε) (hεhalf : ε<1/2) (hM : 1≤A0.M0) (hlo : max A0.δ A0.gminus<1)
    (hhi : 1<A0.gplus) (hH : 1/2<A0.H) (hab : A0.β≤A0.α)
    (hrough : (bracketParameters (A0.withDimension D)).theta<1/2) :
    Model.LowerBracket (effect (D+1)) ((modelClass (A0.withDimension D) ε ∩ Model.smoothDensityClass (D+1) Response))
      (bracketParameters (A0.withDimension D)) := by
  let A:=A0.withDimension D
  obtain ⟨F,hF,hS,he⟩:=independent_selected_family A0 D ε hεhalf hM hlo hhi hH
  let θ:=A.theta
  let τ:=Rates.tau F.rminus F.rplus
  have hθ : 0<θ:=A.theta_pos
  have hτ : 0<τ:=Rates.tau_pos _ _ F.interval.1 (F.interval.2.1.trans F.interval.2.2)
  have hθeq : (bracketParameters A).theta=θ := by
    change (A0.α+min A0.α A0.β)/(D+1:ℕ)=(A0.α+A0.β)/(D+1:ℕ)
    rw [min_eq_right hab]
  have hrough' : θ<1/2 := by rw [← hθeq];exact hrough
  let U : ℕ→ℝ:=fun n=>(n:ℝ)^(-(A0.α/(D+1:ℕ)))/F.rminus
  let V : ℕ→ℝ:=fun n=>(n:ℝ)^(-(A0.β/(D+1:ℕ)))/F.rminus
  let Cn:=smoothIndependentHardClass A ε F.rminus
  have hu0 : Tendsto U atTop (𝓝 0) := by
    simpa [U] using ((tendsto_rpow_neg_atTop (div_pos A0.hα (Nat.cast_pos.mpr (Nat.succ_pos D)))).comp
      tendsto_natCast_atTop_atTop).div_const F.rminus
  have hclass : ∀ c0,F.SelectedClassSequenceClaim θ τ c0 Cn := by
    intro c0
    have hm:=he θ τ c0 1 hθ hrough' hτ zero_lt_one
    have hb:=F.eventually_final_selected_hard_laws hF θ τ c0 1 hθ hrough' hτ zero_lt_one
    filter_upwards [hm,hb,hu0.eventually_lt_const (by norm_num : (0:ℝ)<1/4),eventually_gt_atTop 0]
      with n hn hbn hun hn0
    obtain ⟨W,hsmall,hmem⟩:=hn
    obtain ⟨hN,hmu,hd,hmargin,hsmall',hbounds⟩:=hbn
    let B:=F.selectedFrame θ τ c0 n W
    have hrB : B.rminus=F.rminus:=by rfl
    refine ⟨W,?_,?_⟩
    · change (B.Au+B.Av)/B.rminus*F.scores.C≤1/4
      rw [hrB];exact hsmall
    intro z
    have hs : (B.field z).epsilon*(scores 0 (by norm_num)).C≤1/4 := by
      simpa only [CanonicalFrame.field,hrB,hS] using hsmall
    have hub : ∀ x,|(B.field z).u x|≤U n := (hbounds z).2.1
    have hvb : ∀ x,|(B.field z).v x|≤V n := (hbounds z).2.2
    change _∈(modelClass A ε ∩ Model.smoothDensityClass A.d Response) ∧ _≤ independentErrorEnvelope A.α A.β F.rminus A.d n
    refine ⟨⟨hmem z,B.observationProbability_mem_smoothDensityClass _ _ (by rw [hrB];exact hsmall) z⟩,?_⟩
    simpa only [hS,CanonicalFrame.observationProbability,B,independentErrorEnvelope,U,V,A,Model.Parameters.withDimension] using independent_effect_error A hM (B.field z) hs (U n) (V n)
      (by dsimp [U];positivity [F.interval.1]) (by dsimp [V];positivity [F.interval.1]) hun.le hub hvb
  obtain ⟨c,hc,n0,hn0,hrisk⟩:=F.source_family_rough_lower_sequence hF hrough' Cn hclass
  let t : ℕ→ℝ:=fun n=>2*c*Rates.subcriticalScale n θ (Rates.tau A0.gminus A0.gplus)*Real.log n
  have her : Tendsto (fun n=>independentErrorEnvelope A0.α A0.β F.rminus (D+1) n/t n) atTop (𝓝 0) :=
    independentErrorEnvelope_relative A0.α A0.β F.rminus (Rates.tau A0.gminus A0.gplus) (2*c)
      (D+1) A0.hα (Nat.succ_pos _) (by positivity)
  have htail : ∀ᶠ n in atTop,(3/8:ℝ≥0∞)≤Model.minimaxTail n (effect A.d) (Cn n)
      ((2*c)/4*Model.lowerBracketScale (bracketParameters A) n) := by
    filter_upwards [eventually_ge_atTop n0,eventually_gt_atTop 1,
      her.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with n hn hn1 hen
    have hnR : 1<(n:ℝ):=by exact_mod_cast hn1
    have ht : 0<t n:=mul_pos (mul_pos (by positivity) (Rates.scale_pos _ _ _ hnR)) (Real.log_pos hnR)
    have hehalf : independentErrorEnvelope A.α A.β F.rminus A.d n≤t n/2 := by
      change independentErrorEnvelope A0.α A0.β F.rminus (D+1) n≤t n/2
      simpa only [one_div_mul_eq_div] using (div_le_iff₀ ht).mp hen.le
    have hr:=(hrisk n hn).2
    have htarg : Model.target A (numeratorObservables A hM)=numerator A.d := by
      funext P;exact numerator_target A hM P
    rw [htarg] at hr
    let M:=1/(4*(ε*(1-ε)))
    have hM0 : 0≤M:=by dsimp [M];exact (one_div_nonneg.mpr (mul_nonneg (by norm_num) (mul_nonneg hε.le (by linarith))))
    have hm : ∀ P∈Cn n,effect A.d P∈Icc (-M) M := fun P hP=>effect_range A ε hε hεhalf P hP.1.1
    have hrel : ∀ P∈Cn n,|numerator A.d P-(projIcc (-M) M (neg_le_self hM0) (effect A.d P):ℝ)/4|≤
        independentErrorEnvelope A.α A.β F.rminus A.d n := by
      intro P hP;rw [projIcc_of_mem (neg_le_self hM0) (hm P hP)];exact hP.2
    have htr:=Model.zero_moment_reverse_tail n (effect A.d) (numerator A.d) (Cn n)
      (-M) M (neg_le_self hM0) (fun a=>(a:ℝ)/4) 1 (t n)
      (independentErrorEnvelope A.α A.β F.rminus A.d n) zero_lt_one ht hehalf
      (by intro a b;rw [← sub_div,abs_div];norm_num;linarith [abs_nonneg ((a:ℝ)-b)]) hm hrel
    have hbound:=hr.trans htr
    convert hbound using 1
    rw [Model.lowerBracketScale,ite_eq_left hrough,hθeq]
    change Model.minimaxTail n (effect A.d) (Cn n) (((2*c)/4)*(Rates.subcriticalScale n θ (Rates.tau A0.gminus A0.gplus)*Real.log n))=_
    dsimp [t];congr 1;ring
  exact Model.lowerBracket_of_eventual_hardTail (effect A.d) Cn ((modelClass A ε ∩ Model.smoothDensityClass A.d Response))
    (bracketParameters A) ((2*c)/4) (by positivity)
    (Eventually.of_forall fun _ P hP=>hP.1) htail

end RoughRegime.Applications.Overlap
