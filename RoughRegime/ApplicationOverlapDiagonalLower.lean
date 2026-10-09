module

public import RoughRegime.ApplicationOverlapSelected
public import RoughRegime.ApplicationOverlapReduction
public import RoughRegime.ApplicationOverlapUpper
public import RoughRegime.SourceRoughLower
public import RoughRegime.ModelEventualHardness


@[expose] public section
/-! The genuine correlated diagonal source family gives the rough lower
bracket for overlap effects whenever the treatment exponent is the smaller one. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Overlap
open RoughRegime.LatticePriors RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

 def diagonalHardClass (A : Model.Parameters) (ε : ℝ) :=
  {P | P∈modelClass A ε ∧ numerator A.d P=1/16 ∧ denominator A.d P∈Icc (3/16) (1/4)}
 theorem diagonal_rough_lower (A0 : Model.Parameters) (D : ℕ) (ε : ℝ)
    (hε : ε<1/2) (hM : 1≤A0.M0) (hlo : max A0.δ A0.gminus<1)
    (hhi : 1<A0.gplus) (hH : 1/2<A0.H) (hab : A0.α≤A0.β)
    (hrough : (bracketParameters (A0.withDimension D)).theta<1/2) :
    Model.LowerBracket (effect (D+1)) (modelClass (A0.withDimension D) ε)
      (bracketParameters (A0.withDimension D)) := by
  let A:=A0.withDimension D
  obtain ⟨F,hF,hS,he⟩:=diagonal_selected_family A0 D ε hε hM hlo hhi hH
  let θ:=(diagonalParameters A0).withDimension D |>.theta
  let τ:=Rates.tau F.rminus F.rplus
  have hθ : 0<θ:=(diagonalParameters A0).withDimension D |>.theta_pos
  have hτ : 0<τ:=Rates.tau_pos _ _ F.interval.1 (F.interval.2.1.trans F.interval.2.2)
  have hθeq : (bracketParameters A).theta=θ := by
    change (A0.α+min A0.α A0.β)/(D+1:ℕ)=(A0.α+A0.α)/(D+1:ℕ)
    rw [min_eq_left hab]
  have hrough' : θ<1/2 := by rw [← hθeq];exact hrough
  let C:=diagonalHardClass A ε
  have hclass : ∀ c0,F.SelectedClassClaim θ τ c0 C := by
    intro c0
    have hm:=he θ τ c0 1 hθ hrough' hτ zero_lt_one
    have ha:=F.selectedFrame_amplitude_le_envelope θ τ c0 hθ hrough' hτ
    have hs : Tendsto (fun n=>SourceModelFamily.selectedAmplitudeEnvelope (diagonalParameters A0) (D+1) n/F.rminus)
        atTop (𝓝 0) := by
      simpa using (SourceModelFamily.selectedAmplitudeEnvelope_tendsto (diagonalParameters A0) (D+1)
        (Nat.succ_pos _)).div_const F.rminus
    filter_upwards [hm,ha,hs.eventually_lt_const (by norm_num : (0:ℝ)<1/8)] with n hn han hsn
    obtain ⟨V,hsmall,hmem⟩:=hn
    let B:=F.selectedFrame θ τ c0 n V
    have hrB : B.rminus=F.rminus:=by rfl
    have hb : (B.Au+B.Av)/F.rminus≤1/8 :=
      ((div_le_div_of_nonneg_right (han V) F.interval.1.le).trans hsn.le)
    refine ⟨V,?_,?_⟩
    · change (B.Au+B.Av)/B.rminus*F.scores.C≤1/4
      rw [hrB];exact hsmall
    intro z
    have hsz : (B.field z).epsilon*diagonalScores.C≤1/4 := by
      simpa only [CanonicalFrame.field,hrB,hS] using hsmall
    have hu (x) : |(B.field z).u x+(B.field z).v x|≤1/4 := by
      have hh := (abs_add_le _ _).trans (add_le_add ((B.field z).boundU x) ((B.field z).boundV x))
      simp only [CanonicalFrame.field,hrB] at hh
      change |B.u z x+B.v z x|≤1/4
      linarith
    change _∈modelClass A ε ∧ _=1/16 ∧ _∈Icc (3/16) (1/4)
    refine ⟨hmem z,?_,?_⟩
    · simpa only [hS,CanonicalFrame.observationProbability,B] using diagonal_numerator A hM (B.field z) hsz
    · simpa only [hS,CanonicalFrame.observationProbability,B] using diagonal_denominator_bounds A hM (B.field z) hsz hu
  obtain ⟨c,hc,n0,hn0,hrisk⟩:=F.source_family_rough_lower hF hrough' C hclass
  have htail : ∀ᶠ n in atTop,(3/8:ℝ≥0∞)≤Model.minimaxTail n (effect A.d) C
      ((2*c)/4*Model.lowerBracketScale (bracketParameters A) n) := by
    filter_upwards [eventually_ge_atTop n0,eventually_gt_atTop 1] with n hn hn1
    have ht : 0<2*c*Rates.subcriticalScale n θ (Rates.tau A0.gminus A0.gplus)*Real.log n := by
      have hnR : 1<(n:ℝ):=by exact_mod_cast hn1
      exact mul_pos (mul_pos (by positivity) (Rates.scale_pos _ _ _ hnR)) (Real.log_pos hnR)
    have hr := (hrisk n hn).2
    have htarg : Model.target ((diagonalParameters A0).withDimension D) (denominatorObservables A hM)=denominator A.d := by
      funext P;exact denominator_target A hM P
    rw [htarg] at hr
    have hm : ∀ P∈C,effect A.d P∈Icc (1/4) (1/3) := by
      intro P hP
      exact (diagonal_effect_scalar _ _ hP.2.2.1 hP.2.2.2 (by rw [effect,hP.2.1])).1
    have hrel : ∀ P∈C,|denominator A.d P-1/(16*(projIcc (1/4:ℝ) (1/3) (by norm_num) (effect A.d P):ℝ))|≤0 := by
      intro P hP
      have hγ : effect A.d P=(1/16)/denominator A.d P:=by rw [effect,hP.2.1]
      have hid:=(diagonal_effect_scalar (denominator A.d P) (effect A.d P) hP.2.2.1 hP.2.2.2 hγ).2
      rw [projIcc_of_mem (by norm_num) (hm P hP)]
      rw [hid];simp
    have htr := Model.zero_moment_reverse_tail n (effect A.d) (denominator A.d) C
      (1/4) (1/3) (by norm_num) (fun a=>1/(16*(a:ℝ))) 1
      (2*c*Rates.subcriticalScale n θ (Rates.tau A0.gminus A0.gplus)*Real.log n) 0 zero_lt_one ht
      (by positivity) (by intro a b;simpa only [one_mul] using reciprocal_lipschitz a b) hm hrel
    have hbound:=hr.trans htr
    convert hbound using 1
    rw [Model.lowerBracketScale,ite_eq_left hrough,hθeq]
    change Model.minimaxTail n (effect A.d) C (((2*c)/4)*(Rates.subcriticalScale n θ (Rates.tau A0.gminus A0.gplus)*Real.log n))=_
    congr 1;ring
  exact Model.lowerBracket_of_eventual_hardTail (effect A.d) (fun _=>C) (modelClass A ε)
    (bracketParameters A) ((2*c)/4) (by positivity)
    (Eventually.of_forall fun _ P hP=>hP.1) htail

end RoughRegime.Applications.Overlap
