module

public import RoughRegime.ApplicationsTransfers
public import RoughRegime.ModelEventualHardness
public import RoughRegime.ModelUpperConsequences


@[expose] public section
/-! Actual iid moment pilots preserve the source rough lower bracket. The
vanishing pilot error is proved in the sample experiment with its uniform seed. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Model

 theorem pilot_rough_lowerBracket {Ω : Type*} [MeasurableSpace Ω]
    (S : BracketParameters) (hrough : S.theta < 1/2)
    (T0 T1 : ProbabilityMeasure Ω→ℝ) (Cn : ℕ→Set (ProbabilityMeasure Ω))
    (C : Set (ProbabilityMeasure Ω)) (hC : ∀ᶠn in atTop,Cn n⊆C)
    {k : ℕ} (h : Fin k→Ω→ℝ) (hmh : ∀j,Measurable (h j))
    (hh : ∀(P:ProbabilityMeasure Ω) j,MemLp (h j) 2 (P:Measure Ω))
    (mlo mhi : Fin k→ℝ) (hmlohi : ∀j,mlo j ≤ mhi j)
    (hm : ∀(P:ProbabilityMeasure Ω) j,(∫x,h j x ∂(P:Measure Ω))∈Icc (mlo j) (mhi j))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (Phi : Icc lo hi→Applications.momentRectangle mlo mhi→ℝ)
    (L B : ℝ) (hL : 0 < L)
    (hLip : ∀a b q r,|Phi a q-Phi b r| ≤ L*(|(a:ℝ)-b|+dist q r))
    (hconditions : ∀ᶠn in atTop,
      (∀P∈Cn n,T0 P∈Icc lo hi) ∧
      (∀P∈Cn n,T1 P = Phi (projIcc lo hi hlohi (T0 P))
        ⟨Applications.momentMean (P:Measure Ω) h,hm P⟩) ∧
      (∀P∈Cn n,(∫x,‖Applications.responseVector h x-Applications.momentMean (P:Measure Ω) h‖^2
        ∂(P:Measure Ω)) ≤ B^2))
    (hardness : ∃c:ℝ,0 < c ∧ ∀ᶠn in atTop,
      (3/8:ℝ≥0∞) ≤ minimaxTail n T1 (Cn n) (2*c*lowerBracketScale S n))
    (hdecay : ∀c:ℝ,0 < c→Tendsto (fun n:ℕ => (n:ℝ)*(c*lowerBracketScale S n)^2) atTop atTop) :
    LowerBracket T0 C S := by
  obtain ⟨c,hc,hhard⟩:= hardness
  let t : ℕ→ℝ:= fun n => 2*c*lowerBracketScale S n
  have ht : ∀ᶠn:ℕ in atTop,0 < t n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hnR:1 < (n:ℝ):= by exact_mod_cast hn
    dsimp [t,lowerBracketScale]
    rw [ite_eq_left hrough]
    have hs:=Rates.scale_pos n S.theta (Rates.tau S.lo S.hi) hnR
    have hl:=Real.log_pos hnR
    positivity
  have hcond : ∀ᶠn in atTop,(0:ℝ) ≤ t n/2 ∧
      (∀P∈Cn n,T0 P∈Icc lo hi) ∧
      (∀P∈Cn n,|T1 P-Phi (projIcc lo hi hlohi (T0 P))
        ⟨Applications.momentMean (P:Measure Ω) h,hm P⟩| ≤ 0) ∧
      (∀P∈Cn n,(∫x,‖Applications.responseVector h x-Applications.momentMean (P:Measure Ω) h‖^2
        ∂(P:Measure Ω)) ≤ B^2) := by
    filter_upwards [ht,hconditions] with n htn hn
    exact ⟨by positivity,hn.1,fun P hP => by rw [hn.2.1 P hP];simp,hn.2.2⟩
  have hhard0 := Applications.hardness_reverse_transfer_iid KernelSeedBridge.seedLaw
    (fun P:ProbabilityMeasure Ω => (P:Measure Ω)) T0 T1 Cn h hmh hh
    mlo mhi hmlohi hm lo hi hlohi Phi L B hL hLip t (fun _ => 0) ht hcond
    (Or.inr (hdecay (2*c) (by positivity))) (3/8)
    (le_liminf_of_le (by isBoundedDefault) hhard)
  have hrisks:= hardness_to_risk T0 Cn C (fun n => t n/(4*L))
    (fun n => div_nonneg (mul_nonneg (by positivity) (lowerBracketScale_nonneg S n)) (by positivity)) hC hhard0
  have he : ∀ᶠn in atTop,
      ENNReal.ofReal ((c/(4*L))*lowerBracketScale S n) ≤ minimaxRMSE n T0 C ∧
      (S.theta < 1/2→(1/4:ℝ≥0∞) ≤ minimaxTail n T0 C (2*(c/(4*L))*lowerBracketScale S n)) := by
    filter_upwards [hrisks] with n hn
    have heq:t n/(4*L)/2 = (c/(4*L))*lowerBracketScale S n:= by dsimp [t];ring
    have hteq:t n/(4*L) = 2*(c/(4*L))*lowerBracketScale S n:= by dsimp [t];ring
    exact ⟨by simpa only [heq] using hn.2,fun _ => by simpa only [hteq] using hn.1⟩
  obtain ⟨n0,hn0⟩:= eventually_atTop.mp he
  exact ⟨c/(4*L),by positivity,max 3 n0,le_max_left _ _,fun n hn => hn0 n ((le_max_right _ _).trans hn)⟩

end RoughRegime.Model
