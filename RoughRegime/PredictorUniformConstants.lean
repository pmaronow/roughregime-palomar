module

public import RoughRegime.PredictorUniformBracket
public import RoughRegime.PredictorUniformParametric


@[expose] public section
/-! Corollary 3(b): one pair of constants and one sample cutoff, chosen
before every known measurable predictor bounded by the same number. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace RoughRegime.Applications.Products
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem uniform_excessLoss_constants (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (M : ℝ) (hM0 : 0≤M) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃n0:ℕ,3≤n0 ∧
      ∀f0 : Model.Covariate A.d→ℝ,Measurable f0→(∀x,|f0 x|≤M)→
      ∀n:ℕ,n0≤n→
        ENNReal.ofReal (c*Model.lowerBracketScale A.bracketParameters n)≤
          Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A) ∧
        Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A)≤
          ENNReal.ofReal (C*Model.upperBracketScale A.bracketParameters (A.nu:ℝ) n) ∧
        (A.theta<1/2→(1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A)
          (2*c*Model.lowerBracketScale A.bracketParameters n)) := by
  obtain ⟨C,hC,hupper⟩:=uniform_excessLoss_upper A hM
    ((le_max_left _ _).trans hlo.le) M hM0
  have hlower : ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ∀f0 : Model.Covariate A.d→ℝ,Measurable f0→(∀x,|f0 x|≤M)→
        ENNReal.ofReal (c*Model.lowerBracketScale A.bracketParameters n)≤
          Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A) ∧
        (A.theta<1/2→(1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A)
          (2*c*Model.lowerBracketScale A.bracketParameters n)) := by
    by_cases hrough:A.theta<1/2
    · obtain ⟨c,hc,he⟩:=uniform_excessLoss_rough_lower A hM hlo hhi hab hrough M hM0
      exact ⟨c,hc,he.mono (fun n hn f hf hb=>⟨(hn f hf hb).1,fun _=>(hn f hf hb).2⟩)⟩
    · obtain ⟨c,hc,he⟩:=uniform_excessLoss_parametric_lower A hab
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
theorem uniform_excessLoss_constants_cube (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (M : ℝ) (hM0 : 0≤M) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃n0:ℕ,3≤n0 ∧
      ∀f0 : Model.Covariate A.d→ℝ,Measurable f0→(∀x∈Model.cube A.d,|f0 x|≤M)→
      ∀n:ℕ,n0≤n→
        ENNReal.ofReal (c*Model.lowerBracketScale A.bracketParameters n)≤
          Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A) ∧
        Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A)≤
          ENNReal.ofReal (C*Model.upperBracketScale A.bracketParameters (A.nu:ℝ) n) ∧
        (A.theta<1/2→(1/4:ℝ≥0∞)≤Model.minimaxTail n (excessLoss A f0) (quadraticClass A)
          (2*c*Model.lowerBracketScale A.bracketParameters n)) := by
  obtain ⟨c,C,hc,hC,n0,hn0,he⟩:=uniform_excessLoss_constants A hM hlo hhi hab M hM0
  refine ⟨c,C,hc,hC,n0,hn0,?_⟩
  intro f0 hf hb n hn
  let f:=(Model.cube A.d).indicator f0
  have hcube:MeasurableSet (Model.cube A.d):=(Model.isCompact_cube A.d).isClosed.measurableSet
  have hfb:∀x,|f x|≤M := by
    intro x
    by_cases hx:x∈Model.cube A.d
    · simpa only [f,indicator_of_mem hx] using hb x hx
    · simpa only [f,indicator_of_notMem hx,abs_zero] using hM0
  have htarget:∀P∈quadraticClass A,excessLoss A f0 P=excessLoss A f P := by
    intro P hP
    apply integral_congr_ae
    filter_upwards [quadraticClass_covariate_cube A P hP] with o ho
    simp only [f,indicator_of_mem ho]
  rw [Model.minimaxRMSE_congr_target n (excessLoss A f0) (excessLoss A f) (quadraticClass A) htarget,
    Model.minimaxTail_congr_target n (excessLoss A f0) (excessLoss A f) (quadraticClass A) _ htarget]
  exact he f (hf.indicator hcube) hfb n hn

end RoughRegime.Applications.Products
