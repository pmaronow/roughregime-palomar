module

public import RoughRegime.ApplicationOverlapSmoothDiagonalLower
public import RoughRegime.ApplicationOverlapSmoothIndependentLower
public import RoughRegime.ApplicationOverlapSmoothParametric
public import RoughRegime.ApplicationOverlapBracket


@[expose] public section
/-! The complete original overlap-weighted-effect application: literal
conditional covariance/variance target and its genuine two-sided bracket. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false

 theorem smooth_lowerBracket_dimension (A0 : Model.Parameters) (D : ℕ) (ε : ℝ)
    (hε : 0<ε) (hεhalf : ε<1/2) (hM : 1≤A0.M0) (hlo : max A0.δ A0.gminus<1)
    (hhi : 1<A0.gplus) (hH : 1/2<A0.H) :
    Model.LowerBracket (effect (D+1)) ((modelClass (A0.withDimension D) ε ∩ Model.smoothDensityClass (D+1) Response))
      (bracketParameters (A0.withDimension D)) := by
  let A:=A0.withDimension D
  by_cases hrough : (bracketParameters A).theta<1/2
  · rcases le_total A0.β A0.α with h | h
    · exact smooth_independent_rough_lower A0 D ε hε hεhalf hM hlo hhi hH h hrough
    · exact smooth_diagonal_rough_lower A0 D ε hεhalf hM hlo hhi hH h hrough
  · obtain ⟨c,hc,he⟩:=smooth_parametric_lower A ε hεhalf hM ((le_max_right _ _).trans_lt hlo) hhi hH
    have hbound : ∀ᶠ n in atTop,
        ENNReal.ofReal (c*Model.lowerBracketScale (bracketParameters A) n)≤Model.minimaxRMSE n (effect A.d) ((modelClass A ε ∩ Model.smoothDensityClass A.d Response)) ∧
        ((bracketParameters A).theta<1/2 → (1/4:ℝ≥0∞)≤Model.minimaxTail n (effect A.d) ((modelClass A ε ∩ Model.smoothDensityClass A.d Response))
          (2*c*Model.lowerBracketScale (bracketParameters A) n)) := by
      filter_upwards [he] with n hn
      exact ⟨by simpa only [Model.lowerBracketScale,ite_eq_right hrough] using hn.1,
        fun h=>False.elim (hrough h)⟩
    obtain ⟨n0,hn0⟩:=eventually_atTop.mp hbound
    exact ⟨c,hc,max 3 n0,le_max_left _ _,fun n hn=>hn0 n ((le_max_right _ _).trans hn)⟩

 theorem smooth_lowerBracket (A : Model.Parameters) (ε : ℝ) (hε : 0<ε) (hεhalf : ε<1/2)
    (hM : 1≤A.M0) (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hH : 1/2<A.H) :
    Model.LowerBracket (effect A.d) ((modelClass A ε ∩ Model.smoothDensityClass A.d Response)) (bracketParameters A) := by
  cases A with
  | mk d α β H δ lo hi M hd hα hβ hH0 hδ hlo0 hinterval hM0 =>
    cases d with
    | zero => omega
    | succ D =>
      exact smooth_lowerBracket_dimension (Model.Parameters.mk (D+1) α β H δ lo hi M hd hα hβ hH0 hδ hlo0 hinterval hM0)
        D ε hε hεhalf hM hlo hhi hH

 theorem smooth_bracket (A : Model.Parameters) (ε : ℝ) (hε : 0<ε) (hεhalf : ε<1/2)
    (hM : 1≤A.M0) (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hH : 1/2<A.H) :
    Model.Bracket (effect A.d) ((modelClass A ε ∩ Model.smoothDensityClass A.d Response)) (bracketParameters A) (nu A:ℝ) :=
  ⟨smooth_lowerBracket A ε hε hεhalf hM hlo hhi hH,
    Model.upperBracket_mono_class _ _ _ (fun _ h=>h.1)
      (upperBracket A ε hε hεhalf hM ((le_max_left _ _).trans_lt hlo).le)⟩

/-- Original Section3 overlap application, with its exact literal class,
conditional-covariance/conditional-variance target, and both index formulas. -/
 theorem overlap_weighted_effect_smooth_bracket (d : ℕ) (α β H pminus pplus ε : ℝ) (hd : 1≤d)
    (hα : 0<α) (hβ : 0<β) (hH : 1<H) (hpm : 0<pminus) (hpm1 : pminus<1) (hpp : 1<pplus)
    (hε : 0<ε) (hεhalf : ε<1/2) :
    let A:=paperParameters d α β H pminus pplus hd hα hβ hH hpm hpm1 hpp
    Model.Bracket (effect d) ((modelClass A ε ∩ Model.smoothDensityClass A.d Response)) (bracketParameters A) (nu A:ℝ) ∧
      (bracketParameters A).theta=min ((α+β)/d) (2*α/d) ∧
      nu A=(d+Model.holderOrder α).choose d+(d+Model.holderOrder (min α β)).choose d := by
  dsimp only
  let A:=paperParameters d α β H pminus pplus hd hα hβ hH hpm hpm1 hpp
  refine ⟨smooth_bracket A ε hε hεhalf (by norm_num [A,paperParameters]) ?_ hpp (by dsimp [A,paperParameters];linarith),
    theta_eq A,nu_eq A⟩
  exact max_lt (by norm_num [A,paperParameters]) hpm1

end RoughRegime.Applications.Overlap
