module

public import RoughRegime.ProductDerivedLower
public import RoughRegime.SpatialContrastSmooth
public import RoughRegime.ProductSmoothBrackets


@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace RoughRegime.Applications.Products

 theorem smooth_explained_rough_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) (hrough : A.theta<1/2) :
    Model.LowerBracket (explainedTarget A) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) A.bracketParameters := by
  let f : Model.Observation A BoundedResponse→ℝ:=fun o=>(o.2:ℝ)
  let h:=scalarPilot f
  let lo : Fin 1→ℝ:=fun _=>-1
  let hi : Fin 1→ℝ:=fun _=>1
  let Phi : Icc (0:ℝ) 1→Applications.momentRectangle lo hi→ℝ:=fun a q=>(a:ℝ)+(q.val 0)^2
  apply Model.pilot_rough_lowerBracket A.bracketParameters hrough
    (explainedTarget A) (quadraticTarget A) (fun _=>quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)
    (Eventually.of_forall fun _=>subset_rfl) h
    (fun _=>measurable_subtype_coe.comp measurable_snd)
    (by intro P j;change MemLp f 2 (P:Measure _);exact Applications.bounded_memLp (P:Measure _) f (measurable_subtype_coe.comp measurable_snd) 1 (fun o=>response_bound o.2))
    lo hi (fun _=>by norm_num) (fun P _=>responseMean_range A P)
    0 1 (by norm_num) Phi 2 1 (by norm_num)
  · intro a b q r
    calc
      |Phi a q-Phi b r| ≤ |(a:ℝ)-b| +|(q.val 0)^2-(r.val 0)^2| := by
        dsimp [Phi]
        have he : ((a:ℝ)+(q.val 0)^2)-((b:ℝ)+(r.val 0)^2)=
          ((a:ℝ)-b)+((q.val 0)^2-(r.val 0)^2) := by ring
        rw [he]
        exact abs_add_le _ _
      _ ≤ |(a:ℝ)-b| +2*dist q r := add_le_add le_rfl
        ((square_lipschitz_on_unit _ _ (q.property 0) (r.property 0)).trans
          (mul_le_mul_of_nonneg_left (pilot_coordinate_dist q r) (by norm_num)))
      _ ≤ 2*(|(a:ℝ)-b| +dist q r) := by linarith [abs_nonneg ((a:ℝ)-b)]
  · apply Eventually.of_forall
    intro n
    refine ⟨fun P _=>explainedTarget_range A P,?_,?_⟩
    · intro P _
      rw [projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (explainedTarget_range A P)]
      change quadraticTarget A P=explainedTarget A P+(responseMean A P)^2
      rw [explainedTarget_identity]
      ring
    · intro P _
      exact scalarPilot_variance P f (measurable_subtype_coe.comp measurable_snd) 1 (fun o=>response_bound o.2)
  · exact smooth_quadratic_rough_hardness A hM hlo hhi hab hrough
  · exact Model.rough_lowerBracket_squared_sample_tendsto A.bracketParameters hrough

 theorem smooth_excessLoss_rough_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) (hrough : A.theta<1/2)
    (f0 : Model.Covariate A.d→ℝ) (hf : Measurable f0) (M : ℝ) (hM0 : 0≤M) (hb : ∀x,|f0 x|≤M) :
    Model.LowerBracket (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) A.bracketParameters := by
  let f:=predictionContrast A f0
  let B:=2*M+M^2
  have hB : 0≤B := by dsimp [B];positivity
  have hf' : Measurable f:=predictionContrast_measurable A f0 hf
  have hb' : ∀o,|f o|≤B:=predictionContrast_bound A f0 M hM0 hb
  let h:=scalarPilot f
  let lo : Fin 1→ℝ:=fun _=>-B
  let hi : Fin 1→ℝ:=fun _=>B
  let Phi : Icc (-B) (1+B)→Applications.momentRectangle lo hi→ℝ:=fun a q=>(a:ℝ)+q.val 0
  have hm : ∀P : ProbabilityMeasure (Model.Observation A BoundedResponse),
      (∫o,f o ∂(P:Measure _))∈Icc (-B) B := fun P=>abs_le.mp (bounded_mean_abs P f B hb')
  have htarget : ∀P : ProbabilityMeasure (Model.Observation A BoundedResponse),
      excessLoss A f0 P∈Icc (-B) (1+B) := by
    intro P
    rw [excessLoss_identity A f0 hf M hb]
    have hq:=quadraticTarget_range A P
    have hm':=hm P
    dsimp only [f] at hm'
    rcases hq with ⟨hq0,hq1⟩
    rcases hm' with ⟨hm0,hm1⟩
    exact ⟨by linarith,by linarith⟩
  apply Model.pilot_rough_lowerBracket A.bracketParameters hrough
    (excessLoss A f0) (quadraticTarget A) (fun _=>quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)
    (Eventually.of_forall fun _=>subset_rfl) h (fun _=>hf')
    (by intro P j;change MemLp f 2 (P:Measure _);exact Applications.bounded_memLp (P:Measure _) f hf' B hb')
    lo hi (fun _=>by dsimp [lo,hi];linarith) (fun P _=>hm P)
    (-B) (1+B) (by linarith) Phi 1 B (by norm_num)
  · intro a b q r
    calc
      |Phi a q-Phi b r|≤|(a:ℝ)-b|+|q.val 0-r.val 0| := by
        dsimp [Phi]
        have he : ((a:ℝ)+q.val 0)-((b:ℝ)+r.val 0)=((a:ℝ)-b)+(q.val 0-r.val 0) := by ring
        rw [he]
        exact abs_add_le _ _
      _≤|(a:ℝ)-b|+dist q r := add_le_add le_rfl (pilot_coordinate_dist q r)
      _=1*(|(a:ℝ)-b|+dist q r) := by ring
  · apply Eventually.of_forall
    intro n
    refine ⟨fun P _=>htarget P,?_,?_⟩
    · intro P _
      rw [projIcc_of_mem (by linarith : -B≤1+B) (htarget P)]
      change quadraticTarget A P=excessLoss A f0 P+∫o,f o ∂(P:Measure _)
      rw [excessLoss_identity A f0 hf M hb]
      ring
    · intro P _
      exact scalarPilot_variance P f hf' B hb'
  · exact smooth_quadratic_rough_hardness A hM hlo hhi hab hrough
  · exact Model.rough_lowerBracket_squared_sample_tendsto A.bracketParameters hrough

 theorem smooth_explained_bracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) :
    Model.Bracket (explainedTarget A) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) A.bracketParameters (A.nu:ℝ) := by
  refine ⟨?_,Model.upperBracket_mono_class _ _ _ Set.inter_subset_left
    (explained_upperBracket A hM ((le_max_left _ _).trans hlo.le))⟩
  by_cases hrough : A.theta<1/2
  · exact smooth_explained_rough_lowerBracket A hM hlo hhi hab hrough
  · exact parametric_lowerBracket A _ _ (le_of_not_gt hrough)
      (smooth_explained_parametric_lower A hab ((le_max_right _ _).trans hlo.le) hhi.le)

 theorem smooth_excessLoss_bracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (f0 : Model.Covariate A.d→ℝ) (hf : Measurable f0) (M : ℝ) (hM0 : 0≤M) (hb : ∀x,|f0 x|≤M) :
    Model.Bracket (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) A.bracketParameters (A.nu:ℝ) := by
  refine ⟨?_,Model.upperBracket_mono_class _ _ _ Set.inter_subset_left
    (excessLoss_upperBracket A hM ((le_max_left _ _).trans hlo.le) f0 hf M hM0 hb)⟩
  by_cases hrough : A.theta<1/2
  · exact smooth_excessLoss_rough_lowerBracket A hM hlo hhi hab hrough f0 hf M hM0 hb
  · exact parametric_lowerBracket A _ _ (le_of_not_gt hrough)
      (smooth_excessLoss_parametric_lower A hab ((le_max_right _ _).trans hlo.le) hhi.le f0 hf M hb)

 theorem smooth_excessLoss_bracket_cube (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (f0 : Model.Covariate A.d→ℝ) (hf : Measurable f0) (M : ℝ) (hM0 : 0≤M)
    (hb : ∀x∈Model.cube A.d,|f0 x|≤M) :
    Model.Bracket (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) A.bracketParameters (A.nu:ℝ) := by
  let f := (Model.cube A.d).indicator f0
  have hcube : MeasurableSet (Model.cube A.d) := (Model.isCompact_cube A.d).isClosed.measurableSet
  have hfb : ∀x,|f x|≤M := by
    intro x
    by_cases hx : x∈Model.cube A.d
    · simpa only [f,indicator_of_mem hx] using hb x hx
    · simpa only [f,indicator_of_notMem hx,abs_zero] using hM0
  apply Model.bracket_congr_target _ (excessLoss A f) _ _ _ _
    (smooth_excessLoss_bracket A hM hlo hhi hab f (hf.indicator hcube) M hM0 hfb)
  intro P hP
  apply integral_congr_ae
  filter_upwards [quadraticClass_covariate_cube A P hP.1] with o ho
  simp only [f,indicator_of_mem ho]

end RoughRegime.Applications.Products
