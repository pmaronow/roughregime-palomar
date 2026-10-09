module

public import RoughRegime.ProductDerivedLower
public import RoughRegime.ProductVarianceHardness


@[expose] public section
/-! Actual reverse-pilot lower bounds for the determination coefficient on
the class with a fixed positive response-variance floor. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace RoughRegime.Applications.Products

 theorem bounded_vectorPilot_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) {k : ℕ} (h : Fin k→Ω→ℝ)
    (hm : ∀j,Measurable (h j)) (B : ℝ) (hb : ∀j x,|h j x|≤B) :
    (∫x,‖Applications.responseVector h x-Applications.momentMean (P:Measure Ω) h‖^2 ∂(P:Measure Ω))≤
      (k:ℝ)*B^2 := by
  have he : (fun x=>‖Applications.responseVector h x-Applications.momentMean (P:Measure Ω) h‖^2)=
      fun x=>∑j:Fin k,(h j x-∫y,h j y ∂(P:Measure Ω))^2 := by
    funext x
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he]
  have hiR:=integral_finsetSum Finset.univ (fun j _=>
    ((Applications.bounded_memLp (P:Measure Ω) (h j) (hm j) B (hb j)).sub
      (memLp_const (∫y,h j y ∂(P:Measure Ω)))).integrable_sq)
  change (∫x,∑j:Fin k,(h j x-∫y,h j y ∂(P:Measure Ω))^2 ∂(P:Measure Ω))=
    ∑j:Fin k,∫x,(h j x-∫y,h j y ∂(P:Measure Ω))^2 ∂(P:Measure Ω) at hiR
  rw [hiR]
  have hs:=Finset.sum_le_sum (s := (Finset.univ:Finset (Fin k))) (fun j _=>
    scalarPilot_variance P (h j) (hm j) B (hb j))
  have he' (j:Fin k) : (fun x=>‖Applications.responseVector (scalarPilot (h j)) x-
      Applications.momentMean (P:Measure Ω) (scalarPilot (h j))‖^2)=
      fun x=>(h j x-∫y,h j y ∂(P:Measure Ω))^2 := by
    funext x;rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_one];rfl
  simp_rw [he'] at hs
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hs

 def determinationPilot (A : Model.Parameters) : Fin 2→Model.Observation A BoundedResponse→ℝ :=
  ![fun o=>(o.2:ℝ),fun o=>(o.2:ℝ)^2]

 theorem determinationPilot_measurable (A : Model.Parameters) (j:Fin 2) :
    Measurable (determinationPilot A j) := by
  fin_cases j <;> dsimp [determinationPilot] <;> fun_prop

 theorem determinationPilot_bound (A : Model.Parameters) (j:Fin 2)
    (o:Model.Observation A BoundedResponse) : |determinationPilot A j o|≤1 := by
  fin_cases j
  · exact response_bound o.2
  · change |(o.2:ℝ)^2|≤1
    rw [abs_pow]
    nlinarith [response_bound o.2,abs_nonneg (o.2:ℝ)]

 def unitMomentLo : Fin 2→ℝ:=fun _=>-1
 def unitMomentHi : Fin 2→ℝ:=fun _=>1
 def determinationPhi (K:ℝ) : Icc (0:ℝ) K→Applications.momentRectangle unitMomentLo unitMomentHi→ℝ :=
  fun a q=>(a:ℝ)*(q.val 1-(q.val 0)^2)+(q.val 0)^2

 theorem moment_coordinate_dist {k:ℕ}{lo hi:Fin k→ℝ}
    (q r:Applications.momentRectangle lo hi)(j:Fin k) : |q.val j-r.val j|≤dist q r := by
  simpa only [Real.dist_eq,Subtype.dist_eq] using PiLp.dist_apply_le q.val r.val j

 theorem determinationPhi_lipschitz (K:ℝ)(hK:0≤K) :
    ∀a b q r,|determinationPhi K a q-determinationPhi K b r|≤
      (2+3*K)*(|(a:ℝ)-b|+dist q r) := by
  intro a b q r
  have hq0 : q.val 0∈Icc (-1:ℝ) 1:=q.property 0
  have hq1 : q.val 1∈Icc (-1:ℝ) 1:=q.property 1
  have hr0 : r.val 0∈Icc (-1:ℝ) 1:=r.property 0
  have hqa : |q.val 1-(q.val 0)^2|≤2 := by
    have hq02 : (q.val 0)^2≤1 := by nlinarith [hq0.1,hq0.2]
    exact abs_le.mpr ⟨by nlinarith [hq1.1,hq1.2,sq_nonneg (q.val 0)],by nlinarith [hq1.1,hq1.2,sq_nonneg (q.val 0)]⟩
  have hb : |(b:ℝ)|≤K := by rw [abs_of_nonneg b.property.1];exact b.property.2
  have hb1 : |1-(b:ℝ)|≤1+K := (abs_sub _ _).trans (by simpa only [abs_one] using add_le_add le_rfl hb)
  have hs := (square_lipschitz_on_unit _ _ hq0 hr0).trans
    (mul_le_mul_of_nonneg_left (moment_coordinate_dist q r 0) (by norm_num))
  have hd := moment_coordinate_dist q r 1
  have he : determinationPhi K a q-determinationPhi K b r=
      ((a:ℝ)-b)*(q.val 1-(q.val 0)^2)+(b:ℝ)*(q.val 1-r.val 1)+
      (1-(b:ℝ))*((q.val 0)^2-(r.val 0)^2) := by dsimp [determinationPhi];ring
  rw [he]
  calc
    _≤|((a:ℝ)-b)*(q.val 1-(q.val 0)^2)|+|(b:ℝ)*(q.val 1-r.val 1)|+
      |(1-(b:ℝ))*((q.val 0)^2-(r.val 0)^2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _≤|(a:ℝ)-b| *2+K*dist q r+(1+K)*(2*dist q r) := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hqa (abs_nonneg _))
        (mul_le_mul hb hd (abs_nonneg _) hK))
        (mul_le_mul hb1 hs (abs_nonneg _) (by linarith))
    _≤(2+3*K)*(|(a:ℝ)-b|+dist q r) := by
      nlinarith [abs_nonneg ((a:ℝ)-b),dist_nonneg (x:=q) (y:=r)]

 theorem determination_rough_lowerBracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) (hrough : A.theta<1/2)
    (vmin:ℝ)(hv:0<vmin)(hv1:vmin<1) :
    Model.LowerBracket (determinationTarget A) (positiveVarianceClass A vmin) A.bracketParameters := by
  let K:=1/vmin
  have hK : 0≤K := by dsimp [K];positivity
  let h:=determinationPilot A
  have hm : ∀P : ProbabilityMeasure (Model.Observation A BoundedResponse),
      ∀j:Fin 2,(∫o,h j o ∂(P:Measure _))∈Icc (-1:ℝ) 1 := by
    intro P j
    exact abs_le.mp (bounded_mean_abs P (h j) 1 (determinationPilot_bound A j))
  have htarget : ∀P∈positiveVarianceClass A vmin,determinationTarget A P∈Icc (0:ℝ) K := by
    intro P hP
    have hvar : 0<responseVariance A P:=hv.trans_le hP.2
    refine ⟨div_nonneg (explainedTarget_range A P).1 hvar.le,?_⟩
    exact (div_le_div_of_nonneg_right (explainedTarget_range A P).2 hvar.le).trans
      (one_div_le_one_div_of_le hv hP.2)
  apply Model.pilot_rough_lowerBracket A.bracketParameters hrough
    (determinationTarget A) (quadraticTarget A) (fun _=>positiveVarianceClass A vmin)
    (positiveVarianceClass A vmin) (Eventually.of_forall fun _=>subset_rfl) h
    (determinationPilot_measurable A)
    (fun P j=>Applications.bounded_memLp (P:Measure _) (h j) (determinationPilot_measurable A j) 1 (determinationPilot_bound A j))
    unitMomentLo unitMomentHi (fun _=>by norm_num [unitMomentLo,unitMomentHi]) hm
    0 K hK (determinationPhi K) (2+3*K) 2 (by positivity)
  · exact determinationPhi_lipschitz K hK
  · apply Eventually.of_forall
    intro n
    refine ⟨htarget,?_,?_⟩
    · intro P hP
      rw [projIcc_of_mem hK (htarget P hP)]
      change quadraticTarget A P=determinationTarget A P*
        (responseSecondMoment A P-(responseMean A P)^2)+(responseMean A P)^2
      rw [←responseVariance_identity,determinationTarget,
        div_mul_cancel₀ _ (hv.trans_le hP.2).ne',explainedTarget_identity]
      ring
    · intro P _
      have hb:=bounded_vectorPilot_variance P h (determinationPilot_measurable A) 1 (determinationPilot_bound A)
      norm_num at hb ⊢
      exact hb.trans (by norm_num)
  · exact quadratic_positiveVariance_rough_hardness A hM hlo hhi hab hrough vmin hv hv1
  · exact Model.rough_lowerBracket_squared_sample_tendsto A.bracketParameters hrough

 theorem determination_bracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (vmin:ℝ)(hv:0<vmin)(hv1:vmin<1) :
    Model.Bracket (determinationTarget A) (positiveVarianceClass A vmin) A.bracketParameters (A.nu:ℝ) := by
  refine ⟨?_,determination_upperBracket A hM ((le_max_left _ _).trans hlo.le) vmin hv hv1.le⟩
  by_cases hrough : A.theta<1/2
  · exact determination_rough_lowerBracket A hM hlo hhi hab hrough vmin hv hv1
  · exact parametric_lowerBracket A _ _ (le_of_not_gt hrough)
      (determination_parametric_lower A hab ((le_max_right _ _).trans hlo.le) hhi.le vmin hv1.le)

end RoughRegime.Applications.Products
