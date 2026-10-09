module

public import RoughRegime.ApplicationProductClass
public import RoughRegime.ParametricBaselineLower


@[expose] public section
/-! Actual finite Rademacher baselines for every bilinear and quadratic
generic application, including the full statistical nondegeneracy condition. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace RoughRegime.Applications.Products

def sign (b : Bool) : ℝ := if b then 1 else -1

theorem sign_measurable : Measurable sign := measurable_of_countable _

@[simp] theorem sign_abs (b : Bool) : |sign b|=1 := by cases b <;> norm_num [sign]

def pairBaseline : ProbabilityMeasure (Bool×Bool) :=
  ⟨(PMF.uniformOfFintype (Bool×Bool)).toMeasure,inferInstance⟩

def diagonalBaseline : ProbabilityMeasure Bool :=
  ⟨(PMF.uniformOfFintype Bool).toMeasure,inferInstance⟩

theorem pairBaseline_integral (f : Bool×Bool→ℝ) :
    (∫ z, f z ∂(pairBaseline:Measure (Bool×Bool)))=
      (f (false,false)+f (false,true)+f (true,false)+f (true,true))/4 := by
  change (∫ z, f z ∂(PMF.uniformOfFintype (Bool×Bool)).toMeasure)=_
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,Fintype.card_prod,Fintype.card_bool]
  norm_num [Fintype.sum_prod_type,Fintype.univ_bool,smul_eq_mul]
  ring

theorem diagonalBaseline_integral (f : Bool→ℝ) :
    (∫ z, f z ∂(diagonalBaseline:Measure Bool))=(f false+f true)/2 := by
  change (∫ z, f z ∂(PMF.uniformOfFintype Bool).toMeasure)=_
  rw [PMF.integral_eq_sum]
  norm_num [PMF.uniformOfFintype_apply,Fintype.card_bool,Fintype.univ_bool,smul_eq_mul]
  ring

theorem pair_baseline_nondegenerate (A : Model.Parameters)
    (F : Model.Observables (Bool×Bool) A) (hD : F.D=fun _ => 1)
    (hU : F.U=fun z => sign z.1) (hV : F.V=fun z => sign z.2)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) :
    Model.Nondegenerate A F pairBaseline := by
  have hw : Model.baselineW A F pairBaseline=1 := by
    unfold Model.baselineW
    rw [hD,integral_const,probReal_univ]
    simp
  have hau : (∫ z, F.U z ∂(pairBaseline:Measure (Bool×Bool)))=0 := by
    rw [hU,pairBaseline_integral]
    norm_num [sign]
  have hbv : (∫ z, F.V z ∂(pairBaseline:Measure (Bool×Bool)))=0 := by
    rw [hV,pairBaseline_integral]
    norm_num [sign]
  have ha : Model.baselineA A F pairBaseline=0 := by rw [Model.baselineA,hau,hw]; norm_num
  have hb : Model.baselineB A F pairBaseline=0 := by rw [Model.baselineB,hbv,hw]; norm_num
  refine ⟨⟨Finset.univ,by rw [Finset.coe_univ,measure_univ]⟩,by simpa only [hw] using hlo,by simpa only [hw] using hhi,
    by simpa only [ha,abs_zero] using A.hH,by simpa only [hb,abs_zero] using A.hH,?_⟩
  dsimp only
  rw [ha,hb]
  simp only [zero_mul,sub_zero]
  rw [hU,hV,pairBaseline_integral,pairBaseline_integral,pairBaseline_integral]
  left
  norm_num [sign]

theorem diagonal_baseline_nondegenerate (A : Model.Parameters)
    (F : Model.Observables Bool A) (hD : F.D=fun _ => 1) (hU : F.U=sign) (hV : F.V=sign)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) :
    Model.Nondegenerate A F diagonalBaseline := by
  have hw : Model.baselineW A F diagonalBaseline=1 := by
    unfold Model.baselineW
    rw [hD,integral_const,probReal_univ]
    simp
  have hm : (∫ z, sign z ∂(diagonalBaseline:Measure Bool))=0 := by
    rw [diagonalBaseline_integral]
    norm_num [sign]
  have ha : Model.baselineA A F diagonalBaseline=0 := by rw [Model.baselineA,hU,hm,hw]; norm_num
  have hb : Model.baselineB A F diagonalBaseline=0 := by rw [Model.baselineB,hV,hm,hw]; norm_num
  refine ⟨⟨Finset.univ,by rw [Finset.coe_univ,measure_univ]⟩,by simpa only [hw] using hlo,by simpa only [hw] using hhi,
    by simpa only [ha,abs_zero] using A.hH,by simpa only [hb,abs_zero] using A.hH,?_⟩
  dsimp only
  right
  refine ⟨by rw [hU,hV],hab,?_⟩
  rw [ha,hU]
  simp only [zero_mul,sub_zero]
  rw [diagonalBaseline_integral]
  norm_num [sign]

/-- The bilinear product and conditional covariance targets have a genuine
root-n lower bound on their literal conditional-mean class. -/
theorem pair_class_parametric_lower (A : Model.Parameters)
    (F : Model.Observables (Bool×Bool) A) (hD : F.D=fun _ => 1)
    (hU : F.U=fun z => sign z.1) (hV : F.V=fun z => sign z.2)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (Model.target A F) (modelClass A F.U F.V) := by
  obtain ⟨c,hc,n0,_,hn⟩ := Model.main_parametric_lower A F pairBaseline
    (pair_baseline_nondegenerate A F hD hU hV hlo hhi) 1 zero_lt_one
  refine ⟨c,hc,eventually_atTop.2 ⟨n0,?_⟩⟩
  apply hn
  rw [modelClass_eq_generic A F hD ((le_max_left _ _).trans hlo.le)]
  exact Model.localClass_subset A F pairBaseline 1

/-- The quadratic mean-product and expected conditional variance targets
have a genuine root-n lower bound on the diagonal conditional-mean class. -/
theorem diagonal_class_parametric_lower (A : Model.Parameters)
    (F : Model.Observables Bool A) (hD : F.D=fun _ => 1) (hU : F.U=sign) (hV : F.V=sign)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (Model.target A F) (modelClass A F.U F.V) := by
  obtain ⟨c,hc,n0,_,hn⟩ := Model.main_parametric_lower A F diagonalBaseline
    (diagonal_baseline_nondegenerate A F hD hU hV hlo hhi hab) 1 zero_lt_one
  refine ⟨c,hc,eventually_atTop.2 ⟨n0,?_⟩⟩
  apply hn
  rw [modelClass_eq_generic A F hD ((le_max_left _ _).trans hlo.le)]
  exact Model.localClass_subset A F diagonalBaseline 1

end RoughRegime.Applications.Products
