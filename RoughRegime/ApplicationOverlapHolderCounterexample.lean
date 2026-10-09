module

public import RoughRegime.ApplicationOverlapHolder
public import Mathlib.Analysis.Calculus.Deriv.Abs


@[expose] public section
/-! A concrete overlapping propensity shows the two Hölder conventions can
differ when beta exceeds alpha: alpha=1, beta=2, m=w, gamma=1. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def cuspPropensity (x:Model.Covariate 1):ℝ:=1/2+1/4*min |x 0-1/2| (1/2)

theorem cuspPropensity_range (x:Model.Covariate 1):cuspPropensity x∈Icc (1/2:ℝ) (5/8):=by
  have hm:0 ≤ min |x 0-1/2| (1/2):=le_min (abs_nonneg _) (by norm_num)
  have hb:=min_le_right |x 0-1/2| (1/2:ℝ)
  unfold cuspPropensity
  constructor <;> linarith

theorem cuspPropensity_continuous:Continuous cuspPropensity:=by
  unfold cuspPropensity
  fun_prop

theorem cuspPropensity_lipschitz (x y:Model.Covariate 1):
    |cuspPropensity x-cuspPropensity y| ≤ (1/4:ℝ)*‖x-y‖:=by
  have hmin:=abs_min_sub_min_le_max |x 0-1/2| (1/2:ℝ) |y 0-1/2| (1/2:ℝ)
  have hm:|min |x 0-1/2| (1/2)-min |y 0-1/2| (1/2)| ≤ |x 0-y 0|:=by
    apply hmin.trans
    apply max_le
    · have h:=abs_abs_sub_abs_le_abs_sub (x 0-1/2) (y 0-1/2)
      convert h using 1
      congr 1;ring
    · simp only [sub_self,abs_zero];exact abs_nonneg _
  have hn:|x 0-y 0| ≤ ‖x-y‖:=by
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) 0
  have he:|cuspPropensity x-cuspPropensity y|=(1/4:ℝ)*|min |x 0-1/2| (1/2)-min |y 0-1/2| (1/2)|:=by
    unfold cuspPropensity
    have he:(1/2+1/4*min |x 0-1/2| (1/2))-(1/2+1/4*min |y 0-1/2| (1/2))=
        (1/4:ℝ)*(min |x 0-1/2| (1/2)-min |y 0-1/2| (1/2)):=by ring
    rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
  rw [he]
  exact mul_le_mul_of_nonneg_left (hm.trans hn) (by norm_num)

theorem cuspPropensity_mem_holder_one:cuspPropensity∈Model.holderBall 1 1:=by
  have hk:Model.holderOrder 1=0:=by norm_num [Model.holderOrder]
  have he:Model.holderExponent 1=1:=by rw [Model.holderExponent,hk];norm_num
  have hc (σ:Fin (Model.holderOrder 1)→Fin 1) (x:Model.Covariate 1):
      Model.coordinateDerivative cuspPropensity (Model.holderOrder 1) σ x=cuspPropensity x:=by
    exact Model.coordinateDerivative_of_order_zero cuspPropensity _ hk σ x
  have hreg:ContDiffOn ℝ (Model.holderOrder 1) cuspPropensity (Model.cube 1):=by
    rw [hk];exact contDiffOn_zero.mpr cuspPropensity_continuous.continuousOn
  have hsup:Model.derivativeSup cuspPropensity (Model.holderOrder 1) ≤ ENNReal.ofReal (5/8:ℝ):=by
    apply iSup_le;intro q
    apply iSup_le;intro hq
    have hq0:q=0:=by rw [hk] at hq;omega
    subst q
    apply iSup_le;intro σ
    apply iSup_le;intro x
    apply iSup_le;intro hx
    apply ENNReal.ofReal_le_ofReal
    change |cuspPropensity x| ≤ 5/8
    rw [abs_of_nonneg (by linarith [(cuspPropensity_range x).1])]
    exact (cuspPropensity_range x).2
  have hsem:Model.holderSeminorm cuspPropensity 1 ≤ ENNReal.ofReal (1/4:ℝ):=by
    apply iSup_le;intro σ
    apply iSup_le;intro x
    apply iSup_le;intro hx
    apply iSup_le;intro y
    apply iSup_le;intro hy
    apply iSup_le;intro hxy
    apply ENNReal.ofReal_le_ofReal
    rw [hc σ x,hc σ y,he,Real.rpow_one]
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).mpr (cuspPropensity_lipschitz x y)
  change Model.holderNorm cuspPropensity 1 ≤ _
  rw [Model.holderNorm,ite_eq_left ⟨by norm_num,hreg⟩]
  apply (add_le_add hsup hsem).trans
  rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 5/8) (by norm_num : (0:ℝ) ≤ 1/4)]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (5/8+1/4:ℝ) ≤ 1 by norm_num)

def cuspLine (r:ℝ):Model.Covariate 1:=WithLp.toLp 2 (fun _=>r+1/2)

theorem cuspPropensity_not_mem_holder_two (H:ℝ):cuspPropensity∉Model.holderBall 2 H:=by
  intro h
  have hr:=Model.holderBall_regular cuspPropensity 2 H h
  have hk:Model.holderOrder 2=1:=by norm_num [Model.holderOrder]
  rw [hk] at hr
  have hline:ContDiff ℝ 1 cuspLine:=by
    apply (contDiff_piLp 2).mpr
    intro i
    change ContDiff ℝ 1 (fun r:ℝ=>r+1/2)
    exact contDiff_id.add contDiff_const
  have hmap:MapsTo cuspLine (Icc (-1/4:ℝ) (1/4)) (Model.cube 1):=by
    intro r hr i
    change 0 ≤ r+1/2 ∧ r+1/2 ≤ 1
    constructor <;> linarith [hr.1,hr.2]
  have hwithin:=hr.2.comp hline.contDiffOn hmap
  have hd: DifferentiableAt ℝ (cuspPropensity∘cuspLine) 0:=
    ((hwithin 0 (by norm_num)).differentiableWithinAt (by norm_num)).differentiableAt
      (Icc_mem_nhds (by norm_num) (by norm_num))
  have hEq:(cuspPropensity∘cuspLine)=ᶠ[𝓝 (0:ℝ)] fun r=>1/2+1/4*|r|:=by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1/4:ℝ)<0) (by norm_num : (0:ℝ)<1/4)] with r hr
    have hb:|r| ≤ (1/2:ℝ):=abs_le.mpr ⟨by linarith [hr.1],by linarith [hr.2]⟩
    change 1/2+1/4*min |(r+1/2)-1/2| (1/2)=1/2+1/4*|r|
    rw [add_sub_cancel_right,min_eq_left hb]
  have hd':DifferentiableAt ℝ (fun r:ℝ=>1/2+1/4*|r|) 0:=hd.congr_of_eventuallyEq hEq.symm
  have habs:DifferentiableAt ℝ (abs:ℝ→ℝ) 0:=by
    have h: DifferentiableAt ℝ (fun r:ℝ=>(1/2+1/4*|r|-1/2)*4) 0:=
      (hd'.sub (differentiableAt_const (1/2:ℝ))).mul_const 4
    convert h using 1
    funext r;ring
  exact not_differentiableAt_abs_zero habs

/-- The radius conventions truly differ for higher beta: a positive,
overlapping Lipschitz propensity and m=w have a zero smooth residual,
although m is absent from every beta=2 Hölder ball. -/
theorem higher_beta_radius_conventions_differ:
    ∃ w m:Model.Covariate 1→ℝ,
      (∀ x,w x∈Icc (1/2:ℝ) (5/8)) ∧ w∈Model.holderBall 1 1 ∧
      (fun x=>m x-(1:ℝ)*w x)∈Model.holderBall 2 1 ∧
      ∀ H:ℝ,m∉Model.holderBall 2 H:=by
  refine ⟨cuspPropensity,cuspPropensity,cuspPropensity_range,cuspPropensity_mem_holder_one,?_,cuspPropensity_not_mem_holder_two⟩
  simpa only [one_mul,sub_self] using Model.const_mem_holderBall (d:=1) (t:=2) (c:=0) (H:=1) (by norm_num) (by norm_num)

end RoughRegime.Applications.Overlap
