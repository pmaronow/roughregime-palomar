module

public import RoughRegime.SpatialPredictionLower
public import RoughRegime.UniformTwoPoint


@[expose] public section
/-! The prediction-loss parametric constant and sample cutoff are chosen
before the known predictor. Exact quadratic two-point separation removes
any dependence on a predictor-specific derivative neighborhood. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Products
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000

 theorem uniform_excessLoss_parametric_lower (A : Model.Parameters)
     (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus) (M : ℝ) :
     ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
       ∀(f0 : Model.Covariate A.d→ℝ),Measurable f0→(∀x,|f0 x|≤M)→
       ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
         Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A) := by
   let S:=sineSetup A
   obtain ⟨a,ha,hsmall⟩ := Lower.exists_small_parametric_amplitude (1/2) S.eta
   let h : ℕ→ℝ := fun n=>a/Real.sqrt (n:ℝ)
   let Dmin := S.eta^2/4
   let c := Dmin*a/4
   have hη : 0<S.eta := S.positive
   have hc : 0<c := by dsimp [c,Dmin]; positivity
   have hhzero : Tendsto h atTop (nhds 0) := by
     have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
       (tendsto_natCast_atTop_atTop : Tendsto (fun n:ℕ=>(n:ℝ)) atTop atTop))
     simpa only [h,div_eq_mul_inv,mul_zero,Function.comp_apply] using hi.const_mul a
   refine ⟨c,hc,?_⟩
   filter_upwards [hhzero.eventually_le_const (by norm_num : (0:ℝ)<1/8),eventually_gt_atTop 0]
     with n hnb hn
   intro f0 hf hb
   let B:=∫x,S.phi x*f0 x ∂Model.cubeVolume A.d
   have htchoice : ∃t0:ℝ,(t0=1/4 ∨ t0=1/2) ∧ S.eta^2/8≤|t0*S.eta^2-2*B| := by
     by_cases ht : S.eta^2/8≤|(1/4)*S.eta^2-2*B|
     · exact ⟨1/4,Or.inl rfl,ht⟩
     · refine ⟨1/2,Or.inr rfl,?_⟩
       have he : (1/2)*S.eta^2-2*B-((1/4)*S.eta^2-2*B)=S.eta^2/4 := by ring
       have ht' := abs_add_le ((1/2)*S.eta^2-2*B) (-((1/4)*S.eta^2-2*B))
       simp only [←sub_eq_add_neg,abs_neg] at ht'
       rw [he,abs_of_nonneg (by positivity : 0≤S.eta^2/4)] at ht'
       linarith
   obtain ⟨t0,ht0,hD⟩ := htchoice
   have hnR : 0<(n:ℝ) := by exact_mod_cast hn
   have hnp : 0<h n := div_pos ha (Real.sqrt_pos.mpr hnR)
   have htplus : t0+h n∈Ioo (-1) 1 := by rcases ht0 with rfl | rfl <;> constructor <;> linarith
   have htminus : t0-h n∈Ioo (-1) 1 := by rcases ht0 with rfl | rfl <;> constructor <;> linarith
   have hH : (n:ℝ)*S.eta^2*(h n)^2/(1/2) ≤ 1/4 := by
     have he : (n:ℝ)*S.eta^2*(h n)^2/(1/2)=S.eta^2*a^2/(1/2) := by
       dsimp [h]
       rw [div_pow,Real.sq_sqrt hnR.le]
       field_simp
     rw [he]
     exact hsmall
   have he : excessLoss A f0 (S.probabilityLaw (t0+h n))-
       excessLoss A f0 (S.probabilityLaw (t0-h n))=2*h n*(t0*S.eta^2-2*B) := by
     rw [S.excessLoss_value f0 hf M hb,S.excessLoss_value f0 hf M hb,
       clampedParameter_eq _ ⟨htplus.1.le,htplus.2.le⟩,
       clampedParameter_eq _ ⟨htminus.1.le,htminus.2.le⟩]
     dsimp only [B]
     ring
   have hsep : Dmin*h n ≤ |excessLoss A f0 (S.probabilityLaw (t0+h n))-
       excessLoss A f0 (S.probabilityLaw (t0-h n))| := by
     rw [he,abs_mul,abs_of_pos (by positivity : 0<2*h n)]
     dsimp [Dmin]
     nlinarith [mul_le_mul_of_nonneg_left hD hnp.le]
   have ht := LowerMeasure.affine_two_point_minimax S.densityLaw (fun _=>1)
     (fun o:Model.Observation A BoundedResponse=>(o.2:ℝ)*S.phi o.1)
     (excessLoss A f0) (quadraticClass A) (-1) 1 t0 (h n) Dmin (1/2) S.eta n
     (by dsimp [Dmin]; positivity) hnp (by norm_num) hη.le htplus htminus
     S.affine_density (fun t ht=>ae_of_all _ (S.affine_positive t ht))
     (ae_of_all _ S.affine_score_bound) hH
     (S.quadraticClass_member hab hlo hhi _) (S.quadraticClass_member hab hlo hhi _) hsep
   have hscale : c*(n:ℝ)^(-(1/2:ℝ))=Dmin*h n/4 := by
     rw [Real.rpow_neg hnR.le,←Real.sqrt_eq_rpow]
     dsimp [c,h]
     ring
   rw [hscale]
   exact ht.1

end RoughRegime.Applications.Products
