module

public import RoughRegime.SpatialContrastPath
public import RoughRegime.ProductVarianceUpper
public import RoughRegime.LowerMeasure


@[expose] public section
/-! Parametric lower bounds for the literal explained-variance and
coefficient-of-determination targets, using a nonconstant smooth sine path. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Products
namespace SineSetup
variable {A : Model.Parameters} (S : SineSetup A)

theorem affine_density (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
    (S.densityLaw t).density =ᵐ[(Model.cubeVolume A.d).prod
      (boundedDiagonalBaseline : Measure BoundedResponse)]
      fun o=>1+t*((o.2:ℝ)*S.phi o.1) := by
  apply ae_of_all
  intro o
  rw [S.density_apply,clampedParameter_eq t ⟨ht.1.le,ht.2.le⟩]
  ring

theorem affine_score_bound (o : Model.Observation A BoundedResponse) :
    |(o.2:ℝ)*S.phi o.1| ≤ S.eta := by
  rw [abs_mul]
  exact (mul_le_mul (response_bound o.2) (S.phi_bound o.1) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem affine_positive (t : ℝ) (ht : t ∈ Ioo (-1) 1)
    (o : Model.Observation A BoundedResponse) :
    (1/2:ℝ)≤1+t*((o.2:ℝ)*S.phi o.1) := by
  have ht' : |t|≤1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
  have hb : |t*((o.2:ℝ)*S.phi o.1)| ≤ S.eta := by
    rw [abs_mul]
    exact (mul_le_mul ht' (S.affine_score_bound o) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hh:=abs_le.mp hb
  linarith [S.small]

/-- The genuine density-path lemma specialized to this fixed smooth,
nonconstant covariate contrast and the actual bounded response experiment. -/
theorem path_minimax_bound
    (T : ProbabilityMeasure (Model.Observation A BoundedResponse)→ℝ)
    (C : Set (ProbabilityMeasure (Model.Observation A BoundedResponse)))
    (t0 D : ℝ) (ht0 : t0∈Ioo (-1) 1)
    (hF : HasDerivAt (fun t=>T (S.probabilityLaw t)) D t0) (hD : D≠0)
    (hclass : ∀t∈Ioo (-1) 1,S.probabilityLaw t∈C) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤Model.minimaxRMSE n T C := by
  obtain ⟨c,hc,he⟩ := LowerMeasure.parametric_path_minimax_bound S.densityLaw
    (fun _=>1) (fun o=>(o.2:ℝ)*S.phi o.1) T C (-1) 1 t0 D (1/2) S.eta
    ht0 hF hD (by norm_num) S.positive.le (S.affine_density)
    (fun t ht=>ae_of_all _ (S.affine_positive t ht))
    (ae_of_all _ S.affine_score_bound) hclass
  exact ⟨c,hc,he.mono (fun _ hn=>hn.1)⟩

theorem explained_hasDerivAt (t0 : ℝ) (ht0 : t0 ∈ Ioo (-1) 1) :
    HasDerivAt (fun t=>explainedTarget A (S.probabilityLaw t)) (t0*S.eta^2) t0 := by
  have hp := ((hasDerivAt_id t0).pow 2).mul_const (S.eta^2/2)
  have hd : (2*t0^(2-1)*1)*(S.eta^2/2)=t0*S.eta^2 := by norm_num; ring
  simp only [id_eq,Nat.cast_ofNat] at hp
  rw [hd] at hp
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht0.1 ht0.2] with t ht
  rw [S.explainedTarget_value,clampedParameter_eq t ⟨ht.1.le,ht.2.le⟩]
  dsimp
  ring

theorem determination_value (t : ℝ) : determinationTarget A (S.probabilityLaw t)=
    (clampedParameter t)^2*S.eta^2/2 := by
  rw [determinationTarget,S.explainedTarget_value,S.responseVariance_one,div_one]

theorem determination_hasDerivAt (t0 : ℝ) (ht0 : t0 ∈ Ioo (-1) 1) :
    HasDerivAt (fun t=>determinationTarget A (S.probabilityLaw t)) (t0*S.eta^2) t0 := by
  exact (S.explained_hasDerivAt t0 ht0).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t=>by dsimp only; rw [S.determination_value,S.explainedTarget_value]))

end SineSetup

theorem explained_parametric_lower (A : Model.Parameters)
    (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (explainedTarget A) (quadraticClass A) := by
  let S:=sineSetup A
  exact S.path_minimax_bound _ _ (1/2) ((1/2)*S.eta^2) (by norm_num)
    (S.explained_hasDerivAt _ (by norm_num))
    (by have:=S.positive; positivity) (fun t _=>S.quadraticClass_member hab hlo hhi t)

theorem determination_parametric_lower (A : Model.Parameters)
    (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus)
    (vmin : ℝ) (hv : vmin≤1) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (determinationTarget A) (positiveVarianceClass A vmin) := by
  let S:=sineSetup A
  apply S.path_minimax_bound _ _ (1/2) ((1/2)*S.eta^2) (by norm_num)
    (S.determination_hasDerivAt _ (by norm_num)) (by have:=S.positive; positivity)
  intro t _
  exact ⟨S.quadraticClass_member hab hlo hhi t,by rw [S.responseVariance_one]; exact hv⟩

end RoughRegime.Applications.Products
