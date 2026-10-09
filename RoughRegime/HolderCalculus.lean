module

public import RoughRegime.HolderTensor
public import RoughRegime.HolderRegularity
public import RoughRegime.JetComposition


@[expose] public section
/-! Quantitative calculus for finite Hölder regularity on the closed cube.
All derivatives are the actual derivatives within the cube; no smooth
extension of the input function is assumed. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
namespace RoughRegime.Calculus
set_option maxHeartbeats 1200000

theorem iteratedFDerivWithin_comp_on_open
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : F → G) (s : Set E) (T : Set F) (n : ℕ)
    (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g T)
    (hs : UniqueDiffOn ℝ s) (hT : IsOpen T) (hmap : MapsTo f s T)
    (x : E) (hx : x ∈ s) :
    iteratedFDerivWithin ℝ n (g ∘ f) s x =
      (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeriesWithin ℝ f s x) n := by
  have hcomp := (hg.ftaylorSeriesWithin hT.uniqueDiffOn).comp (hf.ftaylorSeriesWithin hs) hmap
  have he := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := n) le_rfl hs hx
  rw [← he]
  have ho : ftaylorSeriesWithin ℝ g T (f x) = ftaylorSeries ℝ g (f x) := by
    funext q
    exact iteratedFDerivWithin_of_isOpen q hT (hmap hx)
  rw [ho]

end RoughRegime.Calculus
namespace RoughRegime.Model

def holderJetConstant (d : ℕ) (t H : ℝ) : ℝ :=
  ((d : ℝ)+1)^(holderOrder t+1)*H

theorem holderJetConstant_nonneg (d : ℕ) (t H : ℝ) (hH : 0 ≤ H) :
    0 ≤ holderJetConstant d t H := by unfold holderJetConstant; positivity

theorem holderBall_jet_bound_uniform {d : ℕ} (f : Covariate d → ℝ) (t H : ℝ)
    (hH : 0 ≤ H) (hf : f ∈ holderBall t H) (q : ℕ) (hq : q ≤ holderOrder t)
    (x : Covariate d) (hx : x ∈ cube d) :
    ‖iteratedFDerivWithin ℝ q f (cube d) x‖ ≤ holderJetConstant d t H := by
  have hdnn : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hp : (d : ℝ)^q ≤ ((d : ℝ)+1)^(holderOrder t+1) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith : (d : ℝ) ≤ d+1) q).trans
    exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ d+1) (by omega)
  exact (holderBall_iteratedFDerivWithin_bound f t H hH hf q hq x hx).trans
    (mul_le_mul_of_nonneg_right hp hH)

theorem holderBall_jet_modulus_uniform {d : ℕ} (f : Covariate d → ℝ) (t H : ℝ)
    (hH : 0 ≤ H) (hf : f ∈ holderBall t H) (q : ℕ) (hq : q ≤ holderOrder t)
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    ‖iteratedFDerivWithin ℝ q f (cube d) x - iteratedFDerivWithin ℝ q f (cube d) y‖ ≤
      2*holderJetConstant d t H*‖x-y‖^holderExponent t := by
  have hreg := holderBall_regular f t H hf
  have hdnn : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hB := holderJetConstant_nonneg d t H hH
  by_cases heq : q=holderOrder t
  · subst q
    have hb := holderBall_iteratedFDerivWithin_modulus f t H hH hf x y hx hy
    have hp : (d : ℝ)^(holderOrder t)*H ≤ holderJetConstant d t H := by
      apply mul_le_mul_of_nonneg_right _ hH
      apply (pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith : (d : ℝ) ≤ d+1) _).trans
      exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ d+1) (by omega)
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))
  · have hq' : q < holderOrder t := by omega
    have hd := hreg.2.differentiableOn_iteratedFDerivWithin (m := q)
      (by exact_mod_cast hq') (uniqueDiffOn_cube d)
    have hlip := (convex_cube d).norm_image_sub_le_of_norm_fderivWithin_le hd
      (fun z hz => by
        rw [norm_fderivWithin_iteratedFDerivWithin]
        exact holderBall_jet_bound_uniform f t H hH hf (q+1) (by omega) z hz) hy hx
    have hnorm := (norm_sub_le _ _).trans (add_le_add
      (holderBall_jet_bound_uniform f t H hH hf q hq x hx)
      (holderBall_jet_bound_uniform f t H hH hf q hq y hy))
    by_cases hxy : x=y
    · subst y
      simp only [sub_self,norm_zero]
      positivity
    · have hp : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hr := holder_ratio_le hp (holderExponent_pos hreg.1).le (holderExponent_le_one hreg.1)
        (by positivity : 0 ≤ 2*holderJetConstant d t H) hB
        (by linarith only [hnorm]) hlip
      rw [max_eq_left (by linarith : holderJetConstant d t H ≤ 2*holderJetConstant d t H)] at hr
      exact (div_le_iff₀ (Real.rpow_pos_of_pos hp _)).mp hr

end RoughRegime.Model

namespace RoughRegime.Calculus
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure BoundedJetPair (E F G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) (C : ℝ) where
  q1 : FormalMultilinearSeries ℝ F G
  q2 : FormalMultilinearSeries ℝ F G
  p1 : FormalMultilinearSeries ℝ E F
  p2 : FormalMultilinearSeries ℝ E F
  delta : ℝ
  delta_nonneg : 0 ≤ delta
  outer : ∀ k ≤ n, ‖q1 k‖ ≤ C
  inner1 : ∀ k ≤ n, ‖p1 k‖ ≤ C
  inner2 : ∀ k ≤ n, ‖p2 k‖ ≤ C
  outer_difference : ∀ k ≤ n, ‖q1 k-q2 k‖ ≤ C*delta
  inner_difference : ∀ k ≤ n, ‖p1 k-p2 k‖ ≤ C*delta

theorem uniform_taylorComp_difference_constant (n : ℕ) (C : ℝ) :
    ∃ D > 0, ∀ a : BoundedJetPair E F G n C,
      ‖a.q1.taylorComp a.p1 n-a.q2.taylorComp a.p2 n‖ ≤ D*a.delta := by
  exact uniform_taylorComp_difference_bound (fun a : BoundedJetPair E F G n C => a.q1)
    (fun a => a.q2) (fun a => a.p1) (fun a => a.p2) (fun a => a.delta) n C
    (fun a => a.delta_nonneg) (fun k hk a => a.outer k hk)
    (fun k hk a => a.inner1 k hk) (fun k hk a => a.inner2 k hk)
    (fun k hk a => a.outer_difference k hk) (fun k hk a => a.inner_difference k hk)

theorem uniform_taylorComp_norm_constant (n : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D > 0, ∀ (q : FormalMultilinearSeries ℝ F G) (p : FormalMultilinearSeries ℝ E F),
      (∀ k ≤ n, ‖q k‖ ≤ C) → (∀ k ≤ n, ‖p k‖ ≤ C) → ‖q.taylorComp p n‖ ≤ D := by
  obtain ⟨D,hD,hbound⟩ := uniform_taylorComp_difference_constant (E := E) (F := F) (G := G) n C
  refine ⟨D,hD,?_⟩
  intro q p hq hp
  let a : BoundedJetPair E F G n C :=
    ⟨q,fun _ => 0,p,p,1,zero_le_one,hq,hp,hp,
      by simpa only [sub_zero,mul_one] using hq,
      by intro k hk; simp only [sub_self,norm_zero,mul_one]; exact hC⟩
  have hz : (0 : FormalMultilinearSeries ℝ F G).taylorComp p n = 0 := by
    unfold FormalMultilinearSeries.taylorComp
    apply Finset.sum_eq_zero
    intro c _
    unfold FormalMultilinearSeries.compAlongOrderedFinpartition
    rw [← OrderedFinpartition.compAlongOrderedFinpartitionL_apply]
    simp
  have hh := hbound a
  change ‖q.taylorComp p n-(0 : FormalMultilinearSeries ℝ F G).taylorComp p n‖ ≤ D*1 at hh
  simpa only [hz,sub_zero,mul_one] using hh

end RoughRegime.Calculus

namespace RoughRegime.Model

theorem holderBall_of_within_jet_bounds {d : ℕ} (f : Covariate d → ℝ) (t B : ℝ)
    (ht : 0 < t) (hB : 0 ≤ B) (hf : ContDiffOn ℝ (holderOrder t) f (cube d))
    (hb : ∀ q ≤ holderOrder t, ∀ x ∈ cube d, ‖iteratedFDerivWithin ℝ q f (cube d) x‖ ≤ B)
    (hm : ∀ x ∈ cube d, ∀ y ∈ cube d,
      ‖iteratedFDerivWithin ℝ (holderOrder t) f (cube d) x-
        iteratedFDerivWithin ℝ (holderOrder t) f (cube d) y‖ ≤ B*‖x-y‖^holderExponent t) :
    f ∈ holderBall t (2*B) := by
  have hsup : derivativeSup f (holderOrder t) ≤ ENNReal.ofReal B := by
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply ENNReal.ofReal_le_ofReal
    have hh := (iteratedFDerivWithin ℝ q f (cube d) x).le_opNorm
      (fun j => EuclideanSpace.single (σ j) (1 : ℝ))
    have hh' : |coordinateDerivative f q σ x| ≤ ‖iteratedFDerivWithin ℝ q f (cube d) x‖ := by
      simpa only [coordinateDerivative,Real.norm_eq_abs,PiLp.norm_single,norm_one,
        Finset.prod_const_one,mul_one] using hh
    exact hh'.trans (hb q hq x hx)
  have hsem : holderSeminorm f t ≤ ENNReal.ofReal B := by
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hxy
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _)).mpr
    have hh := (iteratedFDerivWithin ℝ (holderOrder t) f (cube d) x-
        iteratedFDerivWithin ℝ (holderOrder t) f (cube d) y).le_opNorm
      (fun j => EuclideanSpace.single (σ j) (1 : ℝ))
    have hh' : |coordinateDerivative f (holderOrder t) σ x-coordinateDerivative f (holderOrder t) σ y| ≤
        ‖iteratedFDerivWithin ℝ (holderOrder t) f (cube d) x-
          iteratedFDerivWithin ℝ (holderOrder t) f (cube d) y‖ := by
      simpa only [coordinateDerivative,sub_apply,Real.norm_eq_abs,
        PiLp.norm_single,norm_one,Finset.prod_const_one,mul_one] using hh
    exact hh'.trans (hm x hx y hy)
  change holderNorm f t ≤ _
  rw [holderNorm,ite_eq_left ⟨ht,hf⟩]
  calc
    _ ≤ ENNReal.ofReal B+ENNReal.ofReal B := add_le_add hsup hsem
    _ = _ := by rw [← ENNReal.ofReal_add hB hB]; congr 1; ring

end RoughRegime.Model
