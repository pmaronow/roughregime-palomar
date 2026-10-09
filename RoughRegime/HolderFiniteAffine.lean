module

public import RoughRegime.HolderQuotient
public import RoughRegime.HolderAffine


@[expose] public section
/-! Exact affine Hölder calculus for functions with only finite regularity
within the closed cube. In particular the complementary propensity retains
the paper's radius `H+1`. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.Model

theorem coordinateDerivative_const_add_finite {d : ℕ} (f : Covariate d → ℝ)
    (t : ℝ) (hf : ContDiffOn ℝ (holderOrder t) f (cube d))
    (c : ℝ) (q : ℕ) (hq : q ≤ holderOrder t) (σ : Fin q → Fin d)
    (x : Covariate d) (hx : x ∈ cube d) :
    coordinateDerivative (fun y => c+f y) q σ x =
      coordinateDerivative (fun _ : Covariate d => c) q σ x + coordinateDerivative f q σ x := by
  unfold coordinateDerivative
  change (iteratedFDerivWithin ℝ q ((fun _ : Covariate d => c)+f) (cube d) x) _ = _
  rw [iteratedFDerivWithin_add_apply contDiffWithinAt_const
    ((hf x hx).of_le (by exact_mod_cast hq)) (uniqueDiffOn_cube d) hx]
  rfl

theorem holderNorm_const_add_le_finite {d : ℕ} (f : Covariate d → ℝ)
    (c t H : ℝ) (ht : 0 < t) (hH : 0 ≤ H) (hf : f ∈ holderBall t H) :
    holderNorm (fun x => c+f x) t ≤ ENNReal.ofReal (|c|+H) := by
  have hregf := (holderBall_regular f t H hf).2
  have hregs : ContDiffOn ℝ (holderOrder t) (fun x => c+f x) (cube d) :=
    contDiffOn_const.add hregf
  have hsup : derivativeSup (fun x => c+f x) (holderOrder t) ≤
      ENNReal.ofReal |c|+derivativeSup f (holderOrder t) := by
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    have hconst : |coordinateDerivative (fun _ : Covariate d => c) q σ x| ≤ |c| := by
      by_cases hq0 : q=0
      · subst q; simp
      · rw [coordinateDerivative_const_pos c hq0]; simpa using abs_nonneg c
    have hcoordSup : ENNReal.ofReal |coordinateDerivative f q σ x| ≤ derivativeSup f (holderOrder t) := by
      unfold derivativeSup
      exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx le_rfl))))
    calc
      _ ≤ ENNReal.ofReal (|coordinateDerivative (fun _ : Covariate d => c) q σ x|+|coordinateDerivative f q σ x|) := by
        apply ENNReal.ofReal_le_ofReal
        rw [coordinateDerivative_const_add_finite f t hregf c q hq σ x hx]
        exact abs_add_le _ _
      _ = ENNReal.ofReal |coordinateDerivative (fun _ : Covariate d => c) q σ x|+
          ENNReal.ofReal |coordinateDerivative f q σ x| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal hconst) hcoordSup
  have hsem : holderSeminorm (fun x => c+f x) t = holderSeminorm f t := by
    unfold holderSeminorm
    congr 1; funext σ
    congr 1; funext x
    congr 1; funext hx
    congr 1; funext y
    congr 1; funext hy
    congr 1; funext hxy
    rw [coordinateDerivative_const_add_finite f t hregf c _ le_rfl σ x hx,
      coordinateDerivative_const_add_finite f t hregf c _ le_rfl σ y hy,
      coordinateDerivative_const_independent c σ x y]
    congr 3 <;> ring
  change holderNorm f t ≤ ENNReal.ofReal H at hf
  rw [holderNorm,ite_eq_left ⟨ht,hregf⟩] at hf
  rw [holderNorm,ite_eq_left ⟨ht,hregs⟩,hsem]
  calc
    _ ≤ (ENNReal.ofReal |c|+derivativeSup f (holderOrder t))+holderSeminorm f t := add_le_add hsup le_rfl
    _ = ENNReal.ofReal |c|+(derivativeSup f (holderOrder t)+holderSeminorm f t) := add_assoc _ _ _
    _ ≤ ENNReal.ofReal |c|+ENNReal.ofReal H := add_le_add le_rfl hf
    _ = _ := (ENNReal.ofReal_add (abs_nonneg _) hH).symm

theorem coordinateDerivative_neg_finite {d : ℕ} (f : Covariate d → ℝ)
    (q : ℕ) (σ : Fin q → Fin d) (x : Covariate d) (hx : x ∈ cube d) :
    coordinateDerivative (fun y => -f y) q σ x = -coordinateDerivative f q σ x := by
  unfold coordinateDerivative
  change (iteratedFDerivWithin ℝ q (-f) (cube d) x) _ = _
  rw [iteratedFDerivWithin_neg_apply (uniqueDiffOn_cube d) hx]
  rfl

theorem holderBall_neg_finite {d : ℕ} (f : Covariate d → ℝ) (t H : ℝ)
    (hf : f ∈ holderBall t H) : (fun x => -f x) ∈ holderBall t H := by
  obtain ⟨ht,hreg⟩ := holderBall_regular f t H hf
  have hsup : derivativeSup (fun x => -f x) (holderOrder t) = derivativeSup f (holderOrder t) := by
    unfold derivativeSup
    congr 1; funext q
    congr 1; funext hq
    congr 1; funext σ
    congr 1; funext x
    congr 1; funext hx
    rw [coordinateDerivative_neg_finite f q σ x hx,abs_neg]
  have hsem : holderSeminorm (fun x => -f x) t = holderSeminorm f t := by
    unfold holderSeminorm
    congr 1; funext σ
    congr 1; funext x
    congr 1; funext hx
    congr 1; funext y
    congr 1; funext hy
    congr 1; funext hxy
    rw [coordinateDerivative_neg_finite f _ σ x hx,coordinateDerivative_neg_finite f _ σ y hy]
    rw [neg_sub_neg,abs_sub_comm]
  change holderNorm _ t ≤ ENNReal.ofReal H
  change holderNorm f t ≤ ENNReal.ofReal H at hf
  rw [holderNorm,ite_eq_left ⟨ht,hreg.neg⟩,hsup,hsem]
  rwa [holderNorm,ite_eq_left ⟨ht,hreg⟩] at hf

theorem holderBall_complement_finite {d : ℕ} (f : Covariate d → ℝ) (t H : ℝ)
    (ht : 0 < t) (hH : 0 ≤ H) (hf : f ∈ holderBall t H) :
    (fun x => 1-f x) ∈ holderBall t (H+1) := by
  have hb := holderNorm_const_add_le_finite (fun x => -f x) 1 t H ht hH
    (holderBall_neg_finite f t H hf)
  change holderNorm _ t ≤ ENNReal.ofReal (H+1)
  simpa only [sub_eq_add_neg,abs_one,add_comm H 1] using hb

end RoughRegime.Model
