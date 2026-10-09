module

public import RoughRegime.ScalarHolder


@[expose] public section
/-! Exact baseline preservation under Hölder-small smooth perturbations. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.Model

 theorem coordinateDerivative_const_add {d : ℕ} (f : Covariate d → ℝ) (hf : ContDiff ℝ ∞ f)
     (c : ℝ) (q : ℕ) (σ : Fin q → Fin d) (x : Covariate d) (hx : x∈cube d) :
     coordinateDerivative (fun y => c+f y) q σ x =
       coordinateDerivative (fun _ : Covariate d => c) q σ x + coordinateDerivative f q σ x := by
   have hs : ContDiff ℝ ∞ (fun y => c+f y) := contDiff_const.add hf
   rw [coordinateDerivative_eq_iteratedFDeriv _ q σ x hx (hs.of_le (by simp)).contDiffAt,
     coordinateDerivative_eq_iteratedFDeriv _ q σ x hx contDiffAt_const,
     coordinateDerivative_eq_iteratedFDeriv _ q σ x hx (hf.of_le (by simp)).contDiffAt]
   change (iteratedFDeriv ℝ q ((fun _ : Covariate d => c)+f) x) _ = _
   rw [iteratedFDeriv_add_apply contDiffAt_const (hf.of_le (by simp)).contDiffAt]
   rfl

 theorem holderNorm_const_add_le {d : ℕ} (f : Covariate d → ℝ) (hf : ContDiff ℝ ∞ f)
     (c t H : ℝ) (ht : 0 < t) (hH : 0 ≤ H) (hb : holderNorm f t ≤ ENNReal.ofReal H) :
     holderNorm (fun x => c+f x) t ≤ ENNReal.ofReal (|c|+H) := by
   have hs : ContDiff ℝ ∞ (fun y => c+f y) := contDiff_const.add hf
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
         rw [coordinateDerivative_const_add f hf c q σ x hx]
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
     rw [coordinateDerivative_const_add f hf c _ σ x hx,coordinateDerivative_const_add f hf c _ σ y hy,
       coordinateDerivative_const_independent c σ x y]
     congr 3 <;> ring
   have hregf : 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) := ⟨ht,(hf.of_le (by simp)).contDiffOn⟩
   have hregs : 0 < t ∧ ContDiffOn ℝ (holderOrder t) (fun x => c+f x) (cube d) := ⟨ht,(hs.of_le (by simp)).contDiffOn⟩
   rw [holderNorm,ite_eq_left hregf] at hb
   rw [holderNorm,ite_eq_left hregs,hsem]
   calc
     _ ≤ (ENNReal.ofReal |c|+derivativeSup f (holderOrder t))+holderSeminorm f t := add_le_add hsup le_rfl
     _ = ENNReal.ofReal |c|+(derivativeSup f (holderOrder t)+holderSeminorm f t) := add_assoc _ _ _
     _ ≤ ENNReal.ofReal |c|+ENNReal.ofReal H := add_le_add le_rfl hb
     _ = _ := (ENNReal.ofReal_add (abs_nonneg _) hH).symm

end RoughRegime.Model
