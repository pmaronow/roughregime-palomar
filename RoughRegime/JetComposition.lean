module

public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp


@[expose] public section
/-! Uniform quantitative continuity of higher derivative composition, obtained
from the actual finite Faà di Bruno formula. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators ContDiff
namespace RoughRegime.Calculus
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Taylor composition has the expected homogeneity in outer and graded inner jets. -/
theorem taylorComp_smul_graded (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) (s r : ℝ) (n : ℕ) :
    FormalMultilinearSeries.taylorComp (fun k => s • q k) (fun k => r ^ k • p k) n =
      (s * r ^ n) • q.taylorComp p n := by
  unfold FormalMultilinearSeries.taylorComp
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition
  have hpow : (∏ i : Fin c.length, r ^ c.partSize i) = r ^ n := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using c.prod_sigma_eq_prod (fun _ => r)
  rw [← OrderedFinpartition.compAlongOrderedFinpartitionL_apply,
    ← OrderedFinpartition.compAlongOrderedFinpartitionL_apply]
  rw [map_smul, smul_apply,
    ContinuousMultilinearMap.map_smul_univ, hpow, smul_smul]

/-- Uniformly bounded finite jets with uniformly O(delta) differences yield
uniformly O(delta) derivative compositions, with a genuine uniform constant. -/
theorem uniform_taylorComp_difference_bound {A : Type*}
    (q₁ q₂ : A → FormalMultilinearSeries ℝ F G)
    (p₁ p₂ : A → FormalMultilinearSeries ℝ E F) (δ : A → ℝ)
    (n : ℕ) (C : ℝ) (hδ : ∀ a, 0 ≤ δ a)
    (hq₁ : ∀ k, k ≤ n → ∀ a, ‖q₁ a k‖ ≤ C)
    (hp₁ : ∀ k, k ≤ n → ∀ a, ‖p₁ a k‖ ≤ C)
    (hp₂ : ∀ k, k ≤ n → ∀ a, ‖p₂ a k‖ ≤ C)
    (hqdiff : ∀ k, k ≤ n → ∀ a, ‖q₁ a k - q₂ a k‖ ≤ C * δ a)
    (hpdiff : ∀ k, k ≤ n → ∀ a, ‖p₁ a k - p₂ a k‖ ≤ C * δ a) :
    ∃ D : ℝ, 0 < D ∧ ∀ a,
      ‖(q₁ a).taylorComp (p₁ a) n - (q₂ a).taylorComp (p₂ a) n‖ ≤ D * δ a := by
  have hbq (k : ℕ) (hk : k ≤ n) : (⊤ : Filter A).IsBoundedUnder (· ≤ ·) (fun a => ‖q₁ a k‖) :=
    isBoundedUnder_of ⟨C, hq₁ k hk⟩
  have hbp₁ (k : ℕ) (hk : k ≤ n) : (⊤ : Filter A).IsBoundedUnder (· ≤ ·) (fun a => ‖p₁ a k‖) :=
    isBoundedUnder_of ⟨C, hp₁ k hk⟩
  have hbp₂ (k : ℕ) (hk : k ≤ n) : (⊤ : Filter A).IsBoundedUnder (· ≤ ·) (fun a => ‖p₂ a k‖) :=
    isBoundedUnder_of ⟨C, hp₂ k hk⟩
  have hoq (k : ℕ) (hk : k ≤ n) : (fun a => q₁ a k - q₂ a k) =O[⊤] δ := by
    apply IsBigO.of_bound C
    exact eventually_top.mpr (fun a => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hδ a)] using hqdiff k hk a)
  have hop (k : ℕ) (hk : k ≤ n) : (fun a => p₁ a k - p₂ a k) =O[⊤] δ := by
    apply IsBigO.of_bound C
    exact eventually_top.mpr (fun a => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hδ a)] using hpdiff k hk a)
  have h := FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO hbq hoq hbp₁ hbp₂ hop
  obtain ⟨D, hD, hb⟩ := h.exists_pos
  refine ⟨D, hD, ?_⟩
  intro a
  have hh := eventually_top.mp hb.bound a
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hδ a)] using hh

/-- A local composition bound uses genuine partial jets at the actual point;
it does not require globally smooth extensions of either function. -/
theorem local_composition_jet_norm_bound (g : F → G) (f : E → F) (x : E) (n : ℕ)
    (hg : ContDiffAt ℝ ∞ g (f x)) (hf : ContDiffAt ℝ ∞ f x)
    (C : ℝ) (hC : 0 ≤ C)
    (houter : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k g (f x)‖ ≤ C)
    (hinner : ∀ k, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) * C := by
  rw [iteratedFDeriv_comp hg hf (by simp)]
  unfold FormalMultilinearSeries.taylorComp
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _c : OrderedFinpartition n, C := by
      apply Finset.sum_le_sum
      intro c _
      apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
      have hp : (∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) f x‖) ≤ 1 := by
        apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
        intro i _
        have hi : 1 ≤ c.partSize i := Nat.one_le_iff_ne_zero.mpr (c.neZero_partSize i).out
        exact hinner _ hi (c.partSize_le i)
      exact (mul_le_mul (houter _ c.length_le) hp (Finset.prod_nonneg (fun i _ => norm_nonneg _)) hC).trans_eq (by ring)
    _ = _ := by simp

/-- The local Faà di Bruno bound at a genuine spatial scale L. -/
theorem local_composition_jet_norm_bound_scaled (g : F → G) (f : E → F) (x : E) (n : ℕ)
    (hg : ContDiffAt ℝ ∞ g (f x)) (hf : ContDiffAt ℝ ∞ f x)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (houter : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k g (f x)‖ ≤ C)
    (hinner : ∀ k, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ L^k) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ)*C*L^n := by
  rw [iteratedFDeriv_comp hg hf (by simp)]
  unfold FormalMultilinearSeries.taylorComp
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _c : OrderedFinpartition n, C*L^n := by
      apply Finset.sum_le_sum
      intro c _
      apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
      have hp : (∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) f x‖) ≤ L^n := by
        have he : (∏ i : Fin c.length, L^c.partSize i) = L^n := by
          simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using c.prod_sigma_eq_prod (fun _ => L)
        rw [← he]
        apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        intro i _
        exact hinner _ (Nat.one_le_iff_ne_zero.mpr (c.neZero_partSize i).out) (c.partSize_le i)
      exact mul_le_mul (houter _ c.length_le) hp (Finset.prod_nonneg (fun i _ => norm_nonneg _)) hC
    _ = _ := by simp [mul_assoc]

end RoughRegime.Calculus
