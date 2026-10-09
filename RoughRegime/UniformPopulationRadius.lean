module

public import RoughRegime.KernelExpressions


@[expose] public section
/-! Source Lemma 5(b) constants depend on a population radius and the fixed
expression and affine maps, and are chosen before the population set itself. -/
noncomputable section
open Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace RoughRegime.KernelExpressions

theorem real_affine_expression_truncations_uniform_radius {p : ℕ} {I : Type*} {dims : I→ℕ}
    (lo hi : ℝ) (hlo : 0<lo) (hlt : lo<hi) (R : ℝ)
    (M : (i : I)→(Fin p→ℂ)→ᵃ[ℂ] Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (f : Expression p dims) :
    ∃ ε C : ℝ, 0<ε ∧ ε≤1 ∧ 0≤C ∧
      ∀ (V : Set (Fin p→ℝ)),
      (∀ x∈V, ‖x‖≤R) →
      (∀ i x, x∈V → (M i (realParametersCLM p x)).IsHermitian) →
      (∀ i x, x∈V → spectrum ℝ (M i (realParametersCLM p x))⊆Icc lo hi) →
      ∀ t : Fin p→ℂ, (∃ t0∈V, ‖t-realParametersCLM p t0‖<ε) → ∀ m : ℕ,
        ‖∑ k∈Finset.range (m+1), PowerSeries.coeff k (f.series lo hi (fun i=>M i) t)‖≤C := by
  let W : Set (Fin p→ℝ) := {x | ‖x‖≤R ∧
    ∀ i, (M i (realParametersCLM p x)).IsHermitian ∧
      spectrum ℝ (M i (realParametersCLM p x))⊆Icc lo hi}
  have hW : Bornology.IsBounded W := isBounded_iff_forall_norm_le.mpr ⟨R,fun _ hx=>hx.1⟩
  obtain ⟨ε,C,hε,hε1,hC,hb⟩ := real_affine_expression_truncations lo hi hlo hlt W hW M
    (fun i _ hx=>(hx.2 i).1) (fun i _ hx=>(hx.2 i).2) f
  refine ⟨ε,C,hε,hε1,hC,?_⟩
  intro V hnorm hHerm hSpec t ht m
  obtain ⟨x,hx,hnear⟩ := ht
  exact hb t ⟨x,⟨hnorm x hx,fun i=>⟨hHerm i x hx,hSpec i x hx⟩⟩,hnear⟩ m

end RoughRegime.KernelExpressions
