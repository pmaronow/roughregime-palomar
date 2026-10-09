module

public import RoughRegime.PoissonInterleaving


@[expose] public section
/-! Exact dependent reindexing of label words by their count vectors. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.PoissonMeasure
variable {ι : Type*} [Fintype ι]

def WordCount {N : ℕ} (a : Fin N → ι) (i : ι) : ℕ := by
  classical
  exact Fintype.card {j : Fin N // a j = i}

theorem WordCount_sum {N : ℕ} (a : Fin N → ι) : (∑ i, WordCount a i) = N := by
  classical
  simpa only [Fintype.card_sigma, Fintype.card_fin, WordCount] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv a)

theorem WordCount_finCongr {N M : ℕ} (h : N = M) (a : Fin M → ι) (i : ι) :
    WordCount (a ∘ finCongr h) i = WordCount a i := by
  classical
  unfold WordCount
  exact Fintype.card_congr ((finCongr h).subtypeEquivOfSubtype (p := fun j => a j = i))

abbrev LabelWord (ι : Type*) := (N : ℕ) × (Fin N → ι)

def labelWordCounts (w : LabelWord ι) : ι → ℕ := WordCount w.2

def fixedCountWordEquiv (c : ι → ℕ) :
    {a : Fin (∑ i, c i) → ι // ∀ i, WordCount a i = c i} ≃
      {w : LabelWord ι // labelWordCounts w = c} where
  toFun a := ⟨⟨∑ i, c i, a.1⟩, funext a.2⟩
  invFun w := by
    have hs : (∑ i, c i) = w.1.1 := by
      calc
        _ = ∑ i, labelWordCounts w.1 i := congrArg (fun t : ι → ℕ => ∑ i, t i) w.2.symm
        _ = _ := WordCount_sum w.1.2
    refine ⟨w.1.2 ∘ finCongr hs, ?_⟩
    intro i
    rw [WordCount_finCongr]
    exact congrFun w.2 i
  left_inv := by
    rintro ⟨a, ha⟩
    apply Subtype.ext
    funext j
    rfl
  right_inv := by
    rintro ⟨⟨N, a⟩, ha⟩
    have hs : N = ∑ i, c i := by rw [← ha]; exact (WordCount_sum a).symm
    subst N
    apply Subtype.ext
    rfl

def countWordEquiv :
    ((c : ι → ℕ) × {a : Fin (∑ i, c i) → ι // ∀ i, WordCount a i = c i}) ≃ LabelWord ι :=
  (Equiv.sigmaCongrRight fixedCountWordEquiv).trans (Equiv.sigmaFiberEquiv labelWordCounts)

@[simp] theorem countWordEquiv_apply (c : ι → ℕ)
    (a : {a : Fin (∑ i, c i) → ι // ∀ i, WordCount a i = c i}) :
    countWordEquiv ⟨c, a⟩ = ⟨∑ i, c i, a.1⟩ := rfl

end RoughRegime.PoissonMeasure
