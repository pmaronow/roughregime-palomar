module

public import RoughRegime.GateLaw


@[expose] public section
/-! Concrete gated Fourier pattern estimates. All band restrictions below
are derived from the sampled sinc laws, not supplied as support axioms. -/
noncomputable section
namespace RoughRegime.LatticePriors
open RoughRegime.Lattice RoughRegime.LatticeFourier
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι]

 def patternFrequency (n p : Finset κ) (s : ι → κ → ℝ) (i : ι) : ℝ :=
  (∑ j ∈ n, s i j) - ∑ j ∈ p, s i j

 def signedPatternFrequency (ε : Bool) (n p : Finset κ) (s : ι → κ → ℝ) (i : ι) : ℝ :=
  if ε then -patternFrequency n p s i else patternFrequency n p s i

 def patternCharacteristic (Q M : ℕ) (η lam : ι → ℝ) (ε : Bool)
    (n p : Finset κ) (s : ι → κ → ℝ) : ℂ :=
  ∏ i, latticeCharacteristic Q M (η i) (lam i) (signedPatternFrequency ε n p s i)

 def patternPenalty (n p : Finset κ) (s : ι → κ → ℝ) (Ω : ι → ℝ) (e : ι → Bool) : ℝ :=
  Real.exp (-(∑ i, Ω i * mismatch n p (s i) (e i)))

 theorem nonzero_characteristic_has_signed_alias (Q M : ℕ) (η lam X : ℝ) (ε : Bool)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hlam : 1 ≤ lam)
    (hne : latticeCharacteristic Q M η lam (if ε then -X else X) ≠ 0) :
    ∃ l : ℤ, |X - (l : ℝ) * M| ≤ 6 * Q / η := by
  have hs : ∃ l : ℤ, |(if ε then -X else X) - (l : ℝ) * M| ≤ 6 * Q / η := by
    by_contra h
    exact hne (latticeCharacteristic_eq_zero Q M η lam _ hQ hM hη hlam h)
  rcases hs with ⟨l, hl⟩
  cases ε with
  | false => exact ⟨l, hl⟩
  | true =>
    refine ⟨-l, ?_⟩
    simp only [↓reduceIte, Int.cast_neg] at hl ⊢
    have heq : X - -(l : ℝ) * M = -(-X - (l : ℝ) * M) := by ring
    rw [heq, abs_neg]
    exact hl

/-- Nonzero products force a single target string obeying every one of
 the paper's digit mismatch inequalities simultaneously. -/
 theorem pattern_nonzero_implies_mismatch (Q M k : ℕ) (η lam : ι → ℝ) (ε : Bool)
    (n p : Finset κ) (s : ι → κ → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hk : 2 * (k : ℝ) < M)
    (hη : ∀ i, 0 < η i) (hlam : ∀ i, 1 ≤ lam i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (hn : n.card = M + k) (hp : p.card = k)
    (hs : ∀ i j, 0 ≤ s i j ∧ s i j ≤ 1)
    (hne : patternCharacteristic Q M η lam ε n p s ≠ 0) :
    ∃ e : ι → Bool, ∀ i, mismatch n p (s i) (e i) ≤ (k : ℝ) + 6 * Q / η i := by
  have hmis : ∀ i, ∃ e : Bool, mismatch n p (s i) e ≤ (k : ℝ) + 6 * Q / η i := by
    intro i
    have hchar : latticeCharacteristic Q M (η i) (lam i) (signedPatternFrequency ε n p s i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
    obtain ⟨l, hl⟩ := nonzero_characteristic_has_signed_alias Q M (η i) (lam i)
      (patternFrequency n p s i) ε hQ hM (hη i) (hlam i) hchar
    exact alias_implies_mismatch n p (s i) M k (6 * Q / η i) l hM hk (hband i) hn hp
      (fun j _ => (hs i j).1) (fun j _ => (hs i j).2)
      (fun j _ => (hs i j).1) (fun j _ => (hs i j).2) hl
  choose e he using hmis
  exact ⟨e, he⟩

 theorem patternCharacteristic_norm_le_one (Q M : ℕ) (η lam : ι → ℝ) (ε : Bool)
    (n p : Finset κ) (s : ι → κ → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ)) :
    ‖patternCharacteristic Q M η lam ε n p s‖ ≤ 1 := by
  unfold patternCharacteristic
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
    (fun i _ => latticeCharacteristic_norm_le_one Q M (η i) (lam i) _ hQ hM (hη i) (hband i))

/-- Exponential soft mismatch bound for the actual product of gated lattice
characteristic functions. The sum runs over all concrete target digit strings. -/
 theorem patternCharacteristic_penalty_bound [DecidableEq ι] (Q M k : ℕ) (η lam Ω : ι → ℝ) (ε : Bool)
    (n p : Finset κ) (s : ι → κ → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hk : 2 * (k : ℝ) < M)
    (hη : ∀ i, 0 < η i) (hlam : ∀ i, 1 ≤ lam i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ)) (hΩ : ∀ i, 0 ≤ Ω i)
    (hn : n.card = M + k) (hp : p.card = k)
    (hs : ∀ i j, 0 ≤ s i j ∧ s i j ≤ 1) :
    ‖patternCharacteristic Q M η lam ε n p s‖ ≤
      Real.exp (∑ i, Ω i * ((k : ℝ) + 6 * Q / η i)) *
        ∑ e : ι → Bool, patternPenalty n p s Ω e := by
  classical
  by_cases hzero : patternCharacteristic Q M η lam ε n p s = 0
  · rw [hzero, norm_zero]
    apply mul_nonneg (Real.exp_pos _).le
    apply Finset.sum_nonneg
    intro e he
    exact (Real.exp_pos _).le
  · obtain ⟨e, he⟩ := pattern_nonzero_implies_mismatch Q M k η lam ε n p s hQ hM hk
      hη hlam hband hn hp hs hzero
    have hsum : (∑ i, Ω i * mismatch n p (s i) (e i)) ≤
        ∑ i, Ω i * ((k : ℝ) + 6 * Q / η i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (he i) (hΩ i))
    have hone : 1 ≤ Real.exp (∑ i, Ω i * ((k : ℝ) + 6 * Q / η i)) * patternPenalty n p s Ω e := by
      unfold patternPenalty
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have heSum : patternPenalty n p s Ω e ≤ ∑ e : ι → Bool, patternPenalty n p s Ω e := by
      unfold patternPenalty
      exact Finset.single_le_sum (f := fun e : ι → Bool => Real.exp (-∑ i, Ω i * mismatch n p (s i) (e i)))
        (fun e _ => (Real.exp_pos _).le) (Finset.mem_univ e)
    exact (patternCharacteristic_norm_le_one Q M η lam ε n p s hQ hM hη hband).trans
      (hone.trans (mul_le_mul_of_nonneg_left heSum (Real.exp_pos _).le))

/-- Exact factorization into separate pointwise penalties, ready for actual
Lebesgue cube integration. -/
 theorem patternPenalty_eq_products (n p : Finset κ) (s : ι → κ → ℝ) (Ω : ι → ℝ)
    (e : ι → Bool) :
    patternPenalty n p s Ω e =
      (∏ j ∈ n, ∏ i, Real.exp (-Ω i * |s i j - if e i then 1 else 0|)) *
      (∏ j ∈ p, ∏ i, Real.exp (-Ω i * |s i j - if e i then 0 else 1|)) := by
  have hm (i : ι) : mismatch n p (s i) (e i) =
      (∑ j ∈ n, |s i j - if e i then 1 else 0|) +
      ∑ j ∈ p, |s i j - if e i then 0 else 1| := by
    cases e i <;> simp [mismatch]
  unfold patternPenalty
  simp_rw [hm, ← Real.exp_sum, ← Real.exp_add]
  congr 1
  simp_rw [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp_rw [neg_mul, Finset.sum_neg_distrib]
  rw [← neg_add]
  congr 1
  congr 1 <;> exact Finset.sum_comm

end RoughRegime.LatticePriors
