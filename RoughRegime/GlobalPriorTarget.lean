module

public import RoughRegime.GlobalProduct
public import RoughRegime.LatticeScales


@[expose] public section
/-! Independent-pair prior expectations and the actual full-volume target separation. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open RoughRegime.LatticeFourier RoughRegime.DyadicDigits
open scoped BigOperators

 variable {D N : ℕ} {ι : Type*} [Fintype ι]

 def blockLabelIndex (label : Bool) : ℕ := if label then 0 else 1

 theorem sign_eq_blockLabelIndex (label : Bool) :
    RoughRegime.Lower.sign label = (-1 : ℝ) ^ blockLabelIndex label := by
  cases label <;> norm_num [RoughRegime.Lower.sign, blockLabelIndex]

 def independentPairTarget (ell : ℝ) (F : Bool → ((ι → ℤ) × (ℝ × (Bool × Bool))) → ℝ)
    (z : GridPair D N → ((ι → ℤ) × (ℝ × (Bool × Bool)))) : ℝ :=
  ell ^ (D + 1) * ∑ b : GridBlock D N, F b.2 (z b.1)

 theorem independentPairTarget_integral (ell : ℝ)
    (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ] (M : ℕ) (positive : Bool)
    (F : Bool → ((ι → ℤ) × (ℝ × (Bool × Bool))) → ℝ)
    (hF : ∀ label, Integrable (F label) (blockPrior μ M positive)) :
    (∫ z, independentPairTarget (D := D) (N := N) ell F z ∂globalBlockPrior μ M positive) =
      ell ^ (D + 1) * ∑ b : GridBlock D N, ∫ s, F b.2 s ∂blockPrior μ M positive := by
  have hi (b : GridBlock D N) : Integrable (fun z : GridPair D N → ((ι → ℤ) × (ℝ × (Bool × Bool))) =>
      F b.2 (z b.1)) (globalBlockPrior μ M positive) :=
    (measurePreserving_eval (fun _ : GridPair D N => blockPrior μ M positive) b.1).integrable_comp_of_integrable (hF b.2)
  unfold independentPairTarget
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun b _ => hi b)]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  exact integral_comp_eval (hF b.2).aestronglyMeasurable

 theorem independentPairTarget_separation (ell : ℝ) (hell : 0 ≤ ell)
    (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ] (M : ℕ)
    (F : Bool → ((ι → ℤ) × (ℝ × (Bool × Bool))) → ℝ)
    (hF : ∀ positive label, Integrable (F label) (blockPrior μ M positive)) (c : ℝ)
    (hc : ∀ label, c ≤ (∫ s, F label s ∂blockPrior μ M true) - (∫ s, F label s ∂blockPrior μ M false)) :
    (ell * (2 * N : ℕ)) ^ (D + 1) * c ≤
      (∫ z, independentPairTarget (D := D) (N := N) ell F z ∂globalBlockPrior μ M true) -
      (∫ z, independentPairTarget (D := D) (N := N) ell F z ∂globalBlockPrior μ M false) := by
  rw [independentPairTarget_integral ell μ M true F (hF true),
    independentPairTarget_integral ell μ M false F (hF false), ← mul_sub, ← Finset.sum_sub_distrib]
  have hh := Finset.sum_le_sum (fun (b : GridBlock D N) (_ : b ∈ Finset.univ) => hc b.2)
  simp only [Finset.sum_const, Finset.card_univ, gridBlock_card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hh
  have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg hell (D + 1))
  convert hm using 1 <;> simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow] <;> ring

/-- Source separation under the actual independent-pair prior, with the
original constant9*v0*I/(16*r0). -/
 theorem global_block_prior_separation (U : SmoothStep) (Q M J : ℕ)
    (a : Fin J × Fin (D + 1) → ℕ) (q : Fin J × Fin (D + 1) → Fin (D + 1))
    (η : Fin J × Fin (D + 1) → ℝ) (w : (Fin (D + 1) → ℝ) → ℝ)
    (hQ : 2 ≤ Q) (hM : 0 < M) (heven : Even M)
    (hη : ∀ i, 0 < η i) (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (γstar lamstar : ℝ) (hγ : 0 < γstar) (hγ1 : γstar ≤ 1 / 4) (hlam : 1 ≤ lamstar)
    (hlamBudget : 8 * Q * (D + 1) * sincSecondMoment Q / 3 ≤ lamstar ^ 2)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hγbudget : γstar ≤ (∫ x, w x ∂cubeUniform (D + 1)) / (16 * (D + 1)))
    (lo hi Au Av ell : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hell : 0 ≤ ell) :
    let μ := gatePrior Q M η (by omega) hM hη hband
    let F := fun label => blockSpatialTarget U Q M a q
      (fun i : Fin J × Fin (D + 1) => γstar / ((i.1 : ℝ) + 1) ^ 2) η
      (fun i : Fin J × Fin (D + 1) => lamstar * ((i.1 : ℝ) + 1)) w lo hi Au Av (blockLabelIndex label)
    (9 * (ell * (2 * N : ℕ)) ^ (D + 1) * (∫ x, w x ∂cubeUniform (D + 1)) /
      (16 * RoughRegime.Upper.intervalCenter lo hi)) * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M ≤
      (∫ z, independentPairTarget (D := D) (N := N) ell F z ∂globalBlockPrior μ M true) -
      (∫ z, independentPairTarget (D := D) (N := N) ell F z ∂globalBlockPrior μ M false) := by
  dsimp only
  let μ := gatePrior Q M η (by omega) hM hη hband
  let γ := fun i : Fin J × Fin (D + 1) => γstar / ((i.1 : ℝ) + 1) ^ 2
  let lam := fun i : Fin J × Fin (D + 1) => lamstar * ((i.1 : ℝ) + 1)
  let F := fun label => blockSpatialTarget U Q M a q γ η lam w lo hi Au Av (blockLabelIndex label)
  have hγpos (i : Fin J × Fin (D + 1)) : 0 < γ i := by dsimp [γ]; positivity
  have hγsmall (i : Fin J × Fin (D + 1)) : γ i ≤ 1 / 4 := by
    exact sourceGamma_le_quarter γstar i.1.val hγ hγ1
  have hF (positive label : Bool) : Integrable (F label) (blockPrior μ M positive) :=
    (blockTarget_integrable U Q M a q γ η lam w lo hi Au Av (blockLabelIndex label)
      hγpos hγsmall hw hlo hlt hw0 hw1 μ positive).integral_prod_left
  have hsep (label : Bool) := actual_block_prior_separation U Q M J (D + 1) a q η w hQ hM heven (by omega)
    hη hband γstar lamstar hγ hγ1 hlam (by simpa only [Nat.cast_add, Nat.cast_one] using hlamBudget) hw hw0 hw1 (by simpa only [Nat.cast_add, Nat.cast_one] using hγbudget) lo hi Au Av 1 hlo hlt hAu hAv (by norm_num) (blockLabelIndex label)
  have hc : ∀ label, (9 * (∫ x, w x ∂cubeUniform (D + 1)) /
      (16 * RoughRegime.Upper.intervalCenter lo hi)) * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M ≤
      (∫ s, F label s ∂blockPrior μ M true) - (∫ s, F label s ∂blockPrior μ M false) := by
    intro label
    simpa only [mul_one, one_mul] using hsep label
  have hh := independentPairTarget_separation (D := D) (N := N) ell hell μ M F hF _ hc
  convert hh using 1 <;> ring

end RoughRegime.LatticePriors
