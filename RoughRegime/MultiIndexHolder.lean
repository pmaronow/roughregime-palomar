module

public import RoughRegime.DerivativeSymmetry
public import RoughRegime.HolderGeometry


@[expose] public section
open Set
open scoped BigOperators ContDiff ENNReal
noncomputable section
namespace RoughRegime.Model
open RoughRegime.Calculus

/-- A classical coordinate multi-index of total order q. -/
def MultiIndex (d q : ℕ) := {ν : Fin d → ℕ // ∑ j, ν j = q}

/-- Multiplicity of a coordinate among an ordered derivative's directions. -/
def wordMultiplicity {d q : ℕ} (σ : Fin q → Fin d) (j : Fin d) : ℕ :=
  Fintype.card {i : Fin q // σ i = j}

lemma wordMultiplicity_sum {d q : ℕ} (σ : Fin q → Fin d) :
    ∑ j, wordMultiplicity σ j = q := by
  simpa only [Fintype.card_sigma,Fintype.card_fin,wordMultiplicity] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv σ)

/-- The usual coordinate-order representative: repeat each coordinate as
many times as the multi-index specifies, in increasing coordinate order. -/
def multiIndexWord {d q : ℕ} (ν : MultiIndex d q) : Fin q → Fin d :=
  fun i => (finSigmaFinEquiv.symm ((finCongr ν.2).symm i)).1

private def sigmaCoordinateFiberEquiv {d : ℕ} (ν : Fin d → ℕ) (j : Fin d) :
    {a : (i : Fin d) × Fin (ν i) // a.1 = j} ≃ Fin (ν j) where
  toFun a := a.2 ▸ a.1.2
  invFun k := ⟨⟨j,k⟩,rfl⟩
  left_inv := by rintro ⟨⟨i,k⟩,h⟩; cases h; rfl
  right_inv := by intro k; rfl

lemma multiIndexWord_multiplicity {d q : ℕ} (ν : MultiIndex d q) :
    wordMultiplicity (multiIndexWord ν) = ν.1 := by
  funext j
  let e : Fin q ≃ (i : Fin d) × Fin (ν.1 i) := (finCongr ν.2).symm.trans finSigmaFinEquiv.symm
  change Fintype.card {i : Fin q // (e i).1 = j} = ν.1 j
  have he := (e.subtypeEquivOfSubtype (p := fun a => a.1 = j)).trans
    (sigmaCoordinateFiberEquiv ν.1 j)
  simpa only [Fintype.card_fin] using Fintype.card_congr he

lemma exists_perm_of_multiplicity_eq {d q : ℕ} (σ τ : Fin q → Fin d)
    (h : wordMultiplicity σ = wordMultiplicity τ) :
    ∃ p : Equiv.Perm (Fin q), σ ∘ p = τ := by
  let e (j : Fin d) : {i : Fin q // τ i = j} ≃ {i : Fin q // σ i = j} :=
    Fintype.equivOfCardEq (congrFun h j).symm
  refine ⟨Equiv.ofFiberEquiv e,?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map e i

/-- The genuine within-cube mixed derivative for a classical multi-index. -/
def multiIndexDerivative {d q : ℕ} (f : Covariate d → ℝ) (ν : MultiIndex d q)
    (x : Covariate d) : ℝ := coordinateDerivative f q (multiIndexWord ν) x

lemma coordinateDerivative_comp_perm {d q : ℕ} (f : Covariate d → ℝ)
    (hf : ContDiffOn ℝ q f (cube d)) (σ : Fin q → Fin d) (p : Equiv.Perm (Fin q))
    (x : Covariate d) (hx : x ∈ cube d) :
    coordinateDerivative f q (σ ∘ p) x = coordinateDerivative f q σ x := by
  have hdense : cube d ⊆ closure (interior (cube d)) := by
    rw [(convex_cube d).closure_interior_eq_closure_of_nonempty_interior (cube_nonempty_interior d)]
    exact subset_closure
  unfold coordinateDerivative
  exact iteratedFDerivWithin_comp_perm_finite hf (uniqueDiffOn_cube d) hdense
    (fun j => EuclideanSpace.single (σ j) 1) p x hx

lemma coordinateDerivative_eq_multiIndex {d q : ℕ} (f : Covariate d → ℝ)
    (hf : ContDiffOn ℝ q f (cube d)) (σ : Fin q → Fin d) (x : Covariate d) (hx : x ∈ cube d) :
    coordinateDerivative f q σ x = multiIndexDerivative f ⟨wordMultiplicity σ,wordMultiplicity_sum σ⟩ x := by
  let ν : MultiIndex d q := ⟨wordMultiplicity σ,wordMultiplicity_sum σ⟩
  obtain ⟨p,hp⟩ := exists_perm_of_multiplicity_eq σ (multiIndexWord ν)
    (multiIndexWord_multiplicity ν).symm
  unfold multiIndexDerivative
  rw [← hp]
  exact (coordinateDerivative_comp_perm f hf σ p x hx).symm



/-- The maximum of classical multi-index derivatives through order k. -/
def classicalDerivativeSup {d : ℕ} (f : Covariate d → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (q : ℕ) (_ : q ≤ k) (ν : MultiIndex d q) (x : Covariate d) (_ : x ∈ cube d),
    ENNReal.ofReal |multiIndexDerivative f ν x|

/-- The classical multi-index Hölder seminorm at the greatest derivative
order strictly below t. This includes the source's Lipschitz convention
at integer exponents. -/
def classicalHolderSeminorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (ν : MultiIndex d (holderOrder t)) (x : Covariate d) (_ : x ∈ cube d)
    (y : Covariate d) (_ : y ∈ cube d) (_ : x ≠ y),
    ENNReal.ofReal (|multiIndexDerivative f ν x-multiIndexDerivative f ν y| /
      ‖x-y‖ ^ holderExponent t)

/-- The literal multi-index max-norm convention of the paper. -/
def classicalHolderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) then
    classicalDerivativeSup f (holderOrder t)+classicalHolderSeminorm f t else ∞

theorem derivativeSup_eq_classical {d : ℕ} (f : Covariate d → ℝ) (k : ℕ)
    (hf : ContDiffOn ℝ k f (cube d)) : derivativeSup f k = classicalDerivativeSup f k := by
  apply le_antisymm
  · unfold derivativeSup
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    rw [coordinateDerivative_eq_multiIndex f (hf.of_le (by exact_mod_cast hq)) σ x hx]
    exact le_iSup_of_le q (le_iSup_of_le hq
      (le_iSup_of_le ⟨wordMultiplicity σ,wordMultiplicity_sum σ⟩
        (le_iSup_of_le x (le_iSup_of_le hx le_rfl))))
  · unfold classicalDerivativeSup
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro ν
    apply iSup_le; intro x
    apply iSup_le; intro hx
    exact le_iSup_of_le q (le_iSup_of_le hq
      (le_iSup_of_le (multiIndexWord ν) (le_iSup_of_le x (le_iSup_of_le hx le_rfl))))

theorem holderSeminorm_eq_classical {d : ℕ} (f : Covariate d → ℝ) (t : ℝ)
    (hf : ContDiffOn ℝ (holderOrder t) f (cube d)) :
    holderSeminorm f t = classicalHolderSeminorm f t := by
  apply le_antisymm
  · unfold holderSeminorm
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hxy
    rw [coordinateDerivative_eq_multiIndex f hf σ x hx,coordinateDerivative_eq_multiIndex f hf σ y hy]
    exact le_iSup_of_le ⟨wordMultiplicity σ,wordMultiplicity_sum σ⟩
      (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y
        (le_iSup_of_le hy (le_iSup_of_le hxy le_rfl)))))
  · unfold classicalHolderSeminorm
    apply iSup_le; intro ν
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hxy
    exact le_iSup_of_le (multiIndexWord ν) (le_iSup_of_le x (le_iSup_of_le hx
      (le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le hxy le_rfl)))))

/-- Exact equality with the source classical multi-index norm, including
boundary derivatives, integer exponents, and the extended-value case. -/
theorem holderNorm_eq_classicalHolderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) :
    holderNorm f t = classicalHolderNorm f t := by
  unfold holderNorm classicalHolderNorm
  split_ifs with hreg
  · rw [derivativeSup_eq_classical f (holderOrder t) hreg.2,
      holderSeminorm_eq_classical f t hreg.2]
  · rfl

end RoughRegime.Model
