module

public import RoughRegime.CompactProjectionComponents
public import RoughRegime.CompactRealConstants
public import RoughRegime.DesignComplexBounds
public import RoughRegime.BasePolynomial


@[expose] public section
/-! The true packed population domain is bounded jointly with compact density
endpoints. The original interval of each population remains in all kernels. -/
noncomputable section
open scoped Matrix.Norms.L2Operator BigOperators
open Matrix MvPolynomial Set
namespace RoughRegime.Model
open RoughRegime.ProjectionIncrementComplex RoughRegime.ProjectionIncrementPolynomial
open RoughRegime.ProjectionPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.ComplexDerivativeBridge RoughRegime.KernelExpressions
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def jointDesignMomentSet (n : ℕ) (G : Set (ℝ×ℝ)) (H : ℝ) :
    Set ((ℝ×ℝ)×(Fin (designMomentDimension n)→ℝ)) :=
  {s | s.1∈G ∧ s.2∈designMomentSet n s.1.1 s.1.2 (H*s.1.2)}

lemma jointDesignMomentSet_bounded (n : ℕ) (G : Set (ℝ×ℝ)) (hG : IsCompact G)
    (hGood : G⊆densityIntervalDomain) (H : ℝ) (hH : 0≤H) :
    Bornology.IsBounded (jointDesignMomentSet n G H) := by
  obtain ⟨lo,hi,hlo,hhi,hbounds⟩ := compact_density_endpoint_bounds G hG hGood
  apply (hG.isBounded.prod (designMomentSet_bounded n 0 hi (H*hi) le_rfl hhi.le)).subset
  intro s hs
  refine ⟨hs.1, ?_⟩
  refine ⟨?_, hs.2.2.1.trans ?_, hs.2.2.2.trans ?_⟩
  · intro t ht
    have hh := hs.2.1 ht
    exact ⟨(hGood hs.1).1.le.trans hh.1, hh.2.trans (hbounds _ hs.1).2⟩
  · exact mul_le_mul_of_nonneg_left (hbounds _ hs.1).2 hH
  · exact mul_le_mul_of_nonneg_left (hbounds _ hs.1).2 hH

theorem compact_design_increment_components (n a b : ℕ)
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆densityIntervalDomain)
    (H : ℝ) (hH : 0≤H)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ*La=1) (hLb : Lbᵀ*Lb=1) :
    ∃ ε B : ℝ, 0<ε ∧ ε≤1 ∧ 0≤B ∧
      ∀ (I : ℝ×ℝ) (hI : I∈G) (t : Fin (designMomentDimension n)→ℂ),
        (∃ x∈designMomentSet n I.1 I.2 (H*I.2),
          ‖t-realParametersCLM (designMomentDimension n) x‖<ε) →
        (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
          (designGramPolynomial n) La (designFirstPolynomial n) i))‖≤B) ∧
        (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
          (designGramPolynomial n) Lb (designSecondPolynomial n) i))‖≤B) ∧
        (∀ m i j, ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix I.1 I.2
          (designGramPolynomial n) (twoGramPolynomials (designGramPolynomial n) La Lb) m i j))‖≤B) ∧
        (∀ m, ‖MvPolynomial.eval t (complexify (incrementPolynomial I.1 I.2
          (designGramPolynomial n) La Lb (designFirstPolynomial n) (designSecondPolynomial n) m))‖≤
            (n:ℝ)^2*B^3) := by
  obtain ⟨ε,B,hε,hε1,hB,hb⟩ := compact_uniform_incrementPolynomial_components G hG hGood
    (jointDesignMomentSet n G H) (jointDesignMomentSet_bounded n G hG hGood H hH)
    (fun s hs => hs.1) (designGramPolynomial n)
    (fun s _ => designMatrix_isHermitian s.2) (fun s hs => hs.2.1)
    La Lb hLa hLb (designFirstPolynomial n) (designSecondPolynomial n)
  refine ⟨ε,B,hε,hε1,hB,?_⟩
  intro I hI t ht
  obtain ⟨x,hx,hnear⟩ := ht
  exact hb I t ⟨x,⟨hI,hx⟩,hnear⟩

theorem compact_uniform_packedInverse_components (n : ℕ)
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆densityIntervalDomain)
    (H : ℝ) (hH : 0≤H) :
    ∃ ε B : ℝ, 0<ε ∧ ε≤1 ∧ 0≤B ∧
      ∀ (I : ℝ×ℝ) (hI : I∈G) (t : Fin (designMomentDimension n)→ℂ),
        (∃ x∈designMomentSet n I.1 I.2 (H*I.2),
          ‖t-realParametersCLM (designMomentDimension n) x‖<ε) →
        (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
          (designGramPolynomial n) (emptyParentMatrix n) (designFirstPolynomial n) i))‖≤B) ∧
        (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
          (designGramPolynomial n) (emptyParentMatrix n) (designSecondPolynomial n) i))‖≤B) ∧
        (∀ m i j, ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix I.1 I.2
          (designGramPolynomial n) (twoGramPolynomials (designGramPolynomial n)
            (emptyParentMatrix n) (emptyParentMatrix n)) m i j))‖≤B) ∧
        (∀ m, ‖MvPolynomial.eval t (complexify (packedInversePolynomial n I.1 I.2 m))‖≤
            (n:ℝ)^2*B^3) :=
  compact_design_increment_components n 0 0 G hG hGood H hH (emptyParentMatrix n)
    (emptyParentMatrix n) (emptyParentMatrix_orthonormal n) (emptyParentMatrix_orthonormal n)

 theorem compact_uniform_localIncrement_components (A : Parameters) (hαβ : A.α ≤ A.β)
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆densityIntervalDomain) :
    ∃ ε B : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧
      ∀ (I : ℝ×ℝ) (hI : I∈G) (t : Fin (localMomentDimension A) → ℂ),
        (∃ x ∈ designMomentSet (localChildDimension A) I.1 I.2 (A.H * I.2),
          ‖t - realParametersCLM (localMomentDimension A) x‖ < ε) →
        ∀ r : Fin A.d,
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial (localChildDimension A)) (localAlphaMatrix A hαβ r)
            (designFirstPolynomial (localChildDimension A)) i))‖ ≤ B) ∧
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial (localChildDimension A)) (localBetaMatrix A r)
            (designSecondPolynomial (localChildDimension A)) i))‖ ≤ B) ∧
          (∀ m i j, ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix I.1 I.2
            (designGramPolynomial (localChildDimension A))
            (twoGramPolynomials (designGramPolynomial (localChildDimension A))
              (localAlphaMatrix A hαβ r) (localBetaMatrix A r)) m i j))‖ ≤ B) ∧
          (∀ m, ‖MvPolynomial.eval t (complexify (localIncrementPolynomial (densityParameters A I (hGood hI)) hαβ r m))‖ ≤
            (localChildDimension A : ℝ) ^ 2 * B ^ 3) := by
  classical
  have perAxis (r : Fin A.d) := compact_design_increment_components
    (localChildDimension A) (localAlphaDimension A) (localBetaDimension A)
    G hG hGood A.H A.hH.le (localAlphaMatrix A hαβ r) (localBetaMatrix A r)
    (referenceParentMatrix_orthonormal _ _ _ r) (referenceParentMatrix_orthonormal _ _ _ r)
  have aux (s : Finset (Fin A.d)) : ∃ ε B : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧
      ∀ (I : ℝ×ℝ) (hI : I∈G) (t : Fin (localMomentDimension A) → ℂ),
        (∃ x ∈ designMomentSet (localChildDimension A) I.1 I.2 (A.H * I.2), ‖t - realParametersCLM (localMomentDimension A) x‖ < ε) →
        ∀ r ∈ s,
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial (localChildDimension A)) (localAlphaMatrix A hαβ r)
            (designFirstPolynomial (localChildDimension A)) i))‖ ≤ B) ∧
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial (localChildDimension A)) (localBetaMatrix A r)
            (designSecondPolynomial (localChildDimension A)) i))‖ ≤ B) ∧
          (∀ m i j, ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix I.1 I.2
            (designGramPolynomial (localChildDimension A))
            (twoGramPolynomials (designGramPolynomial (localChildDimension A))
              (localAlphaMatrix A hαβ r) (localBetaMatrix A r)) m i j))‖ ≤ B) ∧
          (∀ m, ‖MvPolynomial.eval t (complexify (localIncrementPolynomial (densityParameters A I (hGood hI)) hαβ r m))‖ ≤
            (localChildDimension A : ℝ) ^ 2 * B ^ 3) := by
    induction s using Finset.induction with
    | empty => exact ⟨1, 0, by norm_num, le_rfl, le_rfl, by simp⟩
    | @insert r s hr ih =>
      obtain ⟨εs, Bs, hεs, hεs1, hBs, hs⟩ := ih
      obtain ⟨εr, Br, hεr, hεr1, hBr, hb⟩ := perAxis r
      refine ⟨min εs εr, max Bs Br, lt_min hεs hεr,
        (min_le_left _ _).trans hεs1, hBs.trans (le_max_left _ _), ?_⟩
      intro I hI t ht q hq
      obtain ⟨x, hx, hnear⟩ := ht
      rcases Finset.mem_insert.mp hq with rfl | hq
      · obtain ⟨ha, hb', hS, hP⟩ := hb I hI t ⟨x, hx, hnear.trans_le (min_le_right _ _)⟩
        refine ⟨fun i => (ha i).trans (le_max_right _ _),
          fun i => (hb' i).trans (le_max_right _ _),
          fun m i j => (hS m i j).trans (le_max_right _ _), ?_⟩
        intro m
        apply (hP m).trans
        gcongr
        exact le_max_right Bs Br
      · obtain ⟨ha, hb', hS, hP⟩ := hs I hI t ⟨x, hx, hnear.trans_le (min_le_left _ _)⟩ q hq
        refine ⟨fun i => (ha i).trans (le_max_left _ _),
          fun i => (hb' i).trans (le_max_left _ _),
          fun m i j => (hS m i j).trans (le_max_left _ _), ?_⟩
        intro m
        apply (hP m).trans
        gcongr
        exact le_max_left Bs Br
  obtain ⟨ε, B, hε, hε1, hB, hb⟩ := aux Finset.univ
  exact ⟨ε, B, hε, hε1, hB, fun I hI t ht r => hb I hI t ht r (Finset.mem_univ r)⟩


end RoughRegime.Model
