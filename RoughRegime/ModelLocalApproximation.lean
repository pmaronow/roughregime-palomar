module

public import RoughRegime.DesignComplexBounds
public import RoughRegime.DesignWeightedMoments


@[expose] public section
/-! The literal source local polynomial approximation for every genuine model,
with class constants chosen before all response spaces, laws, levels and cells. -/
noncomputable section
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix MeasureTheory MvPolynomial
namespace RoughRegime.Model
universe u
open RoughRegime.HilbertGram RoughRegime.ProjectionGram
open RoughRegime.ProjectionIncrementComplex RoughRegime.ProjectionIncrementPolynomial
open RoughRegime.ComplexDerivativeBridge RoughRegime.KernelExpressions RoughRegime.ProjectionFrame
open RoughRegime.Upper

 def ModelWitness.cellResponseA {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) : Lp ℝ 2 (W.cellDesignMeasure c) :=
  (W.holder_memLp_cell c W.a W.measurableA A.α W.smoothA).toLp W.a
 def ModelWitness.cellResponseB {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) : Lp ℝ 2 (W.cellDesignMeasure c) :=
  (W.holder_memLp_cell c W.b W.measurableB A.β W.smoothB).toLp W.b

 def ModelWitness.localProjectionIncrement {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) : ℝ :=
  ⟪(basisSpan (W.weightedChildBasis (holderOrder A.β) c)).starProjection (W.cellResponseA c),
    (basisSpan (W.weightedChildBasis (holderOrder A.β) c)).starProjection (W.cellResponseB c)⟫ -
  ⟪(basisSpan (W.weightedParentBasis (holderOrder A.β) c)).starProjection (W.cellResponseA c),
    (basisSpan (W.weightedParentBasis (holderOrder A.β) c)).starProjection (W.cellResponseB c)⟫

 def localIncrementFunction (A : Parameters) (r : Fin A.d) (x : Fin (localMomentDimension A) → ℝ) : ℝ :=
  designFirst x ⬝ᵥ (residualOperator (designMatrix x) (localBetaMatrix A r)).mulVec (designSecond x)

 theorem ModelWitness.localProjectionIncrement_eq {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) :
    W.localProjectionIncrement c = localIncrementFunction A
      (dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd))
      (dyadicDesignMean A F P (holderOrder A.β) c) := by
  unfold localIncrementFunction
  rw [W.dyadicDesignMean_gram, W.dyadicDesignMean_first, W.dyadicDesignMean_second]
  have he := projection_increment_identity (W.weightedChildBasis (holderOrder A.β) c)
    (W.weightedChildBasis_linearIndependent _ c)
    (localBetaMatrix A (dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd)))
    (referenceParentMatrix_orthonormal (holderOrder A.β) (holderOrder A.β) le_rfl _)
    (W.cellResponseA c) (W.cellResponseB c)
  rw [show parentBasis (W.weightedChildBasis (holderOrder A.β) c)
    (localBetaMatrix A (dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd))) =
      W.weightedParentBasis (holderOrder A.β) c from W.referenceParentMatrix_expansion c _ _ le_rfl] at he
  exact he

lemma localChildDimension_pos (A : Parameters) : 0 < localChildDimension A := by
  rw [localChildDimension, dyadicChildDimension_eq]
  exact Nat.mul_pos (by decide) (Nat.choose_pos (Nat.le_add_right _ _))

lemma local_parent_dimension_sum (A : Parameters) : localAlphaDimension A + localBetaDimension A = A.nu := by
  simp only [localAlphaDimension, localBetaDimension, polynomialLpSpace_finrank, Parameters.nu]

lemma dyadicScale_pos (A : Parameters) (j : ℕ) : 0 < (2 : ℝ) ^ (-(j : ℝ) / A.d) := by positivity
lemma dyadicScale_le_one (A : Parameters) (j : ℕ) : (2 : ℝ) ^ (-(j : ℝ) / A.d) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg j)) (Nat.cast_nonneg A.d))

/-- All four polynomial conclusions of source Lemma 6 for the actual observable
mean and the actual weighted dyadic projection increment. The polynomial itself
is fixed independently of the model and has exactly the claimed degree. -/
theorem uniform_model_local_polynomials (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j : ℕ) (c : DyadicCell A.d j) (m : ℕ),
      let x := dyadicDesignMean A F P (holderOrder A.β) c
      let r := dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd)
      let q := localIncrementPolynomial A hαβ r m
      let h := (2 : ℝ) ^ (-(j : ℝ) / A.d)
      q.totalDegree ≤ m + A.nu + 2 ∧
      ‖W.localProjectionIncrement c - MvPolynomial.eval x q‖ ≤
        C * h ^ (A.α + A.β) * ((m + 1 : ℕ) : ℝ) ^ A.nu * intervalRho A.gminus A.gplus ^ m ∧
      (∀ t : Fin (localMomentDimension A) → ℂ,
        ‖t - realParametersCLM (localMomentDimension A) x‖ < 1 / C →
        ‖MvPolynomial.eval t (complexify q)‖ ≤ C) ∧
      ‖polynomialGradient q x‖ ≤ C * h ^ min (min A.α A.β) 1 := by
  obtain ⟨Ha, hHa, hfaAll⟩ := uniform_model_cell_approximation.{u} A A.α
  obtain ⟨Hb, hHb, hgbAll⟩ := uniform_model_cell_approximation.{u} A A.β
  obtain ⟨ε, B, hε, hε1, hB, hcomponents⟩ := uniform_localIncrement_components A hαβ
  let K := incrementErrorConstant A.gminus A.gplus (localAlphaDimension A) (localBetaDimension A) Ha Hb
  let D := incrementGradientConstant A.gplus (localMomentDimension A) (localChildDimension A)
    (localAlphaDimension A) (localBetaDimension A) Ha Hb ε B
  let T := (localChildDimension A : ℝ) ^ 2 * B ^ 3
  let C := max 1 (max ε⁻¹ (max T (max K D)))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hεC : ε⁻¹ ≤ C := (le_max_left ε⁻¹ _).trans (le_max_right _ _)
  have hTC : T ≤ C := (le_max_left T _).trans ((le_max_right ε⁻¹ _).trans (le_max_right _ _))
  have hKC : K ≤ C := (le_max_left K D).trans ((le_max_right T _).trans
    ((le_max_right ε⁻¹ _).trans (le_max_right _ _)))
  have hDC : D ≤ C := (le_max_right K D).trans ((le_max_right T _).trans
    ((le_max_right ε⁻¹ _).trans (le_max_right _ _)))
  have hrad : 1 / C ≤ ε := by
    apply (div_le_iff₀ hC).mpr
    calc
      1 = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
      _ ≤ ε * C := mul_le_mul_of_nonneg_left hεC hε.le
  refine ⟨C, hC1, ?_⟩
  intro Z _ F P W j c m
  dsimp only
  let x := dyadicDesignMean A F P (holderOrder A.β) c
  let r := dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd)
  let z := W.weightedChildBasis (holderOrder A.β) c
  let La := localAlphaMatrix A hαβ r
  let Lb := localBetaMatrix A r
  let Ω := designGramPolynomial (localChildDimension A)
  let u := designFirstPolynomial (localChildDimension A)
  let v := designSecondPolynomial (localChildDimension A)
  have hLa : Laᵀ * La = 1 := referenceParentMatrix_orthonormal _ _ _ r
  have hLb : Lbᵀ * Lb = 1 := referenceParentMatrix_orthonormal _ _ _ r
  have heA : parentBasis z La = W.weightedParentBasis (holderOrder A.α) c :=
    W.referenceParentMatrix_expansion c _ _ (holderOrder_monotone hαβ)
  have heB : parentBasis z Lb = W.weightedParentBasis (holderOrder A.β) c :=
    W.referenceParentMatrix_expansion c _ _ le_rfl
  have hsub : basisSpan (parentBasis z La) ≤ basisSpan (parentBasis z Lb) := by
    rw [heA, heB]
    exact W.weighted_parent_span_mono c (holderOrder_monotone hαβ)
  have hGram : Ω.map (MvPolynomial.eval x) = Matrix.gram ℝ z := W.dyadicDesignMean_gram c _
  have hu : (fun i => MvPolynomial.eval x (u i)) = moments z (W.cellResponseA c) :=
    W.dyadicDesignMean_first c _
  have hv : (fun i => MvPolynomial.eval x (v i)) = moments z (W.cellResponseB c) :=
    W.dyadicDesignMean_second c _
  obtain ⟨hqa, hqaDeg, hfa⟩ := hfaAll Z F P W j c W.a W.measurableA W.smoothA
  obtain ⟨hqb, hqbDeg, hgb⟩ := hgbAll Z F P W j c W.b W.measurableB W.smoothB
  let ta := hqa.toLp _
  let tb := hqb.toLp _
  have hta : ta ∈ basisSpan (parentBasis z La) := by
    rw [heA]
    exact W.weighted_polynomial_parent_member c _ hqaDeg hqa
  have htb : tb ∈ basisSpan (parentBasis z Lb) := by
    rw [heB]
    exact W.weighted_polynomial_parent_member c _ hqbDeg hqb
  have hx := dyadicDesignMean_mem A F P W (holderOrder A.β) c
  have hh := dyadicScale_pos A j
  have hh1 := dyadicScale_le_one A j
  have hcomp (t : Fin (localMomentDimension A) → ℂ)
      (ht : ‖t - realParametersCLM (localMomentDimension A) x‖ < ε) :=
    hcomponents t ⟨x, hx, ht⟩ r
  haveI : Nonempty (Fin (localChildDimension A)) := Fin.pos_iff_nonempty.mp (localChildDimension_pos A)
  refine ⟨localIncrementPolynomial_degree A hαβ r m, ?_, ?_, ?_⟩
  · have he := incrementPolynomial_holder_error A.gminus A.gplus A.hgminus A.hgplus x
      Ω La Lb hLa hLb u v z (W.weightedChildBasis_linearIndependent _ c) hGram
      (W.weightedChildBasis_spectrum _ c) hsub (W.cellResponseA c) (W.cellResponseB c)
      ta tb hta htb hu hv _ A.α A.β Ha Hb hh hHa.le hHb.le hfa hgb m
    rw [heB] at he
    change ‖W.localProjectionIncrement c - MvPolynomial.eval x
      (localIncrementPolynomial A hαβ r m)‖ ≤ _ at he
    apply he.trans
    rw [local_parent_dimension_sum]
    have hρ := (intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus).le
    gcongr
  · intro t ht
    exact ((hcomp t (ht.trans_le hrad)).2.2.2 m).trans hTC
  · have hg := incrementPolynomial_gradient_holder_bound A.gminus A.gplus A.hgminus A.hgplus x
      Ω La Lb hLa hLb u v m ε B hε hB
      (fun t ht => ⟨(hcomp t ht).1, (hcomp t ht).2.1, fun i j => (hcomp t ht).2.2.1 m i j⟩)
      z (W.weightedChildBasis_linearIndependent _ c) hGram (W.weightedChildBasis_spectrum _ c)
      (W.cellResponseA c) (W.cellResponseB c) ta tb hta htb hu hv
      _ A.α A.β Ha Hb hh hh1 A.hα A.hβ hHa.le hHb.le hfa hgb
    exact hg.trans (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg hh.le _))

end RoughRegime.Model
