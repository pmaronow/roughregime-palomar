module

public import RoughRegime.CompactDesignComponents
public import RoughRegime.CompactGradientConstants
public import RoughRegime.CompactBaseApproximation
public import RoughRegime.ModelEstimatorControls


@[expose] public section
/-! Genuine compact-endpoint polynomial controls, quantified before every
response space, observable, model, level and truncation order. -/
noncomputable section
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix MeasureTheory MvPolynomial
namespace RoughRegime.Model
universe u
open RoughRegime.HilbertGram RoughRegime.ProjectionGram
open RoughRegime.ProjectionIncrementComplex RoughRegime.ProjectionIncrementPolynomial
open RoughRegime.ComplexDerivativeBridge RoughRegime.KernelExpressions RoughRegime.ProjectionFrame
open RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem compact_uniform_localPolynomialControl (A : Parameters) (hαβ : A.α≤A.β)
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆densityIntervalDomain) :
    ∃ C : ℝ, 1≤C ∧ ∀ (I : ℝ×ℝ) (hI : I∈G),
      LocalPolynomialControl.{u} (densityParameters A I (hGood hI)) hαβ C := by
  obtain ⟨Ha,hHa,hfaAll⟩ := compact_uniform_model_cell_approximation.{u} A G hG hGood A.α
  obtain ⟨Hb,hHb,hgbAll⟩ := compact_uniform_model_cell_approximation.{u} A G hG hGood A.β
  obtain ⟨ε,B,hε,hε1,hB,hcomponents⟩ := compact_uniform_localIncrement_components A hαβ G hG hGood
  obtain ⟨lo,hi,hlo,hhi,hbounds⟩ := compact_density_endpoint_bounds G hG hGood
  obtain ⟨K,hK,hKall⟩ := compact_incrementErrorConstant_bound G hG hGood
    (localAlphaDimension A) (localBetaDimension A) Ha Hb hHa.le hHb.le
  let D := incrementGradientConstant hi (localMomentDimension A) (localChildDimension A)
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
  intro I hI
  let AI := densityParameters A I (hGood hI)
  change LocalPolynomialControl.{u} AI hαβ C
  intro Z _ F P W j c m
  dsimp only
  let x := dyadicDesignMean AI F P (holderOrder AI.β) c
  let r := dyadicSplitAxis AI.d j (lt_of_lt_of_le Nat.zero_lt_one AI.hd)
  let z := W.weightedChildBasis (holderOrder AI.β) c
  let La := localAlphaMatrix AI hαβ r
  let Lb := localBetaMatrix AI r
  let Ω := designGramPolynomial (localChildDimension AI)
  let u := designFirstPolynomial (localChildDimension AI)
  let v := designSecondPolynomial (localChildDimension AI)
  have hLa : Laᵀ * La = 1 := referenceParentMatrix_orthonormal _ _ _ r
  have hLb : Lbᵀ * Lb = 1 := referenceParentMatrix_orthonormal _ _ _ r
  have heA : parentBasis z La = W.weightedParentBasis (holderOrder AI.α) c :=
    W.referenceParentMatrix_expansion c _ _ (holderOrder_monotone hαβ)
  have heB : parentBasis z Lb = W.weightedParentBasis (holderOrder AI.β) c :=
    W.referenceParentMatrix_expansion c _ _ le_rfl
  have hsub : basisSpan (parentBasis z La) ≤ basisSpan (parentBasis z Lb) := by
    rw [heA, heB]
    exact W.weighted_parent_span_mono c (holderOrder_monotone hαβ)
  have hGram : Ω.map (MvPolynomial.eval x) = Matrix.gram ℝ z := W.dyadicDesignMean_gram c _
  have hu : (fun i => MvPolynomial.eval x (u i)) = moments z (W.cellResponseA c) :=
    W.dyadicDesignMean_first c _
  have hv : (fun i => MvPolynomial.eval x (v i)) = moments z (W.cellResponseB c) :=
    W.dyadicDesignMean_second c _
  obtain ⟨hqa, hqaDeg, hfa⟩ := hfaAll I hI Z F P W j c W.a W.measurableA W.smoothA
  obtain ⟨hqb, hqbDeg, hgb⟩ := hgbAll I hI Z F P W j c W.b W.measurableB W.smoothB
  let ta := hqa.toLp _
  let tb := hqb.toLp _
  have hta : ta ∈ basisSpan (parentBasis z La) := by
    rw [heA]
    exact W.weighted_polynomial_parent_member c _ hqaDeg hqa
  have htb : tb ∈ basisSpan (parentBasis z Lb) := by
    rw [heB]
    exact W.weighted_polynomial_parent_member c _ hqbDeg hqb
  have hx := dyadicDesignMean_mem AI F P W (holderOrder AI.β) c
  have hh := dyadicScale_pos AI j
  have hh1 := dyadicScale_le_one AI j
  have hcomp (t : Fin (localMomentDimension AI) → ℂ)
      (ht : ‖t - realParametersCLM (localMomentDimension AI) x‖ < ε) :=
    hcomponents I hI t ⟨x, hx, ht⟩ r
  have : Nonempty (Fin (localChildDimension AI)) := Fin.pos_iff_nonempty.mp (localChildDimension_pos AI)
  have hKI : incrementErrorConstant AI.gminus AI.gplus (localAlphaDimension AI)
      (localBetaDimension AI) Ha Hb ≤ C := (hKall I hI).trans hKC
  have hDI : incrementGradientConstant AI.gplus (localMomentDimension AI) (localChildDimension AI)
      (localAlphaDimension AI) (localBetaDimension AI) Ha Hb ε B ≤ C :=
    (incrementGradientConstant_mono_hi I.2 hi ((hGood hI).1.trans (hGood hI).2).le
      (hbounds I hI).2 _ _ _ _ Ha Hb ε B hHa.le hHb.le hε hB).trans hDC
  refine ⟨?_, ?_, ?_⟩
  · have he := incrementPolynomial_holder_error AI.gminus AI.gplus AI.hgminus AI.hgplus x
      Ω La Lb hLa hLb u v z (W.weightedChildBasis_linearIndependent _ c) hGram
      (W.weightedChildBasis_spectrum _ c) hsub (W.cellResponseA c) (W.cellResponseB c)
      ta tb hta htb hu hv _ AI.α AI.β Ha Hb hh hHa.le hHb.le hfa hgb m
    rw [heB] at he
    change ‖W.localProjectionIncrement c - MvPolynomial.eval x
      (localIncrementPolynomial AI hαβ r m)‖ ≤ _ at he
    apply he.trans
    rw [local_parent_dimension_sum]
    have hρ := (intervalRho_pos AI.gminus AI.gplus AI.hgminus AI.hgplus).le
    gcongr
  · intro t ht
    exact ((hcomp t (ht.trans_le hrad)).2.2.2 m).trans hTC
  · have hg := incrementPolynomial_gradient_holder_bound AI.gminus AI.gplus AI.hgminus AI.hgplus x
      Ω La Lb hLa hLb u v m ε B hε hB
      (fun t ht => ⟨(hcomp t ht).1, (hcomp t ht).2.1, fun i j => (hcomp t ht).2.2.1 m i j⟩)
      z (W.weightedChildBasis_linearIndependent _ c) hGram (W.weightedChildBasis_spectrum _ c)
      (W.cellResponseA c) (W.cellResponseB c) ta tb hta htb hu hv
      _ AI.α AI.β Ha Hb hh hh1 AI.hα AI.hβ hHa.le hHb.le hfa hgb
    exact hg.trans (mul_le_mul_of_nonneg_right hDI (Real.rpow_nonneg hh.le _))

theorem compact_uniform_basePolynomialControl (A : Parameters)
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆densityIntervalDomain) :
    ∃ C : ℝ, 1≤C ∧ ∀ (I : ℝ×ℝ) (hI : I∈G),
      BasePolynomialControl.{u} (densityParameters A I (hGood hI)) C := by
  let n := baseDimension A.d (holderOrder A.β)
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (baseDimension_pos A.d (holderOrder A.β))
  obtain ⟨lo,hi,hlo,hhi,hbounds⟩ := compact_density_endpoint_bounds G hG hGood
  let H := Real.sqrt hi*A.H
  have hH : 0≤H := mul_nonneg (Real.sqrt_nonneg _) A.hH.le
  obtain ⟨C,hC,hall⟩ := compact_uniform_packed_base_approximation.{0} n G hG hGood A.H H A.hH.le hH
  refine ⟨C,hC,?_⟩
  intro I hI
  let AI := densityParameters A I (hGood hI)
  change BasePolynomialControl.{u} AI C
  intro Z _ F P W m
  dsimp only
  have hx := baseDesignMean_mem AI F P W (holderOrder AI.β)
  have hresp : Real.sqrt AI.gplus*AI.H≤H :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hbounds I hI).2) A.hH.le
  obtain ⟨herr,hgrad⟩ := (hall I hI).2.2 (Lp ℝ 2 (W.cellDesignMeasure (dyadicBaseCell AI.d)))
    _ hx (W.weightedParentBasis (holderOrder AI.β) (dyadicBaseCell AI.d))
    (W.weightedParentBasis_linearIndependent _ _) (baseDesignMean_gram AI F P W _)
    (W.cellALp (dyadicBaseCell AI.d)) (W.cellBLp (dyadicBaseCell AI.d))
    (baseDesignMean_first AI F P W _) (baseDesignMean_second AI F P W _)
    (W.base_response_norms.1.trans hresp) (W.base_response_norms.2.trans hresp) m
  change ‖W.cellProjectionTarget (holderOrder AI.β) (dyadicBaseCell AI.d)-
    MvPolynomial.eval _ (baseIncrementPolynomial AI m)‖≤_ at herr
  rw [←W.base_level_projection] at herr
  exact ⟨herr,fun t ht=>(hall I hI).2.1 t ⟨_,hx,ht⟩ m,hgrad⟩

lemma LocalPolynomialControl.mono (A : Parameters) (hαβ : A.α≤A.β) (C D : ℝ)
    (hC : 0<C) (hCD : C≤D) (hcontrol : LocalPolynomialControl.{u} A hαβ C) :
    LocalPolynomialControl.{u} A hαβ D := by
  intro Z _ F P W j c m
  obtain ⟨he,hb,hg⟩ := hcontrol Z F P W j c m
  have hrad := one_div_le_one_div_of_le hC hCD
  have hρ := (intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus).le
  refine ⟨?_,?_,?_⟩
  · exact he.trans (by gcongr)
  · intro t ht
    exact (hb t (ht.trans_le hrad)).trans hCD
  · exact hg.trans (by gcongr)

lemma BasePolynomialControl.mono (A : Parameters) (C D : ℝ)
    (hC : 0<C) (hCD : C≤D) (hcontrol : BasePolynomialControl.{u} A C) :
    BasePolynomialControl.{u} A D := by
  intro Z _ F P W m
  obtain ⟨he,hb,hg⟩ := hcontrol Z F P W m
  have hrad := one_div_le_one_div_of_le hC hCD
  refine ⟨?_,?_,hg.trans hCD⟩
  · exact he.trans (mul_le_mul_of_nonneg_right hCD (pow_nonneg
      (intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus).le m))
  · intro t ht
    exact (hb t (ht.trans_le hrad)).trans hCD

/-- A single source Lemma 6 polynomial constant before all compact endpoints,
all response spaces and observables, all genuine model laws, levels and orders. -/
theorem compact_uniform_polynomial_controls (A : Parameters) (hαβ : A.α≤A.β)
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆densityIntervalDomain) :
    ∃ C : ℝ, 1≤C ∧ ∀ (I : ℝ×ℝ) (hI : I∈G),
      LocalPolynomialControl.{u} (densityParameters A I (hGood hI)) hαβ C ∧
      BasePolynomialControl.{u} (densityParameters A I (hGood hI)) C := by
  obtain ⟨Cl,hCl,hl⟩ := compact_uniform_localPolynomialControl.{u} A hαβ G hG hGood
  obtain ⟨Cb,hCb,hb⟩ := compact_uniform_basePolynomialControl.{u} A G hG hGood
  refine ⟨max Cl Cb,hCl.trans (le_max_left _ _),?_⟩
  intro I hI
  exact ⟨LocalPolynomialControl.mono _ _ _ _ (zero_lt_one.trans_le hCl) (le_max_left _ _) (hl I hI),
    BasePolynomialControl.mono _ _ _ (zero_lt_one.trans_le hCb) (le_max_right _ _) (hb I hI)⟩

end RoughRegime.Model
