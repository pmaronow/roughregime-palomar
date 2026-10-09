module

public import RoughRegime.DesignWeightedChildren
public import RoughRegime.RectangleComposition
public import RoughRegime.DyadicTree
public import RoughRegime.BlockProjectionEnergy


@[expose] public section
/-! Exact actual child-block Gram matrices and moments under the dyadic design. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

 theorem dyadicChildRectangle_subset {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) (b : Bool) :
    dyadicRectangle (dyadicChildCell hd c b) ⊆ dyadicRectangle c := by
  intro x hx
  rw [← dyadic_children_union hd c]
  cases b
  · exact Or.inl hx
  · exact Or.inr hx

 theorem dyadicCellMeasure_closedForm {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    rectangleVolume (dyadicOrigin c) (dyadicSides c) =
      ENNReal.ofReal ((2 : ℝ) ^ j) • volume.restrict (dyadicRectangle c) := by
  rw [rectangleVolume, dyadicSides_prod hd c, one_div_div, div_one]
  rw [← dyadicRectangle_eq_rectangle]

 theorem dyadicCellMeasure_restrict_child {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) (b : Bool) :
    (rectangleVolume (dyadicOrigin c) (dyadicSides c)).restrict
      (dyadicRectangle (dyadicChildCell hd c b)) =
      ENNReal.ofReal (1 / 2 : ℝ) • rectangleVolume
        (dyadicOrigin (dyadicChildCell hd c b)) (dyadicSides (dyadicChildCell hd c b)) := by
  rw [dyadicCellMeasure_closedForm hd c, dyadicCellMeasure_closedForm hd,
    Measure.restrict_smul, Measure.restrict_restrict (dyadicRectangle_measurable _),
    inter_eq_left.mpr (dyadicChildRectangle_subset hd c b), smul_smul,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hr : (2 : ℝ) ^ j = (1 / 2 : ℝ) * (2 : ℝ) ^ (j + 1) := by
    rw [pow_succ]
    ring
  rw [← hr]

 theorem dyadic_child_indicator_integral {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j)
    (b : Bool) (f : Covariate d → ℝ) :
    (∫ x, (dyadicRectangle (dyadicChildCell hd c b)).indicator f x
      ∂rectangleVolume (dyadicOrigin c) (dyadicSides c)) =
      (1 / 2 : ℝ) * ∫ x, f x ∂rectangleVolume
        (dyadicOrigin (dyadicChildCell hd c b)) (dyadicSides (dyadicChildCell hd c b)) := by
  rw [integral_indicator (dyadicRectangle_measurable _), dyadicCellMeasure_restrict_child,
    integral_smul_measure, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul]

 theorem dyadic_children_ae_not_both {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j)
    (b e : Bool) (hbe : b ≠ e) :
    ∀ᵐ x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c),
      ¬ (x ∈ dyadicRectangle (dyadicChildCell hd c b) ∧
        x ∈ dyadicRectangle (dyadicChildCell hd c e)) := by
  have h : AEDisjoint volume (dyadicRectangle (dyadicChildCell hd c b))
      (dyadicRectangle (dyadicChildCell hd c e)) := by
    cases b <;> cases e
    · exact False.elim (hbe rfl)
    · exact dyadic_children_aeDisjoint hd c
    · exact (dyadic_children_aeDisjoint hd c).symm
    · exact False.elim (hbe rfl)
  have hac : rectangleVolume (dyadicOrigin c) (dyadicSides c) ≪ volume := by
    rw [dyadicCellMeasure_closedForm hd c]
    exact Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  apply hac.ae_le
  apply ae_iff.mpr
  have he : {x | ¬¬(x ∈ dyadicRectangle (dyadicChildCell hd c b) ∧
      x ∈ dyadicRectangle (dyadicChildCell hd c e))} =
      dyadicRectangle (dyadicChildCell hd c b) ∩ dyadicRectangle (dyadicChildCell hd c e) := by
    ext x
    simp only [mem_ofPred_eq, not_not, mem_inter_iff]
  rw [he]
  exact h

 theorem lp_inner_representatives {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u v : Lp ℝ 2 μ) (f g : X → ℝ) (hu : u =ᵐ[μ] f) (hv : v =ᵐ[μ] g) :
    inner ℝ u v = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  simp [hx, hy, mul_comm]

variable {A : Parameters} {Z : Type*} [MeasurableSpace Z]
  {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}

 def ModelWitness.weightedSplitChildBasis (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) (bi : SplitIndex A.d k) : Lp ℝ 2 (W.cellDesignMeasure c) :=
  W.weightedChildBasis k c ((Fintype.equivFin (SplitIndex A.d k)) bi)

 theorem ModelWitness.weightedSplitChildBasis_ae (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) (bi : SplitIndex A.d k) :
    W.weightedSplitChildBasis k c bi =ᵐ[W.cellDesignMeasure c]
      dyadicChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c bi := by
  simpa only [weightedSplitChildBasis, dyadicFinChildBasisFunction, Equiv.symm_apply_apply]
    using W.weightedChildBasis_ae k c ((Fintype.equivFin (SplitIndex A.d k)) bi)

 theorem ModelWitness.weightedSplitChildBasis_linearIndependent (W : ModelWitness A F P)
    {j : ℕ} (k : ℕ) (c : DyadicCell A.d j) :
    LinearIndependent ℝ (W.weightedSplitChildBasis k c) :=
  (W.weightedChildBasis_linearIndependent k c).comp _ (Fintype.equivFin _).injective

 theorem ModelWitness.parentGram_integral (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) (i l : Fin (Module.finrank ℝ (polynomialLpSpace A.d k))) :
    Matrix.gram ℝ (W.weightedParentBasis k c) i l =
      ∫ x, W.designDensity x * (dyadicParentBasisFunction k c i x * dyadicParentBasisFunction k c l x)
        ∂rectangleVolume (dyadicOrigin c) (dyadicSides c) := by
  rw [Matrix.gram_apply, lp_inner_representatives _ _ _ _ _
    (W.weightedParentBasis_ae k c i) (W.weightedParentBasis_ae k c l)]
  exact weightedDesignMeasure_integral _ _ W.designDensity_measurable
    ((W.dyadic_density_bounds c).mono (fun _ hx => A.hgminus.le.trans hx.1)) _

 theorem dyadicChildBasisFunction_eq_parent {d j : ℕ} (hd : 0 < d) (k : ℕ)
    (c : DyadicCell d j) (b : Bool) (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    dyadicChildBasisFunction hd k c (b, i) =
      (dyadicRectangle (dyadicChildCell hd c b)).indicator
        (fun x => Real.sqrt 2 * dyadicParentBasisFunction k (dyadicChildCell hd c b) i x) := by
  funext x
  rw [dyadicChildBasisFunction_child]
  congr 1
  funext y
  unfold dyadicParentBasisFunction
  rw [rectanglePolynomial_eval]

 theorem ModelWitness.weightedSplitChildBasis_gram (W : ModelWitness A F P) {j : ℕ}
    (k : ℕ) (c : DyadicCell A.d j) :
    Matrix.gram ℝ (W.weightedSplitChildBasis k c) =
      RoughRegime.BlockProjectionEnergy.blockGram (fun b =>
        Matrix.gram ℝ (W.weightedParentBasis k (dyadicChildCell
          (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b))) := by
  ext ⟨b, i⟩ ⟨e, l⟩
  let hd := lt_of_lt_of_le Nat.zero_lt_one A.hd
  rw [Matrix.gram_apply, lp_inner_representatives _ _ _ _ _
    (W.weightedSplitChildBasis_ae k c (b, i)) (W.weightedSplitChildBasis_ae k c (e, l))]
  change (∫ x, dyadicChildBasisFunction hd k c (b, i) x * dyadicChildBasisFunction hd k c (e, l) x
    ∂weightedDesignMeasure (rectangleVolume (dyadicOrigin c) (dyadicSides c)) W.designDensity) = _
  rw [weightedDesignMeasure_integral _ _ W.designDensity_measurable
      ((W.dyadic_density_bounds c).mono (fun _ hx => A.hgminus.le.trans hx.1)),
    dyadicChildBasisFunction_eq_parent hd, dyadicChildBasisFunction_eq_parent hd,
    RoughRegime.BlockProjectionEnergy.blockGram_apply]
  by_cases hbe : b = e
  · subst e
    rw [ite_eq_left rfl, W.parentGram_integral]
    have he : (fun x => W.designDensity x *
        ((dyadicRectangle (dyadicChildCell hd c b)).indicator
          (fun x => Real.sqrt 2 * dyadicParentBasisFunction k (dyadicChildCell hd c b) i x) x *
        (dyadicRectangle (dyadicChildCell hd c b)).indicator
          (fun x => Real.sqrt 2 * dyadicParentBasisFunction k (dyadicChildCell hd c b) l x) x)) =
      (dyadicRectangle (dyadicChildCell hd c b)).indicator
        (fun x => 2 * (W.designDensity x * (dyadicParentBasisFunction k (dyadicChildCell hd c b) i x *
          dyadicParentBasisFunction k (dyadicChildCell hd c b) l x))) := by
      funext x
      by_cases hx : x ∈ dyadicRectangle (dyadicChildCell hd c b)
      · simp only [indicator_of_mem hx]
        calc
          _ = Real.sqrt 2 ^ 2 * (W.designDensity x *
            (dyadicParentBasisFunction k (dyadicChildCell hd c b) i x *
              dyadicParentBasisFunction k (dyadicChildCell hd c b) l x)) := by ring
          _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      · simp [indicator_of_notMem hx]
    rw [he, dyadic_child_indicator_integral hd, integral_const_mul]
    ring
  · rw [ite_eq_right hbe]
    apply integral_eq_zero_of_ae
    filter_upwards [dyadic_children_ae_not_both hd c b e hbe] with x hx
    by_cases hb : x ∈ dyadicRectangle (dyadicChildCell hd c b)
    · have he : x ∉ dyadicRectangle (dyadicChildCell hd c e) := fun he => hx ⟨hb, he⟩
      simp [indicator_of_notMem he]
    · simp [indicator_of_notMem hb]

 theorem ModelWitness.parentMoments_integral (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) (f : Covariate A.d → ℝ) (hf : MemLp f 2 (W.cellDesignMeasure c))
    (i : Fin (Module.finrank ℝ (polynomialLpSpace A.d k))) :
    HilbertGram.moments (W.weightedParentBasis k c) (hf.toLp f) i =
      ∫ x, W.designDensity x * (dyadicParentBasisFunction k c i x * f x)
        ∂rectangleVolume (dyadicOrigin c) (dyadicSides c) := by
  rw [HilbertGram.moments, lp_inner_representatives _ _ _ _ _
    (W.weightedParentBasis_ae k c i) hf.coeFn_toLp]
  exact weightedDesignMeasure_integral _ _ W.designDensity_measurable
    ((W.dyadic_density_bounds c).mono (fun _ hx => A.hgminus.le.trans hx.1)) _

 theorem ModelWitness.weightedSplitChildBasis_moments (W : ModelWitness A F P) {j : ℕ}
    (k : ℕ) (c : DyadicCell A.d j) (f : Covariate A.d → ℝ)
    (hf : MemLp f 2 (W.cellDesignMeasure c))
    (hc : ∀ b, MemLp f 2 (W.cellDesignMeasure (dyadicChildCell
      (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b))) :
    HilbertGram.moments (W.weightedSplitChildBasis k c) (hf.toLp f) =
      fun bi : SplitIndex A.d k => HilbertGram.moments
        (W.weightedParentBasis k (dyadicChildCell (lt_of_lt_of_le Nat.zero_lt_one A.hd) c bi.1))
          ((hc bi.1).toLp f) bi.2 / Real.sqrt 2 := by
  funext ⟨b, i⟩
  let hd := lt_of_lt_of_le Nat.zero_lt_one A.hd
  rw [HilbertGram.moments, lp_inner_representatives _ _ _ _ _
    (W.weightedSplitChildBasis_ae k c (b, i)) hf.coeFn_toLp]
  change (∫ x, dyadicChildBasisFunction hd k c (b, i) x * f x
    ∂weightedDesignMeasure (rectangleVolume (dyadicOrigin c) (dyadicSides c)) W.designDensity) = _
  rw [weightedDesignMeasure_integral _ _ W.designDensity_measurable
    ((W.dyadic_density_bounds c).mono (fun _ hx => A.hgminus.le.trans hx.1)),
    dyadicChildBasisFunction_eq_parent hd, W.parentMoments_integral]
  have he : (fun x => W.designDensity x *
      ((dyadicRectangle (dyadicChildCell hd c b)).indicator
        (fun x => Real.sqrt 2 * dyadicParentBasisFunction k (dyadicChildCell hd c b) i x) x * f x)) =
      (dyadicRectangle (dyadicChildCell hd c b)).indicator
        (fun x => Real.sqrt 2 * (W.designDensity x *
          (dyadicParentBasisFunction k (dyadicChildCell hd c b) i x * f x))) := by
    funext x
    by_cases hx : x ∈ dyadicRectangle (dyadicChildCell hd c b)
    · simp only [indicator_of_mem hx]
      ring
    · simp [indicator_of_notMem hx]
  rw [he, dyadic_child_indicator_integral hd, integral_const_mul, ← mul_assoc]
  have hr : (1 / 2 : ℝ) * Real.sqrt 2 = 1 / Real.sqrt 2 := by
    apply (eq_div_iff (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne').mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hr]
  ring

 theorem ModelWitness.childParentGram_posDef (W : ModelWitness A F P) {j : ℕ}
    (k : ℕ) (c : DyadicCell A.d j) (b : Bool) :
    (Matrix.gram ℝ (W.weightedParentBasis k (dyadicChildCell
      (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b))).PosDef := by
  have hp := Matrix.posDef_gram_of_linearIndependent (W.weightedSplitChildBasis_linearIndependent k c)
  rw [W.weightedSplitChildBasis_gram] at hp
  have hs := hp.submatrix (show Function.Injective (fun i : Fin (Module.finrank ℝ (polynomialLpSpace A.d k)) => (b, i))
    from fun i l h => Prod.mk.inj h |>.2)
  have he : (RoughRegime.BlockProjectionEnergy.blockGram (fun b =>
      Matrix.gram ℝ (W.weightedParentBasis k (dyadicChildCell
        (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b)))).submatrix (fun i => (b, i)) (fun i => (b, i)) =
      Matrix.gram ℝ (W.weightedParentBasis k (dyadicChildCell
        (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b)) := by
    ext i l
    simp only [Matrix.submatrix_apply, RoughRegime.BlockProjectionEnergy.blockGram_apply, ite_true]
  rw [he] at hs
  exact hs

 theorem ModelWitness.childParentBasis_linearIndependent (W : ModelWitness A F P) {j : ℕ}
    (k : ℕ) (c : DyadicCell A.d j) (b : Bool) :
    LinearIndependent ℝ (W.weightedParentBasis k (dyadicChildCell
      (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b)) :=
  Matrix.linearIndependent_of_posDef_gram (W.childParentGram_posDef k c b)

 theorem ModelWitness.weightedSplitChildBasis_span (W : ModelWitness A F P) {j : ℕ}
    (k : ℕ) (c : DyadicCell A.d j) :
    HilbertGram.basisSpan (W.weightedSplitChildBasis k c) =
      HilbertGram.basisSpan (W.weightedChildBasis k c) := by
  unfold HilbertGram.basisSpan
  congr 1
  ext f
  constructor
  · rintro ⟨bi, rfl⟩
    exact ⟨(Fintype.equivFin (SplitIndex A.d k)) bi, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨(Fintype.equivFin (SplitIndex A.d k)).symm i, ?_⟩
    simp only [weightedSplitChildBasis, Equiv.apply_symm_apply]

/-- The actual parent-normalized projection onto the two-child space has
energy equal to the half-sum of the true child-normalized polynomial energies. -/
 theorem ModelWitness.split_projection_child_energy (W : ModelWitness A F P) {j : ℕ}
    (k : ℕ) (c : DyadicCell A.d j) (f g : Covariate A.d → ℝ)
    (hf : MemLp f 2 (W.cellDesignMeasure c)) (hg : MemLp g 2 (W.cellDesignMeasure c))
    (hfc : ∀ b, MemLp f 2 (W.cellDesignMeasure (dyadicChildCell
      (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b)))
    (hgc : ∀ b, MemLp g 2 (W.cellDesignMeasure (dyadicChildCell
      (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b))) :
    inner ℝ ((HilbertGram.basisSpan (W.weightedSplitChildBasis k c)).starProjection (hf.toLp f))
      ((HilbertGram.basisSpan (W.weightedSplitChildBasis k c)).starProjection (hg.toLp g)) =
      (1 / 2 : ℝ) * ∑ b : Bool,
        inner ℝ ((HilbertGram.basisSpan (W.weightedParentBasis k
          (dyadicChildCell (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b))).starProjection ((hfc b).toLp f))
          ((HilbertGram.basisSpan (W.weightedParentBasis k
            (dyadicChildCell (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b))).starProjection ((hgc b).toLp g)) := by
  rw [HilbertGram.child_projection_inner _ (W.weightedSplitChildBasis_linearIndependent k c),
    W.weightedSplitChildBasis_gram, W.weightedSplitChildBasis_moments k c f hf hfc,
    W.weightedSplitChildBasis_moments k c g hg hgc,
    RoughRegime.BlockProjectionEnergy.bool_child_energy _ (W.childParentGram_posDef k c)
      (fun b => HilbertGram.moments (W.weightedParentBasis k (dyadicChildCell
        (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b)) ((hfc b).toLp f))
      (fun b => HilbertGram.moments (W.weightedParentBasis k (dyadicChildCell
        (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b)) ((hgc b).toLp g))]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact (HilbertGram.child_projection_inner _ (W.childParentBasis_linearIndependent k c b) _ _).symm

/-- The same genuine projection-energy identity in the paper's finite reindexed
child basis, used in the multilevel telescope. -/
 theorem ModelWitness.finite_projection_child_energy (W : ModelWitness A F P) {j : ℕ}
    (k : ℕ) (c : DyadicCell A.d j) (f g : Covariate A.d → ℝ)
    (hf : MemLp f 2 (W.cellDesignMeasure c)) (hg : MemLp g 2 (W.cellDesignMeasure c))
    (hfc : ∀ b, MemLp f 2 (W.cellDesignMeasure (dyadicChildCell
      (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b)))
    (hgc : ∀ b, MemLp g 2 (W.cellDesignMeasure (dyadicChildCell
      (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b))) :
    inner ℝ ((HilbertGram.basisSpan (W.weightedChildBasis k c)).starProjection (hf.toLp f))
      ((HilbertGram.basisSpan (W.weightedChildBasis k c)).starProjection (hg.toLp g)) =
      (1 / 2 : ℝ) * ∑ b : Bool,
        inner ℝ ((HilbertGram.basisSpan (W.weightedParentBasis k
          (dyadicChildCell (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b))).starProjection ((hfc b).toLp f))
          ((HilbertGram.basisSpan (W.weightedParentBasis k
            (dyadicChildCell (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b))).starProjection ((hgc b).toLp g)) := by
  simpa only [W.weightedSplitChildBasis_span k c] using
    W.split_projection_child_energy k c f g hf hg hfc hgc

end RoughRegime.Model
