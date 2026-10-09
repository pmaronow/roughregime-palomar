module

public import RoughRegime.ModelLocalLemma
public import RoughRegime.ModelBaseLemma


@[expose] public section
/-! A single class constant for every base and increment conclusion of source
Lemma 6, with the actual finite observables and actual model means. -/
noncomputable section
open MeasureTheory MvPolynomial
namespace RoughRegime.Model
universe u
open RoughRegime.Upper RoughRegime.ProjectionIncrementComplex
open RoughRegime.KernelExpressions RoughRegime.ComplexDerivativeBridge

def SourceLocalBounds (A : Parameters) (hαβ : A.α ≤ A.β) (C : ℝ) : Prop :=
  ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j : ℕ) (c : DyadicCell A.d j),
      let x := dyadicDesignMean A F P (holderOrder A.β) c
      let r := dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd)
      let h := (2 : ℝ) ^ (-(j : ℝ) / A.d)
      Measurable (localDesignStatistic A F c) ∧
      (fun i => (∫ o, localDesignStatistic A F c o ∂(P : Measure (Observation A Z))) i) = x ∧
      W.localProjectionIncrement c = localIncrementFunction A r x ∧
      (∀ o, ‖localDesignStatistic A F c o‖ ≤ C * (2 : ℝ) ^ j *
        (dyadicPartitionCell c).indicator (fun _ => (1 : ℝ)) o.1) ∧
      (P : Measure (Observation A Z)).real (Prod.fst ⁻¹' dyadicPartitionCell c) ≤ C / (2 : ℝ) ^ j ∧
      ‖W.localProjectionIncrement c‖ ≤ C * h ^ (A.α + A.β) ∧
      ∀ m : ℕ,
        let q := localIncrementPolynomial A hαβ r m
        q.totalDegree ≤ m + A.nu + 2 ∧
        ‖W.localProjectionIncrement c - MvPolynomial.eval x q‖ ≤
          C * h ^ (A.α + A.β) * ((m + 1 : ℕ) : ℝ) ^ A.nu * intervalRho A.gminus A.gplus ^ m ∧
        (∀ t : Fin (localMomentDimension A) → ℂ,
          ‖t - realParametersCLM (localMomentDimension A) x‖ < 1 / C →
          ‖MvPolynomial.eval t (complexify q)‖ ≤ C) ∧
        ‖polynomialGradient q x‖ ≤ C * h ^ min (min A.α A.β) 1

def SourceBaseBounds (A : Parameters) (C : ℝ) : Prop :=
  ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P),
      let x := baseDesignMean A F P (holderOrder A.β)
      Measurable (baseDesignStatistic A F (holderOrder A.β)) ∧
      (fun i => (∫ o, baseDesignStatistic A F (holderOrder A.β) o ∂(P : Measure (Observation A Z))) i) = x ∧
      (∀ o, ‖baseDesignStatistic A F (holderOrder A.β) o‖ ≤
        C * (cube A.d).indicator (fun _ => (1 : ℝ)) o.1) ∧
      (P : Measure (Observation A Z)).real (Prod.fst ⁻¹' cube A.d) ≤ C ∧
      ∀ m,
        let q := baseIncrementPolynomial A m
        q.totalDegree ≤ m + 2 ∧
        ‖W.levelProjectionTarget (holderOrder A.β) 0 - MvPolynomial.eval x q‖ ≤
          C * intervalRho A.gminus A.gplus ^ m ∧
        (∀ t, ‖t - realParametersCLM (designMomentDimension (baseDimension A.d (holderOrder A.β))) x‖ < 1 / C →
          ‖MvPolynomial.eval t (complexify q)‖ ≤ C) ∧
        ‖polynomialGradient q x‖ ≤ C

lemma SourceLocalBounds.mono {A : Parameters} {hαβ : A.α ≤ A.β} {C D : ℝ}
    (h : SourceLocalBounds.{u} A hαβ C) (hC : 0 < C) (hCD : C ≤ D) :
    SourceLocalBounds.{u} A hαβ D := by
  intro Z _ F P W j c
  obtain ⟨hmeas, hmean, hid, hstat, hprob, hsize, hpoly⟩ := h Z F P W j c
  dsimp only at *
  refine ⟨hmeas, hmean, hid, ?_, ?_, ?_, ?_⟩
  · intro o
    exact (hstat o).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (by positivity))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
  · exact hprob.trans (div_le_div_of_nonneg_right hCD (by positivity))
  · exact hsize.trans (mul_le_mul_of_nonneg_right hCD (by positivity))
  · intro m
    obtain ⟨hd, he, hc, hg⟩ := hpoly m
    refine ⟨hd, ?_, ?_, ?_⟩
    · apply he.trans
      have hρ := (intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus).le
      gcongr
    · intro t ht
      exact (hc t (ht.trans_le (one_div_le_one_div_of_le hC hCD))).trans hCD
    · exact hg.trans (mul_le_mul_of_nonneg_right hCD (by positivity))

lemma SourceBaseBounds.mono {A : Parameters} {C D : ℝ}
    (h : SourceBaseBounds.{u} A C) (hC : 0 < C) (hCD : C ≤ D) :
    SourceBaseBounds.{u} A D := by
  intro Z _ F P W
  obtain ⟨hmeas, hmean, hstat, hprob, hpoly⟩ := h Z F P W
  dsimp only at *
  refine ⟨hmeas, hmean, ?_, hprob.trans hCD, ?_⟩
  · intro o
    exact (hstat o).trans (mul_le_mul_of_nonneg_right hCD
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
  · intro m
    obtain ⟨hd, he, hc, hg⟩ := hpoly m
    refine ⟨hd, ?_, ?_, hg.trans hCD⟩
    · exact he.trans (mul_le_mul_of_nonneg_right hCD
        (pow_nonneg (intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus).le m))
    · intro t ht
      exact (hc t (ht.trans_le (one_div_le_one_div_of_le hC hCD))).trans hCD

/-- The full local-and-base bound package of source Lemma 6 has one common
constant, selected before every model, response type, level, cell and order.
The global increment identity is supplied by the separately proved telescope. -/
theorem uniform_source_projection_lemma (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ C : ℝ, 1 ≤ C ∧ SourceLocalBounds.{u} A hαβ C ∧ SourceBaseBounds.{u} A C := by
  obtain ⟨Ci, hCi, hi⟩ := uniform_model_local_lemma.{u} A hαβ
  obtain ⟨Cb, hCb, hb⟩ := uniform_model_base_lemma.{u} A
  refine ⟨max Ci Cb, hCi.trans (le_max_left _ _), ?_, ?_⟩
  · exact SourceLocalBounds.mono hi (zero_lt_one.trans_le hCi) (le_max_left _ _)
  · exact SourceBaseBounds.mono hb (zero_lt_one.trans_le hCb) (le_max_right _ _)

end RoughRegime.Model
