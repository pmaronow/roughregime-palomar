module

public import RoughRegime.ModelFullLocalPolynomials
public import RoughRegime.SourceProjectionLemma


@[expose] public section
/-! The exact uncapped gradient conclusion of source Lemma 6, together with
all its original observable, mean, approximation and base conclusions,
under one class constant chosen before every model and truncation order. -/
noncomputable section
open MeasureTheory MvPolynomial
namespace RoughRegime.Model
universe u
open RoughRegime.Upper RoughRegime.ProjectionIncrementComplex
open RoughRegime.KernelExpressions RoughRegime.ComplexDerivativeBridge
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def SourceLocalFullGradientBounds (A : Parameters) (hαβ : A.α ≤ A.β) (C : ℝ) : Prop :=
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
        ‖polynomialGradient q x‖ ≤ C * h ^ min A.α A.β


/-- The literal full source Lemma 6 package. In particular, the gradient is
bounded by h^min(alpha,beta), without capping this exponent at one. -/
theorem uniform_source_projection_lemma_full_gradient (A : Parameters) (hαβ : A.α≤A.β) :
    ∃C:ℝ,1≤C ∧ SourceLocalFullGradientBounds.{u} A hαβ C ∧ SourceBaseBounds.{u} A C := by
  obtain ⟨C0,hC0,hlocal,hbase⟩:=uniform_source_projection_lemma.{u} A hαβ
  obtain ⟨Cg,hCg,hgradient⟩:=uniform_model_local_polynomials_full_gradient.{u} A hαβ
  let C:=max C0 Cg
  have hC0C:C0≤C:=le_max_left _ _
  have hCgC:Cg≤C:=le_max_right _ _
  have hl:=SourceLocalBounds.mono hlocal (zero_lt_one.trans_le hC0) hC0C
  have hb:=SourceBaseBounds.mono hbase (zero_lt_one.trans_le hC0) hC0C
  refine ⟨C,hC0.trans hC0C,?_,hb⟩
  intro Z _ F P W j c
  obtain ⟨hmeas,hmean,hid,hstat,hprob,hsize,hpoly⟩:=hl Z F P W j c
  dsimp only at *
  refine ⟨hmeas,hmean,hid,hstat,hprob,hsize,?_⟩
  intro m
  obtain ⟨hd,he,hc,_⟩:=hpoly m
  refine ⟨hd,he,hc,?_⟩
  have hg:=(hgradient Z F P W j c m).2.2.2
  exact hg.trans (mul_le_mul_of_nonneg_right hCgC (by positivity))

end RoughRegime.Model
