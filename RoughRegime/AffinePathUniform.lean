module

public import RoughRegime.LowerMeasure


@[expose] public section
/-! An affine path's positive root-n constant is selected before arbitrary
containing classes and additive target offsets. Only neighborhoods and the
sample cutoff may depend on those later inputs. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace RoughRegime.LowerMeasure
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem affine_path_uniform_rootn (P : ℝ → GeneralTesting.DensityLaw μ)
    (f0 f1 : Ω → ℝ) (G : ℝ → ℝ) (l0 r0 D cf Cf : ℝ)
    (h0 : (0:ℝ) ∈ Ioo l0 r0) (hG : HasDerivAt G D 0) (hD : D ≠ 0)
    (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hdens : ∀ t ∈ Ioo l0 r0, (P t).density =ᵐ[μ] fun x => f0 x+t*f1 x)
    (hpos : ∀ t ∈ Ioo l0 r0, ∀ᵐ x ∂μ, cf ≤ f0 x+t*f1 x)
    (hscore : ∀ᵐ x ∂μ, |f1 x| ≤ Cf) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω)) (tstar : ℝ),
      (∀ᶠ t in nhds 0, (P t).probabilityMeasure ∈ C) →
      ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0] fun t => G t+tstar) →
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤ Model.minimaxRMSE n T C := by
  classical
  obtain ⟨a,ha,hsmall⟩ := Lower.exists_small_parametric_amplitude cf Cf
  let c : ℝ := |D| *a/4
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro T C tstar hclass htarget
  have hregion : ∀ᶠ t in nhds (0:ℝ), t∈Ioo l0 r0 := isOpen_Ioo.mem_nhds h0
  have hlocal : ∀ᶠ t in nhds (0:ℝ), t∈Ioo l0 r0 ∧ (P t).probabilityMeasure∈C :=
    hregion.and hclass
  obtain ⟨l,r,hzero,hsub⟩ := hlocal.exists_Ioo_subset
  let ν : Measure ℝ := volume.restrict (Icc 0 1)
  have hν : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  let _ : IsProbabilityMeasure ν := hν
  have hder := (hG.add_const tstar).congr_of_eventuallyEq htarget
  have hroot := affine_path_rootn ν P f0 f1 (fun t=>T (P t).probabilityMeasure)
    l r 0 D cf Cf a hzero hder hD hcf hCf ha hsmall
    (fun t ht=>hdens t (hsub ht).1) (fun t ht=>hpos t (hsub ht).1) hscore
  filter_upwards [hroot] with n hn
  have hinv : (n:ℝ)^(-(1/2:ℝ))=(Real.sqrt (n:ℝ))⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg n),← Real.sqrt_eq_rpow]
  have he : c*(n:ℝ)^(-(1/2:ℝ))=|D| *(a/Real.sqrt (n:ℝ))/4 := by
    rw [hinv]
    dsimp [c]
    ring
  unfold Model.minimaxRMSE
  apply le_iInf
  intro g
  obtain ⟨t,ht,_,hLp⟩ := hn g.val g.property
  change ENNReal.ofReal (|D| *(a/Real.sqrt (n:ℝ))/4) ≤
    eLpNorm (fun xs=>g.val xs-T (P t).probabilityMeasure) 2
      (Model.randomizedExperiment n (P t).probabilityMeasure) at hLp
  rw [he]
  exact le_iSup_of_le (P t).probabilityMeasure (le_iSup_of_le (hsub ht).2 hLp)

end RoughRegime.LowerMeasure
