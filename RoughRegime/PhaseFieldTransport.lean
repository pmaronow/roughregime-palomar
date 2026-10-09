module

public import RoughRegime.PoissonNormalization


@[expose] public section
/-! Exact change of spatial coordinates for the affine-phase coefficient
norm, using the actual product measures of the ordinary observation domain. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Y]

def AffinePhaseField.pullback (F : AffinePhaseField H X) (f : Y → X) : AffinePhaseField H Y where
  c h y := F.c h (f y)
  a h y := F.a h (f y)
  b h y := F.b h (f y)
  hu h y := F.hu h (f y)
  hv h y := F.hv h (f y)

omit [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Y] in
theorem AffinePhaseField.pullback_feature (F : AffinePhaseField H X) (f : Y → X)
    (Au Av : ℝ) (l : Fin 3) (q : PhaseParameter H) (y : Y) :
    (F.pullback f).feature Au Av l q y = F.feature Au Av l q (f y) := by
  rfl

theorem AffinePhaseField.pullback_isMeasurable (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (f : Y → X) (hf : Measurable f) :
    (F.pullback f).IsMeasurable := by
  have hg : Measurable (fun p : H × Y => (p.1,f p.2)) := measurable_fst.prodMk (hf.comp measurable_snd)
  exact ⟨hm.c.comp hg,hm.a.comp hg,hm.b.comp hg,hm.hu.comp hg,hm.hv.comp hg⟩

omit [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Y] in
theorem AffinePhaseField.pullback_bounded (F : AffinePhaseField H X)
    (C : ℝ) (hb : F.Bounded C) (f : Y → X) : (F.pullback f).Bounded C :=
  ⟨fun h y => hb.c h (f y),fun h y => hb.a h (f y),fun h y => hb.b h (f y),
    fun h y => hb.hu h (f y),fun h y => hb.hv h (f y)⟩

/-- The complete ordinary product-domain Γ norm is invariant under a genuine
measure-preserving spatial measurable equivalence. -/
theorem AffinePhaseField.gammaNorm_pullback (F : AffinePhaseField H X)
    (ν : Measure H) (μ : Measure X) (μ' : Measure Y) [SigmaFinite μ]
    (e : Y ≃ᵐ X) (he : MeasurePreserving e μ' μ) (Au Av : ℝ) (M j : ℕ) :
    (F.pullback e).gammaNorm ν μ' Au Av M j = F.gammaNorm ν μ Au Av M j := by
  let E : (Fin (j+2) → Y) ≃ᵐ (Fin (j+2) → X) := MeasurableEquiv.piCongrRight fun _ => e
  have hE : MeasurePreserving E (Measure.pi fun _ : Fin (j+2) => μ')
      (Measure.pi fun _ : Fin (j+2) => μ) :=
    measurePreserving_pi (fun _ => μ') (fun _ => μ) (fun _ => he)
  unfold AffinePhaseField.gammaNorm labeledNormSquared
  have hi := hE.integral_comp' (fun xs =>
    (labeledMixture (phaseBase ν) (phaseDifference M) (F.feature Au Av)
      (j+2) (leadingLabels j) xs)^2)
  dsimp [E,MeasurableEquiv.piCongrRight,Equiv.piCongrRight,labeledMixture,labeledTensor] at hi
  simpa only [labeledMixture,labeledTensor,AffinePhaseField.pullback_feature] using hi

end RoughRegime.PoissonMeasure
