module

public import RoughRegime.PhaseFieldTransport


@[expose] public section
/-! Exact reindexing of the latent coefficient prior in the actual affine-phase norm. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
variable {H K X : Type*} [MeasurableSpace H] [MeasurableSpace K] [MeasurableSpace X]

theorem AffinePhaseField.ext_fields {F G : AffinePhaseField H X}
    (hc : F.c=G.c) (ha : F.a=G.a) (hb : F.b=G.b) (hu : F.hu=G.hu) (hv : F.hv=G.hv) : F=G := by
  cases F
  cases G
  simp_all

def AffinePhaseField.latentPullback (F : AffinePhaseField H X) (f : K → H) : AffinePhaseField K X where
  c k x := F.c (f k) x
  a k x := F.a (f k) x
  b k x := F.b (f k) x
  hu k x := F.hu (f k) x
  hv k x := F.hv (f k) x

theorem AffinePhaseField.gammaNorm_latentPullback (F : AffinePhaseField H X)
    (ν : Measure H) (ν' : Measure K) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (μ : Measure X) (e : K ≃ᵐ H) (he : MeasurePreserving e ν' ν) (Au Av : ℝ) (M j : ℕ) :
    (F.latentPullback e).gammaNorm ν' μ Au Av M j = F.gammaNorm ν μ Au Av M j := by
  let E : PhaseParameter K ≃ᵐ PhaseParameter H :=
    (e.prodCongr (MeasurableEquiv.refl ℝ)).prodCongr (MeasurableEquiv.refl (Bool×Bool))
  have hE : MeasurePreserving E (phaseBase ν') (phaseBase ν) :=
    (he.prod (MeasurePreserving.id _)).prod (MeasurePreserving.id _)
  unfold AffinePhaseField.gammaNorm labeledNormSquared
  congr 1
  funext xs
  have hi := hE.integral_comp' (fun q=>phaseDifference M q *
    labeledTensor (F.feature Au Av) (j+2) (leadingLabels j) q xs)
  convert congrArg (fun t : ℝ => t ^ 2) hi using 1 <;> rfl

end RoughRegime.PoissonMeasure
