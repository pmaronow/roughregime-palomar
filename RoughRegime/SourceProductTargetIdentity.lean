module

public import RoughRegime.SourceTargetSeparation
public import RoughRegime.CanonicalCenteredTargets


@[expose] public section
/-! The true product target and the canonical independent-pair nonlinear
target coincide for the literal bilinear response. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.LatticePriors.CanonicalFrame
set_option backward.isDefEq.respectTransparency false
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

theorem productIntegral_eq_bilinear_response (z : GridPair D N → PairState ι) :
    F.productIntegral z = ∫ x,F.p z x * (F.u z x * F.v z x) ∂Model.cubeVolume (D+1) := by
  unfold productIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => by ring

 theorem productIntegral_eq_independentPairTarget (z : GridPair D N → PairState ι) :
    F.productIntegral z = independentPairTarget F.ell
      (F.centeredBlockTarget (fun x : ℝ×ℝ=>x.1*x.2)) z := by
  have hb (u v : ℝ) (hu : |u|≤F.Au/F.rminus) (hv : |v|≤F.Av/F.rminus) :
      |u*v-(0:ℝ)|≤(F.Au/F.rminus)*(F.Av/F.rminus) := by
    simp only [sub_zero,abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) (div_nonneg F.Au_nonneg F.rminus_pos.le)
  have he := F.global_response_centered_decomposition (fun x : ℝ×ℝ=>x.1*x.2)
    (measurable_fst.mul measurable_snd) ((F.Au/F.rminus)*(F.Av/F.rminus)) (by simpa using hb) z
  simpa using (F.productIntegral_eq_bilinear_response z).trans he

end RoughRegime.LatticePriors.CanonicalFrame
