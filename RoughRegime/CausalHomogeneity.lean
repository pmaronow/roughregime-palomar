module

public import RoughRegime.CausalConditional


@[expose] public section
/-! Mean-effect homogeneity across a larger information field gives the true
conditional selected-effect factorization by tower and pull-out. -/
noncomputable section
open MeasureTheory Filter
namespace RoughRegime.Causal

theorem selected_effect_of_mean_homogeneity {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m1 m2 : MeasurableSpace Ω)
    (hm12 : m1 ≤ m2) (hm2 : m2 ≤ mΩ) (g effect : Ω→ℝ)
    (hg : StronglyMeasurable[m2] g) (M : ℝ) (hgb : ∀ᵐ ω ∂μ,‖g ω‖≤M)
    (hei : Integrable effect μ) (hhom : μ[effect|m2]=ᵐ[μ] μ[effect|m1]) :
    μ[(fun ω=>g ω*effect ω)|m1]=ᵐ[μ]
      fun ω=>μ[g|m1] ω*μ[effect|m1] ω := by
  let : MeasurableSpace Ω := mΩ
  have hga : AEStronglyMeasurable g μ := (hg.mono hm2).aestronglyMeasurable
  have hgi : Integrable g μ := Integrable.of_bound hga M hgb
  have hprod : Integrable (g*effect) μ := hei.bdd_mul hga hgb
  have hceprod : Integrable (g*μ[effect|m1]) μ := integrable_condExp.bdd_mul hga hgb
  have hinner : μ[g*effect|m2]=ᵐ[μ] g*μ[effect|m1] :=
    (condExp_mul_of_stronglyMeasurable_left hg hprod hei).trans
      (EventuallyEq.rfl.mul hhom)
  have htower : μ[g*effect|m1]=ᵐ[μ] μ[μ[g*effect|m2]|m1] :=
    (condExp_condExp_of_le hm12 hm2).symm
  exact htower.trans ((condExp_congr_ae hinner).trans
    (condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp hceprod hgi))

end RoughRegime.Causal
