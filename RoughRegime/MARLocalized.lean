module

public import RoughRegime.MARBaseline
public import RoughRegime.ParametricBaselineLower


@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace RoughRegime.Applications.MAR

/-- The generic conditional ratio `a` determines the literal MAR propensity,
up to the null sets allowed for conditional versions. -/
theorem generic_inverse_eq_propensity (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response))
    (h : Model.ModelWitness A (observables A hM) P) :
    (fun x => (h.a x)⁻¹) =ᵐ[Model.cubeVolume A.d] h.w := by
  have hm : Model.covariateInformation A Response ≤
      (inferInstance : MeasurableSpace (Model.Covariate A.d × Response)) :=
    measurable_fst.comap_le
  have hua : ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × Response)),
      h.w o.1 * h.a o.1 = 1 := by
    have hu := h.momentU
    change (P : Measure (Model.Covariate A.d × Response))[fun _ => (1 : ℝ) |
      Model.covariateInformation A Response] =ᵐ[_] fun o => h.w o.1 * h.a o.1 at hu
    rw [condExp_const hm] at hu
    exact hu.symm
  have hmap : ∀ᵐ x ∂(P : Measure (Model.Covariate A.d × Response)).map Prod.fst,
      h.w x * h.a x = 1 :=
    (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_eq_fun (h.measurableW.mul h.measurableA) measurable_const)).mpr hua
  rw [h.marginal, ae_withDensity_iff
    (f := fun x => ENNReal.ofReal (h.p x))
    (ENNReal.measurable_ofReal.comp h.measurableP)] at hmap
  filter_upwards [hmap, Model.witness_density_positive A (observables A hM) P h] with x hx hp
  exact inv_eq_of_mul_eq_one_left (hx (ENNReal.ofReal_ne_zero_iff.mpr hp))

/-- A generic MAR witness with the upper overlap restriction gives a literal
reciprocal-propensity witness for the paper's MAR class. -/
def genericWitnessToMAR (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response))
    (h : Model.ModelWitness A (observables A hM) P)
    (hupper : ∀ᵐ x ∂Model.cubeVolume A.d, h.w x ≤ 1 - A.δ) : Witness A P where
  p := h.p
  w x := (h.a x)⁻¹
  b := h.b
  measurableP := h.measurableP
  measurableW := h.measurableA.inv
  measurableB := h.measurableB
  nonnegativeP := h.nonnegativeP
  marginal := h.marginal
  momentD := by
    have he := generic_inverse_eq_propensity A hM P h
    have heP : (fun o : Model.Covariate A.d × Response => (h.a o.1)⁻¹) =ᵐ[
        (P : Measure (Model.Covariate A.d × Response))] h.w ∘ Prod.fst := by
      change ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × Response)), (h.a o.1)⁻¹ = h.w o.1
      apply ae_of_ae_map (f := Prod.fst) (p := fun x => (h.a x)⁻¹ = h.w x) measurable_fst.aemeasurable
      rw [h.marginal]
      exact he.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
    exact h.momentD.trans heP.symm
  momentV := by
    have he := generic_inverse_eq_propensity A hM P h
    have heP : (fun o : Model.Covariate A.d × Response => (h.a o.1)⁻¹) =ᵐ[
        (P : Measure (Model.Covariate A.d × Response))] h.w ∘ Prod.fst := by
      change ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × Response)), (h.a o.1)⁻¹ = h.w o.1
      apply ae_of_ae_map (f := Prod.fst) (p := fun x => (h.a x)⁻¹ = h.w x) measurable_fst.aemeasurable
      rw [h.marginal]
      exact he.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [h.momentV, heP] with o hv heo
    change (P : Measure (Model.Covariate A.d × Response))[observedOutcome ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] o = h.w o.1 * h.b o.1 at hv
    simpa only [heo, Function.comp_apply] using hv
  overlap := by
    filter_upwards [generic_inverse_eq_propensity A hM P h, h.overlap, hupper] with x hx hlo hhi
    simpa only [hx] using And.intro hlo hhi
  smoothInverse := by
    simpa only [inv_inv] using h.smoothA
  smoothB := h.smoothB
  densityBounds := by
    filter_upwards [generic_inverse_eq_propensity A hM P h, h.densityBounds] with x hx hg
    simpa only [hx] using hg

/-- The paper's claimed localized MAR inclusion, with the actual finite
baseline and its upper-overlap margin. -/
theorem localized_subset_mar (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (r : ℝ) (hr : r < 1 / 2 - A.δ) :
    Model.localClass A (observables A hM) baseline r ⊆ modelClass A := by
  rintro P ⟨h, hlocal⟩
  refine ⟨genericWitnessToMAR A hM P h ?_⟩
  have hw0 := (baseline_ratios A hM).1
  filter_upwards [hlocal] with x hx
  rw [hw0] at hx
  have he := (abs_le.mp hx.1).2
  linarith

/-- An actual positive root-n minimax lower bound on the MAR class and every
class containing the indicated localized model. -/
theorem mar_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1 / 2) (hhi : 1 / 2 < A.gplus) (hH : 2 < A.H)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      ∀ C : Set (ProbabilityMeasure (Model.Covariate A.d × Response)),
        Model.localClass A (observables A hM) baseline r ⊆ C →
        ∀ n : ℕ, n0 ≤ n → ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
          Model.minimaxRMSE n (Model.target A (observables A hM)) C :=
  Model.main_parametric_lower A (observables A hM) baseline
    (baseline_nondegenerate A hM hlo hhi hH) r hr

theorem mar_class_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1 / 2) (hhi : 1 / 2 < A.gplus) (hH : 2 < A.H) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        Model.minimaxRMSE n (Model.target A (observables A hM)) (modelClass A) := by
  let r : ℝ := (1 / 2 - A.δ) / 2
  have hδ : A.δ < 1 / 2 := (le_max_left _ _).trans_lt hlo
  have hr : 0 < r := by dsimp [r]; linarith
  have hrup : r < 1 / 2 - A.δ := by dsimp [r]; linarith
  obtain ⟨c, hc, n0, _, hn⟩ := mar_parametric_lower A hM hlo hhi hH r hr
  refine ⟨c, hc, eventually_atTop.2 ⟨n0, ?_⟩⟩
  exact hn (modelClass A) (localized_subset_mar A hM r hrup)

end RoughRegime.Applications.MAR
