module

public import RoughRegime.GammaSignBridge


@[expose] public section
/-! Exact regrouping of the ordinary spatial-times-two-block coefficient norm
into the source's two bump arguments, density arguments, and finite label sum. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [MeasurableSpace X]

 def twoPlusTuple (j : ℕ) : (Fin (j + 2) → X) ≃ᵐ ((X × X) × (Fin j → X)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 2) => X) 0).trans
    (((MeasurableEquiv.refl X).prodCongr
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => X) 0)).trans
      MeasurableEquiv.prodAssoc.symm)

 def consTwo (j : ℕ) (z : (X × X) × (Fin j → X)) : Fin (j + 2) → X :=
  Fin.cons z.1.1 (Fin.cons z.1.2 z.2)

 theorem twoPlusTuple_symm (j : ℕ) (z : (X × X) × (Fin j → X)) :
    (twoPlusTuple (X := X) j).symm z = consTwo j z := by
  funext i
  cases i using Fin.cases
  · simp [twoPlusTuple, consTwo, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc, Equiv.prodCongr, Equiv.prodAssoc]
  · rename_i i
    cases i using Fin.cases <;> simp [twoPlusTuple, consTwo, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc, Equiv.prodCongr, Equiv.prodAssoc]

 theorem twoPlusTuple_measurePreserving (μ : Measure X) [SigmaFinite μ] (j : ℕ) :
    MeasurePreserving (twoPlusTuple (X := X) j) (Measure.pi (fun _ : Fin (j + 2) => μ))
      ((μ.prod μ).prod (Measure.pi (fun _ : Fin j => μ))) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (j + 2) => μ) 0
  have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (j + 1) => μ) 0
  have hmid := (MeasurePreserving.id μ).prod h2
  have hassoc := (measurePreserving_prodAssoc μ μ (Measure.pi (fun _ : Fin j => μ))).symm MeasurableEquiv.prodAssoc
  exact hassoc.comp (hmid.comp h1)

 theorem integral_pi_two (μ : Measure X) [SigmaFinite μ] (j : ℕ) (f : (Fin (j + 2) → X) → ℝ) :
    (∫ xs, f xs ∂Measure.pi (fun _ : Fin (j + 2) => μ)) =
      ∫ z, f (consTwo j z) ∂(μ.prod μ).prod (Measure.pi (fun _ : Fin j => μ)) := by
  have hi := ((twoPlusTuple_measurePreserving μ j).symm (twoPlusTuple j)).integral_comp' f
  simpa only [twoPlusTuple_symm] using hi.symm

 theorem pi_count_bool (k : ℕ) :
    Measure.pi (fun _ : Fin k => (Measure.count : Measure Bool)) =
      (Measure.count : Measure (Fin k → Bool)) := by
  apply Measure.ext_of_singleton
  intro xs
  rw [← Set.univ_pi_singleton xs, Measure.pi_pi]
  simp [Set.univ_pi_singleton]

 theorem two_block_mark_regroup (μ : Measure X) [SigmaFinite μ] (j : ℕ)
    (f : (Fin (j + 2) → X × Bool) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin (j + 2) => μ.prod Measure.count))) :
    (∫ xs, f xs ∂Measure.pi (fun _ : Fin (j + 2) => μ.prod Measure.count)) =
    ∑ labels : Fin (j + 2) → Bool,
      ∫ z, f (fun i => (consTwo j z i, labels i))
        ∂(μ.prod μ).prod (Measure.pi (fun _ : Fin j => μ)) := by
  let E := MeasurableEquiv.arrowProdEquivProdArrow X Bool (Fin (j + 2))
  have hE := measurePreserving_arrowProdEquivProdArrow X Bool (Fin (j + 2))
    (fun _ => μ) (fun _ => (Measure.count : Measure Bool))
  let F := fun q : (Fin (j + 2) → X) × (Fin (j + 2) → Bool) => f (fun i => (q.1 i, q.2 i))
  have hFi : Integrable F ((Measure.pi (fun _ : Fin (j + 2) => μ)).prod
      (Measure.pi (fun _ : Fin (j + 2) => (Measure.count : Measure Bool)))) := by
    have hi := (hE.symm E).integrable_comp_of_integrable hf
    simpa [E, F, Function.comp_def, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] using hi
  have he : (∫ xs, f xs ∂Measure.pi (fun _ : Fin (j + 2) => μ.prod Measure.count)) =
      ∫ q, F q ∂(Measure.pi (fun _ : Fin (j + 2) => μ)).prod
        (Measure.pi (fun _ : Fin (j + 2) => (Measure.count : Measure Bool))) := by
    have hi := (hE.symm E).integral_comp' f
    simpa [E, F, Function.comp_def, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] using hi.symm
  rw [he, integral_prod_symm F hFi, pi_count_bool, integral_count]
  apply Finset.sum_congr rfl
  intro labels _
  exact integral_pi_two μ j (fun xs => f (fun i => (xs i, labels i)))

end RoughRegime.PoissonMeasure
