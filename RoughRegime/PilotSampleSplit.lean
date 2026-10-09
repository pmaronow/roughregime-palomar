module

public import RoughRegime.PilotConditionalRisk


@[expose] public section
/-! The two pilot/estimation blocks are the actual disjoint coordinates of
 the original iid sample. Their product law is derived by a measurable
 finite-coordinate permutation, with no independence premise. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RoughRegime.Applications
set_option backward.isDefEq.respectTransparency false

 def splitIID {Ω : Type*} [MeasurableSpace Ω] (n m : ℕ) :
     (Fin (n+m)→Ω) ≃ᵐ ((Fin n→Ω)×(Fin m→Ω)) :=
   (MeasurableEquiv.piCongrLeft (fun _ : Fin n⊕Fin m =>Ω) finSumFinEquiv.symm).trans
     (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n⊕Fin m =>Ω))

 theorem splitIID_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
     (μ : Measure Ω) [SigmaFinite μ] (n m : ℕ) :
     MeasurePreserving (splitIID (Ω:=Ω) n m) (Measure.pi (fun _ : Fin (n+m)=>μ))
       ((Measure.pi (fun _ : Fin n=>μ)).prod (Measure.pi (fun _ : Fin m=>μ))) := by
   exact (measurePreserving_sumPiEquivProdPi (fun _ : Fin n⊕Fin m=>μ)).comp
     (measurePreserving_piCongrLeft (fun _ : Fin n⊕Fin m=>μ) finSumFinEquiv.symm)

 theorem clipped_conditional_iid_error {Ω : Type*} [MeasurableSpace Ω]
     (μ : Measure Ω) [IsProbabilityMeasure μ] (n m : ℕ)
     (E : (Fin n→Ω)×(Fin m→Ω)→ℝ) (hE : Measurable E)
     (good : Set (Fin n→Ω)) (hgood : MeasurableSet good) (target r b : ℝ)
     (ht : target∈Icc (0:ℝ) 1) (hr : 0≤r) (hb : 0≤b)
     (hbad : (Measure.pi (fun _ : Fin n=>μ)).real goodᶜ≤b)
     (hconditional : ∀ p ∈ good,eLpNorm (fun y=>E (p,y)-target) 2
       (Measure.pi (fun _ : Fin m=>μ))≤ENNReal.ofReal r) :
     eLpNorm (fun xs=>clipUnit (E (splitIID n m xs))-target) 2
       (Measure.pi (fun _ : Fin (n+m)=>μ))≤ENNReal.ofReal (r+Real.sqrt b) := by
   have hm : Measurable (fun q=>clipUnit (E q)-target) :=
     (clipUnit_measurable.comp hE).sub measurable_const
   have hbad' : (Measure.pi (fun _ : Fin n=>μ)) goodᶜ≤ENNReal.ofReal b := by
     rw [←ENNReal.ofReal_toReal (measure_ne_top _ _)]
     exact ENNReal.ofReal_le_ofReal hbad
   have h := clipped_conditional_eLpNorm (Measure.pi (fun _ : Fin n=>μ))
     (Measure.pi (fun _ : Fin m=>μ)) E hE good hgood target r b ht hr hb hbad' hconditional
   rw [←eLpNorm_comp_measurePreserving hm.aestronglyMeasurable (splitIID_measurePreserving μ n m)] at h
   exact h

end RoughRegime.Applications
