module

public import RoughRegime.GateExpectation
public import RoughRegime.AngularLaw
public import RoughRegime.PoissonPhase
public import Mathlib.Probability.Kernel.Composition.WithDensity


@[expose] public section
/-! Exact probability-law equivalences between the coordinate-first phase
likelihood representation and the level-first canonical source prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

 theorem measurableEquiv_map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
     (e : X ≃ᵐ Y) (μ : Measure X) (g : Y → ℝ≥0∞) (hg : Measurable g) :
     (μ.withDensity (g ∘ e)).map e = (μ.map e).withDensity g := by
   apply Measure.ext_of_lintegral
   intro f hf
   calc
     _ = ∫⁻ x, f (e x) ∂μ.withDensity (g ∘ e) := lintegral_map hf e.measurable
     _ = ∫⁻ x, g (e x)*f (e x) ∂μ := by
       simpa only [Function.comp_def,Pi.mul_apply] using
         lintegral_withDensity_eq_lintegral_mul μ (hg.comp e.measurable) (hf.comp e.measurable)
     _ = ∫⁻ y, g y*f y ∂μ.map e := (lintegral_map (hg.mul hf) e.measurable).symm
     _ = _ := (lintegral_withDensity_eq_lintegral_mul (μ.map e) hg hf).symm

def angularDensity (M : ℕ) (positive : Bool) (ts : ℝ × (Bool × Bool)) : ℝ≥0∞ :=
  ENNReal.ofReal (phaseDensity (H:=Unit) M (if positive then 1 else -1) (((),ts.1),ts.2))
 theorem angularDensity_measurable (M : ℕ) (positive : Bool) : Measurable (angularDensity M positive) := by
   unfold angularDensity phaseDensity
   have hs : Measurable Lower.sign := measurable_of_countable _
   fun_prop

 theorem angularSignLaw_eq_withDensity (M : ℕ) (positive : Bool) (θ : ℝ) :
     (angularSignLaw M θ positive).toMeasure =
       uniformSigns.withDensity (fun st=>angularDensity M positive (θ,st)) := by
   apply Measure.ext_of_singleton
   intro st
   rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton st),withDensity_apply _ (measurableSet_singleton st),lintegral_singleton]
   simp only [angularSignLaw,signLaw_apply,uniformSigns,Measure.smul_apply,
     Measure.count_singleton,smul_eq_mul,mul_one,angularDensity,phaseDensity,Lower.signWeight]
   rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
   norm_num only [ENNReal.ofReal_ofNat,div_eq_mul_inv,one_div]
   have hnum : 1+Lower.sign st.1*Lower.sign st.2*((if positive then (1:ℝ) else -1)*Real.cos (M*θ)) =
       1+(if positive then (1:ℝ) else -1)*Lower.sign st.1*Lower.sign st.2*Real.cos (M*θ) := by ring
   rw [hnum]
   simp only [one_mul]

 theorem angleSignLaw_eq_withDensity (M : ℕ) (positive : Bool) :
     angleSignLaw M positive = (LatticeFourier.angleUniform.prod uniformSigns).withDensity (angularDensity M positive) := by
   let g := fun θ st=>angularDensity M positive (θ,st)
   have hg : Measurable (Function.uncurry g) := angularDensity_measurable M positive
   letI : IsSFiniteKernel ((Kernel.const ℝ uniformSigns).withDensity g) :=
     Kernel.IsSFiniteKernel.withDensity _ (fun _ _=>ENNReal.ofReal_ne_top)
   have he : angularSignKernel M positive=(Kernel.const ℝ uniformSigns).withDensity g := by
     apply Kernel.ext
     intro θ
     rw [angularSignKernel_apply,Kernel.withDensity_apply _ hg]
     exact angularSignLaw_eq_withDensity M positive θ
   rw [angleSignLaw,he,Measure.compProd_withDensity hg,Measure.compProd_const]

 theorem phasePrior_assoc {H : Type*} [MeasurableSpace H] (ν : Measure H) [IsProbabilityMeasure ν]
     (M : ℕ) (positive : Bool) :
     ((phasePrior ν M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure).map
       (MeasurableEquiv.prodAssoc : ((H×ℝ)×(Bool×Bool)) ≃ᵐ H×(ℝ×(Bool×Bool))) =
       ν.prod (angleSignLaw M positive) := by
   let e : ((H×ℝ)×(Bool×Bool)) ≃ᵐ H×(ℝ×(Bool×Bool)) := MeasurableEquiv.prodAssoc
   let g := fun p : H×(ℝ×(Bool×Bool))=>angularDensity M positive p.2
   have hg : Measurable g := (angularDensity_measurable M positive).comp measurable_snd
   change ((phaseBase ν).withDensity (g ∘ e)).map e=ν.prod (angleSignLaw M positive)
   rw [measurableEquiv_map_withDensity_comp e (phaseBase ν) g hg,phaseBase,Measure.prodAssoc_prod,
     angleSignLaw_eq_withDensity,prod_withDensity_right (angularDensity_measurable M positive)]
   have he : RoughRegime.LatticePriors.angleUniform=LatticeFourier.angleUniform := by
     unfold RoughRegime.LatticePriors.angleUniform LatticeFourier.angleUniform
     rw [ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ)<2*Real.pi)]
   rw [he]

 theorem gatePrior_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
     (e : ι ≃ κ) (Q M : ℕ) (η : κ → ℝ) (hQ : 1≤Q) (hM : 0<M)
     (hη : ∀ k,0<η k) (hband : ∀ k,4*(6*Q/η k)≤(M:ℝ)) :
     MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : κ=>ℤ) e)
       (gatePrior Q M (η ∘ e) hQ hM (fun i=>hη (e i)) (fun i=>hband (e i)))
       (gatePrior Q M η hQ hM hη hband) := by
   unfold gatePrior
   exact measurePreserving_piCongrLeft
     (fun k => (latticeLaw Q M (η k) hQ hM (hη k) (hband k)).toMeasure) e

def phaseStateEquiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    PhaseParameter (ι → ℤ) ≃ᵐ ((κ → ℤ) × (ℝ × (Bool × Bool))) :=
  MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.piCongrLeft (fun _ : κ=>ℤ) e).prodCongr
    (MeasurableEquiv.refl (ℝ × (Bool × Bool))))

@[simp] theorem phaseStateEquiv_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (q : PhaseParameter (ι → ℤ)) :
    phaseStateEquiv e q=((fun k=>q.1.1 (e.symm k)),(q.1.2,q.2)) := by
  change ((MeasurableEquiv.piCongrLeft (fun _ : κ=>ℤ) e) q.1.1,(q.1.2,q.2))=_
  congr 1
  funext k
  simpa only [e.apply_symm_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ => ℤ) e q.1.1 (e.symm k))

 theorem gate_phasePrior_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
     (e : ι ≃ κ) (Q M : ℕ) (η : κ → ℝ) (hQ : 1≤Q) (hM : 0<M)
     (hη : ∀ k,0<η k) (hband : ∀ k,4*(6*Q/η k)≤(M:ℝ)) (positive : Bool) :
     MeasurePreserving (phaseStateEquiv e)
       ((phasePrior (gatePrior Q M (η ∘ e) hQ hM (fun i=>hη (e i)) (fun i=>hband (e i)))
         M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure)
       ((gatePrior Q M η hQ hM hη hband).prod (angleSignLaw M positive)) := by
   let ν := gatePrior Q M (η ∘ e) hQ hM (fun i=>hη (e i)) (fun i=>hband (e i))
   have ha : MeasurePreserving (MeasurableEquiv.prodAssoc : PhaseParameter (ι → ℤ) ≃ᵐ
       ((ι → ℤ) × (ℝ × (Bool × Bool))))
       ((phasePrior ν M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure)
       (ν.prod (angleSignLaw M positive)) :=
     ⟨MeasurableEquiv.prodAssoc.measurable,phasePrior_assoc ν M positive⟩
   have hp := (gatePrior_reindex e Q M η hQ hM hη hband).prod
     (MeasurePreserving.id (angleSignLaw M positive))
   exact hp.comp ha

end RoughRegime.LatticePriors
