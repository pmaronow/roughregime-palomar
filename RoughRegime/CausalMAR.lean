module

public import RoughRegime.CausalConditional
public import RoughRegime.ApplicationEffects
public import RoughRegime.ApplicationMARUpper


@[expose] public section
/-! Literal full-data/coarsened-law MAR identification. Missingness
independence is converted into conditional moments rather than supplied as
those moments. The positivity is the standing assumption of Section2. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def binaryIndicator (j : Bool) (b : Bool) : ℝ := if b=j then 1 else 0

theorem binaryIndicator_measurable (j : Bool) : Measurable (binaryIndicator j) := measurable_of_countable _

theorem binaryIndicator_range (j b : Bool) : binaryIndicator j b∈Icc (0:ℝ) 1 := by
  cases j <;> cases b <;> norm_num [binaryIndicator]

def fullMARObservation {Ω : Type*} (d : ℕ) (X : Ω→Model.Covariate d)
    (R : Ω→Bool) (Y : Ω→Applications.MAR.Outcome) (ω : Ω) :
    Model.Covariate d×Applications.MAR.Response :=
  (X ω,Applications.MAR.keepArmResponse true (R ω,Y ω))

theorem fullMARObservation_measurable {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (X : Ω→Model.Covariate d) (R : Ω→Bool) (Y : Ω→Applications.MAR.Outcome)
    (hX : Measurable X) (hR : Measurable R) (hY : Measurable Y) :
    Measurable (fullMARObservation d X R Y) :=
  hX.prodMk ((Applications.MAR.keepArmResponse_measurable true).comp (hR.prodMk hY))

theorem observedMean_fullData_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (d : ℕ) (P : ProbabilityMeasure Ω)
    (X : Ω→Model.Covariate d) (R : Ω→Bool) (Y : Ω→Applications.MAR.Outcome)
    (hX : Measurable X) (hR : Measurable R) (hY : Measurable Y)
    (hMAR : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le R Y (P:Measure Ω))
    (hpositive : ∀ᵐ ω ∂(P:Measure Ω),
      (P:Measure Ω)[binaryIndicator true∘R|MeasurableSpace.comap X inferInstance] ω≠0) :
    Applications.MAR.observedMean d (P.map (fullMARObservation d X R Y))=
      ∫ ω,(Y ω:ℝ) ∂(P:Measure Ω) := by
  let μ := (P:Measure Ω)
  let T := fullMARObservation d X R Y
  let m : MeasurableSpace (Model.Covariate d×Applications.MAR.Response) :=
    MeasurableSpace.comap Prod.fst inferInstance
  let info := MeasurableSpace.comap X inferInstance
  let r := binaryIndicator true∘R
  let y : Ω→ℝ := fun ω=>(Y ω:ℝ)
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace (Model.Covariate d×Applications.MAR.Response) :=
    (inferInstance : MeasurableSpace (Model.Covariate d)).prod (inferInstance : MeasurableSpace Applications.MAR.Response)
  have hT : Measurable T := fullMARObservation_measurable d X R Y hX hR hY
  have hr : Measurable r := (binaryIndicator_measurable true).comp hR
  have hy : Measurable y := measurable_subtype_coe.comp hY
  have hir : Integrable r μ := Integrable.of_mem_Icc 0 1 hr.aemeasurable
    (Eventually.of_forall (fun ω=>binaryIndicator_range true (R ω)))
  have hiy : Integrable y μ := Integrable.of_mem_Icc 0 1 hy.aemeasurable
    (Eventually.of_forall (fun ω=>(Y ω).property))
  have hiry : Integrable (fun ω=>r ω*y ω) μ :=
    hir.mul_bdd (c:=1) hy.aestronglyMeasurable (Eventually.of_forall (fun ω=>by
      simpa only [y,Real.norm_eq_abs,abs_of_nonneg (Y ω).property.1] using (Y ω).property.2))
  have hv : (Applications.MAR.observedOutcome∘Prod.snd)∘T=(fun ω=>r ω*y ω) := by
    funext ω
    exact (Applications.MAR.keepArmResponse_moments true (R ω,Y ω)).2
  have hd : (Applications.MAR.observed∘Prod.snd)∘T=r := by
    funext ω
    exact (Applications.MAR.keepArmResponse_moments true (R ω,Y ω)).1
  have hinfo : MeasurableSpace.comap T m=info := by
    rw [MeasurableSpace.comap_comp]
    rfl
  have hV : Integrable ((Applications.MAR.observedOutcome∘Prod.snd)∘T) μ := by rw [hv];exact hiry
  have hD : Integrable ((Applications.MAR.observed∘Prod.snd)∘T) μ := by rw [hd];exact hir
  have he := conditional_ratio_map_integral μ T hT m measurable_fst.comap_le
    (Applications.MAR.observedOutcome∘Prod.snd) (Applications.MAR.observed∘Prod.snd)
    (Applications.MAR.observedOutcome_measurable.comp measurable_snd)
    (Applications.MAR.observed_measurable.comp measurable_snd) hV hD
  change Applications.MAR.observedMean d (P.map T)=_ at he
  rw [hv,hd,hinfo] at he
  have hi : CondIndepFun info hX.comap_le r y μ :=
    hMAR.comp (binaryIndicator_measurable true) measurable_subtype_coe
  exact he.trans (selection_mean_identification μ info hX.comap_le r y y hr hy hir hiy hiry
    (EventuallyEq.rfl) hi hpositive)

end RoughRegime.Causal
