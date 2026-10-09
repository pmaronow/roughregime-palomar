module

public import RoughRegime.SmoothDensityLower
public import RoughRegime.ApplicationWaldEmbedding
public import RoughRegime.ApplicationConditionalWaldEmbedding
public import RoughRegime.ApplicationTrialClass


@[expose] public section
/-! Actual preservation of C-infinity design densities by kernels that leave
the observed covariate unchanged, including the paper's application kernels. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Model
set_option maxHeartbeats 1000000

theorem smoothDensityClass_of_marginal_eq (d : ℕ) {Z Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace Y]
    (P : ProbabilityMeasure (Covariate d×Z)) (Q : ProbabilityMeasure (Covariate d×Y))
    (hmap : (Q : Measure (Covariate d×Y)).map Prod.fst=(P : Measure (Covariate d×Z)).map Prod.fst)
    (hP : P∈smoothDensityClass d Z) : Q∈smoothDensityClass d Y := by
  obtain ⟨p,hp,hm⟩ := hP
  exact ⟨p,hp,hmap.trans hm⟩

theorem kernelLaw_fst (d : ℕ) {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (K : Kernel (Covariate d×Z) (Covariate d×Y)) [IsMarkovKernel K]
    (hK : ∀o,(K o).map Prod.fst=Measure.dirac o.1)
    (P : ProbabilityMeasure (Covariate d×Z)) :
    (kernelLaw K P : Measure (Covariate d×Y)).map Prod.fst=(P : Measure (Covariate d×Z)).map Prod.fst := by
  change (K ∘ₘ (P : Measure (Covariate d×Z))).map Prod.fst=_
  rw [Measure.map_comp _ K measurable_fst]
  have hk : K.map Prod.fst=Kernel.deterministic Prod.fst measurable_fst := by
    ext o s hs
    simpa only [Kernel.map_apply _ measurable_fst,Kernel.deterministic_apply] using
      congrArg (fun μ : Measure (Covariate d)=>μ s) (hK o)
  rw [hk,Measure.deterministic_comp_eq_map measurable_fst]

theorem kernelLaw_mem_smoothDensityClass (d : ℕ) {Z Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace Y]
    (K : Kernel (Covariate d×Z) (Covariate d×Y)) [IsMarkovKernel K]
    (hK : ∀o,(K o).map Prod.fst=Measure.dirac o.1)
    (P : ProbabilityMeasure (Covariate d×Z)) (hP : P∈smoothDensityClass d Z) :
    kernelLaw K P∈smoothDensityClass d Y :=
  smoothDensityClass_of_marginal_eq d P _ (kernelLaw_fst d K hK P) hP

theorem map_mem_smoothDensityClass (d : ℕ) {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (f : Covariate d×Z → Covariate d×Y) (hf : Measurable f) (hfst : ∀o,(f o).1=o.1)
    (P : ProbabilityMeasure (Covariate d×Z)) (hP : P∈smoothDensityClass d Z) :
    P.map f∈smoothDensityClass d Y := by
  apply smoothDensityClass_of_marginal_eq d P _ _ hP
  change ((P : Measure (Covariate d×Z)).map f).map Prod.fst=_
  rw [Measure.map_map measurable_fst hf]
  have he : Prod.fst ∘ f=Prod.fst := funext hfst
  rw [he]

end RoughRegime.Model
namespace RoughRegime.Applications.MAR

theorem augmentationLaw_mem_smoothDensityClass (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response))
    (hP : P∈Model.smoothDensityClass A.d Response) :
    augmentationLaw A j P∈Model.smoothDensityClass A.d TreatmentResponse := by
  apply Model.smoothDensityClass_of_marginal_eq A.d P _ _ hP
  rw [augmentationLaw_measure,augmentation_marginal]

theorem keepArmLaw_mem_smoothDensityClass (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d×TreatmentResponse))
    (hP : P∈Model.smoothDensityClass A.d TreatmentResponse) :
    keepArmLaw A j P∈Model.smoothDensityClass A.d Response :=
  Model.map_mem_smoothDensityClass A.d (keepArm A.d j) (keepArm_measurable A.d j) (fun _=>rfl) P hP

end RoughRegime.Applications.MAR
namespace RoughRegime.Applications.Wald

theorem embedLaw_mem_smoothDensityClass (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse))
    (hP : P∈Model.smoothDensityClass A.d MAR.TreatmentResponse) :
    embedLaw A P∈Model.smoothDensityClass A.d Response :=
  Model.map_mem_smoothDensityClass A.d (embed A.d) (embed_measurable A.d) (fun _=>rfl) P hP

end RoughRegime.Applications.Wald
namespace RoughRegime.Applications.ConditionalWald

theorem augmentationLaw_mem_smoothDensityClass (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d×MAR.Response))
    (hP : P∈Model.smoothDensityClass A.d MAR.Response) :
    augmentationLaw A P∈Model.smoothDensityClass A.d Response := by
  apply Model.smoothDensityClass_of_marginal_eq A.d P _ _ hP
  rw [augmentationLaw_measure,augmentation_marginal]

end RoughRegime.Applications.ConditionalWald
namespace RoughRegime.Applications.Trial

theorem reverseLaw_mem_smoothDensityClass (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d×Products.BoundedResponse))
    (hP : P∈Model.smoothDensityClass A.d Products.BoundedResponse) :
    reverseLaw A P∈Model.smoothDensityClass A.d Response := by
  apply Model.smoothDensityClass_of_marginal_eq A.d P _ _ hP
  change (reverseKernel A.d ∘ₘ (P : Measure (Model.Covariate A.d×Products.BoundedResponse))).map Prod.fst=_
  exact reverseKernel_marginal A.d _

end RoughRegime.Applications.Trial
