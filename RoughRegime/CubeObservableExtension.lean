module

public import RoughRegime.Model


@[expose] public section
/-! A measurable bounded observable defined only on the source cube extends
to the ambient covariate encoding with the same bound and identical values
on the cube. Thus ambient bounded observables introduce no extra restriction
in the covariate-dependent upper theorem. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Model

def cubeClip (d:ℕ) (x:Covariate d) : Covariate d :=
  WithLp.toLp 2 (fun i=>(projIcc (0:ℝ) 1 (by norm_num) (x i):ℝ))

theorem cubeClip_mem (d:ℕ)(x:Covariate d) : cubeClip d x∈cube d := by
  intro i
  exact (projIcc (0:ℝ) 1 (by norm_num) (x i)).property

theorem cubeClip_eq (d:ℕ){x:Covariate d}(hx:x∈cube d) : cubeClip d x=x := by
  ext i
  exact congrArg Subtype.val (projIcc_of_mem (a := (0 : ℝ)) (b := 1) (by norm_num) (hx i))

theorem cubeClip_continuous (d:ℕ) : Continuous (cubeClip d) := by
  apply (PiLp.continuous_toLp (p := 2) (fun _ : Fin d => ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp
    (continuous_projIcc.comp (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i))

def cubeRetract (d:ℕ)(x:Covariate d) : cube d := ⟨cubeClip d x,cubeClip_mem d x⟩

theorem cubeRetract_measurable (d:ℕ) : Measurable (cubeRetract d) :=
  (cubeClip_continuous d).measurable.subtype_mk

def cubeObservableExtension {d:ℕ}{Z:Type*}(f:cube d×Z→ℝ)(o:Covariate d×Z) : ℝ :=
  f (cubeRetract d o.1,o.2)

theorem cubeObservableExtension_measurable {d:ℕ}{Z:Type*}[MeasurableSpace Z]
    {f:cube d×Z→ℝ}(hf:Measurable f) : Measurable (cubeObservableExtension f) :=
  hf.comp (((cubeRetract_measurable d).comp measurable_fst).prodMk measurable_snd)

theorem cubeObservableExtension_eq {d:ℕ}{Z:Type*}(f:cube d×Z→ℝ)
    (o:Covariate d×Z)(ho:o.1∈cube d) :
    cubeObservableExtension f o=f (⟨o.1,ho⟩,o.2) := by
  change f (cubeRetract d o.1,o.2)=f (⟨o.1,ho⟩,o.2)
  apply congrArg f
  apply Prod.ext
  · apply Subtype.ext
    exact cubeClip_eq d ho
  · rfl

theorem cubeObservableExtension_bound {d:ℕ}{Z:Type*}(f:cube d×Z→ℝ)(B:ℝ)
    (hb:∀o,|f o|≤B) : ∀o,|cubeObservableExtension f o|≤B :=
  fun o=>hb (cubeRetract d o.1,o.2)

def extendCubeObservables (A:Parameters){Z:Type*}[MeasurableSpace Z]
    (F:Observables (cube A.d×Z) A) : Observables (Observation A Z) A where
  D:=cubeObservableExtension F.D
  U:=cubeObservableExtension F.U
  V:=cubeObservableExtension F.V
  W:=cubeObservableExtension F.W
  lam:=F.lam
  hlam:=F.hlam
  measurableD:=cubeObservableExtension_measurable F.measurableD
  measurableU:=cubeObservableExtension_measurable F.measurableU
  measurableV:=cubeObservableExtension_measurable F.measurableV
  measurableW:=cubeObservableExtension_measurable F.measurableW
  boundD:=fun o=>F.boundD (cubeRetract A.d o.1,o.2)
  boundU:=cubeObservableExtension_bound F.U A.M0 F.boundU
  boundV:=cubeObservableExtension_bound F.V A.M0 F.boundV
  boundW:=by
    obtain ⟨B,hB,hbound⟩:=F.boundW
    exact ⟨B,hB,cubeObservableExtension_bound F.W B hbound⟩

theorem extendCubeObservables_eq (A:Parameters){Z:Type*}[MeasurableSpace Z]
    (F:Observables (cube A.d×Z) A)(o:Observation A Z)(ho:o.1∈cube A.d) :
    (extendCubeObservables A F).D o=F.D (⟨o.1,ho⟩,o.2) ∧
    (extendCubeObservables A F).U o=F.U (⟨o.1,ho⟩,o.2) ∧
    (extendCubeObservables A F).V o=F.V (⟨o.1,ho⟩,o.2) ∧
    (extendCubeObservables A F).W o=F.W (⟨o.1,ho⟩,o.2) :=
  ⟨cubeObservableExtension_eq F.D o ho,cubeObservableExtension_eq F.U o ho,
    cubeObservableExtension_eq F.V o ho,cubeObservableExtension_eq F.W o ho⟩

end RoughRegime.Model
