module

public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
/-! Continuous ordinary coordinate partials imply exact Frechet derivatives. -/
open Set Filter
open scoped Topology
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace RoughRegime.Calculus
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
def gradient (d : ℕ) (c : Fin d → F) : (Fin d → ℝ) →L[ℝ] F :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (c i)
lemma gradient_apply (d : ℕ) (c : Fin d → F) (v : Fin d → ℝ) :
    gradient d c v = ∑ i, v i • c i := by simp [gradient]
lemma gradient_continuousOn {X : Type*} [TopologicalSpace X] (d : ℕ)
    (c : X → Fin d → F) (s : Set X)
    (h : ∀ i, ContinuousOn (fun x => c x i) s) :
    ContinuousOn (fun x => gradient d (c x)) s := by
  unfold gradient
  apply continuousOn_finsetSum
  intro i hi
  exact (ContinuousLinearMap.smulRightL ℝ (Fin d → ℝ) F
    (ContinuousLinearMap.proj i)).continuous.comp_continuousOn (h i)
lemma gradient_cons (d : ℕ) (c : Fin (d+1) → F) :
    (gradient (d+1) c).comp (Fin.consEquivL ℝ (fun _ : Fin (d+1) => ℝ)).toContinuousLinearMap =
      (ContinuousLinearMap.toSpanSingleton ℝ (c 0)).coprod
        (gradient d (fun i => c i.succ)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [gradient_apply, Fin.sum_univ_succ, Fin.consEquivL_apply]
theorem continuous_partials_hasStrictFDerivAt (d : ℕ)
    (f : (Fin d → ℝ) → F) (D : (Fin d → ℝ) → Fin d → F)
    (s : Set (Fin d → ℝ)) (hs : IsOpen s)
    (hD : ∀ i, ContinuousOn (fun x => D x i) s)
    (hpartial : ∀ x ∈ s, ∀ i, HasDerivAt (fun z => f (Function.update x i z)) (D x i) (x i))
    (x : Fin d → ℝ) (hx : x ∈ s) :
    HasStrictFDerivAt f (gradient d (D x)) x := by
  induction d with
  | zero =>
    have heq : f = fun _ => f x := by funext y; congr 1; exact Subsingleton.elim _ _
    rw [heq]
    simpa [gradient] using hasStrictFDerivAt_const (f x) x
  | succ d ih =>
    let e := Fin.consEquivL ℝ (fun _ : Fin (d+1) => ℝ)
    have heapply (v : ℝ × (Fin d → ℝ)) : e v = Fin.cons v.1 v.2 := by
      funext i
      exact Fin.consEquivL_apply ℝ (fun _ : Fin (d+1) => ℝ) v i
    let u := e.symm x
    let f1 : ℝ → (Fin d → ℝ) → F := fun a b => f (e (a,b))
    let D1 : ℝ → (Fin d → ℝ) → ℝ →L[ℝ] F :=
      fun a b => ContinuousLinearMap.toSpanSingleton ℝ (D (e (a,b)) 0)
    let D2 : ℝ → (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] F :=
      fun a b => gradient d (fun i => D (e (a,b)) i.succ)
    have heux : e u = x := e.apply_symm_apply x
    have hu : u ∈ e ⁻¹' s := by simpa only [mem_preimage, heux] using hx
    have hneigh : ∀ᶠ v in 𝓝 u, e v ∈ s :=
      (hs.preimage e.continuous).mem_nhds hu
    have hd1 : ∀ᶠ v in 𝓝 u, HasFDerivAt (f1 · v.2) (D1 v.1 v.2) v.1 := by
      filter_upwards [hneigh] with v hv
      have hp := (hpartial (e v) hv 0).hasFDerivAt
      change HasFDerivAt (fun z => f (Function.update (Fin.cons v.1 v.2) 0 z))
        (ContinuousLinearMap.toSpanSingleton ℝ (D (e v) 0)) v.1 at hp
      simpa only [Fin.update_cons_zero, f1, D1, heapply] using hp
    have hd2 : ∀ᶠ v in 𝓝 u, HasFDerivAt (f1 v.1 ·) (D2 v.1 v.2) v.2 := by
      filter_upwards [hneigh] with v hv
      let sv : Set (Fin d → ℝ) := {b | e (v.1,b) ∈ s}
      have hc : Continuous (fun b : Fin d → ℝ => e (v.1,b)) :=
        e.continuous.comp (continuous_const.prodMk continuous_id)
      have hsv : IsOpen sv := hs.preimage hc
      have hv2 : v.2 ∈ sv := hv
      have hDv : ∀ i : Fin d,
          ContinuousOn (fun b => D (e (v.1,b)) i.succ) sv := by
        intro i
        exact (hD i.succ).comp hc.continuousOn (fun b hb => hb)
      have hpv : ∀ b ∈ sv, ∀ i : Fin d,
          HasDerivAt (fun z => f1 v.1 (Function.update b i z))
            (D (e (v.1,b)) i.succ) (b i) := by
        intro b hb i
        have hp := hpartial (e (v.1,b)) hb i.succ
        change HasDerivAt (fun z => f (Function.update (Fin.cons v.1 b) i.succ z))
          (D (e (v.1,b)) i.succ) (b i) at hp
        simpa only [← Fin.cons_update, f1, heapply] using hp
      exact (ih (f1 v.1) (fun b i => D (e (v.1,b)) i.succ)
        sv hsv hDv hpv v.2 hv2).hasFDerivAt
    have hc1 : ContinuousAt (Function.uncurry D1) u := by
      have hh : ContinuousAt (fun x => D x 0) (e u) := by
        simpa only [heux] using (hD 0).continuousAt (hs.mem_nhds hx)
      change ContinuousAt (fun v => (ContinuousLinearMap.smulRightL ℝ ℝ F 1) (D (e v) 0)) u
      exact (ContinuousLinearMap.smulRightL ℝ ℝ F 1).continuous.continuousAt.comp
        (hh.comp e.continuous.continuousAt)
    have hc2 : ContinuousAt (Function.uncurry D2) u := by
      have hcc := gradient_continuousOn d (fun y i => D y i.succ) s
        (fun i => hD i.succ)
      have hh : ContinuousAt (fun y => gradient d (fun i => D y i.succ)) (e u) := by
        simpa only [heux] using hcc.continuousAt (hs.mem_nhds hx)
      change ContinuousAt ((fun y => gradient d (fun i => D y i.succ)) ∘ e) u
      exact hh.comp e.continuous.continuousAt
    have h := hasStrictFDerivAt_uncurry_coprod (f := f1) (f₁ := D1) (f₂ := D2) hd1 hd2 hc1 hc2
    have hc := h.comp x e.symm.hasStrictFDerivAt
    convert hc using 1
    · funext y; change f y = f (e (e.symm y)); rw [e.apply_symm_apply]
    · change gradient (d+1) (D x) =
        ((ContinuousLinearMap.toSpanSingleton ℝ (D (e u) 0)).coprod
          (gradient d (fun i => D (e u) i.succ))).comp e.symm.toContinuousLinearMap
      rw [heux, ← gradient_cons]
      apply ContinuousLinearMap.ext
      intro v
      change gradient (d+1) (D x) v = gradient (d+1) (D x) (e (e.symm v))
      rw [e.apply_symm_apply]

def euclideanGradient (d : ℕ) (c : Fin d → F) : EuclideanSpace ℝ (Fin d) →L[ℝ] F :=
  ∑ i, (PiLp.proj 2 (fun _ : Fin d => ℝ) i).smulRight (c i)

lemma gradient_comp_piLp (d : ℕ) (c : Fin d → F) :
    (gradient d c).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap =
      euclideanGradient d c := by
  apply ContinuousLinearMap.ext
  intro v
  simp [gradient_apply, euclideanGradient]

theorem continuous_partials_hasStrictFDerivAt_euclidean (d : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → F) (D : EuclideanSpace ℝ (Fin d) → Fin d → F)
    (s : Set (EuclideanSpace ℝ (Fin d))) (hs : IsOpen s)
    (hD : ∀ i, ContinuousOn (fun x => D x i) s)
    (hpartial : ∀ x ∈ s, ∀ i, HasDerivAt
      (fun z => f (WithLp.toLp 2 (Function.update (fun i => x i) i z))) (D x i) (x i))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ s) :
    HasStrictFDerivAt f (euclideanGradient d (D x)) x := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  let sp := e.symm ⁻¹' s
  have hsp : IsOpen sp := hs.preimage e.symm.continuous
  have hDp : ∀ i, ContinuousOn (fun y => D (e.symm y) i) sp := by
    intro i
    exact (hD i).comp e.symm.continuous.continuousOn (fun y hy => hy)
  have hp : ∀ y ∈ sp, ∀ i, HasDerivAt
      (fun z => (f ∘ e.symm) (Function.update y i z))
      (D (e.symm y) i) (y i) := by
    intro y hy i
    exact hpartial (e.symm y) hy i
  have hx' : e x ∈ sp := by
    change e.symm (e x) ∈ s
    simpa only [e.symm_apply_apply] using hx
  have h := continuous_partials_hasStrictFDerivAt d (f ∘ e.symm)
    (fun y i => D (e.symm y) i) sp hsp hDp hp (e x) hx'
  have hc := h.comp x e.hasStrictFDerivAt
  convert hc using 1
  · funext y
    change f y = f (e.symm (e y))
    rw [e.symm_apply_apply]
  · change euclideanGradient d (D x) =
      (gradient d (D (e.symm (e x)))).comp e.toContinuousLinearMap
    rw [e.symm_apply_apply]
    exact (gradient_comp_piLp d (D x)).symm

end RoughRegime.Calculus
