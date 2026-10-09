module

public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import RoughRegime.HolderGeometry

@[expose] public section
/-! Exact reconstruction and continuity of finite coordinate derivative tensors. -/
open Set
open scoped ContDiff
noncomputable section
namespace RoughRegime.Model

def coordinateEvaluation (d q : ℕ) :
    (Covariate d [×q]→L[ℝ] ℝ) →ₗ[ℝ] ((Fin q → Fin d) → ℝ) where
  toFun A σ := A (fun i => EuclideanSpace.single (σ i) 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma coordinateEvaluation_injective (d q : ℕ) :
    Function.Injective (coordinateEvaluation d q) := by
  intro A B hab
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear
    (fun _ : Fin q => (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
  intro σ
  simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, coordinateEvaluation, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMultilinearMap.coe_coe]
    using congrFun hab σ

lemma continuousOn_coordinate_iff {X : Type*} [TopologicalSpace X] (d q : ℕ)
    (A : X → Covariate d [×q]→L[ℝ] ℝ) (s : Set X) :
    ContinuousOn A s ↔ ∀ σ : Fin q → Fin d,
      ContinuousOn (fun x => A x (fun i => EuclideanSpace.single (σ i) 1)) s := by
  let ev := coordinateEvaluation d q
  have hinj := coordinateEvaluation_injective d q
  let : FiniteDimensional ℝ (Covariate d [×q]→L[ℝ] ℝ) :=
    FiniteDimensional.of_injective ev hinj
  have he := ev.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  rw [he.isEmbedding.isInducing.continuousOn_iff (f := A)]
  simpa only [ev, Function.comp_def, coordinateEvaluation, LinearMap.coe_mk, AddHom.coe_mk] using
    (continuousOn_pi (f := fun x => ev (A x)) (s := s))


def coordinateTensor (d q : ℕ) (σ : Fin q → Fin d) : Covariate d [×q]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin q) ℝ).compContinuousLinearMap
    (fun i => PiLp.proj 2 (fun _ : Fin d => ℝ) (σ i))

lemma coordinateTensor_apply (d q : ℕ) (σ τ : Fin q → Fin d) :
    coordinateTensor d q σ (fun i => EuclideanSpace.single (τ i) 1) =
      if σ = τ then 1 else 0 := by
  classical
  simp only [coordinateTensor, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, PiLp.proj_apply, PiLp.single_apply]
  by_cases h : σ = τ
  · subst τ
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

def coordinateReconstruction (d q : ℕ) (c : (Fin q → Fin d) → ℝ) :
    Covariate d [×q]→L[ℝ] ℝ := by
  classical
  exact ∑ σ, c σ • coordinateTensor d q σ

lemma coordinateEvaluation_reconstruction (d q : ℕ) (c : (Fin q → Fin d) → ℝ) :
    coordinateEvaluation d q (coordinateReconstruction d q c) = c := by
  classical
  funext τ
  simp only [coordinateEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    coordinateReconstruction, sum_apply,
    smul_apply, coordinateTensor_apply, smul_eq_mul]
  simp

lemma coordinateReconstruction_evaluation (d q : ℕ) (A : Covariate d [×q]→L[ℝ] ℝ) :
    coordinateReconstruction d q (coordinateEvaluation d q A) = A := by
  apply coordinateEvaluation_injective d q
  exact coordinateEvaluation_reconstruction d q (coordinateEvaluation d q A)

lemma continuousOn_coordinateReconstruction {X : Type*} [TopologicalSpace X] (d q : ℕ)
    (c : X → (Fin q → Fin d) → ℝ) (s : Set X)
    (hc : ∀ σ, ContinuousOn (fun x => c x σ) s) :
    ContinuousOn (fun x => coordinateReconstruction d q (c x)) s := by
  apply (continuousOn_coordinate_iff d q _ s).mpr
  intro σ
  have heq : (fun x => coordinateReconstruction d q (c x)
      (fun i => EuclideanSpace.single (σ i) 1)) = (fun x => c x σ) := by
    funext x
    exact congrFun (coordinateEvaluation_reconstruction d q (c x)) σ
  rw [heq]
  exact hc σ

end RoughRegime.Model
