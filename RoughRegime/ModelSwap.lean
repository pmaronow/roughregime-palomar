module

public import RoughRegime.Model
public import RoughRegime.ProjectionTelescope


@[expose] public section
/-! Exact exchange of the two response ratios and smoothness exponents. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.Model
universe u

def Parameters.swap (A : Parameters) : Parameters :=
  { A with α := A.β, β := A.α, hα := A.hβ, hβ := A.hα }

@[simp] theorem Parameters.swap_swap (A : Parameters) : A.swap.swap = A := by
  cases A
  rfl

@[simp] theorem Parameters.swap_theta (A : Parameters) : A.swap.theta = A.theta := by
  unfold Parameters.theta Parameters.swap
  rw [add_comm]

@[simp] theorem Parameters.swap_nu (A : Parameters) : A.swap.nu = A.nu := by
  unfold Parameters.nu Parameters.swap
  rw [Nat.add_comm]

def Observables.swap {Z : Type*} [MeasurableSpace Z] {A : Parameters}
    (F : Observables Z A) : Observables Z A.swap where
  D := F.D
  U := F.V
  V := F.U
  W := F.W
  lam := F.lam
  hlam := F.hlam
  measurableD := F.measurableD
  measurableU := F.measurableV
  measurableV := F.measurableU
  measurableW := F.measurableW
  boundD := F.boundD
  boundU := F.boundV
  boundV := F.boundU
  boundW := F.boundW

def ModelWitness.swap {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) : ModelWitness A.swap F.swap P where
  p := W.p
  w := W.w
  a := W.b
  b := W.a
  measurableP := W.measurableP
  measurableW := W.measurableW
  measurableA := W.measurableB
  measurableB := W.measurableA
  nonnegativeP := W.nonnegativeP
  marginal := W.marginal
  momentD := W.momentD
  momentU := W.momentV
  momentV := W.momentU
  overlap := W.overlap
  smoothA := W.smoothB
  smoothB := W.smoothA
  densityBounds := W.densityBounds

theorem modelClass_swap {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) : modelClass A.swap F.swap = modelClass A F := by
  ext P
  constructor
  · rintro ⟨W⟩
    exact ⟨{
      p := W.p, w := W.w, a := W.b, b := W.a
      measurableP := W.measurableP, measurableW := W.measurableW
      measurableA := W.measurableB, measurableB := W.measurableA
      nonnegativeP := W.nonnegativeP, marginal := W.marginal
      momentD := W.momentD, momentU := W.momentV, momentV := W.momentU
      overlap := W.overlap, smoothA := W.smoothB, smoothB := W.smoothA
      densityBounds := W.densityBounds }⟩
  · rintro ⟨W⟩
    exact ⟨W.swap⟩

theorem target_swap {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) :
    target A.swap F.swap P = target A F P := by
  unfold target Observables.swap
  congr 2
  apply integral_congr_ae
  filter_upwards [] with o
  change ((P : Measure (Observation A Z))[F.V ∘ Prod.snd | covariateInformation A Z]) o *
    ((P : Measure (Observation A Z))[F.U ∘ Prod.snd | covariateInformation A Z]) o /
      ((P : Measure (Observation A Z))[F.D ∘ Prod.snd | covariateInformation A Z]) o = _
  rw [mul_comm]

theorem ModelWitness.target_eq_linear_product {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) :
    target A F P = (∫ o, F.W o.2 ∂(P : Measure (Observation A Z))) +
      F.lam * W.productTarget :=
  target_weighted_representation A F P W

theorem upperBoundAt_swap {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (C : ℝ) (n0 : ℕ) :
    UpperBoundAt A.swap F.swap C n0 ↔ UpperBoundAt A F C n0 := by
  have ht : target A.swap F.swap = target A F := funext (target_swap F)
  simp only [UpperBoundAt, modelClass_swap, Parameters.swap_theta, Parameters.swap_nu, ht]
  rfl

theorem uniformUpperClaim_of_swap (A : Parameters) (L MW : ℝ)
    (h : UniformUpperClaim.{u} A.swap L MW) : UniformUpperClaim.{u} A L MW := by
  obtain ⟨C, hC, n0, hn0, hu⟩ := h
  refine ⟨C, hC, n0, hn0, ?_⟩
  intro Z mZ F hL hMW
  exact (upperBoundAt_swap F C n0).mp (hu Z mZ F.swap hL hMW)

theorem perModelUpperClaim_swap {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) : PerModelUpperClaim A.swap F.swap ↔ PerModelUpperClaim A F := by
  unfold PerModelUpperClaim
  simp only [upperBoundAt_swap]

end RoughRegime.Model
