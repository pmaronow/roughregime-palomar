module

public import Mathlib

@[expose] public section

/-!
# Standalone mathematical challenge

Selected targets: parts (a) and (b) of the paper's generic minimax theorem.
All statistical objects below are concrete definitions. The only proof holes
are the two intentional challenge theorem placeholders at the end.

The cube uses Euclidean Lebesgue measure. Hölder order is ceil(t)-1, including
the Lipschitz highest-derivative convention at integer t. The experiment is
n iid observations plus an independent uniform seed for real-valued estimators.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RoughRegime.Rates

/-- Geometric reciprocal-series ratio on the density interval [lo, hi]. -/
def rho (lo hi : ℝ) : ℝ :=
  (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo)

/-- Positive decay parameter -log(rho) when 0 < lo < hi. -/
def tau (lo hi : ℝ) : ℝ := -Real.log (rho lo hi)

/-- Subcritical coefficient 2 sqrt(theta (1 - 2 theta) tau). -/
def kappa (θ τ : ℝ) : ℝ := 2 * Real.sqrt (θ * (1 - 2 * θ) * τ)

/-- Common scale n^(-theta) (log n)^(theta/2) exp(-kappa sqrt(log n)); claims use n >= 3. -/
def subcriticalScale (n θ τ : ℝ) : ℝ :=
  n ^ (-θ) * (Real.log n) ^ (θ / 2) * Real.exp (-kappa θ τ * Real.sqrt (Real.log n))

end RoughRegime.Rates

-- Match the auxiliary-proof cache boundary of the original separate Rates module.
-- This affects generated proof names only; the mathematical definitions are unchanged.
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}


namespace RoughRegime.Model

/-- The d-dimensional real Euclidean covariate space. -/
abbrev Covariate (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Closed unit cube [0,1]^d in Euclidean coordinates. -/
def cube (d : ℕ) : Set (Covariate d) := {x | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}

/-- Euclidean Lebesgue measure restricted to the unit cube; it has mass one. -/
def cubeVolume (d : ℕ) : Measure (Covariate d) := volume.restrict (cube d)

/-- Highest differentiated order ceil(t)-1; integer t uses order t-1. -/
def holderOrder (t : ℝ) : ℕ := Nat.ceil t - 1

/-- Highest-derivative Holder exponent t - (ceil(t)-1), in (0,1] for t > 0. -/
def holderExponent (t : ℝ) : ℝ := t - holderOrder t

/-- Order-q derivative within the closed cube in an ordered list of coordinate directions. -/
def coordinateDerivative {d : ℕ} (f : Covariate d → ℝ) (q : ℕ)
    (σ : Fin q → Fin d) (x : Covariate d) : ℝ :=
  iteratedFDerivWithin ℝ q f (cube d) x (fun j ↦ EuclideanSpace.single (σ j) 1)

/-- Maximum absolute coordinate derivative over all orders at most k and all points in the cube. -/
def derivativeSup {d : ℕ} (f : Covariate d → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (q : ℕ) (_ : q ≤ k) (σ : Fin q → Fin d) (x : Covariate d) (_ : x ∈ cube d),
    ENNReal.ofReal |coordinateDerivative f q σ x|

/-- Maximum Holder quotient for order ceil(t)-1 coordinate derivatives on the cube. -/
def holderSeminorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (σ : Fin (holderOrder t) → Fin d) (x : Covariate d) (_ : x ∈ cube d)
    (y : Covariate d) (_ : y ∈ cube d) (_ : x ≠ y),
    ENNReal.ofReal (|coordinateDerivative f (holderOrder t) σ x -
      coordinateDerivative f (holderOrder t) σ y| / ‖x - y‖ ^ holderExponent t)

/-- Derivative supremum plus highest-order seminorm; infinity without positive smoothness and continuous derivatives. -/
def holderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) then
    derivativeSup f (holderOrder t) + holderSeminorm f t else ∞

/-- Functions whose extended-real Holder norm is at most the radius H. -/
def holderBall {d : ℕ} (t H : ℝ) : Set (Covariate d → ℝ) :=
  {f | holderNorm f t ≤ ENNReal.ofReal H}

/-- Fixed dimension, smoothness, Holder radius, overlap, weighted-density interval, and observable bounds with positivity hypotheses. -/
structure Parameters where
  d : ℕ
  α : ℝ
  β : ℝ
  H : ℝ
  δ : ℝ
  gminus : ℝ
  gplus : ℝ
  M0 : ℝ
  hd : 1 ≤ d
  hα : 0 < α
  hβ : 0 < β
  hH : 0 < H
  hδ : 0 < δ
  hgminus : 0 < gminus
  hgplus : gminus < gplus
  hM0 : 0 < M0

/-- Polynomial rate exponent (alpha + beta) / d. -/
def Parameters.theta (A : Parameters) : ℝ := (A.α + A.β) / A.d

/-- Sum of dimensions of the two local polynomial spaces. -/
def Parameters.nu (A : Parameters) : ℕ :=
  (A.d + holderOrder A.α).choose A.d + (A.d + holderOrder A.β).choose A.d

/-- Fixed measurable response functions: D in [0,M0], U and V bounded by M0, bounded W, and nonzero lambda. -/
structure Observables (Z : Type*) [MeasurableSpace Z] (A : Parameters) where
  D : Z → ℝ
  U : Z → ℝ
  V : Z → ℝ
  W : Z → ℝ
  lam : ℝ
  hlam : lam ≠ 0
  measurableD : Measurable D
  measurableU : Measurable U
  measurableV : Measurable V
  measurableW : Measurable W
  boundD : ∀ z, 0 ≤ D z ∧ D z ≤ A.M0
  boundU : ∀ z, |U z| ≤ A.M0
  boundV : ∀ z, |V z| ≤ A.M0
  boundW : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |W z| ≤ C

/-- One observation consists of a covariate and response. -/
abbrev Observation (A : Parameters) (Z : Type*) := Covariate A.d × Z

/-- Sigma-algebra generated by the covariate projection. -/
abbrev covariateInformation (A : Parameters) (Z : Type*) [MeasurableSpace Z] :
    MeasurableSpace (Observation A Z) := MeasurableSpace.comap Prod.fst inferInstance

/-- A witness consists of the density and versions of the conditional ratios. -/
structure ModelWitness (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) where
  p : Covariate A.d → ℝ
  w : Covariate A.d → ℝ
  a : Covariate A.d → ℝ
  b : Covariate A.d → ℝ
  measurableP : Measurable p
  measurableW : Measurable w
  measurableA : Measurable a
  measurableB : Measurable b
  nonnegativeP : 0 ≤ᵐ[cubeVolume A.d] p
  marginal : (P : Measure (Observation A Z)).map Prod.fst =
    (cubeVolume A.d).withDensity (fun x ↦ ENNReal.ofReal (p x))
  momentD : (P : Measure (Observation A Z))[F.D ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))]
    w ∘ Prod.fst
  momentU : (P : Measure (Observation A Z))[F.U ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))]
    fun o ↦ w o.1 * a o.1
  momentV : (P : Measure (Observation A Z))[F.V ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))]
    fun o ↦ w o.1 * b o.1
  overlap : ∀ᵐ x ∂cubeVolume A.d, A.δ ≤ w x
  smoothA : a ∈ holderBall A.α A.H
  smoothB : b ∈ holderBall A.β A.H
  densityBounds : ∀ᵐ x ∂cubeVolume A.d,
    A.gminus ≤ w x * p x ∧ w x * p x ≤ A.gplus

/-- All probability laws admitting the conditional-moment, density, overlap, and Holder witnesses above. -/
def modelClass (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) :
    Set (ProbabilityMeasure (Observation A Z)) := {P | Nonempty (ModelWitness A F P)}

/-- The generic target is defined directly using conditional moments. -/
def target (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (P : ProbabilityMeasure (Observation A Z)) : ℝ :=
  (∫ o, F.W o.2 ∂(P : Measure (Observation A Z))) + F.lam * ∫ o,
    ((P : Measure (Observation A Z))[F.U ∘ Prod.snd | covariateInformation A Z]) o *
    ((P : Measure (Observation A Z))[F.V ∘ Prod.snd | covariateInformation A Z]) o /
    ((P : Measure (Observation A Z))[F.D ∘ Prod.snd | covariateInformation A Z]) o ∂(P : Measure (Observation A Z))

/-- n independent observations from P, multiplied by an independent uniform seed on [0,1]. -/
def randomizedExperiment {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (P : ProbabilityMeasure Ω) : Measure ((Fin n → Ω) × ℝ) :=
  (Measure.pi (fun _ : Fin n ↦ (P : Measure Ω))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- All measurable real-valued estimators of the data and independent uniform seed. -/
abbrev Estimator (Ω : Type*) [MeasurableSpace Ω] (n : ℕ) :=
  {f : (Fin n → Ω) × ℝ → ℝ // Measurable f}

/-- Infimum over measurable randomized estimators of the supremum L2 error over the class; infinity is allowed. -/
def minimaxRMSE {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω)) : ℝ≥0∞ :=
  ⨅ f : Estimator Ω n, ⨆ (P : ProbabilityMeasure Ω) (_ : P ∈ C),
    eLpNorm (fun o ↦ f.1 o - T P) 2 (randomizedExperiment n P)

/-- Infimum over measurable randomized estimators of the largest probability of absolute error at least t. -/
def minimaxTail {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω)) (t : ℝ) : ℝ≥0∞ :=
  ⨅ f : Estimator Ω n, ⨆ (P : ProbabilityMeasure Ω) (_ : P ∈ C),
    randomizedExperiment n P {o | t ≤ |f.1 o - T P|}

/-- The upper inequalities at specified constants. -/
def UpperBoundAt (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n →
    (modelClass A F).Nonempty →
      (1 / 2 ≤ A.theta → minimaxRMSE n (target A F) (modelClass A F) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
      (0 < A.theta ∧ A.theta < 1 / 2 → minimaxRMSE n (target A F) (modelClass A F) ≤
        ENNReal.ofReal (C * RoughRegime.Rates.subcriticalScale n A.theta
          (RoughRegime.Rates.tau A.gminus A.gplus) *
          (Real.log n) ^ ((A.nu : ℝ) / 2 + 1 / 4)))

/-- Uniform upper statement, over response spaces in a fixed universe
and all observables with the same magnitude of λ and the stated W bound. -/
def UniformUpperClaim (A : Parameters) (L MW : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
    ∀ (Z : Type*) (mZ : MeasurableSpace Z) (F : @Observables Z mZ A),
      |F.lam| = L → (∀ z, |F.W z| ≤ MW) → UpperBoundAt A F C n0

/-- Baseline mean of D under the response law pi. -/
def baselineW (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) : ℝ := ∫ z, F.D z ∂(π : Measure Z)

/-- Baseline ratio E_pi U / E_pi D. -/
def baselineA (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) : ℝ := (∫ z, F.U z ∂(π : Measure Z)) / baselineW A F π

/-- Baseline ratio E_pi V / E_pi D. -/
def baselineB (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) : ℝ := (∫ z, F.V z ∂(π : Measure Z)) / baselineW A F π

/-- Finite-support interior baseline with positive-definite residual covariance, or the equal-observable equal-smoothness square case. -/
def Nondegenerate (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) : Prop :=
  (∃ s : Finset Z, (π : Measure Z) (s : Set Z) = 1) ∧
  max A.δ A.gminus < baselineW A F π ∧ baselineW A F π < A.gplus ∧
  |baselineA A F π| < A.H ∧ |baselineB A F π| < A.H ∧
  (let rU := fun z ↦ F.U z - baselineA A F π * F.D z
   let rV := fun z ↦ F.V z - baselineB A F π * F.D z
   let uu := ∫ z, rU z ^ 2 ∂(π : Measure Z)
   let uv := ∫ z, rU z * rV z ∂(π : Measure Z)
   let vv := ∫ z, rV z ^ 2 ∂(π : Measure Z)
   (0 < uu ∧ 0 < uu * vv - uv ^ 2) ∨ (F.U = F.V ∧ A.α = A.β ∧ 0 < uu))

/-- Model laws with w, a, and b within r of their baseline values, Lebesgue almost everywhere on the cube. -/
def localClass (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) (r : ℝ) : Set (ProbabilityMeasure (Observation A Z)) :=
  {P | ∃ h : ModelWitness A F P, ∀ᵐ x ∂cubeVolume A.d,
    |h.w x - baselineW A F π| ≤ r ∧ |h.a x - baselineA A F π| ≤ r ∧
      |h.b x - baselineB A F π| ≤ r}

/-- Lower constants precede every intermediate class and sample size; includes both RMSE regimes and the quarter-tail bound. -/
def MainLowerClaim (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) (r : ℝ) : Prop :=
  Nondegenerate A F π → 0 < r →
  ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
    ∀ C' : Set (ProbabilityMeasure (Observation A Z)),
      localClass A F π r ⊆ C' → C' ⊆ modelClass A F → ∀ n : ℕ, n0 ≤ n →
        (1 / 2 ≤ A.theta → ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
          minimaxRMSE n (target A F) C') ∧
        (0 < A.theta ∧ A.theta < 1 / 2 →
          let a := RoughRegime.Rates.subcriticalScale n A.theta
            (RoughRegime.Rates.tau A.gminus A.gplus)
          ENNReal.ofReal (c * a * Real.log n) ≤ minimaxRMSE n (target A F) C' ∧
          (1 / 4 : ℝ≥0∞) ≤ minimaxTail n (target A F) C' (2 * c * a * Real.log n))

end RoughRegime.Model

namespace RoughRegimeSubmission
universe u

/-- Uniform upper bound, with constants chosen before the response space
and every observable family having the prescribed magnitude bounds. -/
theorem mainUpper (A : RoughRegime.Model.Parameters) (L MW : ℝ) :
    RoughRegime.Model.UniformUpperClaim.{u} A L MW := by
  sorry

/-- Local lower bound under the finite-support baseline nondegeneracy
condition; includes the rough-regime one-quarter probability lower bound. -/
theorem mainLower (A : RoughRegime.Model.Parameters) {Z : Type u} [MeasurableSpace Z]
    (F : RoughRegime.Model.Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ) :
    RoughRegime.Model.MainLowerClaim A F π r := by
  sorry

end RoughRegimeSubmission
