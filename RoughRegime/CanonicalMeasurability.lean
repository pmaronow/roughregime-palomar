module

public import RoughRegime.CanonicalLattice


@[expose] public section
/-! Joint measurability of every actual random density/profile evaluation. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory
open scoped ContDiff

 variable {D N : ℕ} {ι : Type*} [Fintype ι]

 theorem statePhases_joint_measurable (U : SmoothStep) (M : ℕ) (a : ι → ℕ) (q : ι → Fin (D + 1))
    (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4) (k : GridPair D N) :
    Measurable (fun zx : (GridPair D N → PairState ι) × Model.Covariate (D + 1) =>
      statePhases U M a q γ zx.1 k zx.2) := by
  have hs (i : ι) : Measurable (softDigit U (γ i)) := (softDigit_smooth U (γ i) (hγ i) (hγ1 i)).continuous.measurable
  have hz : Measurable (fun n : ℤ => (n : ℝ)) := measurable_of_countable _
  unfold statePhases blockPhase coordinateSoftDigit
  fun_prop

 theorem canonicalDensity_joint_measurable (U : SmoothStep) (M : ℕ) (a : ι → ℕ) (q : ι → Fin (D + 1))
    (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4)
    (offset ell p0 r0 h : ℝ) (outer : Model.Covariate (D + 1) → ℝ) (ho : Measurable outer) :
    Measurable (fun zx : (GridPair D N → PairState ι) × Model.Covariate (D + 1) =>
      globalDensity offset ell p0 r0 h outer (stateAngles zx.1) (statePhases U M a q γ zx.1) zx.2) := by
  have hphase (k : GridPair D N) := statePhases_joint_measurable U M a q γ hγ hγ1 k
  have hcoords (b : GridBlock D N) : Measurable (gridCoords offset ell b) := (gridCoords_smooth offset ell b).continuous.measurable
  have hsign : Measurable RoughRegime.Lower.sign := measurable_of_countable _
  unfold globalDensity pulledCutoff blockOscillatingDensity stateAngles
  fun_prop

 theorem canonicalNumerator_joint_measurable (Q M : ℕ) (η lam : ι → ℝ)
    (offset ell A : ℝ) (inner : Model.Covariate (D + 1) → ℝ) (hi : Measurable inner)
    (which : Bool) :
    Measurable (fun zx : (GridPair D N → PairState ι) × Model.Covariate (D + 1) =>
      globalNumerator offset ell A inner (if which then stateSignU zx.1 else stateSignV zx.1)
        (stateGates Q M η lam zx.1) zx.2) := by
  have hg : Measurable (LatticeFourier.jointGate Q M η lam) := LatticeFourier.jointGate_measurable Q M η lam
  have hcoords (b : GridBlock D N) : Measurable (gridCoords offset ell b) := (gridCoords_smooth offset ell b).continuous.measurable
  have hsign : Measurable RoughRegime.Lower.sign := measurable_of_countable _
  unfold globalNumerator pulledCutoff stateGates stateSignU stateSignV
  cases which <;> simp <;> fun_prop

 theorem canonicalProfile_joint_measurable (U : SmoothStep) (Q M : ℕ) (a : ι → ℕ) (q : ι → Fin (D + 1))
    (γ η lam : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4)
    (offset ell p0 r0 h A : ℝ) (inner outer : Model.Covariate (D + 1) → ℝ)
    (hi : Measurable inner) (ho : Measurable outer) (which : Bool) :
    Measurable (fun zx : (GridPair D N → PairState ι) × Model.Covariate (D + 1) =>
      globalProfile offset ell p0 r0 h A inner outer (stateAngles zx.1) (statePhases U M a q γ zx.1)
        (if which then stateSignU zx.1 else stateSignV zx.1) (stateGates Q M η lam zx.1) zx.2) :=
  (canonicalNumerator_joint_measurable Q M η lam offset ell A inner hi which).div
    (canonicalDensity_joint_measurable U M a q γ hγ hγ1 offset ell p0 r0 h outer ho)

end RoughRegime.LatticePriors
