module

public import RoughRegime.CanonicalMeasurability
public import RoughRegime.GridRegion
public import RoughRegime.LatticePreparation


@[expose] public section
/-! Lemma14(a): every actual lattice realization is a smooth normalized
density with the stated margins and two supported smooth profiles. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open RoughRegime.LatticeFourier
open scoped ContDiff BigOperators

 variable {D N : ℕ} {ι : Type*} [Fintype ι]

 structure RealizationProperties (p u v : Model.Covariate (D + 1) → ℝ)
    (rminus rplus δ Au Av : ℝ) (region : Set (Model.Covariate (D + 1))) : Prop where
  density_smooth : ContDiff ℝ ∞ p
  normalized : (∫ x, p x ∂Model.cubeVolume (D + 1)) = 1
  margins : ∀ x, rminus + δ ≤ p x ∧ p x ≤ rplus - δ
  u_smooth : ContDiff ℝ ∞ u
  v_smooth : ContDiff ℝ ∞ v
  u_bound : ∀ x, |u x| ≤ Au / rminus
  v_bound : ∀ x, |v x| ≤ Av / rminus
  u_support : ∀ x, x ∉ region → u x = 0
  v_support : ∀ x, x ∉ region → v x = 0

 theorem canonical_realization_properties (U : SmoothStep) (Q M : ℕ) (a : ι → ℕ) (q : ι → Fin (D + 1))
    (γ η lam : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4)
    (offset ell p0 rminus rplus δ Au Av : ℝ)
    (hell : 0 < ell) (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1)
    (hrminus : 0 < rminus) (hlt : rminus < rplus) (hδ : 0 < δ)
    (hδr : δ ≤ ((rminus + rplus) / 2 - rminus) / 2)
    (hδp0 : δ ≤ (p0 - rminus) / 2) (hδp1 : δ ≤ (rplus - p0) / 2)
    (hAu : 0 ≤ Au) (hAv : 0 ≤ Av)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (hi : ContDiff ℝ ∞ inner) (ho : ContDiff ℝ ∞ outer)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (hi1 : ∀ y, |inner y| ≤ 1) (ho01 : ∀ y, 0 ≤ outer y ∧ outer y ≤ 1)
    (hden : 1 - (ell * (2 * N : ℕ)) ^ (D + 1) * (∫ y, outer y ∂Model.cubeVolume (D + 1)) ≠ 0)
    (hbase : p0 = sourceBaseline ((ell * (2 * N : ℕ)) ^ (D + 1))
      (∫ y, outer y ∂Model.cubeVolume (D + 1)) ((rminus + rplus) / 2))
    (z : GridPair D N → PairState ι) :
    let r0 := (rminus + rplus) / 2
    let h := (rplus - rminus) / 2 - δ
    let p := globalDensity offset ell p0 r0 h outer (stateAngles z) (statePhases U M a q γ z)
    let u := globalProfile offset ell p0 r0 h Au inner outer (stateAngles z) (statePhases U M a q γ z) (stateSignU z) (stateGates Q M η lam z)
    let v := globalProfile offset ell p0 r0 h Av inner outer (stateAngles z) (statePhases U M a q γ z) (stateSignV z) (stateGates Q M η lam z)
    RealizationProperties p u v rminus rplus δ Au Av (gridRegion (D + 1) N offset ell) := by
  dsimp only
  let r0 := (rminus + rplus) / 2
  let h := (rplus - rminus) / 2 - δ
  have hm := source_margin_parameters rminus rplus p0 δ hδ hlt hδr hδp0 hδp1
  have hp0 : rminus + δ ≤ p0 ∧ p0 ≤ rplus - δ := ⟨hm.2.1, hm.2.2.1⟩
  have hr : rminus + δ ≤ r0 - |h| ∧ r0 + |h| ≤ rplus - δ := hm.2.2.2
  have hphase (k : GridPair D N) : ContDiff ℝ ∞ (statePhases U M a q γ z k) := blockPhase_smooth U M a q γ _ hγ hγ1
  have hb (x : Model.Covariate (D + 1)) := globalDensity_bounds offset ell p0 r0 h (rminus + δ) (rplus - δ)
    hell outer hout ho01 (stateAngles z) (statePhases U M a q γ z) hp0 hr x
  have hp (x : Model.Covariate (D + 1)) : globalDensity offset ell p0 r0 h outer (stateAngles z) (statePhases U M a q γ z) x ≠ 0 :=
    ne_of_gt (hrminus.trans_le ((le_add_of_nonneg_right hδ.le).trans (hb x).1))
  have hsign (s : Bool) : |RoughRegime.Lower.sign s| ≤ 1 := by cases s <;> norm_num [RoughRegime.Lower.sign]
  have hS (k : GridPair D N) : |stateGates Q M η lam z k| ≤ 1 := by
    change |jointGate Q M η lam (z k).1| ≤ 1
    rw [abs_of_nonneg (jointGate_bounds Q M η lam (z k).1).1]
    exact (jointGate_bounds Q M η lam (z k).1).2
  have hpminus (x : Model.Covariate (D + 1)) : rminus ≤ globalDensity offset ell p0 r0 h outer (stateAngles z) (statePhases U M a q γ z) x :=
    (le_add_of_nonneg_right hδ.le).trans (hb x).1
  constructor
  · exact globalDensity_smooth offset ell p0 r0 h outer ho (stateAngles z) _ hphase
  · exact globalDensity_integral_one offset ell p0 r0 h hell hoff hsize outer ho.continuous hout _ _
      (fun k => (hphase k).continuous) hden hbase
  · exact hb
  · exact globalProfile_smooth offset ell p0 r0 h Au inner outer hi ho (stateAngles z) _ hphase _ _ hp
  · exact globalProfile_smooth offset ell p0 r0 h Av inner outer hi ho (stateAngles z) _ hphase _ _ hp
  · intro x
    simpa only [abs_of_nonneg hAu] using globalProfile_abs_bound offset ell p0 r0 h Au rminus hell hrminus
      inner outer hin hi1 (stateAngles z) _ (stateSignU z) _ (fun k => hsign _) hS hpminus x
  · intro x
    simpa only [abs_of_nonneg hAv] using globalProfile_abs_bound offset ell p0 r0 h Av rminus hell hrminus
      inner outer hin hi1 (stateAngles z) _ (stateSignV z) _ (fun k => hsign _) hS hpminus x
  · intro x hx
    exact globalProfile_outside_region offset ell p0 r0 h Au hell inner outer hin _ _ _ _ x hx
  · intro x hx
    exact globalProfile_outside_region offset ell p0 r0 h Av hell inner outer hin _ _ _ _ x hx

end RoughRegime.LatticePriors
