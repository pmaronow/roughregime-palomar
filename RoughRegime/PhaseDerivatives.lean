module

public import RoughRegime.GateRoot
public import Mathlib.Analysis.Calculus.ContDiff.Bounds


@[expose] public section
/-! Actual weighted Frechet derivatives of every truncated hierarchical phase. -/
noncomputable section
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier

def partialBlockPhase {d : ℕ} {ι : Type*} (T : Finset ι) (U : SmoothStep) (M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ : ι → ℝ) (z : ι → ℤ) (x : Model.Covariate d) : ℝ :=
  ∑ i ∈ T, latticeStep M * z i * coordinateSoftDigit U (γ i) (a i) (q i) x

/-- The root-weighted actual phase jets have the source weighted derivative sum;
 no profile derivative bound or coefficient truncation is assumed. -/
theorem gateRoot_phase_derivative_bound (U : SmoothStep) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {ι : Type} [Fintype ι] (T : Finset ι)
      (Q M K : ℕ) (a : ι → ℕ) (q : ι → Fin d) (γ lam η : ι → ℝ) (z : ι → ℤ),
      0 < K → K ≤ 2 * Q → (∀ i, 0 < γ i) → (∀ i, γ i ≤ 1 / 4) →
      (∀ i, 0 < lam i * η i) → ∀ x : Model.Covariate d,
      gateRoot (blockGate Q M lam η z) K *
          ‖iteratedFDeriv ℝ N (partialBlockPhase T U M a q γ z) x‖ ≤
        C * ∑ i ∈ T, (lam i * η i) * ((2 : ℝ) ^ a i / γ i) ^ N := by
  obtain ⟨C, hC, hselect⟩ := coordinateSoftDigit_derivative_bound U N
  refine ⟨C, hC, ?_⟩
  intro d ι inst T Q M K a q γ lam η z hK hKQ hγ hγ1 hscale x
  let β := gateRoot (blockGate Q M lam η z) K
  have hβ : 0 ≤ β := (gateRoot_bounds _ K (blockGate_range Q M lam η z).1
    (blockGate_range Q M lam η z).2).1
  have hsmooth (i : ι) : ContDiff ℝ ∞ (coordinateSoftDigit U (γ i) (a i) (q i)) :=
    coordinateSoftDigit_smooth U (γ i) (a i) (q i) (hγ i) (hγ1 i)
  have heach (i : ι) : β *
      ‖iteratedFDeriv ℝ N (fun y => latticeStep M * z i * coordinateSoftDigit U (γ i) (a i) (q i) y) x‖ ≤
      C * ((lam i * η i) * ((2 : ℝ) ^ a i / γ i) ^ N) := by
    let L : ℝ →L[ℝ] ℝ := (latticeStep M * z i) • ContinuousLinearMap.id ℝ ℝ
    have hn := L.norm_iteratedFDeriv_comp_left (x := x) (n := N) (hsmooth i).contDiffAt (by simp : (N : ℕ∞ω) ≤ ∞)
    have hmul :
        ‖iteratedFDeriv ℝ N (fun y => latticeStep M * z i * coordinateSoftDigit U (γ i) (a i) (q i) y) x‖ ≤
        |latticeStep M * z i| * ‖iteratedFDeriv ℝ N (coordinateSoftDigit U (γ i) (a i) (q i)) x‖ := by
      simpa only [L, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one, Function.comp_def] using hn
    have hbcoef := gateRoot_coefficient_le Q M K lam η z hK hKQ hscale i
    have hsel := hselect (γ i) (hγ i) (hγ1 i) (a i) (q i) x
    calc
      _ ≤ β * (|latticeStep M * z i| *
        ‖iteratedFDeriv ℝ N (coordinateSoftDigit U (γ i) (a i) (q i)) x‖) :=
        mul_le_mul_of_nonneg_left hmul hβ
      _ ≤ β * (|latticeStep M * z i| * (C * ((2 : ℝ) ^ a i / γ i) ^ N)) := by gcongr
      _ = C * ((β * |latticeStep M * z i|) * ((2 : ℝ) ^ a i / γ i) ^ N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbcoef (pow_nonneg (div_nonneg (by positivity) (hγ i).le) N)) hC.le
  unfold partialBlockPhase
  rw [iteratedFDeriv_fun_sum_apply (fun i hi =>
    (contDiff_const.mul (hsmooth i)).of_le (by simp) |>.contDiffAt)]
  calc
    _ ≤ β * ∑ i ∈ T,
        ‖iteratedFDeriv ℝ N (fun y => latticeStep M * z i * coordinateSoftDigit U (γ i) (a i) (q i) y) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hβ
    _ = ∑ i ∈ T, β *
        ‖iteratedFDeriv ℝ N (fun y => latticeStep M * z i * coordinateSoftDigit U (γ i) (a i) (q i) y) x‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ T, C * ((lam i * η i) * ((2 : ℝ) ^ a i / γ i) ^ N) :=
      Finset.sum_le_sum (fun i _ => heach i)
    _ = _ := by rw [Finset.mul_sum]

end RoughRegime.LatticePriors
