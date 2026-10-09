module

public import RoughRegime.Applications


@[expose] public section
/-! The local target's actual derivatives in the diagonal-score case. -/

noncomputable section
open Filter
open scoped Topology

namespace RoughRegime.Applications

def diagonalIntegrand (c0 cu cv lam w0 du dv u v : ℝ) : ℝ :=
  c0 + cu * u + cv * v + lam * (u + v) ^ 2 / (w0 + du * u + dv * v)

def diagonalSlope (cv lam w0 du dv u : ℝ) : ℝ :=
  cv + lam * (2 * u * (w0 + du * u) - dv * u ^ 2) / (w0 + du * u) ^ 2

theorem diagonalIntegrand_v_hasDerivAt (c0 cu cv lam w0 du dv u : ℝ)
    (hw : w0 + du * u ≠ 0) :
    HasDerivAt (fun v => diagonalIntegrand c0 cu cv lam w0 du dv u v)
      (diagonalSlope cv lam w0 du dv u) 0 := by
  have ha : HasDerivAt (fun v : ℝ => c0 + cu * u + cv * v) cv 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul cv |>.const_add (c0 + cu * u)
  have hn := ((hasDerivAt_id (0 : ℝ)).const_add u).pow 2 |>.const_mul lam
  have hd : HasDerivAt (fun v : ℝ => w0 + du * u + dv * v) dv 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul dv |>.const_add (w0 + du * u)
  have h := ha.add (hn.div hd (by simpa using hw))
  change HasDerivAt (fun v => diagonalIntegrand c0 cu cv lam w0 du dv u v) _ 0 at h
  convert h using 1
  simp [diagonalSlope]
  ring

theorem diagonalIntegrand_v_derivative (c0 cu cv lam w0 du dv u : ℝ)
    (hw : w0 + du * u ≠ 0) :
    deriv (fun v => diagonalIntegrand c0 cu cv lam w0 du dv u v) 0 =
      diagonalSlope cv lam w0 du dv u :=
  (diagonalIntegrand_v_hasDerivAt c0 cu cv lam w0 du dv u hw).deriv

theorem diagonalSlope_hasDerivAt (cv lam w0 du dv : ℝ) (hw0 : w0 ≠ 0) :
    HasDerivAt (diagonalSlope cv lam w0 du dv) (2 * lam / w0) 0 := by
  have hid := hasDerivAt_id (0 : ℝ)
  have hd : HasDerivAt (fun u : ℝ => w0 + du * u) du 0 := by
    simpa using hid.const_mul du |>.const_add w0
  have hn := ((hid.const_mul 2).mul hd).sub ((hid.pow 2).const_mul dv) |>.const_mul lam
  have h := (hn.div (hd.pow 2) (by simpa using pow_ne_zero 2 hw0)).const_add cv
  change HasDerivAt (diagonalSlope cv lam w0 du dv) _ 0 at h
  convert h using 1
  simp
  field_simp [hw0]

theorem diagonalIntegrand_nonzero_slope_near (c0 cu cv lam w0 du dv : ℝ)
    (hlam : lam ≠ 0) (hw0 : w0 ≠ 0) :
    ∀ᶠ u in 𝓝 (0 : ℝ), u ≠ 0 →
      deriv (fun v => diagonalIntegrand c0 cu cv lam w0 du dv u v) 0 ≠ 0 := by
  have hd : ContinuousAt (fun u : ℝ => w0 + du * u) 0 := by fun_prop
  have hden := hd.eventually_ne (by simpa using hw0)
  by_cases hcv : cv = 0
  · have hf : ContinuousAt (fun u : ℝ => 2 * w0 + (2 * du - dv) * u) 0 := by fun_prop
    have hfactor : ∀ᶠ u in 𝓝 (0 : ℝ), 2 * w0 + (2 * du - dv) * u ≠ 0 :=
      hf.eventually_ne (by simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hw0)
    filter_upwards [hden, hfactor] with u hu hfu
    intro hune
    rw [diagonalIntegrand_v_derivative c0 cu cv lam w0 du dv u hu]
    have he : diagonalSlope cv lam w0 du dv u =
        lam * u * (2 * w0 + (2 * du - dv) * u) / (w0 + du * u) ^ 2 := by
      unfold diagonalSlope
      rw [hcv]
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hlam hune) hfu) (pow_ne_zero 2 hu)
  · have hc := (diagonalSlope_hasDerivAt cv lam w0 du dv hw0).continuousAt
    have hne := hc.eventually_ne (by simpa [diagonalSlope] using hcv)
    filter_upwards [hden, hne] with u hu huneq
    intro _
    rw [diagonalIntegrand_v_derivative c0 cu cv lam w0 du dv u hu]
    exact huneq

theorem diagonalIntegrand_mixed_derivative (c0 cu cv lam w0 du dv : ℝ)
    (hw0 : w0 ≠ 0) :
    deriv (fun u => deriv (fun v => diagonalIntegrand c0 cu cv lam w0 du dv u v) 0) 0 =
      2 * lam / w0 := by
  have heq : (fun u => deriv (fun v => diagonalIntegrand c0 cu cv lam w0 du dv u v) 0)
      =ᶠ[𝓝 0] diagonalSlope cv lam w0 du dv := by
    have hd : ContinuousAt (fun u : ℝ => w0 + du * u) 0 := by fun_prop
    filter_upwards [hd.eventually_ne (by simpa using hw0)] with u hu
    exact diagonalIntegrand_v_derivative c0 cu cv lam w0 du dv u hu
  exact ((diagonalSlope_hasDerivAt cv lam w0 du dv hw0).congr_of_eventuallyEq heq).deriv

end RoughRegime.Applications
