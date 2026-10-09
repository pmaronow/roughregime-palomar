module

public import RoughRegime.OddTaylor


@[expose] public section
/-! Identification of the expansion coefficient with the actual mixed second
Fréchet derivative and with scalar iterated partial derivatives. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff
namespace RoughRegime.OddTaylor

lemma mixedDerivative_eq_second_fderiv (F : Plane → ℝ) (x : Plane)
    (hF : ContDiffAt ℝ 2 F x) :
    mixedDerivative F x = (fderiv ℝ (fderiv ℝ F) x eV) eU := by
  have hDf : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd : HasFDerivAt (firstPartial F)
      ((ContinuousLinearMap.apply ℝ ℝ eU).comp (fderiv ℝ (fderiv ℝ F) x)) x := by
    convert (ContinuousLinearMap.apply ℝ ℝ eU).hasFDerivAt.comp x hDf.hasFDerivAt using 1
    rfl
  change (fderiv ℝ (firstPartial F) x) eV = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  rfl

/-- Schwarz symmetry identifies the coefficient with the source mixed derivative
in either coordinate order. -/
theorem mixedDerivative_eq_iteratedFDeriv (F : Plane → ℝ) (x : Plane)
    (hF : ContDiffAt ℝ 2 F x) :
    mixedDerivative F x = iteratedFDeriv ℝ 2 F x ![eU, eV] := by
  rw [mixedDerivative_eq_second_fderiv F x hF, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact (hF.isSymmSndFDerivAt (by simp)).eq eV eU

lemma firstPartial_eq_deriv (F : Plane → ℝ) (s t : ℝ)
    (hF : DifferentiableAt ℝ F (s, t)) :
    firstPartial F (s, t) = deriv (fun u => F (u, t)) s :=
  (firstPartial_hasDerivAt F s t hF).deriv.symm

/-- The coefficient is also the genuine scalar `∂v(∂u F)` at the origin. -/
theorem mixedDerivative_eq_scalar_deriv (F : Plane → ℝ)
    (hF : ContDiffAt ℝ 2 F (0 : Plane)) :
    mixedDerivative F 0 = deriv (fun v => deriv (fun u => F (u, v)) 0) 0 := by
  have hline : Tendsto (fun v : ℝ => ((0 : ℝ), v)) (nhds 0) (nhds (0 : Plane)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have he : (fun v : ℝ => firstPartial F (0, v)) =ᶠ[nhds 0]
      (fun v => deriv (fun u => F (u, v)) 0) := by
    filter_upwards [hline.eventually (hF.eventually (by norm_num))] with v hv
    exact firstPartial_eq_deriv F 0 v (hv.differentiableAt (by norm_num))
  have hDu : DifferentiableAt ℝ (firstPartial F) (0 : Plane) :=
    (directionalDerivative_contDiffAt F eU 0 (n := 1) hF).differentiableAt (by norm_num)
  exact (mixedDerivative_hasDerivAt F 0 0 hDu).deriv.symm.trans he.deriv_eq

/-- The coefficient also equals the reverse scalar mixed partial used by the
rational source integrand: `∂u(∂v F)` at the origin. -/
theorem mixedDerivative_eq_reverse_scalar_deriv (F : Plane → ℝ)
    (hF : ContDiffAt ℝ 2 F (0 : Plane)) :
    mixedDerivative F 0 = deriv (fun u => deriv (fun v => F (u, v)) 0) 0 := by
  let G := directionalDerivative F eV
  have hDG : DifferentiableAt ℝ G (0 : Plane) :=
    (directionalDerivative_contDiffAt F eV 0 (n := 1) hF).differentiableAt (by norm_num)
  have hDf : DifferentiableAt ℝ (fderiv ℝ F) (0 : Plane) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdG : HasFDerivAt G
      ((ContinuousLinearMap.apply ℝ ℝ eV).comp (fderiv ℝ (fderiv ℝ F) 0)) 0 := by
    convert (ContinuousLinearMap.apply ℝ ℝ eV).hasFDerivAt.comp 0 hDf.hasFDerivAt using 1
    rfl
  have hm : mixedDerivative F 0 = fderiv ℝ G 0 eU := by
    rw [mixedDerivative_eq_second_fderiv F 0 hF, hdG.fderiv, ContinuousLinearMap.comp_apply]
    exact (hF.isSymmSndFDerivAt (by simp)).eq eV eU
  have houter : HasDerivAt (fun u => G (u, 0)) (fderiv ℝ G 0 eU) 0 := by
    simpa only [Function.comp_def, id_eq, eU] using
      hDG.hasFDerivAt.comp_hasDerivAt (f := fun u : ℝ => (u, (0 : ℝ))) 0 ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
  have hline : Tendsto (fun u : ℝ => (u, (0 : ℝ))) (nhds 0) (nhds (0 : Plane)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have he : (fun u : ℝ => G (u, 0)) =ᶠ[nhds 0]
      (fun u => deriv (fun v => F (u, v)) 0) := by
    filter_upwards [hline.eventually (hF.eventually (by norm_num))] with u hu
    have hd : HasDerivAt (fun v => F (u, v)) (G (u, 0)) 0 := by
      simpa only [Function.comp_def, id_eq, G, directionalDerivative, eV] using
        (hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0
          ((hasDerivAt_const (0 : ℝ) u).prodMk (hasDerivAt_id (0 : ℝ)))
    exact hd.deriv.symm
  exact hm.trans (houter.deriv.symm.trans he.deriv_eq)

end RoughRegime.OddTaylor
