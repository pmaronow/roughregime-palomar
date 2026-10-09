module

public import RoughRegime.SmoothPilotFull
public import RoughRegime.ScalarHolder
public import RoughRegime.CubeTransport
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


@[expose] public section
/-! A literal nonconstant smooth spatial contrast with exact cube moments
and arbitrarily small genuine Hölder norm. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace RoughRegime.Applications.Products
open RoughRegime.DyadicDigits
set_option backward.isDefEq.respectTransparency false

 def sineContrast {d : ℕ} (i : Fin d) (eta : ℝ) (x : Model.Covariate d) : ℝ :=
   eta*Real.sin (2*Real.pi*x i)

 theorem sineContrast_smooth {d : ℕ} (i : Fin d) (eta : ℝ) : ContDiff ℝ ∞ (sineContrast i eta) := by
   unfold sineContrast
   fun_prop

 theorem sineContrast_bound {d : ℕ} (i : Fin d) (eta : ℝ) (heta : 0≤eta) (x : Model.Covariate d) :
     |sineContrast i eta x|≤eta := by
   unfold sineContrast
   rw [abs_mul,abs_of_nonneg heta]
   simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) heta

 theorem unit_sine_mean : (∫ x,Real.sin (2*Real.pi*x) ∂unitUniform)=0 := by
   unfold unitUniform
   rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,
     intervalIntegral.integral_comp_mul_left Real.sin (by positivity : 2*Real.pi≠0),integral_sin]
   simp

 theorem unit_sine_square : (∫ x,Real.sin (2*Real.pi*x)^2 ∂unitUniform)=(1:ℝ)/2 := by
   unfold unitUniform
   rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,
     intervalIntegral.integral_comp_mul_left (fun x=>Real.sin x^2) (by positivity : 2*Real.pi≠0),integral_sin_sq]
   simp only [mul_zero,mul_one,Real.sin_zero,Real.cos_zero,Real.sin_two_pi,zero_mul,sub_zero,zero_add,smul_eq_mul]
   field_simp [Real.pi_ne_zero]

 theorem sineContrast_mean {d : ℕ} (i : Fin d) (eta : ℝ) :
     (∫ x,sineContrast i eta x ∂Model.cubeVolume d)=0 := by
   unfold sineContrast
   rw [integral_const_mul,RoughRegime.LatticePriors.cubeVolume_integral_transport]
   have hi := integral_comp_eval (μ:=fun _ : Fin d=>unitUniform) (i:=i)
     (f:=fun z : ℝ=>Real.sin (2*Real.pi*z)) (by fun_prop : AEStronglyMeasurable _ unitUniform)
   change (eta*(∫ x : Fin d→ℝ,Real.sin (2*Real.pi*x i) ∂Measure.pi (fun _=>unitUniform)))=0
   rw [hi,unit_sine_mean,mul_zero]

 theorem sineContrast_square {d : ℕ} (i : Fin d) (eta : ℝ) :
     (∫ x,sineContrast i eta x^2 ∂Model.cubeVolume d)=eta^2/2 := by
   unfold sineContrast
   simp_rw [mul_pow]
   rw [integral_const_mul,RoughRegime.LatticePriors.cubeVolume_integral_transport]
   have hi := integral_comp_eval (μ:=fun _ : Fin d=>unitUniform) (i:=i)
     (f:=fun z : ℝ=>Real.sin (2*Real.pi*z)^2) (by fun_prop : AEStronglyMeasurable _ unitUniform)
   change eta^2*(∫ x : Fin d→ℝ,Real.sin (2*Real.pi*x i)^2 ∂Measure.pi (fun _=>unitUniform))=eta^2/2
   rw [hi,unit_sine_square]
   ring

 theorem exists_sine_contrast {d : ℕ} (i : Fin d) (beta H : ℝ) (hbeta : 0<beta) (hH : 0<H) :
     ∃ eta : ℝ, 0<eta ∧ eta≤1/4 ∧
       sineContrast i eta∈Model.holderBall beta (H/2) ∧
       (∫ x,sineContrast i eta x ∂Model.cubeVolume d)=0 ∧
       (∫ x,sineContrast i eta x^2 ∂Model.cubeVolume d)=eta^2/2 ∧
       0<(∫ x,sineContrast i eta x^2 ∂Model.cubeVolume d) := by
   obtain ⟨K,hK,hbound⟩ := finite_smooth_combination_holder_bound d
     (fun _ : Fin 1=>sineContrast i 1) (fun _=>sineContrast_smooth i 1) beta hbeta
   have hw : Model.holderNorm (sineContrast i 1) beta≤ENNReal.ofReal K := by
     change sineContrast i 1∈Model.holderBall beta K
     simpa only [Fin.sum_univ_one,one_mul] using hbound (fun _=>1) (fun _=>by norm_num)
   let L := K+1
   have hL : 0<L := by dsimp [L]; linarith
   have hwL : Model.holderNorm (sineContrast i 1) beta≤ENNReal.ofReal L :=
     hw.trans (ENNReal.ofReal_le_ofReal (by dsimp [L]; linarith))
   let eta := min (1/4) (H/(4*L))
   have he : 0<eta := lt_min (by norm_num) (by positivity)
   have he1 : eta≤1/4 := min_le_left _ _
   have heH : 2*eta*L≤H/2 := by
     have hh := (le_div_iff₀ (by positivity : 0<4*L)).mp (min_le_right (1/4) (H/(4*L)))
     dsimp only [eta]
     nlinarith
   have hs := Model.holderNorm_const_mul_le (sineContrast i 1) beta L eta hbeta hL.le
     (sineContrast_smooth i 1) hwL
   have hs' : sineContrast i eta∈Model.holderBall beta (H/2) := by
     change Model.holderNorm (sineContrast i eta) beta≤ENNReal.ofReal (H/2)
     have hf : (fun x=>eta*sineContrast i 1 x)=sineContrast i eta := by funext x; simp [sineContrast]
     rw [hf,abs_of_pos he] at hs
     exact hs.trans (ENNReal.ofReal_le_ofReal heH)
   refine ⟨eta,he,he1,hs',sineContrast_mean i eta,sineContrast_square i eta,?_⟩
   rw [sineContrast_square]
   positivity

end RoughRegime.Applications.Products
