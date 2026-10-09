module

public import RoughRegime.SourceGrid
public import RoughRegime.CanonicalObservation
public import RoughRegime.LatticeCutoffs


@[expose] public section
/-! Automatic source frames: actual fixed cutoffs, original level scales,
B=(2N)^d, fixed region volume v0, exact normalized baseline density. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
set_option backward.isDefEq.respectTransparency false

 def sourceOuterIntegral (d : ℕ) : ℝ := ∫ x, outerBump d x ∂Model.cubeVolume d
 def sourceFixedBaseline (d : ℕ) (v0 rminus rplus : ℝ) : ℝ :=
   sourceBaseline v0 (sourceOuterIntegral d) ((rminus+rplus)/2)
 def sourceMarginBound (d : ℕ) (v0 rminus rplus : ℝ) : ℝ :=
   min ((rplus-rminus)/4) (min ((sourceFixedBaseline d v0 rminus rplus-rminus)/2)
     ((rplus-sourceFixedBaseline d v0 rminus rplus)/2))

 theorem sourceOuterIntegral_bounds (d : ℕ) : 0 ≤ sourceOuterIntegral d ∧ sourceOuterIntegral d ≤ 1 := by
   have hi : Integrable (outerBump d : Model.Covariate d → ℝ) (Model.cubeVolume d) :=
     ((outerBump_smooth d).continuous.continuousOn.integrableOn_compact (Model.isCompact_cube d))
   constructor
   · exact integral_nonneg (fun _ => (outerBump d).nonneg)
   · have he := integral_mono hi (integrable_const (1:ℝ)) (fun _ => (outerBump d).le_one)
     simpa only [sourceOuterIntegral,integral_const,probReal_univ,smul_eq_mul,mul_one] using he

 theorem exists_source_fixed_volume (d : ℕ) (rminus rplus : ℝ) (hrminus : rminus < 1) (hrplus : 1 < rplus) :
     ∃ v0 : ℝ, 0 < v0 ∧ v0 ≤ 1/2 ∧ 0 < 1-v0*sourceOuterIntegral d ∧
       0 < sourceMarginBound d v0 rminus rplus := by
   obtain ⟨vmax,hv,hv1,hprop⟩ := exists_small_baseline_volume rminus rplus ((rminus+rplus)/2)
     (sourceOuterIntegral d) hrminus hrplus (sourceOuterIntegral_bounds d).1 (sourceOuterIntegral_bounds d).2
   have hp := hprop vmax hv le_rfl
   refine ⟨vmax,hv,hv1,hp.1,?_⟩
   unfold sourceMarginBound sourceFixedBaseline
   apply lt_min
   · linarith
   · apply lt_min <;> linarith [hp.2.1,hp.2.2]

 def sourceCanonicalFrame (D N J Q M : ℕ) (hN : 0 < N)
     (gammaStar lambdaStar alpha0 m epsilonU epsilonV alpha beta v0 rminus rplus delta : ℝ)
     (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4) (hm : 0 < m)
     (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hv : 0 < v0) (hv1 : v0 ≤ 1)
     (hrminus : 0 < rminus) (hlt : rminus < rplus) (hd : 0 < delta)
     (hmargin : delta ≤ sourceMarginBound (D+1) v0 rminus rplus)
     (hden : 0 < 1-v0*sourceOuterIntegral (D+1)) : CanonicalFrame D N (Fin J × Fin (D+1)) := by
   let B := sourceGridCount N (D+1)
   let ell := sourceBlockScale v0 B (D+1)
   have hB : 0 < B := sourceGridCount_pos N (D+1) hN
   have hell : 0 < ell := sourceBlockScale_pos hv hB (D+1)
   have hfit := source_grid_fits_cube v0 N (D+1) hv hv1 hN (Nat.succ_pos _)
   have hvol : (ell*(2*N : ℕ))^(D+1)=v0 := by
     rw [sourceBlockScale_grid_side v0 N (D+1) hv.le hN (Nat.succ_pos _)]
     simpa only [sourceGridSide,one_div] using Real.rpow_inv_natCast_pow hv.le (Nat.succ_ne_zero D)
   refine {
     U := canonicalStep
     Q := Q
     M := M
     a := fun i => J-i.1.val
     q := Prod.snd
     gamma := fun i => sourceGamma gammaStar i.1.val
     eta := fun i => sourceEta gammaStar lambdaStar alpha0 m i.1.val
     lambda := fun i => sourceLambda lambdaStar i.1.val
     gamma_pos := fun i => by unfold sourceGamma; positivity
     gamma_le := fun i => sourceGamma_le_quarter gammaStar _ hγ hγ1
     offset := sourceGridOffset v0 (D+1)
     ell := ell
     p0 := sourceFixedBaseline (D+1) v0 rminus rplus
     rminus := rminus
     rplus := rplus
     delta := delta
     Au := sourceAmplitude epsilonU B J (D+1) alpha m
     Av := sourceAmplitude epsilonV B J (D+1) beta m
     ell_pos := hell
     offset_nonneg := hfit.1
     size_bound := hfit.2
     rminus_pos := hrminus
     interval := hlt
     delta_pos := hd
     delta_r := ?_
     delta_p0 := ?_
     delta_p1 := ?_
     Au_nonneg := by unfold sourceAmplitude sourceSpatialVolume; positivity
     Av_nonneg := by unfold sourceAmplitude sourceSpatialVolume; positivity
     inner := innerBump (D+1)
     outer := outerBump (D+1)
     inner_smooth := innerBump_smooth (D+1)
     outer_smooth := outerBump_smooth (D+1)
     inner_zero := innerBump_zero_outside (D+1)
     outer_zero := outerBump_zero_outside (D+1)
     inner_bound := fun _ => by rw [abs_of_nonneg (innerBump (D+1)).nonneg]; exact (innerBump (D+1)).le_one
     outer_bound := fun _ => ⟨(outerBump (D+1)).nonneg,(outerBump (D+1)).le_one⟩
     denominator_ne := ?_
     baseline_eq := ?_ }
   · have he := hmargin.trans (min_le_left _ _)
     linarith
   · exact hmargin.trans ((min_le_right _ _).trans (min_le_left _ _))
   · exact hmargin.trans ((min_le_right _ _).trans (min_le_right _ _))
   · rw [hvol]
     exact hden.ne'
   · rw [hvol]
     rfl

end RoughRegime.LatticePriors
