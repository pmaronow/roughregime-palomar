module

public import RoughRegime.CanonicalCenteredTargets
public import RoughRegime.OddTaylorDerivative


@[expose] public section
/-! Genuine canonical nonlinear prior means and variances. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors.CanonicalFrame
open RoughRegime.LatticeFourier RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Independent of all grid, frequency, margin, and profile parameters, local
C4 regularity controls the actual nonlinear canonical block prior means. -/
theorem block_prior_taylor (Phi : (ℝ × ℝ) → ℝ) (hPhi : Measurable Phi)
    (hPhi4 : ContDiffAt ℝ 4 Phi 0) :
    ∃ epsilon>0, ∃ C≥0, ∀ {D N : ℕ} {ι : Type*} [Fintype ι]
      (F : CanonicalFrame D N ι) (nu : Measure (ι → ℤ)) [IsProbabilityMeasure nu],
      F.Au/F.rminus ≤ epsilon → F.Av/F.rminus ≤ epsilon → ∀ label : Bool,
      |((∫ w, F.centeredBlockTarget Phi label w ∂blockPrior nu F.M true)-
        (∫ w, F.centeredBlockTarget Phi label w ∂blockPrior nu F.M false))-
        OddTaylor.mixedDerivative Phi 0*
          ((∫ w, F.centeredBlockTarget (fun x => x.1*x.2) label w ∂blockPrior nu F.M true)-
           (∫ w, F.centeredBlockTarget (fun x => x.1*x.2) label w ∂blockPrior nu F.M false))|  ≤ 
      C*F.rplus*(F.Au/F.rminus)*(F.Av/F.rminus)*
        ((F.Au/F.rminus)^2+(F.Av/F.rminus)^2) := by
  let PhiC := fun x => Phi x-Phi 0
  have hm : Measurable PhiC := hPhi.sub measurable_const
  have hc : ContDiffAt ℝ 4 PhiC 0 := hPhi4.sub contDiffAt_const
  obtain ⟨epsilon,he,C,hC,hrem⟩ := spatial_prior_target_taylor PhiC hm hc
  refine ⟨epsilon,he,C,hC,?_⟩
  intro D N ι _ F nu _ hAu hAv label
  let state := fun z : (ι → ℤ) × ℝ => (z.1,(z.2,(true,true)))
  let p := fun z : ((ι → ℤ) × ℝ) × Model.Covariate (D+1) => F.localBlockDensity (state z.1) label z.2
  let u := fun z : ((ι → ℤ) × ℝ) × Model.Covariate (D+1) => F.localUnsignedProfile F.Au (state z.1) label z.2
  let v := fun z : ((ι → ℤ) × ℝ) × Model.Covariate (D+1) => F.localUnsignedProfile F.Av (state z.1) label z.2
  have hs : Measurable state := measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have hps : Measurable (fun z : ((ι → ℤ) × ℝ) × Model.Covariate (D+1) => (state z.1,z.2)) :=
    (hs.comp measurable_fst).prodMk measurable_snd
  have hp : Measurable p := (F.localBlockDensity_joint_measurable label).comp hps
  have hu : Measurable u := by
    exact Measurable.comp
      (g := fun q : PairState ι × Model.Covariate (D+1) => F.localUnsignedProfile F.Au q.1 label q.2)
      (f := fun z : ((ι → ℤ) × ℝ) × Model.Covariate (D+1) => (state z.1,z.2))
      (F.localUnsignedProfile_joint_measurable F.Au label) hps
  have hv : Measurable v := by
    exact Measurable.comp
      (g := fun q : PairState ι × Model.Covariate (D+1) => F.localUnsignedProfile F.Av q.1 label q.2)
      (f := fun z : ((ι → ℤ) × ℝ) × Model.Covariate (D+1) => (state z.1,z.2))
      (F.localUnsignedProfile_joint_measurable F.Av label) hps
  have hpb (z) : |p z| ≤ F.rplus := by
    rw [abs_of_pos (F.rminus_pos.trans_le (F.localBlockDensity_bounds (state z.1) label z.2).1)]
    exact (F.localBlockDensity_bounds _ _ _).2
  have hub (z) : |u z| ≤ F.Au/F.rminus := F.localUnsignedProfile_bound _ F.Au_nonneg _ _ _
  have hvb (z) : |v z| ≤ F.Av/F.rminus := F.localUnsignedProfile_bound _ F.Av_nonneg _ _ _
  have hh := hrem nu (Model.cubeVolume (D+1)) F.M p u v hp hu hv F.rplus
    (F.Au/F.rminus) (F.Av/F.rminus) (F.rminus_pos.le.trans F.interval.le)
    (div_nonneg F.Au_nonneg F.rminus_pos.le) (div_nonneg F.Av_nonneg F.rminus_pos.le)
    hAu hAv hpb hub hvb
  have he (positive : Bool) :
      (∫ w, F.centeredBlockTarget Phi label w ∂blockPrior nu F.M positive) =
      ∫ w, spatialSignedTarget (Model.cubeVolume (D+1)) PhiC p u v w
        ∂nu.prod (angleSignLaw F.M positive) := by
    rfl
  have hem (positive : Bool) :
      (∫ w, F.centeredBlockTarget (fun x => x.1*x.2) label w ∂blockPrior nu F.M positive) =
      ∫ w, spatialSignedTarget (Model.cubeVolume (D+1)) (fun x => x.1*x.2) p u v w
        ∂nu.prod (angleSignLaw F.M positive) := by
    apply integral_congr_ae
    filter_upwards with w
    apply integral_congr_ae
    filter_upwards with y
    simp [centeredBlockIntegrand,spatialResponseIntegrand,
      p,u,v,state,localBlockDensity,localUnsignedProfile]
  rw [he true,he false,hem true,hem false]
  simpa only [PhiC,mixedDerivative_sub_const Phi (Phi 0)] using hh

variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

theorem global_response_prior_memLp (Phi : (ℝ × ℝ) → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hbound : ∀ u v : ℝ, |u| ≤ F.Au/F.rminus → |v| ≤ F.Av/F.rminus → |Phi (u,v)-Phi 0| ≤ B)
    (nu : Measure (ι → ℤ)) [IsProbabilityMeasure nu] (positive : Bool) :
    MemLp (fun z => ∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1)) 2
      (globalBlockPrior nu F.M positive) := by
  have hc : MemLp (fun _ : GridPair D N → PairState ι => Phi 0) 2
      (globalBlockPrior nu F.M positive) := memLp_const _
  have hp := independentPairTarget_memLp (D := D) (N := N) F.ell nu F.M positive
    (F.centeredBlockTarget Phi) (F.centeredBlockTarget_measurable Phi hPhi) (F.rplus*B)
    (F.centeredBlockTarget_bound Phi B hbound)
  have he : (fun z => ∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1)) =
      fun z => Phi 0+independentPairTarget (D:=D) (N:=N) F.ell (F.centeredBlockTarget Phi) z :=
    funext (F.global_response_centered_decomposition Phi hPhi B hbound)
  rw [he]
  exact hc.add hp

theorem global_response_prior_variance (Phi : (ℝ × ℝ) → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ u v : ℝ, |u| ≤ F.Au/F.rminus → |v| ≤ F.Av/F.rminus → |Phi (u,v)-Phi 0| ≤ B)
    (nu : Measure (ι → ℤ)) [IsProbabilityMeasure nu] (positive : Bool) :
    variance (fun z => ∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1))
      (globalBlockPrior nu F.M positive)  ≤ 
      8*(F.ell^(D+1))^2*Fintype.card (GridPair D N)*(F.rplus*B)^2 := by
  have he : (fun z => ∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1)) =
      fun z => Phi 0+independentPairTarget (D:=D) (N:=N) F.ell (F.centeredBlockTarget Phi) z :=
    funext (F.global_response_centered_decomposition Phi hPhi B hbound)
  rw [he]
  exact baseline_add_independentPairTarget_variance_bound F.ell (Phi 0) nu F.M positive
    (F.centeredBlockTarget Phi) (F.centeredBlockTarget_measurable Phi hPhi) (F.rplus*B)
    (mul_nonneg (F.rminus_pos.le.trans F.interval.le) hB)
    (F.centeredBlockTarget_bound Phi B hbound)

/-- The source prior variance is genuinely O(1/B) for the actual growing grid.
The constant uses only the fixed local density and response bounds. -/
theorem global_response_prior_variance_grid (hN : 0<N) (Phi : (ℝ × ℝ) → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ u v : ℝ, |u| ≤ F.Au/F.rminus → |v| ≤ F.Av/F.rminus → |Phi (u,v)-Phi 0| ≤ B)
    (nu : Measure (ι → ℤ)) [IsProbabilityMeasure nu] (positive : Bool) :
    variance (fun z => ∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1))
      (globalBlockPrior nu F.M positive)  ≤  4*(F.rplus*B)^2/((2*N : ℕ):ℝ)^(D+1) := by
  have hell := F.ell_pos
  have hsize : F.ell*((2*N : ℕ):ℝ) ≤ 1 := by linarith [F.size_bound,F.offset_nonneg]
  have hvol : (F.ell*((2*N : ℕ):ℝ))^(D+1) ≤ 1 :=
    pow_le_one₀ (by positivity) hsize
  have hmass : (F.ell^(D+1)*((2*N : ℕ):ℝ)^(D+1))^2 ≤ 1 := by
    rw [mul_pow] at hvol
    have hn : 0 ≤ F.ell^(D+1)*((2*N : ℕ):ℝ)^(D+1) := by positivity
    nlinarith
  have hcard : (Fintype.card (GridPair D N):ℝ)=((2*N : ℕ):ℝ)^(D+1)/2 := by
    rw [gridPair_card]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_succ]
    ring
  have hn : 0<((2*N : ℕ):ℝ)^(D+1) := by positivity
  apply (F.global_response_prior_variance Phi hPhi B hB hbound nu positive).trans
  rw [hcard]
  apply (le_div_iff₀ hn).mpr
  convert mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 4*(F.rplus*B)^2) using 1 <;> ring

/-- The constant baseline cancels in the actual two prior means. -/
theorem global_response_prior_mean_difference (Phi : (ℝ × ℝ) → ℝ) (hPhi : Measurable Phi)
    (B : ℝ)
    (hbound : ∀ u v : ℝ, |u| ≤ F.Au/F.rminus → |v| ≤ F.Av/F.rminus → |Phi (u,v)-Phi 0| ≤ B)
    (nu : Measure (ι → ℤ)) [IsProbabilityMeasure nu] :
    ((∫ z, (∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1))
        ∂globalBlockPrior nu F.M true)-
      (∫ z, (∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1))
        ∂globalBlockPrior nu F.M false)) =
    ((∫ z, independentPairTarget (D:=D) (N:=N) F.ell (F.centeredBlockTarget Phi) z
        ∂globalBlockPrior nu F.M true)-
      (∫ z, independentPairTarget (D:=D) (N:=N) F.ell (F.centeredBlockTarget Phi) z
        ∂globalBlockPrior nu F.M false)) := by
  have he : (fun z => ∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1)) =
      fun z => Phi 0+independentPairTarget (D:=D) (N:=N) F.ell (F.centeredBlockTarget Phi) z :=
    funext (F.global_response_centered_decomposition Phi hPhi B hbound)
  rw [he]
  have hi (positive : Bool) : Integrable
      (independentPairTarget (D := D) (N := N) F.ell (F.centeredBlockTarget Phi))
      (globalBlockPrior nu F.M positive) := by
    exact (independentPairTarget_memLp F.ell nu F.M positive
      (F.centeredBlockTarget Phi) (F.centeredBlockTarget_measurable Phi hPhi) (F.rplus*B)
      (F.centeredBlockTarget_bound Phi B hbound)).integrable (by norm_num)
  rw [integral_add (integrable_const _) (hi true),integral_add (integrable_const _) (hi false)]
  simp only [integral_const,probReal_univ,one_smul]
  ring


/-- Actual canonical global prior means inherit the local Taylor remainder.
All integrations are under the genuine continuous/countable block priors. -/
theorem global_response_prior_taylor_transfer (Phi : (ℝ × ℝ) → ℝ) (hPhi : Measurable Phi)
    (B : ℝ)
    (hbound : ∀ u v : ℝ, |u| ≤ F.Au/F.rminus → |v| ≤ F.Av/F.rminus → |Phi (u,v)-Phi 0| ≤ B)
    (nu : Measure (ι → ℤ)) [IsProbabilityMeasure nu] (error : ℝ)
    (hb : ∀ label,
      |((∫ w, F.centeredBlockTarget Phi label w ∂blockPrior nu F.M true)-
        (∫ w, F.centeredBlockTarget Phi label w ∂blockPrior nu F.M false))-
        OddTaylor.mixedDerivative Phi 0*
          ((∫ w, F.centeredBlockTarget (fun x => x.1*x.2) label w ∂blockPrior nu F.M true)-
           (∫ w, F.centeredBlockTarget (fun x => x.1*x.2) label w ∂blockPrior nu F.M false))| ≤ error) :
    |((∫ z, (∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1))
        ∂globalBlockPrior nu F.M true)-
      (∫ z, (∫ x, F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1))
        ∂globalBlockPrior nu F.M false))-
      OddTaylor.mixedDerivative Phi 0*
        ((∫ z, (∫ x, F.p z x*(F.u z x*F.v z x) ∂Model.cubeVolume (D+1))
          ∂globalBlockPrior nu F.M true)-
         (∫ z, (∫ x, F.p z x*(F.u z x*F.v z x) ∂Model.cubeVolume (D+1))
          ∂globalBlockPrior nu F.M false))| ≤ (F.ell*(2*N:ℕ))^(D+1)*error := by
  have hAu : 0 ≤ F.Au/F.rminus := div_nonneg F.Au_nonneg F.rminus_pos.le
  have hgb (u v : ℝ) (hu : |u| ≤ F.Au/F.rminus) (hv : |v| ≤ F.Av/F.rminus) :
      |(fun x : ℝ×ℝ=>x.1*x.2) (u,v)-(fun x : ℝ×ℝ=>x.1*x.2) 0| ≤ 
        (F.Au/F.rminus)*(F.Av/F.rminus) := by
    simpa only [Prod.fst_zero,Prod.snd_zero,mul_zero,sub_zero,abs_mul] using
      mul_le_mul hu hv (abs_nonneg v) hAu
  rw [F.global_response_prior_mean_difference Phi hPhi B hbound nu,
    F.global_response_prior_mean_difference (fun x=>x.1*x.2)
      (measurable_fst.mul measurable_snd) ((F.Au/F.rminus)*(F.Av/F.rminus)) hgb nu]
  exact independentPairTarget_taylor_error F.ell F.ell_pos.le nu F.M
    (F.centeredBlockTarget Phi) (F.centeredBlockTarget (fun x=>x.1*x.2))
    (fun positive label=>bounded_integrable _ _ (F.centeredBlockTarget_measurable Phi hPhi label)
      (F.rplus*B) (F.centeredBlockTarget_bound Phi B hbound label))
    (fun positive label=>bounded_integrable _ _
      (F.centeredBlockTarget_measurable (fun x=>x.1*x.2) (measurable_fst.mul measurable_snd) label)
      (F.rplus*((F.Au/F.rminus)*(F.Av/F.rminus)))
      (F.centeredBlockTarget_bound (fun x=>x.1*x.2) _ hgb label))
    (OddTaylor.mixedDerivative Phi 0) error hb


/-- Literal nonlinear response functional of the actual canonical fields. -/
def responseFunctional (Phi : ℝ×ℝ→ℝ) (z : GridPair D N → PairState ι) : ℝ :=
  ∫ x,F.p z x*Phi (F.u z x,F.v z x) ∂Model.cubeVolume (D+1)

/-- Difference of actual means under the two independent source priors. -/
def priorMeanDifference (Phi : ℝ×ℝ→ℝ) (nu : Measure (ι→ℤ)) : ℝ :=
  (∫ z,F.responseFunctional Phi z ∂globalBlockPrior nu F.M true)-
  (∫ z,F.responseFunctional Phi z ∂globalBlockPrior nu F.M false)

/-- One local C4 neighborhood and fixed constants control all canonical
source realizations, including every increasing sample-dependent grid. -/
theorem uniform_response_prior_taylor (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi)
    (hPhi4 : ContDiffAt ℝ 4 Phi 0) :
    ∃ epsilon>0,∃ C≥0,∃ B≥0,
      (∀ u v:ℝ,|u| ≤ epsilon→|v| ≤ epsilon→|Phi (u,v)-Phi 0| ≤ B) ∧
      ∀ {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)
        (nu : Measure (ι→ℤ)) [IsProbabilityMeasure nu],
      F.Au/F.rminus ≤ epsilon→F.Av/F.rminus ≤ epsilon→
      |F.priorMeanDifference Phi nu-OddTaylor.mixedDerivative Phi 0*
        F.priorMeanDifference (fun x=>x.1*x.2) nu| ≤ 
      (F.ell*(2*N:ℕ))^(D+1)*
        (C*F.rplus*(F.Au/F.rminus)*(F.Av/F.rminus)*
          ((F.Au/F.rminus)^2+(F.Av/F.rminus)^2)) := by
  obtain ⟨epsilon1,he1,C,hC,hrem⟩ := block_prior_taylor Phi hPhi hPhi4
  let PhiC : ℝ×ℝ→ℝ := fun x=>Phi x-Phi 0
  have h4 : ContDiffAt ℝ 4 PhiC 0 := hPhi4.sub contDiffAt_const
  obtain ⟨epsilon2,he2,_,_,B,hB,hlocal⟩ := local_oddOdd_taylor_and_bound PhiC h4
  have hb (u v:ℝ) (hu:|u| ≤ min epsilon1 epsilon2) (hv:|v| ≤ min epsilon1 epsilon2) :
      |Phi (u,v)-Phi 0| ≤ B :=
    (hlocal u v (hu.trans (min_le_right _ _)) (hv.trans (min_le_right _ _))).2
  refine ⟨min epsilon1 epsilon2,lt_min he1 he2,C,hC,B,hB,hb,?_⟩
  intro D N ι _ F nu _ hAu hAv
  exact F.global_response_prior_taylor_transfer Phi hPhi B
    (fun u v hu hv=>hb u v (hu.trans hAu) (hv.trans hAv)) nu _
    (hrem F nu (hAu.trans (min_le_left _ _)) (hAv.trans (min_le_left _ _)))

end RoughRegime.LatticePriors.CanonicalFrame
