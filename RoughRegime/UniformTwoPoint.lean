module

public import RoughRegime.LowerMeasure


@[expose] public section
/-! Finite two-point bounds whose constants depend on density and exact
separation bounds, with no target-dependent derivative neighborhood. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RoughRegime.LowerMeasure
set_option backward.isDefEq.respectTransparency false
variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]

 theorem affine_two_point_seed {Seed : Type*} [MeasurableSpace Seed]
     (nu : Measure Seed) [IsProbabilityMeasure nu]
     (P : ℝ→GeneralTesting.DensityLaw mu) (f0 f1 : Omega→ℝ) (F : ℝ→ℝ)
     (l r t0 h Dmin cf Cf : ℝ) (n : ℕ) (hDmin : 0 ≤ Dmin) (hh : 0<h)
     (hcf : 0<cf) (hCf : 0 ≤ Cf) (hp : t0+h∈Set.Ioo l r) (hm : t0-h∈Set.Ioo l r)
     (hdens : ∀t∈Set.Ioo l r,(P t).density=ᵐ[mu] fun x=>f0 x+t*f1 x)
     (hpos : ∀t∈Set.Ioo l r,∀ᵐ x ∂mu,cf ≤ f0 x+t*f1 x)
     (hscore : ∀ᵐ x ∂mu,|f1 x| ≤ Cf)
     (hsmall : (n:ℝ)*Cf^2*h^2/cf ≤ 1/4)
     (hsep : Dmin*h ≤ |F (t0+h)-F (t0-h)|)
     (g : (Fin n→Omega)×Seed→ℝ) (hg : Measurable g) :
     ∃t,(t=t0+h ∨ t=t0-h) ∧
       (1/4 ≤ ((Measure.pi (fun _ : Fin n=>(P t).measure)).prod nu).real
         {xs | Dmin*h/2 ≤ |g xs-F t|}) ∧
       ENNReal.ofReal (Dmin*h/4) ≤ eLpNorm (fun xs=>g xs-F t) 2
         ((Measure.pi (fun _ : Fin n=>(P t).measure)).prod nu) := by
  let L := densityLawWithSeed nu (iidDensityLaw (P (t0 + h)) n)
  let R := densityLawWithSeed nu (iidDensityLaw (P (t0 - h)) n)
  have hb := affine_hellinger_bound (P (t0 + h)) (P (t0 - h)) f0 f1
    (t0 + h) (t0 - h) cf Cf hcf hCf (hdens _ hp) (hdens _ hm)
    (hpos _ hp) (hpos _ hm) hscore
  have hiid := hellinger_iid_le (P (t0 + h)) (P (t0 - h)) n
  have hi : GeneralTesting.hellingerSquared L R ≤ 1 / 4 := by
    dsimp [L, R]
    rw [hellinger_with_seed]
    have hscale : (n : ℝ) * (Cf ^ 2 * (t0 + h - (t0 - h)) ^ 2 / (4 * cf)) =
        (n : ℝ) * Cf ^ 2 * h ^ 2 / cf := by ring
    calc
      _ ≤ (n : ℝ) * GeneralTesting.hellingerSquared (P (t0 + h)) (P (t0 - h)) := hiid
      _ ≤ (n : ℝ) * (Cf ^ 2 * (t0 + h - (t0 - h)) ^ 2 / (4 * cf)) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
      _ = (n : ℝ) * Cf ^ 2 * h ^ 2 / cf := hscale
      _ ≤ 1 / 4 := hsmall
  have ht := GeneralTesting.two_point_absolute_large_error L R g hg
    (F (t0 + h)) (F (t0 - h)) hi
  rw [abs_sub_comm (F (t0 - h)) (F (t0 + h))] at ht
  have hL : L.measure = (Measure.pi (fun _ : Fin n => (P (t0 + h)).measure)).prod nu := by
    dsimp [L]
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  have hR : R.measure = (Measure.pi (fun _ : Fin n => (P (t0 - h)).measure)).prod nu := by
    dsimp [R]
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  rw [hL, hR] at ht
  rcases ht with ht | ht
  · have htail : 1 / 4 ≤ ((Measure.pi (fun _ : Fin n => (P (t0 + h)).measure)).prod nu).real
        {xs | Dmin*h / 2 ≤ |g xs - F (t0 + h)|} := by
      refine le_trans ht (measureReal_mono ?_)
      intro xs hx
      change |F (t0 + h) - F (t0 - h)| / 2 ≤ |g xs - F (t0 + h)| at hx
      change Dmin*h / 2 ≤ |g xs - F (t0 + h)|
      linarith
    exact ⟨t0 + h, Or.inl rfl, htail, GeneralTesting.tailReal_to_eLpNorm _ g hg _
      (Dmin*h) (mul_nonneg hDmin hh.le) htail⟩
  · have htail : 1 / 4 ≤ ((Measure.pi (fun _ : Fin n => (P (t0 - h)).measure)).prod nu).real
        {xs | Dmin*h / 2 ≤ |g xs - F (t0 - h)|} := by
      refine le_trans ht (measureReal_mono ?_)
      intro xs hx
      change |F (t0 + h) - F (t0 - h)| / 2 ≤ |g xs - F (t0 - h)| at hx
      change Dmin*h / 2 ≤ |g xs - F (t0 - h)|
      linarith
    exact ⟨t0 - h, Or.inr rfl, htail, GeneralTesting.tailReal_to_eLpNorm _ g hg _
      (Dmin*h) (mul_nonneg hDmin hh.le) htail⟩


/-- Genuine finite-sample randomized minimax lower bound for an affine path.
Only the numerical separation at the two selected points is required. -/
 theorem affine_two_point_minimax (P : ℝ→GeneralTesting.DensityLaw mu)
     (f0 f1 : Omega→ℝ) (T : ProbabilityMeasure Omega→ℝ)
     (Cls : Set (ProbabilityMeasure Omega)) (l r t0 h Dmin cf Cf : ℝ) (n : ℕ)
     (hDmin : 0 ≤ Dmin) (hh : 0<h) (hcf : 0<cf) (hCf : 0 ≤ Cf)
     (hp : t0+h∈Set.Ioo l r) (hm : t0-h∈Set.Ioo l r)
     (hdens : ∀t∈Set.Ioo l r,(P t).density=ᵐ[mu] fun x=>f0 x+t*f1 x)
     (hpos : ∀t∈Set.Ioo l r,∀ᵐ x ∂mu,cf ≤ f0 x+t*f1 x)
     (hscore : ∀ᵐ x ∂mu,|f1 x| ≤ Cf)
     (hsmall : (n:ℝ)*Cf^2*h^2/cf ≤ 1/4)
     (hplus : (P (t0+h)).probabilityMeasure∈Cls)
     (hminus : (P (t0-h)).probabilityMeasure∈Cls)
     (hsep : Dmin*h ≤ |T (P (t0+h)).probabilityMeasure-T (P (t0-h)).probabilityMeasure|) :
     ENNReal.ofReal (Dmin*h/4) ≤ Model.minimaxRMSE n T Cls ∧
       (1/4:ℝ≥0∞) ≤ Model.minimaxTail n T Cls (Dmin*h/2) := by
   let nu : Measure ℝ := volume.restrict (Set.Icc 0 1)
   have hnu : IsProbabilityMeasure nu := ⟨by simp [nu]⟩
   let _ : IsProbabilityMeasure nu := hnu
   have hroot := affine_two_point_seed nu P f0 f1 (fun t=>T (P t).probabilityMeasure)
     l r t0 h Dmin cf Cf n hDmin hh hcf hCf hp hm hdens hpos hscore hsmall hsep
   have hclass : ∀t,t=t0+h ∨ t=t0-h→(P t).probabilityMeasure∈Cls := by
     intro t ht
     rcases ht with rfl | rfl
     · exact hplus
     · exact hminus
   constructor
   · unfold Model.minimaxRMSE
     apply le_iInf
     intro g
     obtain ⟨t,ht,_,hLp⟩ := hroot g.val g.property
     change ENNReal.ofReal (Dmin*h/4) ≤ eLpNorm (fun xs=>g.val xs-T (P t).probabilityMeasure) 2
       (Model.randomizedExperiment n (P t).probabilityMeasure) at hLp
     exact le_iSup_of_le (P t).probabilityMeasure (le_iSup_of_le (hclass t ht) hLp)
   · unfold Model.minimaxTail
     apply le_iInf
     intro g
     obtain ⟨t,ht,hTail,_⟩ := hroot g.val g.property
     change 1/4 ≤ (Model.randomizedExperiment n (P t).probabilityMeasure).real
       {xs | Dmin*h/2 ≤ |g.val xs-T (P t).probabilityMeasure|} at hTail
     have hENN := ENNReal.ofReal_le_of_le_toReal hTail
     norm_num only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_one,ENNReal.ofReal_ofNat] at hENN
     exact le_iSup_of_le (P t).probabilityMeasure (le_iSup_of_le (hclass t ht) hENN)

end RoughRegime.LowerMeasure
