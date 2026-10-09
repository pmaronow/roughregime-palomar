module

public import RoughRegime.OddPriorMean


@[expose] public section
/-! Fubini bridges for actual spatially integrated nonlinear hard-prior targets. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

/-- Move the independent spatial integration into the latent space without
changing the actual continuous angle/sign experiment. -/
theorem spatial_target_fubini {H S X : Type*} [MeasurableSpace H]
    [MeasurableSpace S] [MeasurableSpace X]
    (ν : Measure H) (κ : Measure S) (μ : Measure X)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] [IsProbabilityMeasure μ]
    (g : (H × S) × X → ℝ) (hg : Measurable g)
    (B : ℝ) (hb : ∀ q, |g q| ≤ B) :
    (∫ q : H × S, ∫ x, g (q,x) ∂μ ∂ν.prod κ) =
      ∫ q : (X × H) × S, g ((q.1.2,q.2),q.1.1) ∂(μ.prod ν).prod κ := by
  have hi := bounded_integrable ((ν.prod κ).prod μ) g hg B hb
  have hgr : Measurable (fun q : (X × H) × S => g ((q.1.2,q.2),q.1.1)) :=
    hg.comp ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)
  have hir := bounded_integrable ((μ.prod ν).prod κ)
    (fun q : (X × H) × S => g ((q.1.2,q.2),q.1.1)) hgr B (fun q => hb _)
  rw [integral_integral_swap (f := fun q x => g (q,x)) hi, integral_prod _ hir,
    integral_prod _ hir.integral_prod_left]
  apply integral_congr_ae
  filter_upwards with x
  have hs := bounded_integrable (ν.prod κ) (fun q : H × S => g (q,x))
    (hg.comp (measurable_id.prodMk measurable_const)) B (fun q => hb _)
  exact integral_prod _ hs

def spatialResponseIntegrand {H X : Type*} (F : OddTaylor.Plane → ℝ)
    (p u v : (H × ℝ) × X → ℝ) (q : (H × (ℝ × (Bool × Bool))) × X) : ℝ :=
  p ((q.1.1,q.1.2.1),q.2)*
    F (Lower.sign q.1.2.2.1*u ((q.1.1,q.1.2.1),q.2),
       Lower.sign q.1.2.2.2*v ((q.1.1,q.1.2.1),q.2))

def spatialSignedTarget {H X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : OddTaylor.Plane → ℝ) (p u v : (H × ℝ) × X → ℝ)
    (q : H × (ℝ × (Bool × Bool))) : ℝ :=
  ∫ x, spatialResponseIntegrand F p u v (q,x) ∂μ

/-- Original spatial target priors satisfy the nonlinear mean remainder,
with the coefficient identified as the actual mixed derivative. The design
and phase/gate spaces may all be continuous. -/
theorem spatial_prior_target_taylor (F : OddTaylor.Plane → ℝ) (hmF : Measurable F)
    (hF : ContDiffAt ℝ 4 F (0 : OddTaylor.Plane)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
      (ν : Measure H) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
      (M : ℕ) (p u v : (H × ℝ) × X → ℝ)
      (_hp : Measurable p) (_hu : Measurable u) (_hv : Measurable v)
      (P Au Av : ℝ), 0 ≤ P → 0 ≤ Au → 0 ≤ Av → Au ≤ ε → Av ≤ ε →
      (∀ z, |p z| ≤ P) → (∀ z, |u z| ≤ Au) → (∀ z, |v z| ≤ Av) →
      |((∫ q, spatialSignedTarget μ F p u v q ∂ν.prod (LatticeFourier.angleSignLaw M true)) -
        (∫ q, spatialSignedTarget μ F p u v q ∂ν.prod (LatticeFourier.angleSignLaw M false))) -
        OddTaylor.mixedDerivative F 0*
          ((∫ q, spatialSignedTarget μ (fun x => x.1*x.2) p u v q ∂ν.prod (LatticeFourier.angleSignLaw M true)) -
           (∫ q, spatialSignedTarget μ (fun x => x.1*x.2) p u v q ∂ν.prod (LatticeFourier.angleSignLaw M false)))| ≤
        C*P*Au*Av*(Au^2+Av^2) := by
  obtain ⟨ε1,hε1,C,hC,hrem⟩ := native_target_taylor_error F hmF hF
  obtain ⟨ε2,hε2,_,_,B,hB,hlocal⟩ := local_oddOdd_taylor_and_bound F hF
  refine ⟨min ε1 ε2,lt_min hε1 hε2,C,hC,?_⟩
  intro H X _ _ ν μ _ _ M p u v hp hu hv P Au Av hP hAu hAv hAue hAve hpB huB hvB
  let p' : (X × H) × ℝ → ℝ := fun z => p ((z.1.2,z.2),z.1.1)
  let u' : (X × H) × ℝ → ℝ := fun z => u ((z.1.2,z.2),z.1.1)
  let v' : (X × H) × ℝ → ℝ := fun z => v ((z.1.2,z.2),z.1.1)
  have hp' : Measurable p' := hp.comp ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)
  have hu' : Measurable u' := hu.comp ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)
  have hv' : Measurable v' := hv.comp ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)
  have hsign (s : Bool) (x : ℝ) : |Lower.sign s*x| = |x| := by cases s <;> simp [Lower.sign]
  have hFb (z : (H × ℝ) × X) (s t : Bool) :
      |F (Lower.sign s*u z,Lower.sign t*v z)| ≤ B :=
    (hlocal _ _ (by rw [hsign]; exact (huB z).trans (hAue.trans (min_le_right _ _)))
      (by rw [hsign]; exact (hvB z).trans (hAve.trans (min_le_right _ _)))).2
  have hg : Measurable (spatialResponseIntegrand F p u v) := by
    have hs : Measurable Lower.sign := Measurable.of_discrete
    unfold spatialResponseIntegrand
    fun_prop
  have hgb (q : (H × (ℝ × (Bool × Bool))) × X) :
      |spatialResponseIntegrand F p u v q| ≤ P*B := by
    unfold spatialResponseIntegrand
    rw [abs_mul]
    exact mul_le_mul (hpB _) (hFb _ _ _) (abs_nonneg _) hP
  have hgm : Measurable (spatialResponseIntegrand (fun x => x.1*x.2) p u v) := by
    have hs : Measurable Lower.sign := Measurable.of_discrete
    unfold spatialResponseIntegrand
    fun_prop
  have hgmb (q : (H × (ℝ × (Bool × Bool))) × X) :
      |spatialResponseIntegrand (fun x => x.1*x.2) p u v q| ≤ P*Au*Av := by
    unfold spatialResponseIntegrand
    dsimp
    rw [abs_mul,abs_mul,hsign,hsign]
    have hh := mul_le_mul (hpB ((q.1.1,q.1.2.1),q.2))
      (mul_le_mul (huB ((q.1.1,q.1.2.1),q.2)) (hvB ((q.1.1,q.1.2.1),q.2)) (abs_nonneg _) hAu)
      (by positivity : 0 ≤ |u ((q.1.1,q.1.2.1),q.2)| * |v ((q.1.1,q.1.2.1),q.2)|) hP
    simpa only [mul_assoc] using hh
  have he (positive : Bool) :
      (∫ q, spatialSignedTarget μ F p u v q ∂ν.prod (LatticeFourier.angleSignLaw M positive)) =
      ∫ q, signedResponse F p' u' v' q ∂(μ.prod ν).prod (LatticeFourier.angleSignLaw M positive) := by
    exact spatial_target_fubini ν (LatticeFourier.angleSignLaw M positive) μ
      (spatialResponseIntegrand F p u v) hg (P*B) hgb
  have hem (positive : Bool) :
      (∫ q, spatialSignedTarget μ (fun x => x.1*x.2) p u v q ∂ν.prod (LatticeFourier.angleSignLaw M positive)) =
      ∫ q, signedResponse (fun x => x.1*x.2) p' u' v' q ∂(μ.prod ν).prod (LatticeFourier.angleSignLaw M positive) := by
    exact spatial_target_fubini ν (LatticeFourier.angleSignLaw M positive) μ
      (spatialResponseIntegrand (fun x => x.1*x.2) p u v) hgm (P*Au*Av) hgmb
  rw [he true,he false,hem true,hem false]
  exact hrem (μ.prod ν) M p' u' v' hp' hu' hv' P Au Av hP hAu hAv
    (hAue.trans (min_le_left _ _)) (hAve.trans (min_le_left _ _))
    (fun z => hpB _) (fun z => huB _) (fun z => hvB _)

end RoughRegime.PoissonMeasure
