module

public import RoughRegime.WeightedJets
public import RoughRegime.ReciprocalComposition


@[expose] public section
/-! True jets of the phase and cutoff map used in reciprocal composition. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.LatticePriors
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def phaseInput (h θ : ℝ) (cut φ : E → ℝ) (x : E) : ℝ × (ℝ × ℝ) :=
  (h,(cut x,θ+φ x))

theorem phaseInput_contDiffAt (h θ : ℝ) (cut φ : E → ℝ) (x : E)
    (hc : ContDiffAt ℝ ∞ cut x) (hp : ContDiffAt ℝ ∞ φ x) :
    ContDiffAt ℝ ∞ (phaseInput h θ cut φ) x :=
  contDiffAt_const.prodMk (hc.prodMk (contDiffAt_const.add hp))

/-- True positive-order jets are exactly the cutoff and phase jets. -/
theorem norm_phaseInput_jet (h θ : ℝ) (cut φ : E → ℝ) (x : E) (k : ℕ)
    (hk : 0 < k) (hc : ContDiffAt ℝ ∞ cut x) (hp : ContDiffAt ℝ ∞ φ x) :
    ‖iteratedFDeriv ℝ k (phaseInput h θ cut φ) x‖ =
      max ‖iteratedFDeriv ℝ k cut x‖ ‖iteratedFDeriv ℝ k φ x‖ := by
  have he : iteratedFDeriv ℝ k (fun y => θ+φ y) x = iteratedFDeriv ℝ k φ x := by
    rw [show (fun y => θ+φ y) = (fun _ => θ) + φ from rfl,
      iteratedFDeriv_add_apply (contDiffAt_const) (hp.of_le (by simp)),
      iteratedFDeriv_const_of_ne hk.ne']
    simp
  unfold phaseInput
  rw [iteratedFDeriv_prodMk contDiffAt_const (hc.prodMk (contDiffAt_const.add hp)) (by simp),
    iteratedFDeriv_prodMk hc (contDiffAt_const.add hp) (by simp),
    iteratedFDeriv_const_of_ne hk.ne', he,
    ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
  simp only [Pi.zero_apply, norm_zero]
  exact max_eq_right (le_trans (norm_nonneg _) (le_max_left _ _))

/-- Inner jet differences are precisely phase jet differences; the density and
cutoff coordinates agree. -/
theorem norm_phaseInput_jet_difference (h θ : ℝ) (cut φ ψ : E → ℝ) (x : E) (k : ℕ)
    (hk : 0 < k) (hc : ContDiffAt ℝ ∞ cut x)
    (hp : ContDiffAt ℝ ∞ φ x) (hq : ContDiffAt ℝ ∞ ψ x) :
    ‖iteratedFDeriv ℝ k (phaseInput h θ cut φ) x -
      iteratedFDeriv ℝ k (phaseInput h θ cut ψ) x‖ =
      ‖iteratedFDeriv ℝ k φ x - iteratedFDeriv ℝ k ψ x‖ := by
  have he (f : E → ℝ) (hf : ContDiffAt ℝ ∞ f x) :
      iteratedFDeriv ℝ k (phaseInput h θ cut f) x =
      (0 : E [×k]→L[ℝ] ℝ).prod
        ((iteratedFDeriv ℝ k cut x).prod (iteratedFDeriv ℝ k f x)) := by
    have hθ : iteratedFDeriv ℝ k (fun y => θ+f y) x = iteratedFDeriv ℝ k f x := by
      rw [show (fun y => θ+f y) = (fun _ => θ) + f from rfl,
        iteratedFDeriv_add_apply contDiffAt_const (hf.of_le (by simp)), iteratedFDeriv_const_of_ne hk.ne']
      simp
    unfold phaseInput
    rw [iteratedFDeriv_prodMk contDiffAt_const (hc.prodMk (contDiffAt_const.add hf)) (by simp),
      iteratedFDeriv_prodMk hc (contDiffAt_const.add hf) (by simp), iteratedFDeriv_const_of_ne hk.ne', hθ]
    rfl
  rw [he φ hp,he ψ hq, ← ContinuousMultilinearMap.sub_prod_sub,
    ← ContinuousMultilinearMap.sub_prod_sub]
  simp only [sub_self, ContinuousMultilinearMap.opNorm_prod, norm_zero,
    max_eq_right (norm_nonneg _)]

end RoughRegime.LatticePriors
