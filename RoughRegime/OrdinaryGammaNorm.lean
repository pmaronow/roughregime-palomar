module

public import RoughRegime.MarkRegrouping
public import RoughRegime.SourceCoefficients


@[expose] public section
/-! Lemma14(c) on the ordinary product domain of spatial-times-block marks,
for the literal coefficient defined under the genuine signed phase priors. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory
open RoughRegime.LatticeFourier RoughRegime.DyadicDigits RoughRegime.PoissonMeasure
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

 variable {J d j : ℕ}

 def splitSpatialMarks (xs : Fin (j + 2) → (Fin d → ℝ) × Bool) :
    ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin j → Fin d → ℝ) :=
  (((xs 0).1, (xs 1).1), fun k => (xs k.succ.succ).1)
 def spatialMarkLabels (xs : Fin (j + 2) → (Fin d → ℝ) × Bool) : Fin (j + 2) → Bool :=
  fun i => (xs i).2

 def ordinarySignedGamma (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ)
    (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ)
    (xs : Fin (j + 2) → (Fin d → ℝ) × Bool) : ℝ :=
  signedMarkedGamma U Q M γ η lam hQ hM hη hband Au Av bump
    (c (spatialMarkLabels xs)) (w (spatialMarkLabels xs)) (splitSpatialMarks xs)

 theorem ordinarySignedGamma_eq (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ)
    (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ)
    (xs : Fin (j + 2) → (Fin d → ℝ) × Bool) :
    ordinarySignedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w xs =
      markedGamma U Q M γ η lam hQ hM hη hband Au Av bump
        (c (spatialMarkLabels xs)) (w (spatialMarkLabels xs)) (splitSpatialMarks xs) :=
  signedMarkedGamma_eq U Q M γ η lam hQ hM hη hband Au Av bump _ _ _

 theorem ordinarySignedGamma_measurable (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ) (hbump : Continuous bump)
    (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ)
    (hc : ∀ labels k, Continuous (c labels k)) (hw : ∀ labels k, Continuous (w labels k)) :
    Measurable (ordinarySignedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w) := by
  let F := fun p : (Fin (j + 2) → Bool) × (((Fin d → ℝ) × (Fin d → ℝ)) × (Fin j → Fin d → ℝ)) =>
    markedGamma U Q M γ η lam hQ hM hη hband Au Av bump (c p.1) (w p.1) p.2
  have hF : Continuous F := by
    apply continuous_prod_of_discrete_left.mpr
    intro labels
    have hG := spatialLatticeGamma_continuous U Q M γ η lam hQ hM hη hband hγ hγ1
      (c labels) (w labels) (hc labels) (hw labels)
    unfold F markedGamma
    dsimp only
    exact (((continuous_const.mul continuous_const).mul (hbump.comp (continuous_fst.comp continuous_fst))).mul
      (hbump.comp (continuous_snd.comp continuous_fst))).mul (hG.comp continuous_snd)
  have hmaps : Measurable (fun xs : Fin (j + 2) → (Fin d → ℝ) × Bool =>
      (spatialMarkLabels xs, splitSpatialMarks xs)) := by
    unfold spatialMarkLabels splitSpatialMarks
    fun_prop
  have heq : ordinarySignedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w =
      fun xs => F (spatialMarkLabels xs, splitSpatialMarks xs) := by
    funext xs
    exact ordinarySignedGamma_eq U Q M γ η lam hQ hM hη hband Au Av bump c w xs
  rw [heq]
  exact hF.measurable.comp hmaps

 theorem ordinarySignedGamma_abs_bound (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ) (hbump : ∀ x, |bump x| ≤ 1)
    (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ labels k x φ θ, |phasedAngular (c labels k x) (w labels k x) φ θ| ≤ L)
    (xs : Fin (j + 2) → (Fin d → ℝ) × Bool) :
    |ordinarySignedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w xs| ≤
      2 * |Au| * |Av| * L ^ j := by
  rw [ordinarySignedGamma_eq]
  let z := splitSpatialMarks xs
  let labels := spatialMarkLabels xs
  have hG : |spatialLatticeGamma U Q M γ η lam hQ hM hη hband (c labels) (w labels) z.2| ≤ 2 * L ^ j :=
    latticeGamma_abs_bound Q M η lam hQ hM hη hband _ _ _ L hL (fun _ θ k => hb labels k (z.2 k) _ θ)
  change |Au * Av * bump z.1.1 * bump z.1.2 * _| ≤ _
  simp only [abs_mul]
  calc
    _ ≤ |Au| * |Av| * 1 * 1 * (2 * L ^ j) := by
      gcongr
      · exact hbump _
      · exact hbump _

    _ = 2 * |Au| * |Av| * L ^ j := by ring

 theorem ordinarySignedGamma_square_integrable (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ) (hbc : Continuous bump) (hbump : ∀ x, |bump x| ≤ 1)
    (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ)
    (hc : ∀ labels k, Continuous (c labels k)) (hw : ∀ labels k, Continuous (w labels k))
    (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ labels k x φ θ, |phasedAngular (c labels k x) (w labels k x) φ θ| ≤ L) :
    Integrable (fun xs => ordinarySignedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w xs ^ 2)
      (Measure.pi (fun _ : Fin (j + 2) => (cubeUniform d).prod (Measure.count : Measure Bool))) := by
  apply Integrable.of_bound
    ((ordinarySignedGamma_measurable U Q M γ η lam hQ hM hη hband hγ hγ1 Au Av bump hbc c w hc hw).pow_const 2).aestronglyMeasurable
    ((2 * |Au| * |Av| * L ^ j) ^ 2)
  apply Filter.Eventually.of_forall
  intro xs
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := ordinarySignedGamma_abs_bound U Q M γ η lam hQ hM hη hband Au Av bump hbump c w L hL hb xs
  have hC : 0 ≤ 2 * |Au| * |Av| * L ^ j := by positivity
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr h

 theorem ordinarySignedGamma_norm_eq (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ)
    (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ)
    (hf : Integrable (fun xs => ordinarySignedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w xs ^ 2)
      (Measure.pi (fun _ : Fin (j + 2) => (cubeUniform d).prod (Measure.count : Measure Bool)))) :
    (∫ xs, ordinarySignedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w xs ^ 2
      ∂Measure.pi (fun _ : Fin (j + 2) => (cubeUniform d).prod (Measure.count : Measure Bool))) =
      labeledGammaL2Squared U Q M γ η lam hQ hM hη hband Au Av bump c w := by
  rw [two_block_mark_regroup (cubeUniform d) j _ hf]
  unfold labeledGammaL2Squared markedSpatialMeasure
  apply Finset.sum_congr rfl
  intro labels _
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [ordinarySignedGamma_eq]
  have hlabels : spatialMarkLabels (fun i => (consTwo j z i, labels i)) = labels := rfl
  have hsplit : splitSpatialMarks (fun i => (consTwo j z i, labels i)) = z := by
    simp [splitSpatialMarks, consTwo]
  rw [hlabels, hsplit]

/-- The literal signed-prior coefficient, on the ordinary product mark domain,
with all source scales and centered-density bounds discharged. -/
 theorem ordinary_source_density_coefficient_bound (U : SmoothStep) (d Q : ℕ)
    (hd : 0 < d) (hQ : 1 ≤ Q) (gammaStar lambdaStar alpha0 s0 L p0 r0 h : ℝ)
    (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4)
    (hlam : 1 ≤ lambdaStar) (ha : 0 < alpha0) (hs0 : 0 < s0) (hL : 0 ≤ L)
    (outer : (Fin d → ℝ) → ℝ) (ho : Continuous outer)
    (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1)
    (hp : 0 ≤ p0 ∧ p0 ≤ L) (hh : 0 ≤ h) (hrlo : 0 ≤ r0 - h) (hrhi : r0 + h ≤ L) :
    ∃ CE : ℝ, 0 ≤ CE ∧ 1 ≤ gammaConstant L ∧
      ∀ (J M j : ℕ) (hM : 0 < M)
      (hmM : sourceFineScale J s0 ≤ sourceCStar Q gammaStar lambdaStar alpha0 * M)
      (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ) (hbc : Continuous bump) (hbump : ∀ x, |bump x| ≤ 1),
      (∫ xs, ordinarySignedGamma (j := j) U Q M (sourceGammas J d gammaStar)
        (sourceEtas J d gammaStar lambdaStar alpha0 s0) (sourceLambdas J d lambdaStar)
        hQ hM (sourceEtas_pos J d gammaStar lambdaStar alpha0 s0 hγ hlam)
        (sourceEtas_band J d Q M gammaStar lambdaStar alpha0 s0 hQ hγ hγ1 hlam ha hmM)
        Au Av bump (fun (_ : Fin (j + 2) → Bool) (_ : Fin j) => centeredZero p0 r0 outer)
        (fun (labels : Fin (j + 2) → Bool) (k : Fin j) => centeredWave h outer (labels k.succ.succ)) xs ^ 2
        ∂Measure.pi (fun _ : Fin (j + 2) => (cubeUniform d).prod (Measure.count : Measure Bool))) ≤
        if M ≤ j then gammaConstant L ^ (j + 1) * Au ^ 2 * Av ^ 2 * Real.exp (CE * M) *
          gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j else 0 := by
  obtain ⟨CE, hCE, hC, hbound⟩ := source_centered_density_coefficient_bound U d Q hd hQ
    gammaStar lambdaStar alpha0 s0 L p0 r0 h hγ hγ1 hlam ha hs0 hL outer ho ho0 ho1 hp hh hrlo hrhi
  refine ⟨CE, hCE, hC, ?_⟩
  intro J M j hM hmM Au Av bump hbc hbump
  let c := fun (_ : Fin (j + 2) → Bool) (_ : Fin j) => centeredZero p0 r0 outer
  let w := fun (labels : Fin (j + 2) → Bool) (k : Fin j) => centeredWave h outer (labels k.succ.succ)
  have hγs : ∀ q i, 0 < sourceGammas J d gammaStar q i := by
    intro q i
    unfold sourceGammas sourceGamma
    positivity
  have hγs1 : ∀ q i, sourceGammas J d gammaStar q i ≤ 1 / 4 :=
    fun q i => sourceGamma_le_quarter gammaStar i.val hγ hγ1
  have hi := ordinarySignedGamma_square_integrable U Q M (sourceGammas J d gammaStar)
    (sourceEtas J d gammaStar lambdaStar alpha0 s0) (sourceLambdas J d lambdaStar) hQ hM
    (sourceEtas_pos J d gammaStar lambdaStar alpha0 s0 hγ hlam)
    (sourceEtas_band J d Q M gammaStar lambdaStar alpha0 s0 hQ hγ hγ1 hlam ha hmM)
    hγs hγs1 Au Av bump hbc hbump c w
    (fun _ _ => centeredZero_continuous p0 r0 outer ho)
    (fun labels k => centeredWave_continuous h outer ho _)
    L hL (fun labels k x φ θ => centered_phasedAngular_bound p0 r0 h L outer ho0 ho1 hp hh hrlo hrhi
      (labels k.succ.succ) x φ θ)
  rw [ordinarySignedGamma_norm_eq U Q M (sourceGammas J d gammaStar)
    (sourceEtas J d gammaStar lambdaStar alpha0 s0) (sourceLambdas J d lambdaStar) hQ hM
    (sourceEtas_pos J d gammaStar lambdaStar alpha0 s0 hγ hlam)
    (sourceEtas_band J d Q M gammaStar lambdaStar alpha0 s0 hQ hγ hγ1 hlam ha hmM)
    Au Av bump c w hi]
  exact hbound J M j hM hmM Au Av bump hbump

 theorem ordinarySignedGamma_zero (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ)
    (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ)
    (hj : j < M) (xs : Fin (j + 2) → (Fin d → ℝ) × Bool) :
    ordinarySignedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w xs = 0 :=
  signedMarkedGamma_zero U Q M γ η lam hQ hM hη hband Au Av bump _ _ hj _

end RoughRegime.LatticePriors
