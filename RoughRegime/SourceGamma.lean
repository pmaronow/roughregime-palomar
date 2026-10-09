module

public import RoughRegime.MarkedGamma
public import RoughRegime.SourceBands


@[expose] public section
/-! Lemma 14(c) with the construction's literal level scales and uniform
constants, including the exact supremum-defined admissibility threshold. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory
open RoughRegime.LatticeFourier RoughRegime.DyadicDigits
open scoped BigOperators

 def sourceFineScale (J : ℕ) (s0 : ℝ) : ℝ := (2 : ℝ) ^ ((J : ℝ) * s0)
 def sourceGammas (J d : ℕ) (gammaStar : ℝ) : Fin d → Fin J → ℝ :=
  fun _ i => sourceGamma gammaStar i.val
 def sourceEtas (J d : ℕ) (gammaStar lambdaStar alpha0 s0 : ℝ) : Fin d × Fin J → ℝ :=
  fun qi => sourceEta gammaStar lambdaStar alpha0 (sourceFineScale J s0) qi.2.val
 def sourceLambdas (J d : ℕ) (lambdaStar : ℝ) : Fin d × Fin J → ℝ :=
  fun qi => sourceLambda lambdaStar qi.2.val

 theorem sourceEtas_pos (J d : ℕ) (gammaStar lambdaStar alpha0 s0 : ℝ)
    (hγ : 0 < gammaStar) (hlam : 1 ≤ lambdaStar) :
    ∀ qi, 0 < sourceEtas J d gammaStar lambdaStar alpha0 s0 qi :=
  fun qi => sourceEta_pos _ _ _ _ _ hγ (zero_lt_one.trans_le hlam) (Real.rpow_pos_of_pos (by norm_num) _)

 theorem sourceEtas_band (J d Q M : ℕ) (gammaStar lambdaStar alpha0 s0 : ℝ)
    (hQ : 1 ≤ Q) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4)
    (hlam : 1 ≤ lambdaStar) (ha : 0 < alpha0)
    (hmM : sourceFineScale J s0 ≤ sourceCStar Q gammaStar lambdaStar alpha0 * M) :
    ∀ qi, 4 * (6 * Q / sourceEtas J d gammaStar lambdaStar alpha0 s0 qi) ≤ (M : ℝ) :=
  fun qi => source_lattice_band _ _ _ _ _ _ hQ hγ hγ1 hlam ha (Real.rpow_pos_of_pos (by norm_num) _) hmM qi.2.val

/-- The actual marked coefficient bound, with constants independent of all
fine levels, lattice frequencies, amplitudes, label strings, and observations. -/
 theorem source_lattice_coefficient_bound (U : SmoothStep) (d Q : ℕ)
    (hd : 0 < d) (hQ : 1 ≤ Q) (gammaStar lambdaStar alpha0 s0 L : ℝ)
    (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4)
    (hlam : 1 ≤ lambdaStar) (ha : 0 < alpha0) (hs0 : 0 < s0) (hL : 0 ≤ L) :
    ∃ CE : ℝ, 0 ≤ CE ∧ 1 ≤ gammaConstant L ∧
      ∀ (J M j : ℕ) (hM : 0 < M)
      (hmM : sourceFineScale J s0 ≤ sourceCStar Q gammaStar lambdaStar alpha0 * M)
      (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ) (hbump : ∀ x, |bump x| ≤ 1)
      (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ),
      (∀ labels k, Continuous (c labels k)) → (∀ labels k, Continuous (w labels k)) →
      (∀ labels k x, |c labels k x| ≤ L) → (∀ labels k x, |w labels k x| ≤ L) →
      (∀ labels k x φ θ, |phasedAngular (c labels k x) (w labels k x) φ θ| ≤ L) →
      labeledGammaL2Squared U Q M (sourceGammas J d gammaStar)
        (sourceEtas J d gammaStar lambdaStar alpha0 s0) (sourceLambdas J d lambdaStar)
        hQ hM (sourceEtas_pos J d gammaStar lambdaStar alpha0 s0 hγ hlam)
        (sourceEtas_band J d Q M gammaStar lambdaStar alpha0 s0 hQ hγ hγ1 hlam ha hmM)
        Au Av bump c w ≤
        if M ≤ j then gammaConstant L ^ (j + 1) * Au ^ 2 * Av ^ 2 * Real.exp (CE * M) *
          gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j else 0 := by
  obtain ⟨CE, hCE, hbudget⟩ := source_spatialGamma_constants d Q hd gammaStar lambdaStar alpha0 s0
    hγ (zero_lt_one.trans_le hlam) ha hs0
  refine ⟨CE, hCE, gammaConstant_ge_one L, ?_⟩
  intro J M j hM hmM Au Av bump hbump c w hc hw hcL hwL hb
  have hmM' := source_scale_le_M Q M gammaStar lambdaStar alpha0 (sourceFineScale J s0)
    hQ hγ hγ1 hlam ha hmM
  exact labeledGamma_coefficient_bound U Q M _ _ _ hd hQ hM (by omega)
    (sourceEtas_pos J d gammaStar lambdaStar alpha0 s0 hγ hlam)
    (fun qi => sourceLambda_ge_one lambdaStar qi.2.val hlam)
    (sourceEtas_band J d Q M gammaStar lambdaStar alpha0 s0 hQ hγ hγ1 hlam ha hmM)
    (fun _q i => by unfold sourceGamma; positivity)
    (fun q i => sourceGamma_le_quarter gammaStar i.val hγ hγ1)
    Au Av bump hbump c w hc hw L CE hL hCE hcL hwL hb
    (fun k hk => hbudget J M k hmM' hk)

end RoughRegime.LatticePriors
