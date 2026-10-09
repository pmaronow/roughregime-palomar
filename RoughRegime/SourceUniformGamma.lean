module

public import RoughRegime.OrdinaryGammaNorm


@[expose] public section
/-! A single coefficient constant before every centered density parameter.
This quantifier order includes the shrinking density margin of Lemma14. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory
open RoughRegime.DyadicDigits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

 theorem uniform_ordinary_source_density_coefficient_bound (U : SmoothStep) (d Q : ℕ)
    (hd : 0 < d) (hQ : 1 ≤ Q) (gammaStar lambdaStar alpha0 s0 L : ℝ)
    (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4)
    (hlam : 1 ≤ lambdaStar) (ha : 0 < alpha0) (hs0 : 0 < s0) (hL : 0 ≤ L) :
    ∃ CE : ℝ, 0 ≤ CE ∧ 1 ≤ gammaConstant L ∧
      ∀ (outer : (Fin d → ℝ) → ℝ), Continuous outer →
      (∀ x, 0 ≤ outer x) → (∀ x, outer x ≤ 1) →
      ∀ (p0 r0 h : ℝ), (0 ≤ p0 ∧ p0 ≤ L) → 0 ≤ h → 0 ≤ r0-h → r0+h ≤ L →
      ∀ (J M j : ℕ) (hM : 0 < M)
      (hmM : sourceFineScale J s0 ≤ sourceCStar Q gammaStar lambdaStar alpha0 * M)
      (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ), Continuous bump → (∀ x, |bump x| ≤ 1) →
      (∫ xs, ordinarySignedGamma (j := j) U Q M (sourceGammas J d gammaStar)
        (sourceEtas J d gammaStar lambdaStar alpha0 s0) (sourceLambdas J d lambdaStar)
        hQ hM (sourceEtas_pos J d gammaStar lambdaStar alpha0 s0 hγ hlam)
        (sourceEtas_band J d Q M gammaStar lambdaStar alpha0 s0 hQ hγ hγ1 hlam ha hmM)
        Au Av bump (fun (_ : Fin (j+2) → Bool) (_ : Fin j) => centeredZero p0 r0 outer)
        (fun (labels : Fin (j+2) → Bool) (k : Fin j) => centeredWave h outer (labels k.succ.succ)) xs ^ 2
        ∂Measure.pi (fun _ : Fin (j+2) => (cubeUniform d).prod (Measure.count : Measure Bool))) ≤
        if M ≤ j then gammaConstant L ^ (j+1) * Au^2 * Av^2 * Real.exp (CE*M) *
          gammaSpatialFactor ((2 : ℝ)^(d*J)) M j else 0 := by
  obtain ⟨CE,hCE,hC,hbound⟩ := source_lattice_coefficient_bound U d Q hd hQ
    gammaStar lambdaStar alpha0 s0 L hγ hγ1 hlam ha hs0 hL
  refine ⟨CE,hCE,hC,?_⟩
  intro outer ho ho0 ho1 p0 r0 h hp hh hrlo hrhi J M j hM hmM Au Av bump hbc hbump
  let c := fun (_ : Fin (j+2) → Bool) (_ : Fin j) => centeredZero p0 r0 outer
  let w := fun (labels : Fin (j+2) → Bool) (k : Fin j) => centeredWave h outer (labels k.succ.succ)
  have hγs : ∀ q i, 0 < sourceGammas J d gammaStar q i := by
    intro q i; unfold sourceGammas sourceGamma; positivity
  have hγs1 : ∀ q i, sourceGammas J d gammaStar q i ≤ 1/4 :=
    fun q i => sourceGamma_le_quarter gammaStar i.val hγ hγ1
  have hc : ∀ labels k, Continuous (c labels k) := fun _ _ => centeredZero_continuous p0 r0 outer ho
  have hw : ∀ labels k, Continuous (w labels k) := fun labels k => centeredWave_continuous h outer ho _
  have hcL : ∀ labels k x, |c labels k x| ≤ L := fun _ _ x =>
    (centered_coefficients_bounds p0 r0 h L outer ho0 ho1 hp hh hrlo hrhi false x).1
  have hwL : ∀ labels k x, |w labels k x| ≤ L := fun labels k x =>
    (centered_coefficients_bounds p0 r0 h L outer ho0 ho1 hp hh hrlo hrhi (labels k.succ.succ) x).2
  have hph : ∀ labels k x φ θ, |phasedAngular (c labels k x) (w labels k x) φ θ| ≤ L :=
    fun labels k x φ θ => centered_phasedAngular_bound p0 r0 h L outer ho0 ho1 hp hh hrlo hrhi
      (labels k.succ.succ) x φ θ
  have hi := ordinarySignedGamma_square_integrable U Q M (sourceGammas J d gammaStar)
    (sourceEtas J d gammaStar lambdaStar alpha0 s0) (sourceLambdas J d lambdaStar) hQ hM
    (sourceEtas_pos J d gammaStar lambdaStar alpha0 s0 hγ hlam)
    (sourceEtas_band J d Q M gammaStar lambdaStar alpha0 s0 hQ hγ hγ1 hlam ha hmM)
    hγs hγs1 Au Av bump hbc hbump c w hc hw L hL hph
  rw [ordinarySignedGamma_norm_eq U Q M (sourceGammas J d gammaStar)
    (sourceEtas J d gammaStar lambdaStar alpha0 s0) (sourceLambdas J d lambdaStar) hQ hM
    (sourceEtas_pos J d gammaStar lambdaStar alpha0 s0 hγ hlam)
    (sourceEtas_band J d Q M gammaStar lambdaStar alpha0 s0 hQ hγ hγ1 hlam ha hmM)
    Au Av bump c w hi]
  exact hbound J M j hM hmM Au Av bump hbump c w hc hw hcL hwL hph

end RoughRegime.LatticePriors
