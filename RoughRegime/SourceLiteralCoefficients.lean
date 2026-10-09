module

public import RoughRegime.SourceLiteralFrame
public import RoughRegime.SourceUniformGamma


@[expose] public section
/-! The literal signed density coefficient and its ordinary product L²
integral, uniformly before the shrinking margin and all resolutions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RoughRegime.LatticePriors.SourceLatticeSetup
open RoughRegime.DyadicDigits
set_option backward.isDefEq.respectTransparency false
variable {D : ℕ} {alpha beta rminus rplus : ℝ} (S : SourceLatticeSetup D alpha beta rminus rplus)

abbrev ordinaryGamma (J M j : ℕ) (delta Au Av : ℝ) (hM : 0<M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M) :
    (Fin (j+2) → (Fin (D+1) → ℝ) × Bool) → ℝ :=
  ordinarySignedGamma canonicalStep (sourceGateOrder alpha beta) M
    (sourceGammas J (D+1) (sourceGammaStar (D+1)))
    (sourceEtas J (D+1) (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta)
      (sourceAlpha0 alpha beta) (min alpha beta))
    (sourceLambdas J (D+1) (sourceLambdaStar (D+1) alpha beta))
    (by have:=S.Q_ge_three; omega) hM
    (sourceEtas_pos _ _ _ _ _ _ S.gamma_bounds.1 S.lambda_ge_one)
    (sourceEtas_band _ _ _ _ _ _ _ _ (by have:=S.Q_ge_three; omega) S.gamma_bounds.1
      S.gamma_bounds.2.1 S.lambda_ge_one S.alpha0_pos hscale)
    Au Av (fun x=>innerBump (D+1) (WithLp.toLp 2 x))
    (fun (_ : Fin (j+2) → Bool) (_ : Fin j)=>centeredZero
      (sourceFixedBaseline (D+1) S.v0 rminus rplus) ((rminus+rplus)/2)
      (fun x=>outerBump (D+1) (WithLp.toLp 2 x)))
    (fun (labels : Fin (j+2) → Bool) (k : Fin j)=>centeredWave ((rplus-rminus)/2-delta)
      (fun x=>outerBump (D+1) (WithLp.toLp 2 x)) (labels k.succ.succ))

def gammaL2Squared (J M j : ℕ) (delta Au Av : ℝ) (hM : 0<M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M) : ℝ :=
  ∫ xs, S.ordinaryGamma J M j delta Au Av hM hscale xs ^ 2
    ∂Measure.pi (fun _ : Fin (j+2)=>(cubeUniform (D+1)).prod (Measure.count : Measure Bool))

 theorem uniform_coefficient_bound : ∃ CE : ℝ, 0≤CE ∧ 1≤gammaConstant rplus ∧
     ∀ (J M j : ℕ) (delta Au Av : ℝ) (hM : 0<M)
       (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M),
       0<delta → delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus →
       S.gammaL2Squared J M j delta Au Av hM hscale ≤
         if M≤j then gammaConstant rplus ^ (j+1)*Au^2*Av^2*Real.exp (CE*M)*
           gammaSpatialFactor ((2:ℝ)^((D+1)*J)) M j else 0 := by
   obtain ⟨CE,hCE,hCG,hbound⟩ := uniform_ordinary_source_density_coefficient_bound canonicalStep
     (D+1) (sourceGateOrder alpha beta) (Nat.succ_pos _) (by have:=S.Q_ge_three; omega)
     (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta) (sourceAlpha0 alpha beta)
     (min alpha beta) rplus S.gamma_bounds.1 S.gamma_bounds.2.1 S.lambda_ge_one S.alpha0_pos
     (lt_min S.alpha_pos S.beta_pos) (S.lower_pos.le.trans S.interval.le)
   refine ⟨CE,hCE,hCG,?_⟩
   intro J M j delta Au Av hM hscale hd hmargin
   let outer := fun x : Fin (D+1) → ℝ=>outerBump (D+1) (WithLp.toLp 2 x)
   let inner := fun x : Fin (D+1) → ℝ=>innerBump (D+1) (WithLp.toLp 2 x)
   have ho : Continuous outer := (outerBump_smooth (D+1)).continuous.comp (PiLp.continuous_toLp 2 _)
   have hi : Continuous inner := (innerBump_smooth (D+1)).continuous.comp (PiLp.continuous_toLp 2 _)
   let p0 := sourceFixedBaseline (D+1) S.v0 rminus rplus
   have h0 : delta≤(p0-rminus)/2 := hmargin.trans ((min_le_right _ _).trans (min_le_left _ _))
   have h1 : delta≤(rplus-p0)/2 := hmargin.trans ((min_le_right _ _).trans (min_le_right _ _))
   have hr : delta≤(rplus-rminus)/4 := hmargin.trans (min_le_left _ _)
   have hp : 0≤p0 ∧ p0≤rplus := by have hl:=S.lower_pos; constructor <;> linarith
   have hh : 0≤(rplus-rminus)/2-delta := by linarith [S.interval]
   have hl : 0≤(rminus+rplus)/2-((rplus-rminus)/2-delta) := by have hlo:=S.lower_pos; linarith
   have hu : (rminus+rplus)/2+((rplus-rminus)/2-delta)≤rplus := by linarith
   exact hbound outer ho (fun _=>(outerBump (D+1)).nonneg) (fun _=>(outerBump (D+1)).le_one)
     p0 ((rminus+rplus)/2) ((rplus-rminus)/2-delta) hp hh hl hu J M j hM hscale
     Au Av inner hi (fun _=>by rw [abs_of_nonneg (innerBump (D+1)).nonneg]; exact (innerBump (D+1)).le_one)

end RoughRegime.LatticePriors.SourceLatticeSetup
