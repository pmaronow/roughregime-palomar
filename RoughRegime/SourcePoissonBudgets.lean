module

public import RoughRegime.SourceFinalScales


@[expose] public section
/-! The literal physical Poisson leading and remainder budget tends to zero
for the original rounded grid and the largest admissible source hierarchy. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales
set_option maxHeartbeats 800000

 def selectedSourceLambda (A : Model.Parameters) (d : ℕ) (θ τ c0 v0 n : ℝ) : ℝ :=
   2 * v0 / blockInflation θ τ c0 (selectedSourceVolume A d θ τ) d n
 def selectedSourceAmplitude (A : Model.Parameters) (d : ℕ) (θ τ c0 epsilon t n : ℝ) : ℝ :=
   amplitude epsilon (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n)
     (selectedSourceVolume A d θ τ n) (t/d) (selectedSourceMultiplier A d θ τ n)
 def selectedSourceRawI (A : Model.Parameters) (d : ℕ) (θ τ c0 v0 epsilonU epsilonV CE Cstar CΓ n : ℝ) : ℝ :=
   rawLeadingHardness n (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n) θ v0 (epsilonU*epsilonV)
     (selectedSourceVolume A d θ τ n) (selectedSourceMultiplier A d θ τ n) CE (2*v0*Cstar*CΓ) (frequency n θ τ)
 def selectedSourcePoissonMajorant (A : Model.Parameters) (d : ℕ)
     (θ τ c0 v0 epsilonU epsilonV CE Cstar CΓ n : ℝ) : ℝ :=
   Cstar*CΓ * selectedSourceRawI A d θ τ c0 v0 epsilonU epsilonV CE Cstar CΓ n *
     Real.exp (CΓ*Cstar*selectedSourceLambda A d θ τ c0 v0 n *
       (selectedSourceVolume A d θ τ n)^Real.sqrt (frequency n θ τ)) +
   selectedSourceRawI A d θ τ c0 v0 epsilonU epsilonV CE Cstar CΓ n *
     remainderRatio Cstar (selectedSourceLambda A d θ τ c0 v0 n)
       (selectedSourceAmplitude A d θ τ c0 epsilonU A.α n)
       (selectedSourceAmplitude A d θ τ c0 epsilonV A.β n)
       (selectedSourceVolume A d θ τ n) CE CΓ (frequency n θ τ)

 theorem selectedSourceRawI_eq_physical (A : Model.Parameters) (d : ℕ)
     (θ τ c0 v0 epsilonU epsilonV CE Cstar CΓ n : ℝ) (hn : 0 < n)
     (hab : A.α/d + A.β/d = θ) :
     selectedSourceRawI A d θ τ c0 v0 epsilonU epsilonV CE Cstar CΓ n =
       (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ) *
       (selectedSourceLambda A d θ τ c0 v0 n)^2 *
       (selectedSourceAmplitude A d θ τ c0 epsilonU A.α n)^2 *
       (selectedSourceAmplitude A d θ τ c0 epsilonV A.β n)^2 *
       (selectedSourceVolume A d θ τ n)^(1 - (frequency n θ τ : ℝ)) * Real.exp (CE * frequency n θ τ) *
       (Cstar*CΓ*selectedSourceLambda A d θ τ c0 v0 n)^(frequency n θ τ) / (frequency n θ τ).factorial := by
   let B : ℝ := selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n
   let R := selectedSourceVolume A d θ τ n
   let m := selectedSourceMultiplier A d θ τ n
   have hR : 0 < R := zero_lt_one.trans_le (selectedSourceVolume_ge_one A d θ τ n)
   have hB : 0 < B := by
     dsimp [B,selectedBlockCount]
     exact_mod_cast blockCount_positive n R (logResolution n θ τ c0) d hn hR
   have hΛ : selectedSourceLambda A d θ τ c0 v0 n = 2*v0*n/B := by
     unfold selectedSourceLambda blockInflation
     rw [div_div_eq_mul_div]
   have hy : Cstar*CΓ*(2*v0*n/B) = (2*v0*Cstar*CΓ)*n/B := by ring
   rw [hΛ,hy]
   have hraw := rawLeadingHardness_eq n B θ v0 (epsilonU*epsilonV) R m CE (2*v0*Cstar*CΓ)
     (frequency n θ τ) hn hB hR
   have hamp := rawLeadingHardness_amplitudes_eq n B (A.α/d) (A.β/d) θ v0 epsilonU epsilonV R m CE
     (2*v0*Cstar*CΓ) (frequency n θ τ) hn hB hR hab
   exact hraw.trans (hamp.symm.trans (by dsimp [selectedSourceAmplitude]; ring))

 theorem selectedSourcePoissonMajorant_tendsto_zero (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ c0 v0 epsilonU epsilonV CE Cstar CΓ : ℝ)
     (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) (hv : 0 < v0)
     (hεu : 0 < epsilonU) (hεu1 : epsilonU ≤ 1) (hεv : 0 < epsilonV) (hεv1 : epsilonV ≤ 1)
     (hCE : 0 ≤ CE) (hCstar : 1 ≤ Cstar) (hCΓ : 1 ≤ CΓ)
     (hmargin : 1 + Real.log (2*v0*Cstar*CΓ) + CE < c0) :
     Tendsto (selectedSourcePoissonMajorant A d θ τ c0 v0 epsilonU epsilonV CE Cstar CΓ) atTop (nhds 0) := by
   have hCp : 0 < Cstar := zero_lt_one.trans_le hCstar
   have hΓp : 0 < CΓ := zero_lt_one.trans_le hCΓ
   have hC1 : 0 < 2*v0*Cstar*CΓ := by positivity
   have heps : epsilonU*epsilonV ≤ 1 := by
     calc
       _ ≤ 1*1 := mul_le_mul hεu1 hεv1 hεv.le (by norm_num)
       _ = _ := by norm_num
   have hI := selectedSource_rawHardness_tendsto_zero A d hd θ τ c0 v0 (epsilonU*epsilonV) CE (2*v0*Cstar*CΓ)
     hθ hθhalf hτ hv (mul_pos hεu hεv) heps hC1 hmargin
   have hrem := selectedSource_remainderRatio_tendsto_zero A d hd θ τ c0 epsilonU epsilonV Cstar v0 CE CΓ
     hθ hθhalf hτ hεu hεu1 hεv hεv1 hCp.le hv hCE hCΓ
   have ht := selectedSource_poisson_tail_budget_tendsto_zero A d hd θ τ c0 (2*v0*Cstar*CΓ)
     hθ hθhalf hτ hC1
   have ht' : Tendsto (fun n : ℝ => CΓ*Cstar*selectedSourceLambda A d θ τ c0 v0 n *
       (selectedSourceVolume A d θ τ n)^Real.sqrt (frequency n θ τ)) atTop (nhds 0) := by
     apply Filter.Tendsto.congr' _ ht
     exact Eventually.of_forall (fun n => by unfold selectedSourceLambda; ring)
   have hexp := Real.continuous_exp.continuousAt.tendsto.comp ht'
   simp only [Real.exp_zero] at hexp
   have hfirst := (hI.mul hexp).const_mul (Cstar*CΓ)
   have hsecond := hI.mul hrem
   simp only [zero_mul,mul_zero] at hfirst hsecond
   have hsum := hfirst.add hsecond
   simp only [zero_add] at hsum
   apply Filter.Tendsto.congr' _ hsum
   exact Eventually.of_forall (fun n => by
     simp only [Function.comp_apply]
     unfold selectedSourcePoissonMajorant selectedSourceRawI selectedSourceLambda selectedSourceAmplitude
     ring)

end RoughRegime.LatticePriors
