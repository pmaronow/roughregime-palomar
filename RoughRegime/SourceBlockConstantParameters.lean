module

public import RoughRegime.SourceModelLattice
public import RoughRegime.BlockConstantReduction


@[expose] public section
/-! Actual J=0 source tuning uses the numerical reduction with R=m=1.
The comparison constants are fixed before all sample sizes and grids. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {pi : ProbabilityMeasure Z}

 def blockConstantParameters (F : SourceModelFamily A0 D O pi)
     (hrough : (A0.withDimension D).theta<1/2)
     (Cstar CG CE : ℝ) (hstar : 1 ≤ Cstar) (hCG : 1 ≤ CG) (hCE : 0 ≤ CE) : AbstractScaleParameters where
   d := D+1
   hd := Nat.succ_pos _
   a := A0.α/(D+1:ℕ)
   b := A0.β/(D+1:ℕ)
   lo := F.rminus
   hi := F.rplus
   v0 := F.volume
   epsilonU := F.epsilonU
   epsilonV := F.epsilonV
   Cstar := Cstar
   CΓ := CG
   CE := CE
   cstar := sourceBandConstant (D+1) A0.α A0.β
   c0 := 2+Real.log (2*F.volume*Cstar*CG)+CE
   ha := div_pos A0.hα (Nat.cast_pos.mpr (Nat.succ_pos _))
   hb := div_pos A0.hβ (Nat.cast_pos.mpr (Nat.succ_pos _))
   hhalf := by simpa only [←add_div,Model.Parameters.theta,Model.Parameters.withDimension] using hrough
   hlo := F.interval.1
   hlt := F.interval.2.1.trans F.interval.2.2
   hv := F.volume_pos
   hεu := F.epsilonU_pos
   hεu1 := F.epsilonU_le
   hεv := F.epsilonV_pos
   hεv1 := F.epsilonV_le
   hCstar := hstar
   hCΓ := hCG
   hCE := hCE
   hcstar := (sourceBandConstant_bounds (D+1) (Nat.succ_pos _) A0.α A0.β A0.hα A0.hβ).1
   hmargin := by linarith

 theorem blockConstantParameters_theta (F : SourceModelFamily A0 D O pi)
     (hrough : (A0.withDimension D).theta<1/2)
     (Cstar CG CE : ℝ) (hstar : 1 ≤ Cstar) (hCG : 1 ≤ CG) (hCE : 0 ≤ CE) :
     (F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE).theta=(A0.withDimension D).theta := by
   change A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=(A0.α+A0.β)/(D+1:ℕ)
   rw [add_div]

end RoughRegime.LatticePriors.SourceModelFamily
