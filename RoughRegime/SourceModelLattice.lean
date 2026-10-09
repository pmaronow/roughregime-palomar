module

public import RoughRegime.SourceNondegenerate
public import RoughRegime.SourceLiteralFrame


@[expose] public section
/-! The statistical hard-law family uses exactly the same fixed lattice setup
and actual frames as the literal source priors and separation theorems. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.LatticePriors.SourceModelFamily
set_option backward.isDefEq.respectTransparency false
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 def latticeSetup (F : SourceModelFamily A0 D O π) :
     SourceLatticeSetup D A0.α A0.β F.rminus F.rplus where
   alpha_pos := A0.hα
   beta_pos := A0.hβ
   lower_pos := F.interval.1
   lower_lt_one := F.interval.2.1
   one_lt_upper := F.interval.2.2
   v0 := F.volume
   volume_pos := F.volume_pos
   volume_le_half := F.volume_half
   denominator_pos := F.denominator_pos
   margin_pos := F.margin_pos

 theorem frame_eq_latticeSetup (F : SourceModelFamily A0 D O π)
     (N J M : ℕ) (hN : 0 < N) (m delta : ℝ) (hm : 0 < m) (hd : 0 < delta)
     (hmargin : delta≤F.margin) (hfine : m=sourceFineScale J (min A0.α A0.β)) :
     F.frame N J M hN m delta hm hd hmargin =
       F.latticeSetup.frame N J M hN F.epsilonU F.epsilonV delta
         F.epsilonU_pos.le F.epsilonV_pos.le hd hmargin := by
   subst m
   rfl

 theorem latticeSetup_volume (F : SourceModelFamily A0 D O π) : F.latticeSetup.v0=F.volume := rfl

end RoughRegime.LatticePriors.SourceModelFamily
