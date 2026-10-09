module

public import RoughRegime.SourceDiagonalWeights
public import RoughRegime.SourceIntervals
public import RoughRegime.SpatialSourceScores
public import RoughRegime.SourceAnalyticParameters


@[expose] public section
/-! Actual source observation families derived from the original
nondegeneracy assumption, including both score branches. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.LatticePriors
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

structure SourceModelFamily (A0 : Model.Parameters) (D : ℕ) {Z : Type*} [MeasurableSpace Z]
    (O : Model.Observables Z (A0.withDimension D)) (π : ProbabilityMeasure Z) where
  nondegenerate : Model.Nondegenerate (A0.withDimension D) O π
  scores : Scores (π:Measure Z)
  score_case :
    (residualMomentU (A0.withDimension D) O π scores true=1 ∧
      residualMomentU (A0.withDimension D) O π scores false=0 ∧
      residualMomentV (A0.withDimension D) O π scores true=0 ∧
      residualMomentV (A0.withDimension D) O π scores false=1) ∨
    (O.U=O.V ∧ A0.α=A0.β ∧ scores.su=scores.sv ∧
      residualMomentU (A0.withDimension D) O π scores true=1)
  volume : ℝ
  volume_pos : 0 < volume
  volume_half : volume ≤ 1/2
  denominator_pos : 0 < 1-volume*sourceOuterIntegral (D+1)
  margin_pos : 0 < sourceMarginBound (D+1) volume
    (A0.gminus/Model.baselineW (A0.withDimension D) O π)
    (A0.gplus/Model.baselineW (A0.withDimension D) O π)
  epsilonU : ℝ
  epsilonV : ℝ
  threshold : ℝ
  epsilonU_pos : 0 < epsilonU
  epsilonU_le : epsilonU ≤ 1
  epsilonV_pos : 0 < epsilonV
  epsilonV_le : epsilonV ≤ 1
  threshold_pos : 0 < threshold

namespace SourceModelFamily
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
  {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 def rminus (F : SourceModelFamily A0 D O π) : ℝ := A0.gminus/Model.baselineW (A0.withDimension D) O π
 def rplus (F : SourceModelFamily A0 D O π) : ℝ := A0.gplus/Model.baselineW (A0.withDimension D) O π
 def margin (F : SourceModelFamily A0 D O π) : ℝ := sourceMarginBound (D+1) F.volume F.rminus F.rplus
 theorem interval (F : SourceModelFamily A0 D O π) : 0 < F.rminus ∧ F.rminus < 1 ∧ 1 < F.rplus := by
   have he := nondegenerate_source_interval (A0.withDimension D) O π F.nondegenerate
   exact ⟨he.1,he.2.1,he.2.2.1⟩

 def frame (F : SourceModelFamily A0 D O π) (N J M : ℕ) (hN : 0 < N) (m delta : ℝ)
     (hm : 0 < m) (hd : 0 < delta) (hmargin : delta ≤ F.margin) :
     CanonicalFrame D N (Fin J × Fin (D+1)) :=
   sourceCanonicalFrame D N J (sourceGateOrder A0.α A0.β) M hN
     (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) A0.α A0.β) (sourceAlpha0 A0.α A0.β) m
     F.epsilonU F.epsilonV A0.α A0.β F.volume F.rminus F.rplus delta
     (sourceGammaStar_bounds (D+1) (Nat.succ_pos _)).1
     (sourceGammaStar_bounds (D+1) (Nat.succ_pos _)).2.1 hm F.epsilonU_pos.le F.epsilonV_pos.le
     F.volume_pos (F.volume_half.trans (by norm_num)) F.interval.1
     (F.interval.2.1.trans F.interval.2.2) hd hmargin F.denominator_pos

 def Localized (F : SourceModelFamily A0 D O π) : Prop :=
   ∀ (N J M : ℕ) (hN : 0 < N) (m delta r : ℝ),
   ∀ (hm : 0 < m) (hd : 0 < delta) (hr : 0 ≤ r) (hmargin : delta ≤ F.margin),
   (2:ℝ)^((J:ℝ)*sourceAlpha0 A0.α A0.β) ≤ m →
   m ≤ (2:ℝ)^((J:ℝ)*A0.α) → m ≤ (2:ℝ)^((J:ℝ)*A0.β) →
   let G := F.frame N J M hN m delta hm hd hmargin
   G.Au+G.Av ≤ F.threshold*min delta (min r 1) →
   ∃ hsmall : (G.Au+G.Av)/F.rminus*F.scores.C ≤ 1/4,
   ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
     (law F.scores (G.field z) hsmall).probabilityMeasure ∈ Model.localClass (A0.withDimension D) O π r

end SourceModelFamily

 theorem nondegenerate_source_model_family (A0 : Model.Parameters) (D : ℕ)
     {Z : Type*} [MeasurableSpace Z] (O : Model.Observables Z (A0.withDimension D))
     (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate (A0.withDimension D) O π) :
     ∃ F : SourceModelFamily A0 D O π, F.Localized := by
   obtain ⟨S,hS⟩ := nondegenerate_exists_source_scores (A0.withDimension D) O π hnd
   obtain ⟨v0,hv,hvhalf,hden,hmargin⟩ := nondegenerate_source_volume (A0.withDimension D) O π hnd
   let rm := A0.gminus/Model.baselineW (A0.withDimension D) O π
   let rp := A0.gplus/Model.baselineW (A0.withDimension D) O π
   have hint := nondegenerate_source_interval (A0.withDimension D) O π hnd
   have hbase : A0.δ < Model.baselineW (A0.withDimension D) O π :=
     (le_max_left _ _).trans_lt hnd.2.1
   have hδg : A0.gminus ≤ Model.baselineW (A0.withDimension D) O π*rm ∧
       Model.baselineW (A0.withDimension D) O π*rp ≤ A0.gplus := ⟨hint.2.2.2.1.ge,hint.2.2.2.2.le⟩
   have hγ := sourceGammaStar_bounds (D+1) (Nat.succ_pos _)
   have hLambda : 0 < sourceLambdaStar (D+1) A0.α A0.β := zero_lt_one.trans_le (sourceLambdaStar_ge_one _ _ _)
   have ha0 := sourceAlpha0_pos A0.α A0.β A0.hα A0.hβ
   have hdata := source_analytic_parameter_budget A0.α A0.β A0.hα A0.hβ
   have hvol : v0 ≤ 1 := hvhalf.trans (by norm_num)
   have hlt : rm < rp := hint.2.1.trans hint.2.2.1
   rcases hS with hpos | hdiag
   · obtain ⟨epsilonU,epsilonV,c,heU,heU1,heV,heV1,hc,hclass⟩ := source_positive_fixed_weights
       A0 D (sourceGateOrder A0.α A0.β) (sourceJetBudget A0.α A0.β) O π S
       (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) A0.α A0.β) (sourceAlpha0 A0.α A0.β) v0 rm rp
       hγ.1 hγ.2.1 hLambda ha0.le hdata.2.1 hdata.2.2.2.2.2.1 hdata.2.2.2.2.2.2.1
       hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2.2.2.1 hdata.2.2.2.2.2.2.2.2
       hv hvol hint.1 hlt hden hbase hpos.2.1 hpos.2.2.1 hnd.2.2.2.1 hnd.2.2.2.2.1 hδg
     let F : SourceModelFamily A0 D O π := {
       nondegenerate := hnd
       scores := S
       score_case := Or.inl hpos
       volume := v0
       volume_pos := hv
       volume_half := hvhalf
       denominator_pos := hden
       margin_pos := hmargin
       epsilonU := epsilonU
       epsilonV := epsilonV
       threshold := c
       epsilonU_pos := heU
       epsilonU_le := heU1
       epsilonV_pos := heV
       epsilonV_le := heV1
       threshold_pos := hc }
     refine ⟨F,?_⟩
     intro N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV
     exact hclass heU.le heV.le N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV
   · obtain ⟨epsilonU,epsilonV,c,heU,heU1,heV,heV1,hc,hclass⟩ := source_equal_exponent_fixed_weights
       A0 D (sourceGateOrder A0.α A0.β) (sourceJetBudget A0.α A0.β) O π S
       (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) A0.α A0.β) (sourceAlpha0 A0.α A0.β) v0 rm rp
       hγ.1 hγ.2.1 hLambda ha0.le hdata.2.1 hdata.2.2.2.2.2.1 hdata.2.2.2.2.2.2.1
       hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2.2.2.1 hdata.2.2.2.2.2.2.2.2
       hv hvol hint.1 hlt hden hbase hdiag.2.1 hnd.2.2.2.1 hnd.2.2.2.2.1 hδg
     let F : SourceModelFamily A0 D O π := {
       nondegenerate := hnd
       scores := S
       score_case := Or.inr hdiag
       volume := v0
       volume_pos := hv
       volume_half := hvhalf
       denominator_pos := hden
       margin_pos := hmargin
       epsilonU := epsilonU
       epsilonV := epsilonV
       threshold := c
       epsilonU_pos := heU
       epsilonU_le := heU1
       epsilonV_pos := heV
       epsilonV_le := heV1
       threshold_pos := hc }
     refine ⟨F,?_⟩
     intro N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV
     exact hclass heU.le heV.le N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV

 theorem nondegenerate_source_model_family_all_dimensions (A : Model.Parameters)
     {Z : Type*} [MeasurableSpace Z] (O : Model.Observables Z A)
     (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate A O π) :
     ∃ D : ℕ, ∃ hA : A.withDimension D=A,
       ∃ F : SourceModelFamily A D (hA.symm ▸ O) π, F.Localized := by
   cases A with
   | mk d α β H δ gminus gplus M0 hd hα hβ hH hδ hgminus hgplus hM0 =>
     cases d with
     | zero => omega
     | succ D =>
       refine ⟨D,rfl,?_⟩
       exact nondegenerate_source_model_family
         (Model.Parameters.mk (D+1) α β H δ gminus gplus M0 hd hα hβ hH hδ hgminus hgplus hM0) D O π hnd

end RoughRegime.LatticePriors
