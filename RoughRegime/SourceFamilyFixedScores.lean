module

public import RoughRegime.SourceModelWeights


@[expose] public section
/-! The actual source family can retain any prescribed bounded measurable
scores with the proved residual moment identities. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.LatticePriors
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
 theorem source_model_family_fixed_scores (A0 : Model.Parameters) (D : ℕ)
     {Z : Type*} [MeasurableSpace Z] (O : Model.Observables Z (A0.withDimension D))
     (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate (A0.withDimension D) O π) :
     ∀ (S : Scores (π:Measure Z)),
     ((residualMomentU (A0.withDimension D) O π S true=1 ∧
       residualMomentU (A0.withDimension D) O π S false=0 ∧
       residualMomentV (A0.withDimension D) O π S true=0 ∧
       residualMomentV (A0.withDimension D) O π S false=1) ∨
      (O.U=O.V ∧ A0.α=A0.β ∧ S.su=S.sv ∧
       residualMomentU (A0.withDimension D) O π S true=1)) →
     ∃ F : SourceModelFamily A0 D O π, F.AllWeightsLocalized ∧ F.scores=S := by
   intro S hS
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
   · obtain ⟨epsilonU,epsilonV,c,heU,heU1,heV,heV1,hc,hclass⟩ := source_positive_smaller_weights
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
     refine ⟨F,?_,rfl⟩
     intro epsilonU' epsilonV' heU' heV' hleU hleV N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV
     exact hclass epsilonU' epsilonV' hleU hleV heU'.le heV'.le
       N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV
   · obtain ⟨epsilonU,epsilonV,c,heU,heU1,heV,heV1,hc,hclass⟩ := source_equal_exponent_smaller_weights
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
     refine ⟨F,?_,rfl⟩
     intro epsilonU' epsilonV' heU' heV' hleU hleV N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV
     exact hclass epsilonU' epsilonV' hleU hleV heU'.le heV'.le
       N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV

end RoughRegime.LatticePriors
