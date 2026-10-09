module

public import RoughRegime.SourceSmallerWeights


@[expose] public section
/-! A single actual score/design family with arbitrarily smaller positive
construction weights. This keeps the score functions and design volume fixed
when finite additional smooth-germ restrictions are imposed. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.LatticePriors
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

namespace SourceModelFamily
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

def withWeights (F : SourceModelFamily A0 D O π) (epsilonU epsilonV : ℝ)
    (heU : 0 < epsilonU) (heV : 0 < epsilonV)
    (hleU : epsilonU ≤ F.epsilonU) (hleV : epsilonV ≤ F.epsilonV) : SourceModelFamily A0 D O π :=
  { F with
    epsilonU := epsilonU
    epsilonV := epsilonV
    epsilonU_pos := heU
    epsilonV_pos := heV
    epsilonU_le := hleU.trans F.epsilonU_le
    epsilonV_le := hleV.trans F.epsilonV_le }

def AllWeightsLocalized (F : SourceModelFamily A0 D O π) : Prop :=
  ∀ (epsilonU epsilonV : ℝ) (heU : 0 < epsilonU) (heV : 0 < epsilonV)
    (hleU : epsilonU ≤ F.epsilonU) (hleV : epsilonV ≤ F.epsilonV),
      (F.withWeights epsilonU epsilonV heU heV hleU hleV).Localized

theorem AllWeightsLocalized.localized {F : SourceModelFamily A0 D O π}
    (hF : F.AllWeightsLocalized) : F.Localized := by
  exact hF F.epsilonU F.epsilonV F.epsilonU_pos F.epsilonV_pos le_rfl le_rfl

/-- Arbitrary finite smoothness budgets can be met without changing the
actual baseline scores, design volume, or localization threshold. -/
theorem AllWeightsLocalized.capped {F : SourceModelFamily A0 D O π}
    (hF : F.AllWeightsLocalized) (cap : ℝ) (hcap : 0 < cap) :
    ∃ G : SourceModelFamily A0 D O π, G.Localized ∧ G.epsilonU + G.epsilonV ≤ cap ∧
      G.scores = F.scores ∧ G.volume = F.volume ∧ G.threshold = F.threshold := by
  let epsilonU := min F.epsilonU (cap / 2)
  let epsilonV := min F.epsilonV (cap / 2)
  have heU : 0 < epsilonU := lt_min F.epsilonU_pos (by positivity)
  have heV : 0 < epsilonV := lt_min F.epsilonV_pos (by positivity)
  have hleU : epsilonU ≤ F.epsilonU := min_le_left _ _
  have hleV : epsilonV ≤ F.epsilonV := min_le_left _ _
  let G := F.withWeights epsilonU epsilonV heU heV hleU hleV
  refine ⟨G, hF epsilonU epsilonV heU heV hleU hleV, ?_, rfl, rfl, rfl⟩
  change epsilonU + epsilonV ≤ cap
  calc
    epsilonU + epsilonV ≤ cap / 2 + cap / 2 := add_le_add (min_le_right _ _) (min_le_right _ _)
    _ = cap := by ring

end SourceModelFamily

 theorem nondegenerate_source_model_family_smaller (A0 : Model.Parameters) (D : ℕ)
     {Z : Type*} [MeasurableSpace Z] (O : Model.Observables Z (A0.withDimension D))
     (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate (A0.withDimension D) O π) :
     ∃ F : SourceModelFamily A0 D O π, F.AllWeightsLocalized := by
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
     refine ⟨F,?_⟩
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
     refine ⟨F,?_⟩
     intro epsilonU' epsilonV' heU' heV' hleU hleV N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV
     exact hclass epsilonU' epsilonV' hleU hleV heU'.le heV'.le
       N J M hN m delta r hm hd hr hdmargin hm0 hmU hmV


theorem nondegenerate_source_model_family_capped (A0 : Model.Parameters) (D : ℕ)
    {Z : Type*} [MeasurableSpace Z] (O : Model.Observables Z (A0.withDimension D))
    (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate (A0.withDimension D) O π)
    (cap : ℝ) (hcap : 0 < cap) :
    ∃ F : SourceModelFamily A0 D O π, F.Localized ∧ F.epsilonU + F.epsilonV ≤ cap := by
  obtain ⟨F, hF⟩ := nondegenerate_source_model_family_smaller A0 D O π hnd
  obtain ⟨G, hG, hcapG, _⟩ := hF.capped cap hcap
  exact ⟨G, hG, hcapG⟩

end RoughRegime.LatticePriors
