module

public import RoughRegime.SourceUniversalExtras


@[expose] public section
/-! The finite-restriction construction also preserves any initially supplied
small construction budget. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace RoughRegime.LatticePriors
open RoughRegime.Localization RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
namespace SourceModelFamily
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}
 theorem exists_universal_selected_extra_family_bounded (F : SourceModelFamily A0 D O π) (hF : F.AllWeightsLocalized)
     {ι : Type*} [Fintype ι] (e : ι→SourceExtraCondition A0.α A0.β)
     (hbase : ∀ i, (e i).condition.baselineAdmissible F.rminus F.rplus)
     : ∃ G : SourceModelFamily A0 D O π, G.Localized ∧ G.epsilonU+G.epsilonV ≤ F.epsilonU+F.epsilonV ∧ G.scores=F.scores ∧ G.volume=F.volume ∧
       G.threshold=F.threshold ∧
       ∀ (θ τ c0 r : ℝ), 0 < θ → θ < 1/2 → 0 < τ → 0 < r →
       ∀ᶠ n in atTop, ∃ V : G.SelectedValidity θ τ c0 n,
         let B := G.selectedFrame θ τ c0 n V
         ∃ hsmall : (B.Au+B.Av)/G.rminus*G.scores.C ≤ 1/4,
           ∀ z : GridPair D (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n)→
             PairState (Fin (selectedSourceLevel A0 (D+1) θ τ n)×Fin (D+1)),
           (SpatialAffine.law G.scores (B.field z) hsmall).probabilityMeasure∈
             Model.localClass (A0.withDimension D) O π r ∧
           ∀ i, (e i).condition.Holds (B.field z).p (B.field z).u (B.field z).v := by
   choose eta cost heta hcost hbudget using (fun i => F.extra_condition_budget (e i) (hbase i))
   obtain ⟨cap,hcap,hcapcost⟩ := F.finite_extra_holder_cap e hbase cost
   let epsilonU := min F.epsilonU (cap/2)
   let epsilonV := min F.epsilonV (cap/2)
   have heU : 0 < epsilonU := lt_min F.epsilonU_pos (by positivity)
   have heV : 0 < epsilonV := lt_min F.epsilonV_pos (by positivity)
   have hleU : epsilonU ≤ F.epsilonU := min_le_left _ _
   have hleV : epsilonV ≤ F.epsilonV := min_le_left _ _
   let G := F.withWeights epsilonU epsilonV heU heV hleU hleV
   have hG : G.Localized := hF epsilonU epsilonV heU heV hleU hleV
   have hweight : epsilonU+epsilonV ≤ cap := by
     have hu : epsilonU ≤ cap/2 := min_le_right _ _
     have hv : epsilonV ≤ cap/2 := min_le_right _ _
     linarith
   have hbudgetcost (i : ι) : cost i*(epsilonU+epsilonV) ≤ (e i).condition.holderBudget :=
     (mul_le_mul_of_nonneg_left hweight (hcost i).le).trans (hcapcost i)
   refine ⟨G,hG,add_le_add hleU hleV,rfl,rfl,rfl,?_⟩
   intro θ τ c0 r hθ hθhalf hτ hr
   have hamp := G.selectedFrame_amplitude_le_envelope θ τ c0 hθ hθhalf hτ
   have ha0 := selectedAmplitudeEnvelope_tendsto A0 (D+1) (Nat.succ_pos _)
   have had := selectedAmplitudeEnvelope_div_margin_tendsto A0 (D+1) (Nat.succ_pos _)
   have hmodel := G.eventually_final_selected_hard_laws hG θ τ c0 r hθ hθhalf hτ hr
   have hextra : ∀ᶠ n in atTop, ∀ V : G.SelectedValidity θ τ c0 n, ∀ z i,
       (e i).condition.Holds ((G.selectedFrame θ τ c0 n V).field z).p
         ((G.selectedFrame θ τ c0 n V).field z).u ((G.selectedFrame θ τ c0 n V).field z).v := by
     suffices hh : ∀ᶠ n in atTop, ∀ i V z,
         (e i).condition.Holds ((G.selectedFrame θ τ c0 n V).field z).p
           ((G.selectedFrame θ τ c0 n V).field z).u ((G.selectedFrame θ τ c0 n V).field z).v by
       filter_upwards [hh] with n hn
       exact fun V z i => hn i V z
     apply eventually_all.mpr
     intro i
     cases hci : (e i).condition with
     | holder germ t H =>
       have hb := hbase i
       rw [hci] at hb
       have he := ha0.eventually_lt_const (heta i)
       filter_upwards [hamp,he] with n hn hneta
       intro V z
       have hsmall : (G.selectedFrame θ τ c0 n V).Au+(G.selectedFrame θ τ c0 n V).Av ≤ eta i :=
         (hn V).trans hneta.le
       have hmmin : selectedSourceMultiplier A0 (D+1) θ τ n ≤
           (2:ℝ)^((selectedSourceLevel A0 (D+1) θ τ n:ℝ)*min A0.α A0.β) := le_rfl
       have hh := hbudget i epsilonU epsilonV heU heV hleU hleV
         _ _ (frequency n θ τ) V.positive_grid _ _ V.positive_multiplier V.positive_margin V.margin_le
         (selectedSource_level_budgets A0 (D+1) θ τ n).1 hmmin hsmall z
       rw [hci] at hh
       apply holder_membership germ _ _ t H (cost i*(epsilonU+epsilonV)) hb.1
         (mul_nonneg (hcost i).le (add_nonneg heU.le heV.le)) hh.1 hh.2
       have hm := hbudgetcost i
       rw [hci] at hm
       change cost i*(epsilonU+epsilonV) ≤ H-|germ.baseline| at hm
       linarith
     | interval germ lo hi =>
       have hb := hbase i
       rw [hci] at hb
       obtain ⟨et,CS,het,hCS,hcontrol⟩ := canonical_germ_sup_control germ F.rminus F.interval.1
       have he := ha0.eventually_lt_const het
       have hCS0 : Tendsto (fun n => CS*selectedAmplitudeEnvelope A0 (D+1) n) atTop (𝓝 0) := by
         simpa only [mul_zero] using ha0.const_mul CS
       have hel := hCS0.eventually_lt_const (sub_pos.mpr hb.1)
       have heh := hCS0.eventually_lt_const (sub_pos.mpr hb.2)
       filter_upwards [hamp,he,hel,heh] with n hn hne hnl hnh
       intro V z
       let B := G.selectedFrame θ τ c0 n V
       have hBs : B.Au+B.Av ≤ et := (hn V).trans hne.le
       have hsup := (hcontrol D _ _ B rfl hBs z).1
       have hsup' (x) : |germ.K ((B.field z).u x,(B.field z).v x)-germ.baseline| ≤
           CS*selectedAmplitudeEnvelope A0 (D+1) n :=
         (hsup x).trans (mul_le_mul_of_nonneg_left (hn V) hCS.le)
       exact fun x _ => interval_membership _ germ.baseline lo hi _ hsup' hnl.le hnh.le x
     | weighted germ lo hi =>
       have hb := hbase i
       rw [hci] at hb
       obtain ⟨et,CS,het,hCS,hcontrol⟩ := canonical_germ_sup_control germ F.rminus F.interval.1
       have he := ha0.eventually_lt_const het
       have hrat : Tendsto (fun n => (F.rplus*CS)*(selectedAmplitudeEnvelope A0 (D+1) n/sourceDensityMargin n))
           atTop (𝓝 0) := by simpa only [mul_zero] using had.const_mul (F.rplus*CS)
       have hew := hrat.eventually_lt_const hb.1
       filter_upwards [hamp,he,hew] with n hn hne hnw
       intro V z
       let B := G.selectedFrame θ τ c0 n V
       have hBs : B.Au+B.Av ≤ et := (hn V).trans hne.le
       have hsup := (hcontrol D _ _ B rfl hBs z).1
       have hsup' (x) : |germ.K ((B.field z).u x,(B.field z).v x)-germ.baseline| ≤
           CS*selectedAmplitudeEnvelope A0 (D+1) n :=
         (hsup x).trans (mul_le_mul_of_nonneg_left (hn V) hCS.le)
       have hnum : F.rplus*(CS*selectedAmplitudeEnvelope A0 (D+1) n) ≤
           germ.baseline*sourceDensityMargin n := by
         have hh' : (F.rplus*CS*selectedAmplitudeEnvelope A0 (D+1) n)/sourceDensityMargin n ≤
             germ.baseline := by simpa only [mul_div_assoc] using hnw.le
         have hh := (div_le_iff₀ V.positive_margin).mp hh'
         convert hh using 1 <;> ring
       exact fun x _ => weighted_membership (B.field z).p
         (fun y => germ.K ((B.field z).u y,(B.field z).v y)) germ.baseline
         (CS*selectedAmplitudeEnvelope A0 (D+1) n) (sourceDensityMargin n) F.rminus F.rplus lo hi
         hb.1 (mul_nonneg hCS.le (selectedAmplitudeEnvelope_nonneg A0 (D+1) n)) F.interval.1.le
         V.positive_margin.le (B.realization z).margins hsup' hnum hb.2.1 hb.2.2 x
   filter_upwards [hmodel,hextra] with n hn hex
   obtain ⟨hN,hm,hd,hmargin,hsmall,hmodeln⟩ := hn
   let V : G.SelectedValidity θ τ c0 n := ⟨hN,hm,hd,hmargin⟩
   refine ⟨V,hsmall,?_⟩
   intro z
   exact ⟨(hmodeln z).1,hex V z⟩

 theorem AllWeightsLocalized.withWeights {F : SourceModelFamily A0 D O π}
     (hF : F.AllWeightsLocalized) (epsilonU epsilonV : ℝ)
     (heU : 0 < epsilonU) (heV : 0 < epsilonV)
     (hleU : epsilonU ≤ F.epsilonU) (hleV : epsilonV ≤ F.epsilonV) :
     (F.withWeights epsilonU epsilonV heU heV hleU hleV).AllWeightsLocalized := by
   intro eu ev heu hev hleu hlev
   exact hF eu ev heu hev (hleu.trans hleU) (hlev.trans hleV)

 theorem AllWeightsLocalized.capped_all {F : SourceModelFamily A0 D O π}
     (hF : F.AllWeightsLocalized) (cap : ℝ) (hcap : 0 < cap) :
     ∃ G : SourceModelFamily A0 D O π, G.AllWeightsLocalized ∧
       G.epsilonU+G.epsilonV ≤ cap ∧ G.scores=F.scores ∧
       G.volume=F.volume ∧ G.threshold=F.threshold := by
   let eu := min F.epsilonU (cap/2)
   let ev := min F.epsilonV (cap/2)
   have heu : 0 < eu := lt_min F.epsilonU_pos (by positivity)
   have hev : 0 < ev := lt_min F.epsilonV_pos (by positivity)
   have hleu : eu ≤ F.epsilonU := min_le_left _ _
   have hlev : ev ≤ F.epsilonV := min_le_left _ _
   refine ⟨F.withWeights eu ev heu hev hleu hlev,
     hF.withWeights eu ev heu hev hleu hlev,?_,rfl,rfl,rfl⟩
   change eu+ev ≤ cap
   have hu : eu ≤ cap/2 := min_le_right _ _
   have hv : ev ≤ cap/2 := min_le_right _ _
   linarith

end SourceModelFamily
end RoughRegime.LatticePriors
