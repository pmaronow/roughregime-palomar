module

public import RoughRegime.SourceExtraConditions


@[expose] public section
/-! Actual simultaneous finite H/I/W membership along the original selected
source grid. Validity is stated explicitly and its eventual existence follows
from the independently proved selected model admissibility theorem. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace RoughRegime.LatticePriors
open RoughRegime.Localization RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false

namespace SourceModelFamily
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

structure SelectedValidity (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ) : Prop where
  positive_grid : 0 < selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n
  positive_multiplier : 0 < selectedSourceMultiplier A0 (D+1) θ τ n
  positive_margin : 0 < sourceDensityMargin n
  margin_le : sourceDensityMargin n ≤ F.margin

def selectedFrame (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ)
    (V : F.SelectedValidity θ τ c0 n) :
    CanonicalFrame D (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n)
      (Fin (selectedSourceLevel A0 (D+1) θ τ n)×Fin (D+1)) :=
  F.frame _ _ (frequency n θ τ) V.positive_grid (selectedSourceMultiplier A0 (D+1) θ τ n)
    (sourceDensityMargin n) V.positive_multiplier V.positive_margin V.margin_le

 theorem selectedValidity_eventually (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (θ τ c0 r : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) (hr : 0 < r) :
     ∀ᶠ n in atTop, Nonempty (F.SelectedValidity θ τ c0 n) := by
   filter_upwards [F.eventually_final_selected_hard_laws hF θ τ c0 r hθ hθhalf hτ hr] with n hn
   obtain ⟨hN,hm,hd,hmargin,_⟩ := hn
   exact ⟨⟨hN,hm,hd,hmargin⟩⟩

 def selectedAmplitudeEnvelope (A : Model.Parameters) (d : ℕ) (n : ℕ) : ℝ :=
   (n:ℝ)^(-(A.α/(d:ℝ)))+(n:ℝ)^(-(A.β/(d:ℝ)))

 theorem selectedAmplitudeEnvelope_nonneg (A : Model.Parameters) (d : ℕ) (n : ℕ) :
     0 ≤ selectedAmplitudeEnvelope A d n := by unfold selectedAmplitudeEnvelope; positivity

 theorem selectedAmplitudeEnvelope_tendsto (A : Model.Parameters) (d : ℕ) (hd : 0 < d) :
     Tendsto (selectedAmplitudeEnvelope A d) atTop (𝓝 0) := by
   have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
   have hu := (tendsto_rpow_neg_atTop (div_pos A.hα hdr)).comp tendsto_natCast_atTop_atTop
   have hv := (tendsto_rpow_neg_atTop (div_pos A.hβ hdr)).comp tendsto_natCast_atTop_atTop
   change Tendsto (fun n : ℕ => (n:ℝ)^(-(A.α/(d:ℝ)))+(n:ℝ)^(-(A.β/(d:ℝ)))) atTop (𝓝 0)
   simpa only [Function.comp_apply,zero_add] using hu.add hv

 theorem selectedAmplitudeEnvelope_div_margin_tendsto (A : Model.Parameters) (d : ℕ) (hd : 0 < d) :
     Tendsto (fun n => selectedAmplitudeEnvelope A d n/sourceDensityMargin n) atTop (𝓝 0) := by
   have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
   have hu := polynomial_div_sourceDensityMargin_tendsto (A.α/(d:ℝ)) (div_pos A.hα hdr)
   have hv := polynomial_div_sourceDensityMargin_tendsto (A.β/(d:ℝ)) (div_pos A.hβ hdr)
   simpa only [selectedAmplitudeEnvelope,add_div,zero_add] using hu.add hv

 theorem selectedFrame_amplitude_le_envelope (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) :
     ∀ᶠ n in atTop, ∀ V : F.SelectedValidity θ τ c0 n,
       (F.selectedFrame θ τ c0 n V).Au+(F.selectedFrame θ τ c0 n V).Av ≤
         selectedAmplitudeEnvelope A0 (D+1) n := by
   let R := selectedSourceVolume A0 (D+1) θ τ
   have hR : ∀ᶠ n : ℝ in atTop, 1 ≤ R n := Eventually.of_forall (selectedSourceVolume_ge_one A0 (D+1) θ τ)
   have hB := tendsto_natCast_atTop_atTop.eventually
     (selectedBlockCount_eventually_ge_sample θ τ c0 hθ hθhalf hτ R hR
       (selectedSourceVolume_log_isBigO A0 (D+1) (Nat.succ_pos _) θ τ hθ hθhalf hτ) (D+1) (Nat.succ_pos _))
   filter_upwards [hB,eventually_gt_atTop 1] with n hnB hn
   intro V
   have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
   have hRp : 0 < R n := zero_lt_one.trans_le (selectedSourceVolume_ge_one A0 (D+1) θ τ n)
   have hu := sourceAmplitude_selected_le_sample θ τ c0 R n F.epsilonU A0.α
     (selectedSourceMultiplier A0 (D+1) θ τ n) (selectedSourceLevel A0 (D+1) θ τ n) (D+1)
     hn0 hRp (Nat.succ_pos _) F.epsilonU_pos.le F.epsilonU_le A0.hα.le hnB
     (selectedSource_level_budgets A0 (D+1) θ τ n).2.1
   have hv := sourceAmplitude_selected_le_sample θ τ c0 R n F.epsilonV A0.β
     (selectedSourceMultiplier A0 (D+1) θ τ n) (selectedSourceLevel A0 (D+1) θ τ n) (D+1)
     hn0 hRp (Nat.succ_pos _) F.epsilonV_pos.le F.epsilonV_le A0.hβ.le hnB
     (selectedSource_level_budgets A0 (D+1) θ τ n).2.2
   exact add_le_add hu hv


 theorem exists_selected_extra_family (F : SourceModelFamily A0 D O π) (hF : F.AllWeightsLocalized)
     {ι : Type*} [Fintype ι] (e : ι→SourceExtraCondition A0.α A0.β)
     (hbase : ∀ i, (e i).condition.baselineAdmissible F.rminus F.rplus)
     (θ τ c0 r : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) (hr : 0 < r) :
     ∃ G : SourceModelFamily A0 D O π, G.Localized ∧ G.scores=F.scores ∧ G.volume=F.volume ∧
       G.threshold=F.threshold ∧
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
   refine ⟨G,hG,rfl,rfl,rfl,?_⟩
   filter_upwards [hmodel,hextra] with n hn hex
   obtain ⟨hN,hm,hd,hmargin,hsmall,hmodeln⟩ := hn
   let V : G.SelectedValidity θ τ c0 n := ⟨hN,hm,hd,hmargin⟩
   refine ⟨V,hsmall,?_⟩
   intro z
   exact ⟨(hmodeln z).1,hex V z⟩

end SourceModelFamily
end RoughRegime.LatticePriors
