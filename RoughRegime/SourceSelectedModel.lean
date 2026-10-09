module

public import RoughRegime.SourceNondegenerate
public import RoughRegime.SourceSelectedGrid


@[expose] public section
/-! Actual hard-law model admissibility along the paper's rounded block
sequence and its original logarithmically shrinking density margins. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.SpatialAffine RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false

 theorem eventually_selected_hard_laws {A0 : Model.Parameters} {D : ℕ}
     {Z : Type*} [MeasurableSpace Z] {O : Model.Observables Z (A0.withDimension D)}
     {π : ProbabilityMeasure Z} (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (θ τ c0 r : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) (hr : 0 < r)
     (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
     (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
     (J : ℕ → ℕ) (m : ℕ → ℝ)
     (hm0 : ∀ᶠ n in atTop, (2:ℝ)^((J n:ℝ)*sourceAlpha0 A0.α A0.β) ≤ m n)
     (hmU : ∀ᶠ n in atTop, m n ≤ (2:ℝ)^((J n:ℝ)*A0.α))
     (hmV : ∀ᶠ n in atTop, m n ≤ (2:ℝ)^((J n:ℝ)*A0.β)) :
     ∀ᶠ n : ℕ in atTop,
       ∃ (hN : 0 < selectedGridPairs θ τ c0 R (D+1) n) (hm : 0 < m n)
         (hd : 0 < sourceDensityMargin n) (hmargin : sourceDensityMargin n ≤ F.margin),
       let G := F.frame (selectedGridPairs θ τ c0 R (D+1) n) (J n) (frequency n θ τ)
         hN (m n) (sourceDensityMargin n) hm hd hmargin
       ∃ hsmall : (G.Au+G.Av)/F.rminus*F.scores.C ≤ 1/4,
       ∀ z : GridPair D (selectedGridPairs θ τ c0 R (D+1) n) → PairState (Fin (J n) × Fin (D+1)),
         (law F.scores (G.field z) hsmall).probabilityMeasure ∈ Model.localClass (A0.withDimension D) O π r ∧
         (∀ x, |G.u z x| ≤ (n:ℝ)^(-(A0.α/(D+1:ℕ)))/F.rminus) ∧
         (∀ x, |G.v z x| ≤ (n:ℝ)^(-(A0.β/(D+1:ℕ)))/F.rminus) := by
   have hamp := eventually_selected_source_amplitudes_small θ τ c0 F.epsilonU F.epsilonV A0.α A0.β F.threshold r
     hθ hθhalf hτ R hRpos hR (D+1) (Nat.succ_pos _) F.epsilonU_pos.le F.epsilonU_le
     F.epsilonV_pos.le F.epsilonV_le A0.hα A0.hβ F.threshold_pos hr
   have hmargin := sourceDensityMargin_tendsto.eventually (Iio_mem_nhds F.margin_pos)
   have hRu := tendsto_natCast_atTop_atTop.eventually hRpos
   have hBu := tendsto_natCast_atTop_atTop.eventually
     (selectedBlockCount_eventually_ge_sample θ τ c0 hθ hθhalf hτ R hRpos hR (D+1) (Nat.succ_pos _))
   filter_upwards [hamp,hmargin,hRu,hBu,hm0,hmU,hmV,eventually_gt_atTop 1] with n hampn hδn hRn hBn hm0n hmUn hmVn hn
   have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
   have hRp : 0 < R n := zero_lt_one.trans_le hRn
   have hN := selectedGridPairs_pos θ τ c0 R (D+1) n hn0 hRp
   have hm : 0 < m n := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm0n
   have hd := sourceDensityMargin_pos n hn
   have hδmargin : sourceDensityMargin n ≤ F.margin := hδn.le
   refine ⟨hN,hm,hd,hδmargin,?_⟩
   let G := F.frame (selectedGridPairs θ τ c0 R (D+1) n) (J n) (frequency n θ τ)
     hN (m n) (sourceDensityMargin n) hm hd hδmargin
   have hbound : G.Au+G.Av ≤ F.threshold*min (sourceDensityMargin n) (min r 1) := hampn (J n) (m n) hmUn hmVn
   obtain ⟨hsmall,hclass⟩ := hF _ _ _ hN _ _ _ hm hd hr.le hδmargin hm0n hmUn hmVn hbound
   refine ⟨hsmall,?_⟩
   intro z
   refine ⟨hclass z,?_,?_⟩
   · intro x
     have hu : G.Au ≤ (n:ℝ)^(-(A0.α/(D+1:ℕ))) := sourceAmplitude_selected_le_sample θ τ c0 R
       n F.epsilonU A0.α (m n) (J n) (D+1) hn0 hRp (Nat.succ_pos _) F.epsilonU_pos.le F.epsilonU_le A0.hα.le hBn hmUn
     exact ((G.realization z).u_bound x).trans (div_le_div_of_nonneg_right hu F.interval.1.le)
   · intro x
     have hv : G.Av ≤ (n:ℝ)^(-(A0.β/(D+1:ℕ))) := sourceAmplitude_selected_le_sample θ τ c0 R
       n F.epsilonV A0.β (m n) (J n) (D+1) hn0 hRp (Nat.succ_pos _) F.epsilonV_pos.le F.epsilonV_le A0.hβ.le hBn hmVn
     exact ((G.realization z).v_bound x).trans (div_le_div_of_nonneg_right hv F.interval.1.le)

end RoughRegime.LatticePriors.SourceModelFamily
