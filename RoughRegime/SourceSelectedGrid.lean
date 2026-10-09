module

public import RoughRegime.SourceDensityMargins
public import RoughRegime.ReductionAmplitudes


@[expose] public section
/-! The literal rounded grid from Proposition12 is the actual paired grid
used by the canonical source laws. It retains the original growing block
inflation and gives the stated sample-size amplitude envelopes. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales

 def selectedGridPairs (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ) : ℕ :=
   Nat.ceil (idealSideLength n (R n) (logResolution n θ τ c0) d/2)

 theorem selectedGridPairs_eq_half_evenCeiling (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ) :
     selectedGridPairs θ τ c0 R d n =
       evenCeiling (idealSideLength n (R n) (logResolution n θ τ c0) d)/2 := by
   unfold selectedGridPairs evenCeiling
   omega

 theorem selectedGridPairs_pos (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ)
     (hn : 0 < n) (hR : 0 < R n) : 0 < selectedGridPairs θ τ c0 R d n := by
   apply Nat.ceil_pos.mpr
   exact div_pos (idealSideLength_positive n (R n) _ d hn hR) (by norm_num)

 theorem selectedGrid_blockCount_eq (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ) :
     sourceGridCount (selectedGridPairs θ τ c0 R d n) d =
       (selectedBlockCount θ τ c0 R d n : ℝ) := by
   unfold sourceGridCount selectedGridPairs selectedBlockCount blockCount evenCeiling
   push_cast
   rfl

 theorem selectedBlockCount_eventually_ge_sample (θ τ c0 : ℝ)
     (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ)
     (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
     (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
     (d : ℕ) (hd : 0 < d) :
     ∀ᶠ n : ℝ in atTop, n ≤ (selectedBlockCount θ τ c0 R d n : ℝ) := by
   have he := (blockInflation_div_logPower_tendsto θ τ c0 0 hθ hθhalf hτ R hRpos hR d hd).eventually_ge_atTop 1
   filter_upwards [he,eventually_gt_atTop (0:ℝ)] with n hn hnp
   simp only [Real.rpow_zero,div_one,blockInflation] at hn
   simpa only [one_mul] using (le_div_iff₀ hnp).mp hn

 theorem sourceAmplitude_selected_le_sample (θ τ c0 : ℝ) (R : ℝ → ℝ)
     (n epsilon t m : ℝ) (J d : ℕ) (hn : 0 < n) (_hR : 0 < R n) (hd : 0 < d)
     (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (ht : 0 ≤ t)
     (hB : n ≤ (selectedBlockCount θ τ c0 R d n : ℝ))
     (hm : m ≤ (2:ℝ)^((J:ℝ)*t)) :
     sourceAmplitude epsilon (sourceGridCount (selectedGridPairs θ τ c0 R d n) d) J d t m ≤
       n^(-(t/(d:ℝ))) := by
   rw [selectedGrid_blockCount_eq]
   have hspace : 0 < sourceSpatialVolume J d := by unfold sourceSpatialVolume; positivity
   have hbudget : m ≤ (sourceSpatialVolume J d)^(t/(d:ℝ)) := by
     rwa [sourceSpatialVolume_rpow J d hd t]
   exact amplitude_le_sample epsilon _ _ _ m n he he1 hn hB hspace (by positivity) hbudget

 theorem eventually_selected_source_amplitudes_small (θ τ c0 epsilonU epsilonV t s c r : ℝ)
     (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ)
     (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
     (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
     (d : ℕ) (hd : 0 < d) (heU : 0 ≤ epsilonU) (heU1 : epsilonU ≤ 1)
     (heV : 0 ≤ epsilonV) (heV1 : epsilonV ≤ 1) (ht : 0 < t) (hs : 0 < s) (hc : 0 < c) (hr : 0 < r) :
     ∀ᶠ n : ℕ in atTop, ∀ J : ℕ, ∀ m : ℝ,
       m ≤ (2:ℝ)^((J:ℝ)*t) → m ≤ (2:ℝ)^((J:ℝ)*s) →
       sourceAmplitude epsilonU (sourceGridCount (selectedGridPairs θ τ c0 R d n) d) J d t m+
       sourceAmplitude epsilonV (sourceGridCount (selectedGridPairs θ τ c0 R d n) d) J d s m ≤
         c*min (sourceDensityMargin n) (min r 1) := by
   have hBt := selectedBlockCount_eventually_ge_sample θ τ c0 hθ hθhalf hτ R hRpos hR d hd
   have hBu := tendsto_natCast_atTop_atTop.eventually hBt
   have hRu := tendsto_natCast_atTop_atTop.eventually hRpos
   have hU := eventually_polynomial_le_sourceDensityMargin 1 (t/(d:ℝ)) (c/2) (by positivity) (by positivity)
   have hV := eventually_polynomial_le_sourceDensityMargin 1 (s/(d:ℝ)) (c/2) (by positivity) (by positivity)
   have hδr := sourceDensityMargin_tendsto.eventually (Iio_mem_nhds hr)
   have hδ1 := sourceDensityMargin_tendsto.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
   filter_upwards [hBu,hRu,hU,hV,hδr,hδ1,eventually_gt_atTop 1] with n hB hRn hUn hVn hmr hm1 hn
   intro J m hmU hmV
   have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
   have hRp : 0 < R n := zero_lt_one.trans_le hRn
   have hu := sourceAmplitude_selected_le_sample θ τ c0 R n epsilonU t m J d hn0 hRp hd heU heU1 ht.le hB hmU
   have hv := sourceAmplitude_selected_le_sample θ τ c0 R n epsilonV s m J d hn0 hRp hd heV heV1 hs.le hB hmV
   rw [min_eq_left (le_min hmr.le hm1.le)]
   have he := add_le_add (hu.trans (by simpa only [one_mul] using hUn))
     (hv.trans (by simpa only [one_mul] using hVn))
   convert he using 1 <;> ring

end RoughRegime.LatticePriors
