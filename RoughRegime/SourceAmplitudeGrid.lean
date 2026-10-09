module

public import RoughRegime.SourceGrid


@[expose] public section
/-! Uniform sup-amplitude decay of the actual source profiles in the number
of blocks, independent of the hierarchical resolution. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.LatticePriors

 theorem sourceAmplitude_grid_le (epsilon : ℝ) (N J d : ℕ) (t m : ℝ)
     (he : 0 ≤ epsilon) (hN : 0 < N) (hd : 0 < d) (_hm : 0 ≤ m)
     (hbudget : m ≤ (2:ℝ)^((J:ℝ)*t)) :
     sourceAmplitude epsilon (sourceGridCount N d) J d t m ≤ epsilon*(2*(N:ℝ))^(-t) := by
   have hn : 0 < 2*(N:ℝ) := by positivity
   have hB := sourceGridCount_pos N d hN
   have hR : 0 < sourceSpatialVolume J d := by unfold sourceSpatialVolume; positivity
   have hg : (sourceGridCount N d)^(-(t/(d:ℝ))) = (2*(N:ℝ))^(-t) := by
     unfold sourceGridCount
     rw [← Real.rpow_natCast_mul hn.le]
     congr 1
     field_simp
   have hr : (sourceSpatialVolume J d)^(-(t/(d:ℝ))) = ((2:ℝ)^((J:ℝ)*t))⁻¹ := by
     rw [Real.rpow_neg hR.le,sourceSpatialVolume_rpow J d hd t]
   have hF : 0 < (2:ℝ)^((J:ℝ)*t) := by positivity
   unfold sourceAmplitude
   rw [Real.mul_rpow hB.le hR.le,hg,hr]
   have heq : epsilon*((2*(N:ℝ))^(-t)*((2:ℝ)^((J:ℝ)*t))⁻¹)*m =
       (epsilon*(2*(N:ℝ))^(-t))*(m/((2:ℝ)^((J:ℝ)*t))) := by ring
   rw [heq]
   have hratio := (div_le_one hF).mpr hbudget
   simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ epsilon*(2*(N:ℝ))^(-t))

 theorem source_grid_amplitude_bound_tendsto (epsilon t : ℝ) (ht : 0 < t) :
     Tendsto (fun N : ℕ => epsilon*(2*(N:ℝ))^(-t)) atTop (𝓝 0) := by
   have hn : Tendsto (fun N : ℕ => 2*(N:ℝ)) atTop atTop :=
     tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
   simpa only [mul_zero,Function.comp_apply] using (tendsto_rpow_neg_atTop ht).comp hn |>.const_mul epsilon

 theorem source_grid_two_amplitudes_tendsto (epsilonU epsilonV t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
     Tendsto (fun N : ℕ => epsilonU*(2*(N:ℝ))^(-t)+epsilonV*(2*(N:ℝ))^(-s)) atTop (𝓝 0) := by
   simpa only [add_zero] using (source_grid_amplitude_bound_tendsto epsilonU t ht).add
     (source_grid_amplitude_bound_tendsto epsilonV s hs)

 theorem eventually_source_totalAmplitude_small (epsilonU epsilonV t s c delta r : ℝ)
     (d : ℕ) (hd : 0 < d) (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV)
     (ht : 0 < t) (hs : 0 < s) (hc : 0 < c) (hδ : 0 < delta) (hr : 0 < r) :
     ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ J : ℕ, ∀ m : ℝ, 0 ≤ m →
       m ≤ (2:ℝ)^((J:ℝ)*t) → m ≤ (2:ℝ)^((J:ℝ)*s) →
       sourceAmplitude epsilonU (sourceGridCount N d) J d t m+
         sourceAmplitude epsilonV (sourceGridCount N d) J d s m ≤ c*min delta (min r 1) := by
   have hbound : 0 < c*min delta (min r 1) :=
     mul_pos hc (lt_min hδ (lt_min hr (by norm_num)))
   have he := (source_grid_two_amplitudes_tendsto epsilonU epsilonV t s ht hs).eventually
     (Iio_mem_nhds hbound)
   filter_upwards [he,eventually_gt_atTop 0] with N hN hN0
   refine ⟨hN0,?_⟩
   intro J m hm hmU hmV
   exact (add_le_add (sourceAmplitude_grid_le epsilonU N J d t m heU hN0 hd hm hmU)
     (sourceAmplitude_grid_le epsilonV N J d s m heV hN0 hd hm hmV)).trans hN.le

end RoughRegime.LatticePriors
