module

public import RoughRegime.SourceAmplitude
public import RoughRegime.GridRegion


@[expose] public section
/-! The literal B=(2N)^d source subdivision has the prescribed fixed region
volume and always fits inside the design cube. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.LatticePriors

 def sourceGridCount (N d : ℕ) : ℝ := (2*(N:ℝ))^d
 def sourceGridSide (v0 : ℝ) (d : ℕ) : ℝ := v0^(1/(d:ℝ))
 def sourceGridOffset (v0 : ℝ) (d : ℕ) : ℝ := (1-sourceGridSide v0 d)/2

 theorem sourceGridCount_pos (N d : ℕ) (hN : 0 < N) : 0 < sourceGridCount N d := by
   unfold sourceGridCount
   positivity
 theorem sourceGridCount_ge_one (N d : ℕ) (hN : 0 < N) : 1 ≤ sourceGridCount N d := by
   apply one_le_pow₀
   have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
   linarith

 theorem sourceBlockScale_grid_side (v0 : ℝ) (N d : ℕ) (hv : 0 ≤ v0) (hN : 0 < N) (hd : 0 < d) :
     sourceBlockScale v0 (sourceGridCount N d) d*(2*N : ℕ) = sourceGridSide v0 d := by
   have hn : 0 < (2*(N:ℝ)) := by positivity
   unfold sourceBlockScale sourceGridCount sourceGridSide
   rw [Real.div_rpow hv (pow_nonneg hn.le _)]
   have hr : ((2*(N:ℝ))^d)^(1/(d:ℝ)) = 2*(N:ℝ) := by
     simpa only [one_div] using Real.pow_rpow_inv_natCast hn.le (Nat.ne_of_gt hd)
   rw [hr]
   push_cast
   field_simp

 theorem sourceBlockScale_grid_le_one (v0 : ℝ) (N d : ℕ) (hv : 0 < v0) (hv1 : v0 ≤ 1)
     (hN : 0 < N) : sourceBlockScale v0 (sourceGridCount N d) d ≤ 1 := by
   have hB := sourceGridCount_pos N d hN
   have hB1 := sourceGridCount_ge_one N d hN
   unfold sourceBlockScale
   apply Real.rpow_le_one (by positivity)
   · apply (div_le_one hB).mpr
     exact hv1.trans hB1
   · positivity

 theorem sourceGridSide_pos {v0 : ℝ} (hv : 0 < v0) (d : ℕ) : 0 < sourceGridSide v0 d := by
   unfold sourceGridSide
   positivity
 theorem sourceGridSide_le_one {v0 : ℝ} (hv : 0 ≤ v0) (hv1 : v0 ≤ 1) (d : ℕ) : sourceGridSide v0 d ≤ 1 :=
   Real.rpow_le_one hv hv1 (by positivity)

 theorem source_grid_region_volume (v0 : ℝ) (N d : ℕ) (hv : 0 < v0) (hN : 0 < N) (hd : 0 < d) :
     volume (gridRegion d N (sourceGridOffset v0 d) (sourceBlockScale v0 (sourceGridCount N d) d)) = ENNReal.ofReal v0 := by
   rw [gridRegion_volume _ _ _ _ (sourceBlockScale_pos hv (sourceGridCount_pos N d hN) d).le,
     sourceBlockScale_grid_side v0 N d hv.le hN hd]
   congr 1
   exact (by simpa only [sourceGridSide,one_div] using Real.rpow_inv_natCast_pow hv.le (Nat.ne_of_gt hd))

 theorem source_grid_fits_cube (v0 : ℝ) (N d : ℕ) (hv : 0 < v0) (hv1 : v0 ≤ 1)
     (hN : 0 < N) (hd : 0 < d) :
     0 ≤ sourceGridOffset v0 d ∧ sourceGridOffset v0 d+
       sourceBlockScale v0 (sourceGridCount N d) d*(2*N : ℕ) ≤ 1 := by
   have hs := sourceGridSide_le_one hv.le hv1 d
   rw [sourceBlockScale_grid_side v0 N d hv.le hN hd]
   unfold sourceGridOffset
   constructor <;> linarith

 theorem source_grid_region_subset (v0 : ℝ) (N d : ℕ) (hv : 0 < v0) (hv1 : v0 ≤ 1)
     (hN : 0 < N) (hd : 0 < d) :
     gridRegion d N (sourceGridOffset v0 d) (sourceBlockScale v0 (sourceGridCount N d) d) ⊆ Model.cube d :=
   gridRegion_subset_cube _ _ _ _ (source_grid_fits_cube v0 N d hv hv1 hN hd).1
     (source_grid_fits_cube v0 N d hv hv1 hN hd).2


end RoughRegime.LatticePriors
