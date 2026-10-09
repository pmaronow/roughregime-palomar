module

public import RoughRegime.GlobalProfileHolder


@[expose] public section
/-! Exact cancellation of the paper's block volume and amplitude scales.
These estimates use the actual source amplitudes, rather than assuming a
Hölder bound for the resulting profiles. -/
noncomputable section
namespace RoughRegime.LatticePriors

 def sourceSpatialVolume (J d : ℕ) : ℝ := (2 : ℝ) ^ (J*d)
 def sourceBlockScale (v0 B : ℝ) (d : ℕ) : ℝ := (v0/B) ^ (1/(d : ℝ))
 def sourceAmplitude (epsilon B : ℝ) (J d : ℕ) (t m : ℝ) : ℝ :=
   epsilon * (B*sourceSpatialVolume J d) ^ (-(t/(d : ℝ))) * m

 theorem sourceSpatialVolume_rpow (J d : ℕ) (hd : 0 < d) (t : ℝ) :
     sourceSpatialVolume J d ^ (t/(d : ℝ)) = (2 : ℝ) ^ ((J : ℝ)*t) := by
   unfold sourceSpatialVolume
   rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
   congr 1
   push_cast
   field_simp

 theorem sourceBlockScale_pos {v0 B : ℝ} (hv : 0 < v0) (hB : 0 < B) (d : ℕ) :
     0 < sourceBlockScale v0 B d := by unfold sourceBlockScale; positivity

 theorem sourceBlockScale_inv_rpow (v0 B : ℝ) (d : ℕ) (hv : 0 < v0) (hB : 0 < B)
     (t : ℝ) : (sourceBlockScale v0 B d)⁻¹ ^ t = B ^ (t/(d : ℝ)) / v0 ^ (t/(d : ℝ)) := by
   unfold sourceBlockScale
   rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_mul (by positivity : 0 ≤ v0/B)]
   have he : 1/(d : ℝ)*(-t) = -(t/(d : ℝ)) := by ring
   rw [he, Real.rpow_neg (by positivity : 0 ≤ v0/B), Real.div_rpow hv.le hB.le]
   rw [inv_div]

 theorem sourceAmplitude_scale_identity (epsilon B v0 : ℝ) (J d : ℕ) (t m : ℝ)
     (hB : 0 < B) (hv : 0 < v0) (hd : 0 < d) (hm : 0 < m) :
     sourceAmplitude epsilon B J d t m * (sourceBlockScale v0 B d)⁻¹ ^ t *
       (1 + (2 : ℝ)^((J : ℝ)*t)/m) =
       epsilon * v0 ^ (-(t/(d : ℝ))) * (m / (2 : ℝ)^((J : ℝ)*t) + 1) := by
   have hR : 0 < sourceSpatialVolume J d := by unfold sourceSpatialVolume; positivity
   have hBp : 0 < B ^ (t/(d : ℝ)) := Real.rpow_pos_of_pos hB _
   have hVp : 0 < v0 ^ (t/(d : ℝ)) := Real.rpow_pos_of_pos hv _
   have hF : 0 < (2 : ℝ)^((J : ℝ)*t) := by positivity
   unfold sourceAmplitude
   rw [sourceBlockScale_inv_rpow v0 B d hv hB t,
     Real.rpow_neg (mul_pos hB hR).le,
     Real.mul_rpow hB.le hR.le,
     sourceSpatialVolume_rpow J d hd t,
     Real.rpow_neg hv.le]
   field_simp

 theorem sourceAmplitude_scale_le (epsilon B v0 : ℝ) (J d : ℕ) (t m : ℝ)
     (he : 0 ≤ epsilon) (hB : 0 < B) (hv : 0 < v0) (hd : 0 < d) (hm : 0 < m)
     (hbudget : m ≤ (2 : ℝ)^((J : ℝ)*t)) :
     |sourceAmplitude epsilon B J d t m| * (sourceBlockScale v0 B d)⁻¹ ^ t *
       (1 + (2 : ℝ)^((J : ℝ)*t)/m) ≤ 2 * v0 ^ (-(t/(d : ℝ))) * epsilon := by
   have hA : 0 ≤ sourceAmplitude epsilon B J d t m := by unfold sourceAmplitude sourceSpatialVolume; positivity
   rw [abs_of_nonneg hA, sourceAmplitude_scale_identity epsilon B v0 J d t m hB hv hd hm]
   have hratio : m / (2 : ℝ)^((J : ℝ)*t) ≤ 1 :=
     (div_le_one (by positivity : 0 < (2 : ℝ)^((J : ℝ)*t))).2 hbudget
   have hh := mul_le_mul_of_nonneg_left (show m / (2 : ℝ)^((J : ℝ)*t)+1 ≤ 2 by linarith)
     (show 0 ≤ epsilon*v0^(-(t/(d : ℝ))) by positivity)
   nlinarith

end RoughRegime.LatticePriors
