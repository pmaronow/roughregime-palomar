module

public import RoughRegime.SecondOrderRemainder


@[expose] public section
/-! The source fourth-order odd/odd expansion from actual local C⁴ regularity. -/
noncomputable section
open Set Metric Filter MeasureTheory
open scoped BigOperators ContDiff
namespace RoughRegime.OddTaylor

abbrev Plane := ℝ × ℝ

def eU : Plane := (1, 0)
def eV : Plane := (0, 1)

def directionalDerivative (F : Plane → ℝ) (e : Plane) : Plane → ℝ :=
  fun x => fderiv ℝ F x e

def firstPartial (F : Plane → ℝ) : Plane → ℝ := directionalDerivative F eU

def mixedDerivative (F : Plane → ℝ) : Plane → ℝ := directionalDerivative (firstPartial F) eV

def oddOdd (F : Plane → ℝ) (u v : ℝ) : ℝ :=
  (F (u, v) - F (-u, v) - F (u, -v) + F (-u, -v)) / 4

lemma directionalDerivative_contDiffAt (F : Plane → ℝ) (e x : Plane) {n : ℕ∞ω}
    (hF : ContDiffAt ℝ (n + 1) F x) : ContDiffAt ℝ n (directionalDerivative F e) x := by
  exact (hF.fderiv_right le_rfl).clm_apply contDiffAt_const

lemma symmetric_interval_abs_le (u s : ℝ) (hs : s ∈ uIcc (-u) u) : |s| ≤ |u| := by
  by_cases hu : 0 ≤ u
  · rw [uIcc_of_le (by linarith : -u ≤ u)] at hs
    rw [abs_of_nonneg hu]
    exact abs_le.mpr hs
  · have hu' : u ≤ 0 := le_of_not_ge hu
    rw [uIcc_comm, uIcc_of_le (by linarith : u ≤ -u)] at hs
    rw [abs_of_nonpos hu']
    exact abs_le.mpr (by simpa using hs)

lemma rectangle_mem_ball (r u v s t : ℝ) (hu : |u| < r) (hv : |v| < r)
    (hs : s ∈ uIcc (-u) u) (ht : t ∈ uIcc (-v) v) : (s, t) ∈ ball (0 : Plane) r := by
  simp only [mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff]
  exact ⟨(symmetric_interval_abs_le u s hs).trans_lt hu,
    (symmetric_interval_abs_le v t ht).trans_lt hv⟩

lemma rectangle_norm_sq_le (u v s t : ℝ) (hs : s ∈ uIcc (-u) u)
    (ht : t ∈ uIcc (-v) v) : ‖(s, t)‖ ^ 2 ≤ u ^ 2 + v ^ 2 := by
  have hs2 : s ^ 2 ≤ u ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg s) (symmetric_interval_abs_le u s hs) 2
  have ht2 : t ^ 2 ≤ v ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) (symmetric_interval_abs_le v t ht) 2
  simp only [Prod.norm_def, Real.norm_eq_abs]
  rcases le_total |s| |t| with h | h
  · rw [max_eq_right h, sq_abs]
    linarith [sq_nonneg u]
  · rw [max_eq_left h, sq_abs]
    linarith [sq_nonneg v]

lemma firstPartial_hasDerivAt (F : Plane → ℝ) (s t : ℝ)
    (hF : DifferentiableAt ℝ F (s, t)) :
    HasDerivAt (fun y => F (y, t)) (firstPartial F (s, t)) s := by
  simpa only [Function.comp_def, id_eq, firstPartial, directionalDerivative, eU] using
    hF.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))

lemma mixedDerivative_hasDerivAt (F : Plane → ℝ) (s t : ℝ)
    (hF : DifferentiableAt ℝ (firstPartial F) (s, t)) :
    HasDerivAt (fun y => firstPartial F (s, y)) (mixedDerivative F (s, t)) t := by
  simpa only [Function.comp_def, mixedDerivative, directionalDerivative, eV] using
    hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))

/-- The actual odd/odd part is the rectangle integral of the actual mixed partial. -/
theorem oddOdd_eq_rectangle (F : Plane → ℝ) (r : ℝ)
    (hF : ∀ x ∈ ball (0 : Plane) r, ContDiffAt ℝ 2 F x)
    (u v : ℝ) (hu : |u| < r) (hv : |v| < r) :
    oddOdd F u v = (∫ s in (-u)..u, ∫ t in (-v)..v, mixedDerivative F (s, t)) / 4 := by
  have hP (x : Plane) (hx : x ∈ ball 0 r) : ContDiffAt ℝ 1 (firstPartial F) x :=
    directionalDerivative_contDiffAt F eU x (hF x hx)
  have hG (x : Plane) (hx : x ∈ ball 0 r) : ContinuousAt (mixedDerivative F) x :=
    ((hP x hx).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have hinner (s : ℝ) (hs : s ∈ uIcc (-u) u) :
      (∫ t in (-v)..v, mixedDerivative F (s, t)) = firstPartial F (s, v) - firstPartial F (s, -v) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      exact mixedDerivative_hasDerivAt F s t
        ((hP _ (rectangle_mem_ball r u v s t hu hv hs ht)).differentiableAt (by norm_num))
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      exact ((hG _ (rectangle_mem_ball r u v s t hu hv hs ht)).comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have houter (t : ℝ) (ht : t ∈ uIcc (-v) v) :
      (∫ s in (-u)..u, firstPartial F (s, t)) = F (u, t) - F (-u, t) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s hs
      exact firstPartial_hasDerivAt F s t
        ((hF _ (rectangle_mem_ball r u v s t hu hv hs ht)).differentiableAt (by norm_num))
    · apply ContinuousOn.intervalIntegrable
      intro s hs
      have hl : ContinuousAt (fun y : ℝ => (y, t)) s :=
        (continuous_id.prodMk continuous_const).continuousAt
      simpa only [Function.comp_def] using
        ((hP (s, t) (rectangle_mem_ball r u v s t hu hv hs ht)).continuousAt.comp (f := fun y : ℝ => (y, t)) hl).continuousWithinAt
  have hint (t : ℝ) (ht : t ∈ uIcc (-v) v) :
      IntervalIntegrable (fun s => firstPartial F (s, t)) volume (-u) u := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have hl : ContinuousAt (fun y : ℝ => (y, t)) s :=
      (continuous_id.prodMk continuous_const).continuousAt
    simpa only [Function.comp_def] using
      ((hP (s, t) (rectangle_mem_ball r u v s t hu hv hs ht)).continuousAt.comp (f := fun y : ℝ => (y, t)) hl).continuousWithinAt
  rw [intervalIntegral.integral_congr hinner,
    intervalIntegral.integral_sub (hint v right_mem_uIcc) (hint (-v) left_mem_uIcc),
    houter v right_mem_uIcc, houter (-v) left_mem_uIcc]
  unfold oddOdd
  ring

lemma integral_affine (a b l r : ℝ) :
    (∫ t in l..r, a + b * t) = a * (r - l) + b * ((r ^ 2 - l ^ 2) / 2) := by
  have hi : IntervalIntegrable (fun t : ℝ => b * t) volume l r :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => a) (g := fun t : ℝ => b * t)
    intervalIntegrable_const hi,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

lemma linear_plane_eval (D : Plane →L[ℝ] ℝ) (s t : ℝ) :
    D (s, t) = D eU * s + D eV * t := by
  have he : (s, t) = s • eU + t • eV := by ext <;> simp [eU, eV]
  rw [he, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

lemma affine_rectangle_integral (G : Plane → ℝ) (u v : ℝ) :
    (∫ s in (-u)..u, ∫ t in (-v)..v, G 0 + (fderiv ℝ G 0) (s, t)) =
      4 * u * v * G 0 := by
  have hin (s : ℝ) : (∫ t in (-v)..v, G 0 + (fderiv ℝ G 0) (s, t)) =
      2 * v * (G 0 + (fderiv ℝ G 0) eU * s) := by
    simp_rw [linear_plane_eval]
    have he : (fun t : ℝ => G 0 + ((fderiv ℝ G 0) eU * s + (fderiv ℝ G 0) eV * t)) =
      (fun t => (G 0 + (fderiv ℝ G 0) eU * s) + (fderiv ℝ G 0) eV * t) := by
      funext t
      ring
    rw [he, integral_affine]
    ring
  simp_rw [hin]
  rw [intervalIntegral.integral_const_mul, integral_affine]
  ring

lemma firstPartial_sub (F P : Plane → ℝ) (x : Plane)
    (hF : DifferentiableAt ℝ F x) (hP : DifferentiableAt ℝ P x) :
    firstPartial (fun y => F y - P y) x = firstPartial F x - firstPartial P x := by
  change (fderiv ℝ (F - P) x) eU = _
  rw [fderiv_sub hF hP, sub_apply]
  rfl

lemma mixedDerivative_sub (F P : Plane → ℝ) (x : Plane)
    (hF : ContDiffAt ℝ 2 F x) (hP : ContDiffAt ℝ 2 P x) :
    mixedDerivative (fun y => F y - P y) x = mixedDerivative F x - mixedDerivative P x := by
  have he : firstPartial (fun y => F y - P y) =ᶠ[nhds x]
      (fun y => firstPartial F y - firstPartial P y) := by
    filter_upwards [hF.eventually (by norm_num), hP.eventually (by norm_num)] with y hyF hyP
    exact firstPartial_sub F P y (hyF.differentiableAt (by norm_num)) (hyP.differentiableAt (by norm_num))
  have hDuF : DifferentiableAt ℝ (firstPartial F) x :=
    (directionalDerivative_contDiffAt F eU x (n := 1) hF).differentiableAt (by norm_num)
  have hDuP : DifferentiableAt ℝ (firstPartial P) x :=
    (directionalDerivative_contDiffAt P eU x (n := 1) hP).differentiableAt (by norm_num)
  unfold mixedDerivative directionalDerivative
  rw [he.fderiv_eq]
  change (fderiv ℝ (firstPartial F - firstPartial P) x) eV = _
  rw [fderiv_sub hDuF hDuP, sub_apply]

def cubicCorrection (d a b : ℝ) (x : Plane) : ℝ :=
  d * x.1 * x.2 + (a / 2) * x.1 ^ 2 * x.2 + (b / 2) * x.1 * x.2 ^ 2

lemma firstPartial_cubicCorrection (d a b : ℝ) (x : Plane) :
    firstPartial (cubicCorrection d a b) x = d * x.2 + a * x.1 * x.2 + (b / 2) * x.2 ^ 2 := by
  rcases x with ⟨s, t⟩
  have ha : HasDerivAt (fun y => cubicCorrection d a b (y, t))
      (d * t + a * s * t + (b / 2) * t ^ 2) s := by
    convert (((hasDerivAt_id s).const_mul d).mul_const t).add
      ((((hasDerivAt_id s).pow 2).const_mul (a / 2)).mul_const t) |>.add
      (((hasDerivAt_id s).const_mul (b / 2)).mul_const (t ^ 2)) using 1 <;>
      (try funext y) <;> simp only [cubicCorrection, id_eq, Pi.add_apply, Pi.pow_apply] <;> ring
  exact (firstPartial_hasDerivAt (cubicCorrection d a b) s t (by
    unfold cubicCorrection
    fun_prop)).unique ha

lemma mixedDerivative_cubicCorrection (d a b : ℝ) (x : Plane) :
    mixedDerivative (cubicCorrection d a b) x = d + a * x.1 + b * x.2 := by
  rcases x with ⟨s, t⟩
  have ha : HasDerivAt (fun y => firstPartial (cubicCorrection d a b) (s, y))
      (d + a * s + b * t) t := by
    simp_rw [firstPartial_cubicCorrection]
    convert ((hasDerivAt_id t).const_mul d).add ((hasDerivAt_id t).const_mul (a * s)) |>.add
      (((hasDerivAt_id t).pow 2).const_mul (b / 2)) using 1 <;> (try funext y) <;> simp only [id_eq, Pi.add_apply, Pi.pow_apply] <;> ring
  have hp : ContDiffAt ℝ 2 (cubicCorrection d a b) (s, t) := by
    unfold cubicCorrection
    fun_prop
  exact (mixedDerivative_hasDerivAt (cubicCorrection d a b) s t
    ((directionalDerivative_contDiffAt _ eU _ (n := 1) hp).differentiableAt (by norm_num))).unique ha

lemma oddOdd_sub_cubicCorrection (F : Plane → ℝ) (d a b u v : ℝ) :
    oddOdd (fun x => F x - cubicCorrection d a b x) u v = oddOdd F u v - d * u * v := by
  unfold oddOdd cubicCorrection
  ring

/-- The source odd/odd Taylor bound follows from the actual fourth derivative
bound on a neighborhood, by integrating the true mixed derivative. -/
theorem oddOdd_remainder_of_second_bound (F : Plane → ℝ) (r C : ℝ) (hr : 0 < r)
    (hF : ∀ x ∈ ball (0 : Plane) r, ContDiffAt ℝ 4 F x)
    (hD : ∀ x ∈ ball (0 : Plane) r,
      ‖fderiv ℝ (fderiv ℝ (mixedDerivative F)) x‖ ≤ C)
    (u v : ℝ) (hu : |u| < r) (hv : |v| < r) :
    |oddOdd F u v - mixedDerivative F 0 * u * v| ≤ C * |u * v| * (u ^ 2 + v ^ 2) := by
  let G := mixedDerivative F
  let d := G 0
  let a := (fderiv ℝ G 0) eU
  let b := (fderiv ℝ G 0) eV
  let P := cubicCorrection d a b
  let H : Plane → ℝ := fun x => F x - P x
  have hG (x : Plane) (hx : x ∈ ball 0 r) : ContDiffAt ℝ 2 G x := by
    exact directionalDerivative_contDiffAt (firstPartial F) eV x
      (directionalDerivative_contDiffAt F eU x (hF x hx))
  have hzero : (0 : Plane) ∈ ball 0 r := by simpa using hr
  have hC : 0 ≤ C := (norm_nonneg (fderiv ℝ (fderiv ℝ G) 0)).trans (hD 0 hzero)
  have hP (x : Plane) : ContDiffAt ℝ 2 P x := by
    change ContDiffAt ℝ 2 (cubicCorrection d a b) x
    unfold cubicCorrection
    fun_prop
  have hH (x : Plane) (hx : x ∈ ball 0 r) : ContDiffAt ℝ 2 H x :=
    ((hF x hx).of_le (by norm_num)).sub (hP x)
  have hTaylor (x : Plane) (hx : x ∈ ball 0 r) :
      ‖G x - G 0 - (fderiv ℝ G 0) x‖ ≤ C * ‖x‖ ^ 2 := by
    apply SecondOrderRemainder.first_order_remainder G r C hr
      (fun y hy => (hG y hy).differentiableAt (by norm_num))
      (fun y hy => ((hG y hy).fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)) hD
    simpa using hx
  have hpoint (s t : ℝ) (hs : s ∈ uIcc (-u) u) (ht : t ∈ uIcc (-v) v) :
      ‖mixedDerivative H (s, t)‖ ≤ C * (u ^ 2 + v ^ 2) := by
    have hx := rectangle_mem_ball r u v s t hu hv hs ht
    have he : mixedDerivative H (s, t) = G (s, t) - G 0 - (fderiv ℝ G 0) (s, t) := by
      rw [mixedDerivative_sub F P (s, t) ((hF _ hx).of_le (by norm_num)) (hP _)]
      dsimp [P]
      rw [mixedDerivative_cubicCorrection, linear_plane_eval]
      dsimp [G, d, a, b]
      ring
    rw [he]
    exact (hTaylor (s, t) hx).trans (mul_le_mul_of_nonneg_left (rectangle_norm_sq_le u v s t hs ht) hC)
  have hinner (s : ℝ) (hs : s ∈ uIoc (-u) u) :
      ‖∫ t in (-v)..v, mixedDerivative H (s, t)‖ ≤ C * (u ^ 2 + v ^ 2) * |v - (-v)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    exact hpoint s t (uIoc_subset_uIcc hs) (uIoc_subset_uIcc ht)
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const hinner
  rw [← oddOdd_sub_cubicCorrection F d a b u v, oddOdd_eq_rectangle H r hH u v hu hv]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply (div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using houter) (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
  rw [show v - (-v) = 2 * v by ring, show u - (-u) = 2 * u by ring, abs_mul, abs_mul, abs_mul]
  norm_num
  ring

/-- Source Lemma 12's precise odd/odd expansion from local C⁴ regularity alone.
The mixed coefficient is the actual second partial derivative, and the error
retains the factor `|u*v|` even for very unequal coordinates. -/
theorem oddOdd_taylor (F : Plane → ℝ) (hF : ContDiffAt ℝ 4 F (0 : Plane)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ u v : ℝ, |u| ≤ ε → |v| ≤ ε →
      |oddOdd F u v - mixedDerivative F 0 * u * v| ≤ C * |u * v| * (u ^ 2 + v ^ 2) := by
  let G := mixedDerivative F
  have hG : ContDiffAt ℝ 2 G (0 : Plane) :=
    directionalDerivative_contDiffAt (firstPartial F) eV 0 (n := 2)
      (directionalDerivative_contDiffAt F eU 0 (n := 3) hF)
  have hDG : ContDiffAt ℝ 1 (fderiv ℝ G) (0 : Plane) := hG.fderiv_right (by norm_num)
  have hDD : ContinuousAt (fderiv ℝ (fderiv ℝ G)) (0 : Plane) :=
    hDG.continuousAt_fderiv (by norm_num)
  let C := ‖fderiv ℝ (fderiv ℝ G) 0‖ + 1
  have hn : ContinuousAt (fun x : Plane => ‖fderiv ℝ (fderiv ℝ G) x‖) (0 : Plane) :=
    ContinuousAt.norm (E := Plane →L[ℝ] Plane →L[ℝ] ℝ)
      (f := fun x : Plane => fderiv ℝ (fderiv ℝ G) x) (a := 0) hDD
  have hbound : {x : Plane | ‖fderiv ℝ (fderiv ℝ G) x‖ < C} ∈ nhds 0 := by
    change (fun x : Plane => ‖fderiv ℝ (fderiv ℝ G) x‖) ⁻¹' Iio C ∈ nhds 0
    exact hn.preimage_mem_nhds (Iio_mem_nhds (show ‖fderiv ℝ (fderiv ℝ G) 0‖ < C from lt_add_one _))
  have he : {x : Plane | ContDiffAt ℝ 4 F x ∧ ‖fderiv ℝ (fderiv ℝ G) x‖ < C} ∈ nhds 0 :=
    (hF.eventually (by norm_num)).and hbound
  obtain ⟨r, hr, hs⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r / 2, by positivity, C, by positivity, ?_⟩
  intro u v hu hv
  exact oddOdd_remainder_of_second_bound F r C hr
    (fun x hx => (hs hx).1) (fun x hx => (hs hx).2.le) u v
    (hu.trans_lt (by linarith)) (hv.trans_lt (by linarith))

end RoughRegime.OddTaylor
