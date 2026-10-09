module

public import RoughRegime.PilotConcentration


@[expose] public section
/-! A concrete smooth nonnegative finite grid partition for the fixed-accuracy pilot. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace RoughRegime.Applications

/-- Cumulative grid weights, with constant endpoint functions. -/
def gridCumulative (k j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then 1 else if k ≤ j then 0
  else Real.smoothTransition ((k : ℝ) * x - j + 1 / 2)

def gridWeight (k : ℕ) (j : Fin k) (x : ℝ) : ℝ :=
  gridCumulative k j x - gridCumulative k (j + 1) x

lemma gridCumulative_smooth (k j : ℕ) : ContDiff ℝ ∞ (gridCumulative k j) := by
  unfold gridCumulative
  split_ifs <;> fun_prop

lemma gridCumulative_range (k j : ℕ) (x : ℝ) :
    gridCumulative k j x ∈ Icc (0 : ℝ) 1 := by
  unfold gridCumulative
  split_ifs
  · norm_num
  · norm_num
  · exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma gridWeight_nonneg (k : ℕ) (j : Fin k) (x : ℝ) : 0 ≤ gridWeight k j x := by
  unfold gridWeight
  apply sub_nonneg.mpr
  by_cases hj0 : (j : ℕ) = 0
  · have hc : gridCumulative k j x = 1 := by simp [gridCumulative, hj0]
    rw [hc]
    exact (gridCumulative_range k (j + 1) x).2
  · by_cases hjlast : k ≤ (j : ℕ) + 1
    · rw [gridCumulative, ite_eq_right (by omega : (j : ℕ) + 1 ≠ 0), ite_eq_left hjlast]
      exact (gridCumulative_range k j x).1
    · simp only [gridCumulative, ite_eq_right hj0, ite_eq_right (Nat.not_le.mpr j.isLt),
        ite_eq_right (by omega : (j : ℕ) + 1 ≠ 0), ite_eq_right hjlast]
      apply Real.smoothTransition.monotone
      push_cast
      linarith

lemma gridWeight_smooth (k : ℕ) (j : Fin k) : ContDiff ℝ ∞ (gridWeight k j) :=
  (gridCumulative_smooth k j).sub (gridCumulative_smooth k (j + 1))

/-- The finite grid weights sum exactly to one, with no normalization denominator. -/
lemma gridWeight_sum (k : ℕ) (hk : 0 < k) (x : ℝ) : ∑ j : Fin k, gridWeight k j x = 1 := by
  unfold gridWeight
  change (∑ j : Fin k, (fun q : ℕ => gridCumulative k q x - gridCumulative k (q + 1) x) (j : ℕ)) = 1
  rw [Fin.sum_univ_eq_sum_range (fun q : ℕ => gridCumulative k q x - gridCumulative k (q + 1) x)]
  change (∑ j ∈ Finset.range k, (gridCumulative k j x - gridCumulative k (j + 1) x)) = 1
  rw [Finset.sum_range_sub']
  simp [gridCumulative, Nat.ne_of_gt hk]

/-- A nonzero grid weight lies in the source's expanded cell interval. -/
lemma gridWeight_localized (k : ℕ) (j : Fin k) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (hw : gridWeight k j x ≠ 0) :
    ((j : ℝ) - 1 / 2) / k ≤ x ∧ x ≤ ((j : ℝ) + 3 / 2) / k := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hn := gridWeight_nonneg k j x
  have hp : 0 < gridWeight k j x := lt_of_le_of_ne hn hw.symm
  constructor
  · by_cases hj0 : (j : ℕ) = 0
    · have hjr : (j : ℝ) = 0 := by exact_mod_cast hj0
      rw [hjr]
      exact (div_nonpos_of_nonpos_of_nonneg (by norm_num) hkr.le).trans hx.1
    · by_contra h
      have hl : (k : ℝ) * x - j + 1 / 2 ≤ 0 := by
        have hh := (lt_div_iff₀ hkr).mp (lt_of_not_ge h)
        linarith
      have hc : gridCumulative k j x = 0 := by
        simp only [gridCumulative, ite_eq_right hj0, ite_eq_right (Nat.not_le.mpr j.isLt)]
        exact Real.smoothTransition.zero_of_nonpos hl
      have hcnext := (gridCumulative_range k (j + 1) x).1
      unfold gridWeight at hp
      rw [hc] at hp
      linarith
  · by_cases hjlast : k ≤ (j : ℕ) + 1
    · have hjr : (k : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hjlast
      exact hx.2.trans ((le_div_iff₀ hkr).mpr (by linarith))
    · by_contra h
      have hl : 1 ≤ (k : ℝ) * x - ((j : ℕ) + 1) + 1 / 2 := by
        have hh := (div_lt_iff₀ hkr).mp (lt_of_not_ge h)
        linarith
      have hc : gridCumulative k (j + 1) x = 1 := by
        simp only [gridCumulative, ite_eq_right (by omega : (j : ℕ) + 1 ≠ 0), ite_eq_right hjlast]
        apply Real.smoothTransition.one_of_one_le
        simpa only [Nat.cast_add, Nat.cast_one] using hl
      have hcprev := (gridCumulative_range k j x).2
      unfold gridWeight at hp
      rw [hc] at hp
      linarith

def tensorGridWeight (d k : ℕ) (j : Fin d → Fin k)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∏ i, gridWeight k (j i) (x i)

lemma tensorGridWeight_nonneg (d k : ℕ) (j : Fin d → Fin k)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ tensorGridWeight d k j x :=
  Finset.prod_nonneg (fun i _ => gridWeight_nonneg k (j i) (x i))

lemma tensorGridWeight_smooth (d k : ℕ) (j : Fin d → Fin k) :
    ContDiff ℝ ∞ (tensorGridWeight d k j) := by
  apply contDiff_prod
  intro i _
  apply (gridWeight_smooth k (j i)).comp
  fun_prop

lemma tensorGridWeight_sum (d k : ℕ) (hk : 0 < k) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ j : Fin d → Fin k, tensorGridWeight d k j x = 1 := by
  unfold tensorGridWeight
  rw [← Fintype.prod_sum (fun i j => gridWeight k j (x i))]
  simp only [gridWeight_sum k hk, Finset.prod_const_one]

def gridCell (d k : ℕ) (j : Fin d → Fin k) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | ∀ i, (j i : ℝ) / k ≤ y i ∧ y i ≤ ((j i : ℝ) + 1) / k}

lemma gridCell_measurable (d k : ℕ) (j : Fin d → Fin k) : MeasurableSet (gridCell d k j) := by
  change MeasurableSet {y : EuclideanSpace ℝ (Fin d) |
    ∀ i, (j i : ℝ) / k ≤ y i ∧ y i ≤ ((j i : ℝ) + 1) / k}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hi : Measurable (fun y : EuclideanSpace ℝ (Fin d) => y i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable
  exact (measurableSet_le measurable_const hi).inter (measurableSet_le hi measurable_const)

lemma gridCell_subset_cube (d k : ℕ) (hk : 0 < k) (j : Fin d → Fin k)
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ gridCell d k j) :
    ∀ i, y i ∈ Icc (0 : ℝ) 1 := by
  intro i
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hji : (j i : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt (j i).isLt
  exact ⟨(div_nonneg (Nat.cast_nonneg _) hkr.le).trans (hy i).1,
    (hy i).2.trans ((div_le_one hkr).mpr hji)⟩

/-- Every point in a cell is close to any point where that cell's smooth weight is nonzero. -/
lemma tensorGridWeight_cell_distance (d k : ℕ) (hk : 0 < k) (j : Fin d → Fin k)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (hy : y ∈ gridCell d k j)
    (hw : tensorGridWeight d k j x ≠ 0) :
    ‖x - y‖ ≤ 2 * Real.sqrt d / k := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hcoord : ∀ i, |x i - y i| ≤ 2 / k := by
    intro i
    have hwi : gridWeight k (j i) (x i) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mp hw i (Finset.mem_univ i)
    have hl := gridWeight_localized k (j i) (x i) (hx i) hwi
    have hyi := hy i
    apply abs_le.mpr
    constructor
    · have hh := sub_le_sub hyi.2 hl.1
      have heq : ((j i : ℝ) + 1) / k - ((j i : ℝ) - 1 / 2) / k = 3 / (2 * k) := by ring
      rw [heq] at hh
      have hh' : 3 / (2 * (k : ℝ)) ≤ 2 / k := by field_simp; linarith
      linarith
    · have hh := sub_le_sub hl.2 hyi.1
      have heq : ((j i : ℝ) + 3 / 2) / k - (j i : ℝ) / k = 3 / (2 * k) := by ring
      rw [heq] at hh
      have hh' : 3 / (2 * (k : ℝ)) ≤ 2 / k := by field_simp; linarith
      exact hh.trans hh'
  have hsq : ‖x - y‖ ^ 2 ≤ (d : ℝ) * (2 / (k : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d, (2 / (k : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hh := hcoord i
        simp only [PiLp.sub_apply]
        nlinarith [abs_nonneg (x i - y i), sq_abs (x i - y i)]
      _ = _ := by simp
  have hd : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt (by positivity)
  have hbound : 0 ≤ 2 * Real.sqrt d / k := by positivity
  have heq : (2 * Real.sqrt d / k) ^ 2 = (d : ℝ) * (2 / (k : ℝ)) ^ 2 := by
    rw [div_pow, mul_pow, hd]
    ring
  nlinarith [norm_nonneg (x - y)]

/-- A fixed finite smooth basis has uniform bounds at every derivative order
for all coefficient vectors in the unit rectangle. -/
theorem finite_smooth_combination_derivative_bound {X J : Type*} [Fintype J]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : Set X) (hD : IsCompact D) (φ : J → X → ℝ)
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : J → ℝ, (∀ j, |a j| ≤ 1) →
      ∀ x ∈ D, ‖iteratedFDeriv ℝ q (fun y => ∑ j, a j * φ j y) x‖ ≤ B := by
  have hbounds : ∀ j, ∃ b : ℝ, ∀ x ∈ D, ‖iteratedFDeriv ℝ q (φ j) x‖ ≤ b := by
    intro j
    exact hD.exists_bound_of_continuousOn
      ((hφ j).continuous_iteratedFDeriv (by simp)).continuousOn
  choose b hb using hbounds
  refine ⟨∑ j, max (b j) 0, Finset.sum_nonneg (fun j _ => le_max_right _ _), ?_⟩
  intro a ha x hx
  have hsum : iteratedFDeriv ℝ q (fun y => ∑ j, a j * φ j y) x =
      ∑ j, a j • iteratedFDeriv ℝ q (φ j) x := by
    rw [iteratedFDeriv_fun_sum_apply (fun j _ =>
      (contDiff_const.mul (hφ j)).of_le (by simp) |>.contDiffAt)]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [smul_eq_mul] using
      iteratedFDeriv_const_smul_apply' (a := a j) (x := x) (i := q)
        ((hφ j).of_le (by simp) |>.contDiffAt)
  rw [hsum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ q (φ j) x‖ :=
      mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)
    _ ≤ max (b j) 0 := by simpa only [one_mul] using (hb j x hx).trans (le_max_left _ _)

/-- The constructed pilot family has uniform derivative bounds on every compact
set, independently of the sample size and data. -/
theorem fixedGridPilot_derivative_bounds {Ω X J : Type*} [Fintype J]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Q : J → Set Ω) (R : Ω → ℝ) (φ : J → X → ℝ)
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (D : Set X) (hD : IsCompact D)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 - ε) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ data : Fin n → Ω, ∀ x ∈ D,
      ‖iteratedFDeriv ℝ q (fun y => fixedGridPilot Q R φ ε hε y data) x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := finite_smooth_combination_derivative_bound D hD φ hφ q
  refine ⟨B, hB, fun n data x hx => ?_⟩
  have ha : ∀ j, |(Set.projIcc ε (1 - ε) hε (cellAverage (Q j) R data) : ℝ)| ≤ 1 := by
    intro j
    have hh := (Set.projIcc ε (1 - ε) hε (cellAverage (Q j) R data)).property
    rw [abs_of_nonneg (hε0.trans hh.1)]
    linarith [hh.2]
  simpa only [fixedGridPilot, mul_comm] using
    hb (fun j => (Set.projIcc ε (1 - ε) hε (cellAverage (Q j) R data) : ℝ)) ha x hx

end RoughRegime.Applications
