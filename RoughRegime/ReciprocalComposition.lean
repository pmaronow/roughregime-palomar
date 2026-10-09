module

public import RoughRegime.CompactJets
public import RoughRegime.Upper


@[expose] public section
/-! True uniformly amplitude-scaled outer jets for the reciprocal and smooth
scalar composition used in the lattice Hölder proof. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper

/-- The full outer family; the density oscillation and cutoff are parameters. -/
def oscillatorOuter (κ : ℝ → ℝ) (center : ℝ) (S : ℝ) (v : ℝ × (ℝ × ℝ)) : ℝ :=
  κ (S * v.2.1 / (center + v.1 * Real.cos v.2.2))

/-- All true outer jets on the compact parameter set have the required factor S.
The constant is derived from smoothness and compactness, rather than assumed. -/
theorem oscillatorOuter_compact_jet_bound (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0 : ℝ) (1 / lo) ⊆ N) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S ∈ Icc (0 : ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ φ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖iteratedFDeriv ℝ n (oscillatorOuter κ (intervalCenter lo hi) S) (h, (a, φ))‖ ≤ C * S := by
  let K : Set (ℝ × (ℝ × ℝ)) := Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi) ×ˢ
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi))
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hf : ∀ p ∈ (Icc (0 : ℝ) 1) ×ˢ K,
      ContDiffAt ℝ ∞ (Function.uncurry (oscillatorOuter κ (intervalCenter lo hi))) p := by
    intro p hp
    have hS := hp.1
    have hh := hp.2.1
    have ha := hp.2.2.1
    have hw : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
    have habs : |p.2.1| ≤ intervalHalfWidth lo hi := abs_le.mpr hh
    have hcos : |p.2.1 * Real.cos p.2.2.2| ≤ intervalHalfWidth lo hi := by
      rw [abs_mul]
      exact (mul_le_mul habs (Real.abs_cos_le_one _) (abs_nonneg _) hw.le).trans_eq (by ring)
    have hden : lo ≤ intervalCenter lo hi + p.2.1 * Real.cos p.2.2.2 := by
      have hh' := (abs_le.mp hcos).1
      unfold intervalCenter intervalHalfWidth at *
      linarith
    have hden0 : 0 < intervalCenter lo hi + p.2.1 * Real.cos p.2.2.2 := hlo.trans_le hden
    have harg : p.1 * p.2.2.1 / (intervalCenter lo hi + p.2.1 * Real.cos p.2.2.2) ∈ Icc (0 : ℝ) (1 / lo) := by
      constructor
      · exact div_nonneg (mul_nonneg hS.1 ha.1) hden0.le
      · apply div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) _ hlo hden
        exact (mul_le_mul hS.2 ha.2 ha.1 (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
    have hsmooth : ContDiffAt ℝ ∞
        (fun z : ℝ × (ℝ × (ℝ × ℝ)) => z.1 * z.2.2.1 /
          (intervalCenter lo hi + z.2.1 * Real.cos z.2.2.2)) p :=
      (contDiffAt_fst.mul contDiffAt_snd.snd.fst).div
        (contDiffAt_const.add (contDiffAt_snd.fst.mul contDiffAt_snd.snd.snd.cos)) hden0.ne'
    exact (hκ.contDiffAt (hN.mem_nhds (hinterval harg))).comp p hsmooth
  obtain ⟨C, hC, hbound⟩ := compact_amplitude_jet_bound
    (oscillatorOuter κ (intervalCenter lo hi)) K hK hf
    (by intro x; simp [oscillatorOuter, hκ0]) n
  refine ⟨C, hC, ?_⟩
  intro S hS h hh a ha φ hφ
  exact hbound S hS (h, (a, φ)) ⟨hh, ha, hφ⟩

/-- Periodicity removes the compact angular restriction, so the same constant
 controls every realized phase and every independent angular parameter. -/
theorem oscillatorOuter_jet_bound (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0 : ℝ) (1 / lo) ⊆ N) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S ∈ Icc (0 : ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ φ : ℝ,
      ‖iteratedFDeriv ℝ n (oscillatorOuter κ (intervalCenter lo hi) S) (h, (a, φ))‖ ≤ C * S := by
  obtain ⟨C, hC, hbound⟩ := oscillatorOuter_compact_jet_bound κ lo hi hlo hlt N hN hκ hκ0 hinterval n
  refine ⟨C, hC, ?_⟩
  intro S hS h hh a ha φ
  let k : ℤ := Int.floor (φ / (2 * Real.pi))
  let ψ : ℝ := φ - (k : ℝ) * (2 * Real.pi)
  have hT : 0 < 2 * Real.pi := by positivity
  have hψ : ψ ∈ Icc (0 : ℝ) (2 * Real.pi) := by
    have hlo' := mul_le_mul_of_nonneg_right (Int.floor_le (φ / (2 * Real.pi))) hT.le
    have hhi' := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (φ / (2 * Real.pi))) hT
    rw [div_mul_cancel₀ _ hT.ne'] at hlo' hhi'
    dsimp [ψ, k]
    constructor <;> nlinarith
  let v : ℝ × (ℝ × ℝ) := (h, (a, ψ))
  let t : ℝ × (ℝ × ℝ) := (0, (0, (k : ℝ) * (2 * Real.pi)))
  have hfun : (fun y => oscillatorOuter κ (intervalCenter lo hi) S (y + t)) =
      oscillatorOuter κ (intervalCenter lo hi) S := by
    funext y
    simp [oscillatorOuter, t, Real.cos_add_int_mul_two_pi]
  have hshift : iteratedFDeriv ℝ n (oscillatorOuter κ (intervalCenter lo hi) S) (v + t) =
      iteratedFDeriv ℝ n (oscillatorOuter κ (intervalCenter lo hi) S) v := by
    rw [← iteratedFDeriv_comp_add_right n t v, hfun]
  have hv : v + t = (h, (a, φ)) := by
    ext <;> simp [v, t, ψ]
  rw [hv] at hshift
  rw [hshift]
  exact hbound S hS h hh a ha ψ hψ

/-- Actual local smoothness holds at every admissible realized phase. -/
theorem oscillatorOuter_contDiffAt (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hinterval : Icc (0 : ℝ) (1 / lo) ⊆ N)
    (S : ℝ) (hS : S ∈ Icc (0 : ℝ) 1) (h a φ : ℝ)
    (hh : h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi))
    (ha : a ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,φ)) := by
  have hw : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
  have habs : |h| ≤ intervalHalfWidth lo hi := abs_le.mpr hh
  have hcos : |h * Real.cos φ| ≤ intervalHalfWidth lo hi := by
    rw [abs_mul]
    exact (mul_le_mul habs (Real.abs_cos_le_one _) (abs_nonneg _) hw.le).trans_eq (by ring)
  have hden : lo ≤ intervalCenter lo hi + h * Real.cos φ := by
    have hh' := (abs_le.mp hcos).1
    unfold intervalCenter intervalHalfWidth at *
    linarith
  have hden0 : 0 < intervalCenter lo hi + h * Real.cos φ := hlo.trans_le hden
  have harg : S*a / (intervalCenter lo hi + h*Real.cos φ) ∈ Icc (0 : ℝ) (1/lo) := by
    constructor
    · exact div_nonneg (mul_nonneg hS.1 ha.1) hden0.le
    · apply div_le_div₀ (by norm_num : (0:ℝ) ≤ 1) _ hlo hden
      exact (mul_le_mul hS.2 ha.2 ha.1 (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by ring)
  have hinner : ContDiffAt ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) => S*y.2.1/(intervalCenter lo hi+y.1*Real.cos y.2.2)) (h,(a,φ)) :=
    (contDiffAt_const.mul contDiffAt_snd.fst).div
      (contDiffAt_const.add (contDiffAt_fst.mul contDiffAt_snd.snd.cos)) hden0.ne'
  exact (hκ.contDiffAt (hN.mem_nhds (hinterval harg))).comp (h,(a,φ)) hinner

/-- Every true outer jet is uniformly Lipschitz in the angle, with the same
amplitude factor S. This is obtained by the mean value theorem on the actual
unbounded phase strip. -/
theorem oscillatorOuter_jet_phase_difference_bound (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0 : ℝ) (1 / lo) ⊆ N) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S ∈ Icc (0 : ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ φ ψ : ℝ,
      ‖iteratedFDeriv ℝ n (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,φ)) -
        iteratedFDeriv ℝ n (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,ψ))‖ ≤ C*S*|φ-ψ| := by
  obtain ⟨C,hC,hbound⟩ := oscillatorOuter_jet_bound κ lo hi hlo hlt N hN hκ hκ0 hinterval (n+1)
  refine ⟨C,hC,?_⟩
  intro S hS h hh a ha φ ψ
  let T : Set (ℝ × (ℝ × ℝ)) := Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi) ×ˢ (Icc (0:ℝ) 1 ×ˢ Set.univ)
  have hconv : Convex ℝ T := (convex_Icc _ _).prod ((convex_Icc _ _).prod convex_univ)
  let f := oscillatorOuter κ (intervalCenter lo hi) S
  have hd (y : ℝ × (ℝ × ℝ)) (hy : y ∈ T) : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y := by
    exact ((oscillatorOuter_contDiffAt κ lo hi hlo hlt N hN hκ hinterval S hS y.1 y.2.1 y.2.2 hy.1 hy.2.1).iteratedFDeriv_right (m := 1) (i := n)
      (by simp)).differentiableAt (by norm_num)
  have hb (y : ℝ × (ℝ × ℝ)) (hy : y ∈ T) : ‖fderiv ℝ (iteratedFDeriv ℝ n f) y‖ ≤ C*S := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hbound S hS y.1 hy.1 y.2.1 hy.2.1 y.2.2
  have he := hconv.norm_image_sub_le_of_norm_fderiv_le hd hb
    (show (h,(a,ψ)) ∈ T from ⟨hh,ha,Set.mem_univ _⟩)
    (show (h,(a,φ)) ∈ T from ⟨hh,ha,Set.mem_univ _⟩)
  simpa [f, Prod.norm_def, max_eq_right (abs_nonneg (φ-ψ))] using he

/-- One constant simultaneously controls the finite jet family and its true
angular differences. -/
theorem oscillatorOuter_finite_jet_bound (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0 : ℝ) (1 / lo) ⊆ N) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ n, ∀ S ∈ Icc (0 : ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ φ ψ : ℝ,
      ‖iteratedFDeriv ℝ k (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,φ))‖ ≤ C*S ∧
      ‖iteratedFDeriv ℝ k (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,φ)) -
        iteratedFDeriv ℝ k (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,ψ))‖ ≤ C*S*|φ-ψ| := by
  choose C hC hb using fun k => oscillatorOuter_jet_bound κ lo hi hlo hlt N hN hκ hκ0 hinterval k
  choose D hD hd using fun k => oscillatorOuter_jet_phase_difference_bound κ lo hi hlo hlt N hN hκ hκ0 hinterval k
  let B : ℝ := 1 + ∑ k ∈ Finset.range (n+1), (C k + D k)
  have hterms (k : ℕ) : 0 ≤ C k + D k := by linarith [hC k,hD k]
  have hB : 0 < B := by
    have hs := Finset.sum_nonneg (s := Finset.range (n+1)) (fun k _ => hterms k)
    dsimp [B]
    linarith
  have hCB (k : ℕ) (hk : k ≤ n) : C k ≤ B ∧ D k ≤ B := by
    have hm : k ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    have he := Finset.single_le_sum (fun i _ => hterms i) hm
    dsimp [B]
    constructor <;> linarith [hC k,hD k]
  refine ⟨B,hB,?_⟩
  intro k hk S hS h hh a ha φ ψ
  exact ⟨(hb k S hS h hh a ha φ).trans (mul_le_mul_of_nonneg_right (hCB k hk).1 hS.1),
    (hd k S hS h hh a ha φ ψ).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCB k hk).2 hS.1) (abs_nonneg _))⟩

end RoughRegime.LatticePriors
