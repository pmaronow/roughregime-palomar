module

public import RoughRegime.HadamardSmooth
public import RoughRegime.ReciprocalComposition


@[expose] public section
open Set
open scoped ContDiff

noncomputable section

namespace RoughRegime.LatticePriors

open RoughRegime.Calculus RoughRegime.Upper

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma oscillator_denominator_positive (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (h : ℝ) (hh : h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi)) (φ : ℝ) :
    0 < intervalCenter lo hi + h * Real.cos φ := by
  have hw : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
  have habs : |h| ≤ intervalHalfWidth lo hi := abs_le.mpr hh
  have hcos : |h * Real.cos φ| ≤ intervalHalfWidth lo hi := by
    rw [abs_mul]
    exact (mul_le_mul habs (Real.abs_cos_le_one _) (abs_nonneg _) hw.le).trans_eq (by ring)
  have hden : lo ≤ intervalCenter lo hi + h * Real.cos φ := by
    have hh' := (abs_le.mp hcos).1
    unfold intervalCenter intervalHalfWidth at *
    linarith
  exact hlo.trans_le hden

theorem familyOuter_contDiffAt (κ : P → ℝ → ℝ)
    (hκ : ContDiff ℝ ∞ (Function.uncurry κ)) (center S : ℝ) (p : P)
    (v : ℝ × (ℝ × ℝ)) (hden : center + v.1 * Real.cos v.2.2 ≠ 0) :
    ContDiffAt ℝ ∞
      (fun y : (ℝ × P) × (ℝ × (ℝ × ℝ)) =>
        oscillatorOuter (κ y.1.2) center y.1.1 y.2) ((S,p),v) := by
  change ContDiffAt ℝ ∞ (Function.uncurry κ ∘
    (fun y : (ℝ × P) × (ℝ × (ℝ × ℝ)) =>
      (y.1.2, y.1.1 * y.2.2.1 / (center + y.2.1 * Real.cos y.2.2.2)))) ((S,p),v)
  apply hκ.contDiffAt.comp ((S,p),v)
  exact contDiffAt_fst.snd.prodMk
    ((contDiffAt_fst.fst.mul contDiffAt_snd.snd.fst).div
      (contDiffAt_const.add (contDiffAt_snd.fst.mul contDiffAt_snd.snd.snd.cos)) hden)

/-- Compactness bounds genuine partial jets uniformly across an entire
smooth scalar family. Smoothness of the partial jet is proved from the joint
family, and its amplitude-zero identity is exact. -/
theorem familyOuter_compact_jet_bound (κ : P → ℝ → ℝ)
    (hκ : ContDiff ℝ ∞ (Function.uncurry κ)) (hκ0 : ∀ p, κ p 0 = 0)
    (KP : Set P) (hKP : IsCompact KP) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ KP, ∀ S ∈ Icc (0 : ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ φ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖iteratedFDeriv ℝ n (oscillatorOuter (κ p) (intervalCenter lo hi) S) (h,(a,φ))‖ ≤ C*S := by
  let V : Set (ℝ × (ℝ × ℝ)) := Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi) ×ˢ
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi))
  let K : Set (P × (ℝ × (ℝ × ℝ))) := KP ×ˢ V
  have hK : IsCompact K := hKP.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  let F : (ℝ × P) → (ℝ × (ℝ × ℝ)) → ℝ :=
    fun q v => oscillatorOuter (κ q.2) (intervalCenter lo hi) q.1 v
  let J : ℝ → (P × (ℝ × (ℝ × ℝ))) → ((ℝ × (ℝ × ℝ)) [×n]→L[ℝ] ℝ) :=
    fun S y => iteratedFDeriv ℝ n (F (S,y.1)) y.2
  have hJ : ∀ y ∈ Icc (0 : ℝ) 1 ×ˢ K,
      ContDiffAt ℝ ∞ (Function.uncurry J) y := by
    intro y hy
    have hden := oscillator_denominator_positive lo hi hlo hlt y.2.2.1 hy.2.2.1 y.2.2.2.2
    have hf : ContDiffAt ℝ ∞ (Function.uncurry F) ((y.1,y.2.1),y.2.2) :=
      familyOuter_contDiffAt κ hκ (intervalCenter lo hi) y.1 y.2.1 y.2.2 hden.ne'
    have hj := contDiffAt_parametric_iteratedFDeriv F (y.1,y.2.1) y.2.2 hf n
    exact hj.comp y
      ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  have hzero : ∀ y, J 0 y = 0 := by
    intro y
    have he : F (0,y.1) = fun _ => (0 : ℝ) := by
      funext v
      simp [F,oscillatorOuter,hκ0]
    dsimp [J]
    rw [he]
    simp
  obtain ⟨C,hC,hbound⟩ := compact_amplitude_jet_bound J K hK hJ hzero 0
  refine ⟨C,hC,?_⟩
  intro p hp S hS h hh a ha φ hφ
  have hb := hbound S hS (p,(h,(a,φ))) ⟨hp,hh,ha,hφ⟩
  simpa only [norm_iteratedFDeriv_zero,J,F] using hb

theorem familyOuter_jet_bound (κ : P → ℝ → ℝ)
    (hκ : ContDiff ℝ ∞ (Function.uncurry κ)) (hκ0 : ∀ p, κ p 0 = 0)
    (KP : Set P) (hKP : IsCompact KP) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ KP, ∀ S ∈ Icc (0 : ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ φ : ℝ,
      ‖iteratedFDeriv ℝ n (oscillatorOuter (κ p) (intervalCenter lo hi) S) (h,(a,φ))‖ ≤ C*S := by
  obtain ⟨C,hC,hbound⟩ := familyOuter_compact_jet_bound κ hκ hκ0 KP hKP lo hi hlo hlt n
  refine ⟨C,hC,?_⟩
  intro p hp S hS h hh a ha φ
  let k : ℤ := Int.floor (φ / (2 * Real.pi))
  let ψ : ℝ := φ - (k : ℝ) * (2 * Real.pi)
  have hT : 0 < 2 * Real.pi := by positivity
  have hψ : ψ ∈ Icc (0 : ℝ) (2 * Real.pi) := by
    have hlo' := mul_le_mul_of_nonneg_right (Int.floor_le (φ / (2 * Real.pi))) hT.le
    have hhi' := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (φ / (2 * Real.pi))) hT
    rw [div_mul_cancel₀ _ hT.ne'] at hlo' hhi'
    dsimp [ψ,k]
    constructor <;> nlinarith
  let v : ℝ × (ℝ × ℝ) := (h,(a,ψ))
  let t : ℝ × (ℝ × ℝ) := (0,(0,(k : ℝ)*(2*Real.pi)))
  have hfun : (fun y => oscillatorOuter (κ p) (intervalCenter lo hi) S (y+t)) =
      oscillatorOuter (κ p) (intervalCenter lo hi) S := by
    funext y
    simp [oscillatorOuter,t,Real.cos_add_int_mul_two_pi]
  have hshift : iteratedFDeriv ℝ n (oscillatorOuter (κ p) (intervalCenter lo hi) S) (v+t) =
      iteratedFDeriv ℝ n (oscillatorOuter (κ p) (intervalCenter lo hi) S) v := by
    rw [← iteratedFDeriv_comp_add_right n t v,hfun]
  have hv : v+t = (h,(a,φ)) := by ext <;> simp [v,t,ψ]
  rw [hv] at hshift
  rw [hshift]
  exact hbound p hp S hS h hh a ha ψ hψ

theorem familyOuter_jet_phase_difference_bound (κ : P → ℝ → ℝ)
    (hκ : ContDiff ℝ ∞ (Function.uncurry κ)) (hκ0 : ∀ p, κ p 0 = 0)
    (KP : Set P) (hKP : IsCompact KP) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ KP, ∀ S ∈ Icc (0 : ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ φ ψ : ℝ,
      ‖iteratedFDeriv ℝ n (oscillatorOuter (κ p) (intervalCenter lo hi) S) (h,(a,φ)) -
        iteratedFDeriv ℝ n (oscillatorOuter (κ p) (intervalCenter lo hi) S) (h,(a,ψ))‖ ≤ C*S*|φ-ψ| := by
  obtain ⟨C,hC,hbound⟩ := familyOuter_jet_bound κ hκ hκ0 KP hKP lo hi hlo hlt (n+1)
  refine ⟨C,hC,?_⟩
  intro p hp S hS h hh a ha φ ψ
  let T : Set (ℝ × (ℝ × ℝ)) := Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi) ×ˢ
    (Icc (0 : ℝ) 1 ×ˢ univ)
  have hconv : Convex ℝ T := (convex_Icc _ _).prod ((convex_Icc _ _).prod convex_univ)
  let f := oscillatorOuter (κ p) (intervalCenter lo hi) S
  have hf (y : ℝ × (ℝ × ℝ)) (hy : y ∈ T) : ContDiffAt ℝ ∞ f y := by
    have he := familyOuter_contDiffAt κ hκ (intervalCenter lo hi) S p y
      (oscillator_denominator_positive lo hi hlo hlt y.1 hy.1 y.2.2).ne'
    exact he.comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hd (y : ℝ × (ℝ × ℝ)) (hy : y ∈ T) : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
    ((hf y hy).iteratedFDeriv_right (m := 1) (i := n) (by simp)).differentiableAt (by norm_num)
  have hb (y : ℝ × (ℝ × ℝ)) (hy : y ∈ T) : ‖fderiv ℝ (iteratedFDeriv ℝ n f) y‖ ≤ C*S := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hbound p hp S hS y.1 hy.1 y.2.1 hy.2.1 y.2.2
  have he := hconv.norm_image_sub_le_of_norm_fderiv_le hd hb
    (show (h,(a,ψ)) ∈ T from ⟨hh,ha,mem_univ _⟩)
    (show (h,(a,φ)) ∈ T from ⟨hh,ha,mem_univ _⟩)
  simpa [f,Prod.norm_def,max_eq_right (abs_nonneg (φ-ψ))] using he

theorem familyOuter_finite_jet_bound (κ : P → ℝ → ℝ)
    (hκ : ContDiff ℝ ∞ (Function.uncurry κ)) (hκ0 : ∀ p, κ p 0 = 0)
    (KP : Set P) (hKP : IsCompact KP) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ KP, ∀ k ≤ n, ∀ S ∈ Icc (0 : ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ φ ψ : ℝ,
      ‖iteratedFDeriv ℝ k (oscillatorOuter (κ p) (intervalCenter lo hi) S) (h,(a,φ))‖ ≤ C*S ∧
      ‖iteratedFDeriv ℝ k (oscillatorOuter (κ p) (intervalCenter lo hi) S) (h,(a,φ)) -
        iteratedFDeriv ℝ k (oscillatorOuter (κ p) (intervalCenter lo hi) S) (h,(a,ψ))‖ ≤ C*S*|φ-ψ| := by
  choose C hC hb using fun k => familyOuter_jet_bound κ hκ hκ0 KP hKP lo hi hlo hlt k
  choose D hD hd using fun k => familyOuter_jet_phase_difference_bound κ hκ hκ0 KP hKP lo hi hlo hlt k
  let B : ℝ := 1 + ∑ k ∈ Finset.range (n+1), (C k+D k)
  have hterms (k : ℕ) : 0 ≤ C k+D k := by linarith [hC k,hD k]
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
  intro p hp k hk S hS h hh a ha φ ψ
  exact ⟨(hb k p hp S hS h hh a ha φ).trans (mul_le_mul_of_nonneg_right (hCB k hk).1 hS.1),
    (hd k p hp S hS h hh a ha φ ψ).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCB k hk).2 hS.1) (abs_nonneg _))⟩

/-- Signed amplitudes are compact real coefficients. This concrete family is
the smooth factor used in Hadamard's lemma. -/
def hadamardScalarFamily (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (z : ℝ) : ℝ :=
  z * F (p.1*z,p.2*z)

theorem hadamardScalarFamily_contDiff (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Function.uncurry (hadamardScalarFamily F)) :=
  contDiff_snd.mul (hF.comp
    ((contDiff_fst.fst.mul contDiff_snd).prodMk (contDiff_fst.snd.mul contDiff_snd)))

theorem hadamardScalarFamily_zero (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    hadamardScalarFamily F p 0 = 0 := by simp [hadamardScalarFamily]

end RoughRegime.LatticePriors
