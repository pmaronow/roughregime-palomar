module

public import RoughRegime.SmoothCompactIntegral
public import RoughRegime.CompactJets
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension


@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace RoughRegime.Calculus

def partialFirst (K : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ K p (1,0)

def hadamardFactor (K : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s in Icc (0 : ℝ) 1, partialFirst K (s * p.1, p.2)

theorem partialFirst_contDiff (K : ℝ × ℝ → ℝ) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (partialFirst K) :=
  (hK.fderiv_right (by simp)).clm_apply contDiff_const

/-- Hadamard's factor is the actual integral of the first partial derivative.
Its smoothness follows by differentiation under the fixed compact interval. -/
theorem hadamardFactor_contDiff (K : ℝ × ℝ → ℝ) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (hadamardFactor K) := by
  unfold hadamardFactor
  apply contDiff_compactIntegral (fun p : ℝ × ℝ => fun s => partialFirst K (s * p.1, p.2)) _ (Icc (0 : ℝ) 1) isCompact_Icc
  exact (partialFirst_contDiff K hK).comp
    ((contDiff_snd.mul contDiff_fst.fst).prodMk contDiff_fst.snd)

theorem hadamardFactor_identity (K : ℝ × ℝ → ℝ) (hK : ContDiff ℝ ∞ K)
    (hzero : ∀ v : ℝ, K (0,v) = 0) (p : ℝ × ℝ) :
    K p = p.1 * hadamardFactor K p := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0)
    (f := K) (x := (0,p.2)) (y := (p.1,0)) (fun _ _ => hK.contDiffAt.of_le (by simp))
  have he : ∀ s : ℝ, fderiv ℝ K ((0,p.2) + s • (p.1,0)) (p.1,0) =
      p.1 * partialFirst K (s * p.1,p.2) := by
    intro s
    have hv : (p.1,0) = p.1 • ((1,0) : ℝ × ℝ) := by simp
    have hp : (0,p.2) + s • (p.1,0) = (s * p.1,p.2) := by simp
    rw [hp, hv, map_smul]
    rfl
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero,
    Nat.cast_one, inv_one, iteratedFDeriv_zero_apply, one_smul, pow_zero,
    Nat.reduceAdd, iteratedFDeriv_one_apply, hzero, zero_add] at ht
  have hp : ((0,p.2) : ℝ × ℝ) + (p.1,0) = p := by ext <;> simp
  rw [hp] at ht
  simp_rw [he] at ht
  rw [intervalIntegral.integral_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc,
    integral_const_mul] at ht
  exact ht

/-- Every smooth germ at the origin has a globally smooth representative
on a smaller closed square; this is constructed by a smooth coordinate cutoff. -/
theorem local_smooth_extension (K : ℝ × ℝ → ℝ) (N : Set (ℝ × ℝ))
    (hN : IsOpen N) (h0 : (0 : ℝ × ℝ) ∈ N) (hK : ContDiffOn ℝ ∞ K N) :
    ∃ r : ℝ, 0 < r ∧ ∃ L : ℝ × ℝ → ℝ, ContDiff ℝ ∞ L ∧
      ∀ p : ℝ × ℝ, |p.1| ≤ r → |p.2| ≤ r → L p = K p := by
  obtain ⟨R,hR,hRN⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hN.mem_nhds h0)
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := R / 2, rOut := R, rIn_pos := half_pos hR, rIn_lt_rOut := half_lt_self hR }
  let φ : ℝ → ℝ := fun u => u * b u
  have hφ : ContDiff ℝ ∞ φ := contDiff_id.mul b.contDiff
  have hφrange (u : ℝ) : |φ u| ≤ R := by
    by_cases hu : |u| ≤ R
    · dsimp [φ]
      rw [abs_mul, abs_of_nonneg b.nonneg]
      exact (mul_le_mul_of_nonneg_left b.le_one (abs_nonneg u)).trans (by simpa using hu)
    · have hz : b u = 0 := b.zero_of_le_dist (by simpa [Real.dist_eq] using le_of_lt (lt_of_not_ge hu))
      simp [φ,hz,hR.le]
  have hφeq (u : ℝ) (hu : |u| ≤ R / 2) : φ u = u := by
    have hb : b u = 1 := b.one_of_mem_closedBall (by simpa [b,Real.dist_eq] using hu)
    simp [φ,hb]
  let L : ℝ × ℝ → ℝ := fun p => K (φ p.1,φ p.2)
  have hargs (p : ℝ × ℝ) : (φ p.1,φ p.2) ∈ N := by
    apply hRN
    simpa only [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, max_le_iff] using
      And.intro (hφrange p.1) (hφrange p.2)
  have hL : ContDiff ℝ ∞ L := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact ((hK _ (hargs p)).contDiffAt (hN.mem_nhds (hargs p))).comp p
      ((hφ.contDiffAt.comp p contDiffAt_fst).prodMk (hφ.contDiffAt.comp p contDiffAt_snd))
  refine ⟨R / 2,half_pos hR,L,hL,?_⟩
  intro p hu hv
  dsimp [L]
  rw [hφeq p.1 hu,hφeq p.2 hv]

/-- A smooth local map has an actual globally smooth representative on a
smaller closed square. A smooth coordinate cutoff keeps its arguments inside
the original open neighborhood. The representative retains the vanishing
first-coordinate axis. -/
theorem local_smooth_axis_extension (K : ℝ × ℝ → ℝ) (N : Set (ℝ × ℝ))
    (hN : IsOpen N) (h0 : (0 : ℝ × ℝ) ∈ N) (hK : ContDiffOn ℝ ∞ K N)
    (hzero : ∀ v : ℝ, (0,v) ∈ N → K (0,v) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ L : ℝ × ℝ → ℝ, ContDiff ℝ ∞ L ∧
      (∀ v : ℝ, L (0,v) = 0) ∧
      (∀ p : ℝ × ℝ, |p.1| ≤ r → |p.2| ≤ r → L p = K p) := by
  obtain ⟨R,hR,hRN⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hN.mem_nhds h0)
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := R / 2, rOut := R, rIn_pos := half_pos hR, rIn_lt_rOut := half_lt_self hR }
  let φ : ℝ → ℝ := fun u => u * b u
  have hφ : ContDiff ℝ ∞ φ := contDiff_id.mul b.contDiff
  have hφrange (u : ℝ) : |φ u| ≤ R := by
    by_cases hu : |u| ≤ R
    · dsimp [φ]
      rw [abs_mul, abs_of_nonneg b.nonneg]
      exact (mul_le_mul_of_nonneg_left b.le_one (abs_nonneg u)).trans (by simpa using hu)
    · have hz : b u = 0 := b.zero_of_le_dist (by simpa [Real.dist_eq] using le_of_lt (lt_of_not_ge hu))
      simp [φ,hz,hR.le]
  have hφeq (u : ℝ) (hu : |u| ≤ R / 2) : φ u = u := by
    have hb : b u = 1 := b.one_of_mem_closedBall (by simpa [b,Real.dist_eq] using hu)
    simp [φ,hb]
  let L : ℝ × ℝ → ℝ := fun p => K (φ p.1,φ p.2)
  have hargs (p : ℝ × ℝ) : (φ p.1,φ p.2) ∈ N := by
    apply hRN
    simpa only [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, max_le_iff] using
      And.intro (hφrange p.1) (hφrange p.2)
  have hL : ContDiff ℝ ∞ L := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact ((hK _ (hargs p)).contDiffAt (hN.mem_nhds (hargs p))).comp p
      ((hφ.contDiffAt.comp p contDiffAt_fst).prodMk (hφ.contDiffAt.comp p contDiffAt_snd))
  refine ⟨R / 2, half_pos hR, L,hL,?_,?_⟩
  · intro v
    dsimp [L]
    have hz : φ 0 = 0 := by simp [φ]
    rw [hz]
    apply hzero
    simpa only [hz] using hargs (0,v)
  · intro p hu hv
    dsimp [L]
    rw [hφeq p.1 hu,hφeq p.2 hv]

/-- The local smooth Hadamard factorization needed for nonlinear application
restrictions. The smooth factor is constructed from a genuine derivative
integral; no divisibility or derivative bound is assumed. -/
theorem local_hadamard_factorization (K : ℝ × ℝ → ℝ) (N : Set (ℝ × ℝ))
    (hN : IsOpen N) (h0 : (0 : ℝ × ℝ) ∈ N) (hK : ContDiffOn ℝ ∞ K N)
    (hzero : ∀ v : ℝ, (0,v) ∈ N → K (0,v) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℝ × ℝ → ℝ, ContDiff ℝ ∞ F ∧
      ∀ p : ℝ × ℝ, |p.1| ≤ r → |p.2| ≤ r → K p = p.1 * F p := by
  obtain ⟨r,hr,L,hL,hzeroL,heq⟩ := local_smooth_axis_extension K N hN h0 hK hzero
  exact ⟨r,hr,hadamardFactor L,hadamardFactor_contDiff L hL,
    fun p hp1 hp2 => (heq p hp1 hp2).symm.trans (hadamardFactor_identity L hL hzeroL p)⟩

theorem local_hadamard_constant_first (K : ℝ × ℝ → ℝ) (k0 : ℝ) (N : Set (ℝ × ℝ))
    (hN : IsOpen N) (h0 : (0 : ℝ × ℝ) ∈ N) (hK : ContDiffOn ℝ ∞ K N)
    (hconstant : ∀ v : ℝ, (0,v) ∈ N → K (0,v) = k0) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℝ × ℝ → ℝ, ContDiff ℝ ∞ F ∧
      ∀ p : ℝ × ℝ, |p.1| ≤ r → |p.2| ≤ r → K p = k0+p.1*F p := by
  obtain ⟨r,hr,F,hF,he⟩ := local_hadamard_factorization (fun p => K p-k0) N hN h0
    (hK.sub contDiffOn_const) (fun v hv => by rw [hconstant v hv]; ring)
  refine ⟨r,hr,F,hF,?_⟩
  intro p hp1 hp2
  have hh := he p hp1 hp2
  linarith

theorem local_hadamard_constant_second (K : ℝ × ℝ → ℝ) (k0 : ℝ) (N : Set (ℝ × ℝ))
    (hN : IsOpen N) (h0 : (0 : ℝ × ℝ) ∈ N) (hK : ContDiffOn ℝ ∞ K N)
    (hconstant : ∀ u : ℝ, (u,0) ∈ N → K (u,0) = k0) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℝ × ℝ → ℝ, ContDiff ℝ ∞ F ∧
      ∀ p : ℝ × ℝ, |p.1| ≤ r → |p.2| ≤ r → K p = k0+p.2*F p := by
  let M : Set (ℝ × ℝ) := Prod.swap ⁻¹' N
  have hM : IsOpen M := hN.preimage continuous_swap
  have hM0 : (0 : ℝ × ℝ) ∈ M := h0
  have hswap : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K (p.2,p.1)) M :=
    hK.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hp => hp)
  obtain ⟨r,hr,F,hF,he⟩ := local_hadamard_constant_first (fun p : ℝ × ℝ => K (p.2,p.1))
    k0 M hM hM0 hswap (fun v hv => hconstant v hv)
  refine ⟨r,hr,fun p => F (p.2,p.1),hF.comp (contDiff_snd.prodMk contDiff_fst),?_⟩
  intro p hp1 hp2
  exact he (p.2,p.1) hp2 hp1

/-- The unrestricted smooth germ has the two-coordinate version of Hadamard's
factorization. This handles the minimum-smoothness case in Lemma14(b). -/
theorem local_hadamard_two_factors (K : ℝ × ℝ → ℝ) (N : Set (ℝ × ℝ))
    (hN : IsOpen N) (h0 : (0 : ℝ × ℝ) ∈ N) (hK : ContDiffOn ℝ ∞ K N) :
    ∃ r : ℝ, 0 < r ∧ ∃ F G : ℝ × ℝ → ℝ,
      ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ G ∧
      ∀ p : ℝ × ℝ, |p.1| ≤ r → |p.2| ≤ r →
        K p = K (0,0)+p.1*F p+p.2*G p := by
  obtain ⟨r,hr,L,hL,he⟩ := local_smooth_extension K N hN h0 hK
  let A : ℝ × ℝ → ℝ := fun p => L p-L (0,p.2)
  let B : ℝ × ℝ → ℝ := fun p => L (0,p.1)-L (0,0)
  have hA : ContDiff ℝ ∞ A := hL.sub (hL.comp (contDiff_const.prodMk contDiff_snd))
  have hB : ContDiff ℝ ∞ B := (hL.comp (contDiff_const.prodMk contDiff_fst)).sub contDiff_const
  have hA0 : ∀ v : ℝ, A (0,v) = 0 := by intro v; simp [A]
  have hB0 : ∀ v : ℝ, B (0,v) = 0 := by intro v; simp [B]
  refine ⟨r,hr,hadamardFactor A,fun p => hadamardFactor B (p.2,p.1),
    hadamardFactor_contDiff A hA,
    (hadamardFactor_contDiff B hB).comp (contDiff_snd.prodMk contDiff_fst),?_⟩
  intro p hp1 hp2
  have hu := hadamardFactor_identity A hA hA0 p
  have hv := hadamardFactor_identity B hB hB0 (p.2,p.1)
  have h00 := he (0,0) (by simpa using hr.le) (by simpa using hr.le)
  have hpp := he p hp1 hp2
  dsimp [A] at hu
  dsimp [B] at hv
  rw [← hpp,← h00]
  linarith

end RoughRegime.Calculus
