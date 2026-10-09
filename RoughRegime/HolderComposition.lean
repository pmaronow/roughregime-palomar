module

public import RoughRegime.HolderCalculus


@[expose] public section
/-! Uniform finite Hölder composition on the closed cube. The outer constants
are derived from genuine smoothness on a compact convex range. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Calculus
set_option maxHeartbeats 1600000
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_finite_jet_bound_on_open (g : F → ℝ) (T K : Set F)
    (hT : IsOpen T) (hK : IsCompact K) (hKT : K ⊆ T)
    (hg : ContDiffOn ℝ ∞ g T) (n : ℕ) :
    ∃ C ≥ 0, ∀ q ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ q g x‖ ≤ C := by
  have he (q : Fin (n+1)) : ∃ C ≥ 0, ∀ x ∈ K, ‖iteratedFDeriv ℝ q.val g x‖ ≤ C := by
    have hc : ContinuousOn (fun x => ‖iteratedFDeriv ℝ q.val g x‖) K := by
      intro x hx
      exact (((hg.contDiffAt (hT.mem_nhds (hKT hx))).iteratedFDeriv_right
        (m := 0) (i := q.val) (by simp)).continuousAt.norm).continuousWithinAt
    obtain ⟨C,hC⟩ := hK.bddAbove_image hc
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro x hx
    exact (hC ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  choose C hC hb using he
  refine ⟨∑ q,C q,Finset.sum_nonneg (fun q _ => hC q),?_⟩
  intro q hq x hx
  let i : Fin (n+1) := ⟨q,by omega⟩
  exact (hb i x hx).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

theorem compact_jet_difference_bound (g : F → ℝ) (T K : Set F)
    (hT : IsOpen T) (hconv : Convex ℝ K) (hKT : K ⊆ T)
    (hg : ContDiffOn ℝ ∞ g T) (q : ℕ) (C : ℝ)
    (hb : ∀ x ∈ K, ‖iteratedFDeriv ℝ (q+1) g x‖ ≤ C)
    (x y : F) (hx : x ∈ K) (hy : y ∈ K) :
    ‖iteratedFDeriv ℝ q g x-iteratedFDeriv ℝ q g y‖ ≤ C*‖x-y‖ := by
  have hd : ∀ z ∈ K, DifferentiableAt ℝ (iteratedFDeriv ℝ q g) z := by
    intro z hz
    exact ((hg.contDiffAt (hT.mem_nhds (hKT hz))).iteratedFDeriv_right
      (m := 1) (i := q) (by simp)).differentiableAt (by norm_num)
  have hbound : ∀ z ∈ K, ‖fderiv ℝ (iteratedFDeriv ℝ q g) z‖ ≤ C := by
    intro z hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hb z hz
  exact hconv.norm_image_sub_le_of_norm_fderiv_le hd hbound hy hx

end RoughRegime.Calculus
namespace RoughRegime.Model
open RoughRegime.Calculus
set_option maxHeartbeats 1800000

/-- One radius controls every genuine finite Hölder input whose actual jets
have the indicated common bound and modulus. These jet conditions will be
derived from the input Hölder balls in the product and quotient theorems. -/
theorem uniform_holder_comp_of_jets {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℕ) (t H : ℝ) (ht : 0 < t) (hH : 0 ≤ H)
    (g : F → ℝ) (T K : Set F) (hT : IsOpen T) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hKT : K ⊆ T) (hg : ContDiffOn ℝ ∞ g T) :
    ∃ B > 0, ∀ f : Covariate d → F,
      ContDiffOn ℝ (holderOrder t) f (cube d) → MapsTo f (cube d) K →
      (∀ q ≤ holderOrder t, ∀ x ∈ cube d, ‖iteratedFDerivWithin ℝ q f (cube d) x‖ ≤ H) →
      (∀ q ≤ holderOrder t, ∀ x ∈ cube d, ∀ y ∈ cube d,
        ‖iteratedFDerivWithin ℝ q f (cube d) x-iteratedFDerivWithin ℝ q f (cube d) y‖ ≤
          H*‖x-y‖^holderExponent t) →
      (g ∘ f) ∈ holderBall t B := by
  classical
  let k := holderOrder t
  obtain ⟨C0,hC0,houter⟩ := compact_finite_jet_bound_on_open g T K hT hK hKT hg (k+1)
  let C := max 1 (max C0 (max H (C0*H)))
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hOC : C0 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hHC : H ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hPC : C0*H ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hex (q : Fin (k+1)) := uniform_taylorComp_norm_constant
    (E := Covariate d) (F := F) (G := ℝ) q.val C hC
  choose D hD hnorm using hex
  obtain ⟨Dm,hDm,hmod⟩ := uniform_taylorComp_difference_constant
    (E := Covariate d) (F := F) (G := ℝ) k C
  let B := (∑ q,D q)+Dm+1
  have hsum : 0 ≤ ∑ q,D q := Finset.sum_nonneg (fun q _ => (hD q).le)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨2*B,by positivity,?_⟩
  intro f hf hmap hb hm
  have hmapT : MapsTo f (cube d) T := fun _ hx => hKT (hmap hx)
  have hjet (q : ℕ) (hq : q ≤ k) (x : Covariate d) (hx : x ∈ cube d) :
      iteratedFDerivWithin ℝ q (g ∘ f) (cube d) x =
        (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeriesWithin ℝ f (cube d) x) q :=
    iteratedFDerivWithin_comp_on_open f g (cube d) T q (hf.of_le (by exact_mod_cast hq))
      (hg.of_le (by simp)) (uniqueDiffOn_cube d) hT hmapT x hx
  have hBq (q : Fin (k+1)) : D q ≤ B := by
    have hh := Finset.single_le_sum (fun i _ => (hD i).le) (Finset.mem_univ q)
    dsimp only [B]
    linarith
  have hDmB : Dm ≤ B := by dsimp only [B]; linarith
  apply holderBall_of_within_jet_bounds (g ∘ f) t B ht hB.le
    ((hg.of_le (by simp)).comp hf hmapT)
  · intro q hq x hx
    rw [hjet q hq x hx]
    let i : Fin (k+1) := ⟨q,by omega⟩
    apply (hnorm i _ _ _ _).trans (hBq i)
    · intro j hj
      exact (houter j (by omega) (f x) (hmap hx)).trans hOC
    · intro j hj
      exact (hb j (by omega) x hx).trans hHC
  · intro x hx y hy
    rw [hjet k le_rfl x hx,hjet k le_rfl y hy]
    let delta := ‖x-y‖^holderExponent t
    have hdelta : 0 ≤ delta := Real.rpow_nonneg (norm_nonneg _) _
    have hvalue : ‖f x-f y‖ ≤ H*delta := by
      simpa only [delta,← dist_eq_norm,dist_iteratedFDerivWithin_zero] using hm 0 (Nat.zero_le _) x hx y hy
    let a : BoundedJetPair (Covariate d) F ℝ k C := {
      q1 := ftaylorSeries ℝ g (f x)
      q2 := ftaylorSeries ℝ g (f y)
      p1 := ftaylorSeriesWithin ℝ f (cube d) x
      p2 := ftaylorSeriesWithin ℝ f (cube d) y
      delta := delta
      delta_nonneg := hdelta
      outer := fun j hj => (houter j (by omega) (f x) (hmap hx)).trans hOC
      inner1 := fun j hj => (hb j hj x hx).trans hHC
      inner2 := fun j hj => (hb j hj y hy).trans hHC
      outer_difference := by
        intro j hj
        have hh := compact_jet_difference_bound g T K hT hconv hKT hg j C0
          (fun z hz => houter (j+1) (by omega) z hz) (f x) (f y) (hmap hx) (hmap hy)
        apply hh.trans
        calc
          C0*‖f x-f y‖ ≤ C0*(H*delta) := mul_le_mul_of_nonneg_left hvalue hC0
          _ = (C0*H)*delta := by ring
          _ ≤ C*delta := mul_le_mul_of_nonneg_right hPC hdelta
      inner_difference := by
        intro j hj
        exact (hm j hj x hx y hy).trans (mul_le_mul_of_nonneg_right hHC hdelta) }
    exact (hmod a).trans (mul_le_mul_of_nonneg_right hDmB hdelta)

end RoughRegime.Model
