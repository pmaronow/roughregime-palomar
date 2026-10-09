module

public import RoughRegime.HolderComposition


@[expose] public section
/-! Genuine uniform finite Hölder product and quotient estimates. The input
functions only have the paper's finite regularity on the closed cube. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model
set_option maxHeartbeats 1800000

theorem holder_pair_jet_bounds {d : ℕ} (f g : Covariate d → ℝ) (t Hf Hg : ℝ)
    (hHf : 0 ≤ Hf) (hHg : 0 ≤ Hg) (hf : f ∈ holderBall t Hf) (hg : g ∈ holderBall t Hg) :
    let B := 2*(holderJetConstant d t Hf+holderJetConstant d t Hg)+1
    (∀ q ≤ holderOrder t, ∀ x ∈ cube d,
      ‖iteratedFDerivWithin ℝ q (fun x => (f x,g x)) (cube d) x‖ ≤ B) ∧
    (∀ q ≤ holderOrder t, ∀ x ∈ cube d, ∀ y ∈ cube d,
      ‖iteratedFDerivWithin ℝ q (fun x => (f x,g x)) (cube d) x-
        iteratedFDerivWithin ℝ q (fun x => (f x,g x)) (cube d) y‖ ≤ B*‖x-y‖^holderExponent t) := by
  let Df := holderJetConstant d t Hf
  let Dg := holderJetConstant d t Hg
  have hDf : 0 ≤ Df := holderJetConstant_nonneg d t Hf hHf
  have hDg : 0 ≤ Dg := holderJetConstant_nonneg d t Hg hHg
  let B := 2*(Df+Dg)+1
  have hDfB : Df ≤ B := by dsimp only [B]; linarith
  have hDgB : Dg ≤ B := by dsimp only [B]; linarith
  have h2DfB : 2*Df ≤ B := by dsimp only [B]; linarith
  have h2DgB : 2*Dg ≤ B := by dsimp only [B]; linarith
  have hfreg := (holderBall_regular f t Hf hf).2
  have hgreg := (holderBall_regular g t Hg hg).2
  have hjet (q : ℕ) (hq : q ≤ holderOrder t) (x : Covariate d) (hx : x ∈ cube d) :
      iteratedFDerivWithin ℝ q (fun x => (f x,g x)) (cube d) x =
        (iteratedFDerivWithin ℝ q f (cube d) x).prod (iteratedFDerivWithin ℝ q g (cube d) x) :=
    iteratedFDerivWithin_prodMk (hfreg x hx) (hgreg x hx) (uniqueDiffOn_cube d) hx (by exact_mod_cast hq)
  constructor
  · intro q hq x hx
    rw [hjet q hq x hx,ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact (holderBall_jet_bound_uniform f t Hf hHf hf q hq x hx).trans hDfB
    · exact (holderBall_jet_bound_uniform g t Hg hHg hg q hq x hx).trans hDgB
  · intro q hq x hx y hy
    rw [hjet q hq x hx,hjet q hq y hy]
    have he :
        (iteratedFDerivWithin ℝ q f (cube d) x).prod (iteratedFDerivWithin ℝ q g (cube d) x)-
          (iteratedFDerivWithin ℝ q f (cube d) y).prod (iteratedFDerivWithin ℝ q g (cube d) y) =
        (iteratedFDerivWithin ℝ q f (cube d) x-iteratedFDerivWithin ℝ q f (cube d) y).prod
          (iteratedFDerivWithin ℝ q g (cube d) x-iteratedFDerivWithin ℝ q g (cube d) y) := by
      ext v <;> rfl
    rw [he,ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact (holderBall_jet_modulus_uniform f t Hf hHf hf q hq x y hx hy).trans
        (mul_le_mul_of_nonneg_right h2DfB (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (holderBall_jet_modulus_uniform g t Hg hHg hg q hq x y hx hy).trans
        (mul_le_mul_of_nonneg_right h2DgB (Real.rpow_nonneg (norm_nonneg _) _))

theorem uniform_holder_quotient (d : ℕ) (t Hf Hg epsilon : ℝ)
    (ht : 0 < t) (hHf : 0 ≤ Hf) (hHg : 0 ≤ Hg) (hepsilon : 0 < epsilon) :
    ∃ B > 0, ∀ f g : Covariate d → ℝ,
      f ∈ holderBall t Hf → g ∈ holderBall t Hg →
      (∀ x ∈ cube d, epsilon ≤ g x) → (fun x => f x/g x) ∈ holderBall t B := by
  let K : Set (ℝ×ℝ) := Icc (-Hf) Hf ×ˢ Icc epsilon Hg
  let T : Set (ℝ×ℝ) := univ ×ˢ Ioi (0 : ℝ)
  let outer : ℝ×ℝ → ℝ := fun z => z.1/z.2
  have hT : IsOpen T := isOpen_univ.prod isOpen_Ioi
  have hKT : K ⊆ T := fun _ hx => ⟨mem_univ _,hepsilon.trans_le hx.2.1⟩
  have hg : ContDiffOn ℝ ∞ outer T := by
    intro z hz
    exact contDiffWithinAt_fst.div contDiffWithinAt_snd (ne_of_gt hz.2)
  let C := 2*(holderJetConstant d t Hf+holderJetConstant d t Hg)+1
  have hC : 0 ≤ C := by
    have h1 := holderJetConstant_nonneg d t Hf hHf
    have h2 := holderJetConstant_nonneg d t Hg hHg
    dsimp only [C]
    positivity
  obtain ⟨B,hB,hcomp⟩ := uniform_holder_comp_of_jets d t C ht hC outer T K hT
    (isCompact_Icc.prod isCompact_Icc) ((convex_Icc _ _).prod (convex_Icc _ _)) hKT hg
  refine ⟨B,hB,?_⟩
  intro f g hf hg hpositive
  obtain ⟨hb,hm⟩ := holder_pair_jet_bounds f g t Hf Hg hHf hHg hf hg
  apply hcomp (fun x => (f x,g x))
    ((holderBall_regular f t Hf hf).2.prodMk (holderBall_regular g t Hg hg).2) _ hb hm
  intro x hx
  exact ⟨abs_le.mp (holderNorm_bounds_values f t Hf hHf hf x hx),
    hpositive x hx,(le_abs_self _).trans (holderNorm_bounds_values g t Hg hHg hg x hx)⟩

theorem uniform_holder_product (d : ℕ) (t Hf Hg : ℝ)
    (ht : 0 < t) (hHf : 0 ≤ Hf) (hHg : 0 ≤ Hg) :
    ∃ B > 0, ∀ f g : Covariate d → ℝ,
      f ∈ holderBall t Hf → g ∈ holderBall t Hg → (fun x => f x*g x) ∈ holderBall t B := by
  let K : Set (ℝ×ℝ) := Icc (-Hf) Hf ×ˢ Icc (-Hg) Hg
  let outer : ℝ×ℝ → ℝ := fun z => z.1*z.2
  let C := 2*(holderJetConstant d t Hf+holderJetConstant d t Hg)+1
  have hC : 0 ≤ C := by
    have h1 := holderJetConstant_nonneg d t Hf hHf
    have h2 := holderJetConstant_nonneg d t Hg hHg
    dsimp only [C]
    positivity
  obtain ⟨B,hB,hcomp⟩ := uniform_holder_comp_of_jets d t C ht hC outer univ K isOpen_univ
    (isCompact_Icc.prod isCompact_Icc) ((convex_Icc _ _).prod (convex_Icc _ _)) (subset_univ K)
    (contDiff_fst.mul contDiff_snd).contDiffOn
  refine ⟨B,hB,?_⟩
  intro f g hf hg
  obtain ⟨hb,hm⟩ := holder_pair_jet_bounds f g t Hf Hg hHf hHg hf hg
  apply hcomp (fun x => (f x,g x))
    ((holderBall_regular f t Hf hf).2.prodMk (holderBall_regular g t Hg hg).2) _ hb hm
  intro x hx
  exact ⟨abs_le.mp (holderNorm_bounds_values f t Hf hHf hf x hx),
    abs_le.mp (holderNorm_bounds_values g t Hg hHg hg x hx)⟩

theorem uniform_holder_inverse (d : ℕ) (t H epsilon : ℝ)
    (ht : 0 < t) (hH : 0 ≤ H) (hepsilon : 0 < epsilon) :
    ∃ B > 0, ∀ g : Covariate d → ℝ,
      g ∈ holderBall t H → (∀ x ∈ cube d, epsilon ≤ g x) →
        (fun x => (g x)⁻¹) ∈ holderBall t B := by
  obtain ⟨B,hB,hquot⟩ := uniform_holder_quotient d t 1 H epsilon ht zero_le_one hH hepsilon
  refine ⟨B,hB,?_⟩
  intro g hg hp
  simpa only [one_div] using hquot (fun _ => 1) g (const_mem_holderBall ht (by norm_num)) hg hp

end RoughRegime.Model
