module

public import Mathlib


@[expose] public section
open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace RoughRegime.Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite continuous differentiability suffices for interchange of the
first two true Fréchet derivative directions. -/
lemma iteratedFDeriv_swap_head {n : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n+2 : ℕ) f x) (a b : E) (w : Fin n → E) :
    iteratedFDeriv ℝ (n+2) f x (Fin.cons a (Fin.cons b w)) =
      iteratedFDeriv ℝ (n+2) f x (Fin.cons b (Fin.cons a w)) := by
  let g : E → F := fun y => iteratedFDeriv ℝ n f y w
  have hg : ContDiffAt ℝ 2 g x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F w).contDiff.contDiffAt.comp x
      (hf.iteratedFDeriv_right (by simp [add_comm]))
  have hdf : DifferentiableAt ℝ (iteratedFDeriv ℝ (n+1) f) x :=
    hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self (n+1))
  have hid (a b : E) : iteratedFDeriv ℝ (n+2) f x (Fin.cons a (Fin.cons b w)) =
      fderiv ℝ (fderiv ℝ g) x a b := by
    rw [hdf.iteratedFDeriv_succ_apply_left']
    simp only [Fin.tail_cons,Fin.cons_zero]
    have heq : (fun y => iteratedFDeriv ℝ (n+1) f y (Fin.cons b w)) =ᶠ[𝓝 x]
        fun y => fderiv ℝ g y b := by
      filter_upwards [hf.eventually (by exact Ne.symm (ne_of_beq_false rfl))] with y hy
      have hdy : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
        hy.differentiableAt_iteratedFDeriv (by exact_mod_cast (show n < n+2 by omega))
      simpa only [Fin.tail_cons,Fin.cons_zero,g] using
        (hdy.iteratedFDeriv_succ_apply_left' (m := Fin.cons b w))
    rw [heq.fderiv_eq]
    have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [fderiv_clm_apply hdg (differentiableAt_const b)]
    simp
  rw [hid a b,hid b a]
  exact (hg.isSymmSndFDerivAt (by simp)) a b



lemma iteratedFDeriv_adjacent_swap (n : ℕ) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n+1 : ℕ) f x) (i : Fin n) (v : Fin (n+1) → E) :
    iteratedFDeriv ℝ (n+1) f x (v ∘ Equiv.swap i.castSucc i.succ) =
      iteratedFDeriv ℝ (n+1) f x v := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · have heq : v ∘ Equiv.swap (0 : Fin (n+2)) 1 =
          Fin.cons (v 1) (Fin.cons (v 0) (Fin.tail (Fin.tail v))) := by
        ext j
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
        · simp
        · simp
        · simp only [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne
            (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _),Fin.cons_succ]
          rfl
      have hdecomp : Fin.cons (v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail v))) = v := by
        rw [show v 1 = Fin.tail v 0 from rfl,Fin.cons_self_tail,Fin.cons_self_tail]
      simpa only [Fin.castSucc_zero,Fin.succ_zero_eq_one,heq,hdecomp] using
        iteratedFDeriv_swap_head hf (v 1) (v 0) (Fin.tail (Fin.tail v))
    · have hzero : (v ∘ Equiv.swap i.succ.castSucc i.succ.succ) 0 = v 0 := by
        simp only [Function.comp_apply,Fin.castSucc_succ,Equiv.swap_apply_of_ne_of_ne
          (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm]
      have htail : Fin.tail (v ∘ Equiv.swap i.succ.castSucc i.succ.succ) =
          Fin.tail v ∘ Equiv.swap i.castSucc i.succ := by
        funext j
        simp only [Fin.tail,Function.comp_apply,Fin.castSucc_succ]
        rw [← (Fin.succ_injective _).map_swap]
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ (n+1) f) x :=
        hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self (n+1))
      rw [hd.iteratedFDeriv_succ_apply_left',hd.iteratedFDeriv_succ_apply_left',hzero,htail]
      have he : (fun y => iteratedFDeriv ℝ (n+1) f y (Fin.tail v ∘ Equiv.swap i.castSucc i.succ)) =ᶠ[𝓝 x]
          fun y => iteratedFDeriv ℝ (n+1) f y (Fin.tail v) := by
        filter_upwards [hf.eventually (by exact Ne.symm (ne_of_beq_false rfl))] with y hy
        exact ih (hy.of_le (by exact_mod_cast (show n+1 ≤ n+2 by omega))) i (Fin.tail v)
      rw [he.fderiv_eq]



/-- The actual q-th Fréchet derivative of a real C^q function is symmetric.
This uses finite differentiability and genuine adjacent transpositions,
rather than analytic regularity. -/
theorem iteratedFDeriv_comp_perm_finite {q : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ q f x) (v : Fin q → E) (σ : Equiv.Perm (Fin q)) :
    iteratedFDeriv ℝ q f x (v ∘ σ) = iteratedFDeriv ℝ q f x v := by
  cases q with
  | zero => congr 1; exact Subsingleton.elim _ _
  | succ n =>
    let S : Submonoid (Equiv.Perm (Fin (n+1))) := {
      carrier := {p | ∀ v : Fin (n+1) → E,
        iteratedFDeriv ℝ (n+1) f x (v ∘ p) = iteratedFDeriv ℝ (n+1) f x v}
      one_mem' := by intro v; rfl
      mul_mem' := by
        intro a b ha hb v
        simpa only [Equiv.Perm.coe_mul,Function.comp_assoc] using (hb (v ∘ a)).trans (ha v) }
    have hgen : Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ) ⊆ S := by
      rintro p ⟨i,rfl⟩
      exact fun v => iteratedFDeriv_adjacent_swap n hf i v
    have hclosure := Submonoid.closure_le.mpr hgen
    have hmem : σ ∈ Submonoid.closure (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    exact hclosure hmem v



/-- Symmetry also holds for the actual within-set derivative at boundary
points, provided the interior is dense and derivatives are unique. -/
theorem iteratedFDerivWithin_comp_perm_finite {q : ℕ} {f : E → F} {s : Set E}
    (hf : ContDiffOn ℝ q f s) (hs : UniqueDiffOn ℝ s)
    (hdense : s ⊆ closure (interior s)) (v : Fin q → E) (σ : Equiv.Perm (Fin q))
    (x : E) (hx : x ∈ s) :
    iteratedFDerivWithin ℝ q f s x (v ∘ σ) = iteratedFDerivWithin ℝ q f s x v := by
  have hj := ContinuousOn.continuousOn_iteratedFDerivWithin hf hs (le_refl (q : ℕ∞ω))
  have hleft : ContinuousOn (fun y => iteratedFDerivWithin ℝ q f s y (v ∘ σ)) s :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => E) F (v ∘ σ)).continuous.comp_continuousOn hj
  have hright : ContinuousOn (fun y => iteratedFDerivWithin ℝ q f s y v) s :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => E) F v).continuous.comp_continuousOn hj
  have he : EqOn (fun y => iteratedFDerivWithin ℝ q f s y (v ∘ σ))
      (fun y => iteratedFDerivWithin ℝ q f s y v) (interior s) := by
    intro y hy
    have hfy := hf.contDiffAt (mem_interior_iff_mem_nhds.mp hy)
    dsimp only
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hs hfy (interior_subset hy)]
    exact iteratedFDeriv_comp_perm_finite hfy v σ
  exact he.of_subset_closure hleft hright interior_subset hdense hx

end RoughRegime.Calculus
