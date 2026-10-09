module

public import RoughRegime.GlobalKProfiles


@[expose] public section
open Set
open scoped BigOperators ContDiff
noncomputable section
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper

/-- The literal global source profile stays in the amplitude-scaled local
range, including outside the union of the blocks. No ambient density bound
is needed because the numerator vanishes there. -/
theorem globalProfile_normalized_abs_bound {D N : ℕ}
    (offset ell p0 A lo hi h : ℝ) (hell : 0 < ell) (hlo : 0 < lo) (hlt : lo < hi)
    (hh : h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi))
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (hin01 : ∀ y, inner y ∈ Icc (0 : ℝ) 1)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
    (σ S : GridPair D N → ℝ) (hσ : ∀ b, |σ b| ≤ 1)
    (hS : ∀ b, S b ∈ Icc (0 : ℝ) 1) (x : Model.Covariate (D+1)) :
    |globalProfile offset ell p0 (intervalCenter lo hi) h A inner outer θ phase σ S x| ≤ |A|/lo := by
  by_cases hx : ∃ b : GridBlock D N, x ∈ gridBlockOpen offset ell b
  · obtain ⟨b,hb⟩ := hx
    rw [globalProfile_eq_local offset ell p0 (intervalCenter lo hi) h A hell inner outer
      hin hout θ phase σ S b x hb,
      blockProfile_eq_oscillator A (σ b.1) (S b.1) p0 (intervalCenter lo hi) h (θ b.1)
        (RoughRegime.Lower.sign b.2) inner outer (phase b.1) hiota]
    let y := gridCoords offset ell b x
    let φ := θ b.1 + phase b.1 y
    have hab : |RoughRegime.Lower.sign b.2*h| ≤ intervalHalfWidth lo hi := by
      rw [abs_mul]
      have hs : |RoughRegime.Lower.sign b.2| = 1 := by cases b.2 <;> norm_num [RoughRegime.Lower.sign]
      rw [hs,one_mul]
      exact abs_le.mpr hh
    have hw : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
    have hc : |(RoughRegime.Lower.sign b.2*h)*Real.cos φ| ≤ intervalHalfWidth lo hi := by
      rw [abs_mul]
      exact (mul_le_mul hab (Real.abs_cos_le_one _) (abs_nonneg _) hw.le).trans_eq (by ring)
    have hd : lo ≤ intervalCenter lo hi + (RoughRegime.Lower.sign b.2*h)*Real.cos φ := by
      have hc' := (abs_le.mp hc).1
      unfold intervalCenter intervalHalfWidth at *
      linarith
    have hn : |S b.1*inner y| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg (hS b.1).1 (hin01 y).1)]
      exact (mul_le_mul (hS b.1).2 (hin01 y).2 (hin01 y).1 zero_le_one).trans_eq (by ring)
    change |(A*σ b.1)*(S b.1*inner y/(intervalCenter lo hi+(RoughRegime.Lower.sign b.2*h)*Real.cos φ))| ≤ _
    rw [abs_mul,abs_mul,abs_div,abs_of_pos (hlo.trans_le hd)]
    have hdiv : |S b.1*inner y|/(intervalCenter lo hi+(RoughRegime.Lower.sign b.2*h)*Real.cos φ) ≤ 1/lo :=
      div_le_div₀ zero_le_one hn hlo hd
    have hmul := mul_le_mul_of_nonneg_left (mul_le_mul (hσ b.1) hdiv
      (div_nonneg (abs_nonneg _) (hlo.trans_le hd).le) zero_le_one) (abs_nonneg A)
    convert hmul using 1 <;> ring
  · rw [globalProfile_outside offset ell p0 (intervalCenter lo hi) h A inner outer hin θ phase σ S x (not_exists.mp hx),abs_zero]
    positivity

/-- A transparent abbreviation for the paper's literal globally glued
hierarchical source profile. -/
abbrev sourceGridProfile (U : SmoothStep) (D N Q J M : ℕ)
    (gammaStar lambdaStar alpha0 m offset ell p0 lo hi h A : ℝ)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (z : GridPair D N → (Fin (D+1) × Fin J → ℤ)) (θ σ : GridPair D N → ℝ) :=
  globalProfile offset ell p0 (intervalCenter lo hi) h A inner outer θ
    (fun b => sourcePartialPhase U (D+1) J M gammaStar (z b) 0) σ
    (fun b => sourceGate (D+1) J Q M gammaStar lambdaStar alpha0 m (z b))



/-- The complete first-axis constant clause of the source smooth-map
restriction: the local map is evaluated on the actual global u/v profiles,
and both its smoothness and its amplitude-linear Hölder bound are proved. -/
theorem source_global_K_holder_first (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
    (hin01 : ∀ y, inner y ∈ Icc (0 : ℝ) 1) (hsupport : tsupport inner ⊆ unitCubeOpen (D+1))
    (t : ℝ) (ht : alpha0 < t) (hbudget : Model.holderOrder t+2 ≤ K)
    (map : ℝ × ℝ → ℝ) (k0 : ℝ) (V : Set (ℝ × ℝ))
    (hV : IsOpen V) (hV0 : (0 : ℝ × ℝ) ∈ V) (hmap : ContDiffOn ℝ ∞ map V)
    (hconstant : ∀ v : ℝ, (0,v) ∈ V → map (0,v) = k0) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧ ∀ N : ℕ, ∀ offset ell p0 Au Av : ℝ,
      0 < ell → ell ≤ 1 → |Au| ≤ ε → |Av| ≤ ε → ∀ J M : ℕ, ∀ m : ℝ,
      (2 : ℝ)^((J : ℝ)*alpha0) ≤ m →
      ∀ z : GridPair D N → (Fin (D+1) × Fin J → ℤ),
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ θ σu σv : GridPair D N → ℝ, (∀ b, |σu b| ≤ 1) → (∀ b, |σv b| ≤ 1) →
      let u := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Au inner outer z θ σu
      let v := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Av inner outer z θ σv
      ContDiff ℝ ∞ (fun x => map (u x,v x)-k0) ∧
        Model.holderNorm (fun x => map (u x,v x)-k0) t ≤
          ENNReal.ofReal (C*|Au| * ell⁻¹^t*(1+(2 : ℝ)^((J : ℝ)*t)/m)) := by
  obtain ⟨r,hr,F,hF,hfactor⟩ := local_hadamard_constant_first map k0 V hV hV0 hmap hconstant
  obtain ⟨C,hC,hcomponent⟩ := source_global_component_holder_bound U D Q K
    gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ F hF lo hi hlo hlt
    inner outer hiota hin hout hsmooth hcompact hin01 hsupport t ht hbudget
  refine ⟨min 1 (lo*r),C,lt_min zero_lt_one (mul_pos hlo hr),min_le_left _ _,hC,?_⟩
  intro N offset ell p0 Au Av hell hell1 hAu hAv J M m hm z h hh θ σu σv hσu hσv
  dsimp only
  let u := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Au inner outer z θ σu
  let v := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Av inner outer z θ σv
  have hab (A : ℝ) (σ : GridPair D N → ℝ) (hA : |A| ≤ min 1 (lo*r)) (hσ : ∀ b, |σ b| ≤ 1) (x) :
      |sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h A inner outer z θ σ x| ≤ r := by
    apply (globalProfile_normalized_abs_bound offset ell p0 A lo hi h hell hlo hlt hh
      inner outer hin hout hiota hin01 θ _ σ _ hσ (fun b => blockGate_range Q M _ _ (z b)) x).trans
    apply (div_le_iff₀ hlo).mpr
    exact (hA.trans (min_le_right _ _)).trans_eq (mul_comm lo r)
  have heq : (fun x => map (u x,v x)-k0) = fun x => u x*F (u x,v x) := by
    funext x
    have hhf := hfactor (u x,v x) (hab Au σu hAu hσu x) (hab Av σv hAv hσv x)
    dsimp only at hhf
    linarith
  change ContDiff ℝ ∞ (fun x => map (u x,v x)-k0) ∧ _
  rw [heq]
  exact hcomponent N offset ell p0 Au Av hell hell1 (hAu.trans (min_le_left _ _))
    (hAv.trans (min_le_left _ _)) J M m hm z h hh θ σu σv hσu hσv



/-- The second-axis constant clause, with the second amplitude factored out. -/
theorem source_global_K_holder_second (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
    (hin01 : ∀ y, inner y ∈ Icc (0 : ℝ) 1) (hsupport : tsupport inner ⊆ unitCubeOpen (D+1))
    (t : ℝ) (ht : alpha0 < t) (hbudget : Model.holderOrder t+2 ≤ K)
    (map : ℝ × ℝ → ℝ) (k0 : ℝ) (V : Set (ℝ × ℝ))
    (hV : IsOpen V) (hV0 : (0 : ℝ × ℝ) ∈ V) (hmap : ContDiffOn ℝ ∞ map V)
    (hconstant : ∀ u : ℝ, (u,0) ∈ V → map (u,0) = k0) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧ ∀ N : ℕ, ∀ offset ell p0 Au Av : ℝ,
      0 < ell → ell ≤ 1 → |Au| ≤ ε → |Av| ≤ ε → ∀ J M : ℕ, ∀ m : ℝ,
      (2 : ℝ)^((J : ℝ)*alpha0) ≤ m →
      ∀ z : GridPair D N → (Fin (D+1) × Fin J → ℤ),
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ θ σu σv : GridPair D N → ℝ, (∀ b, |σu b| ≤ 1) → (∀ b, |σv b| ≤ 1) →
      let u := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Au inner outer z θ σu
      let v := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Av inner outer z θ σv
      ContDiff ℝ ∞ (fun x => map (u x,v x)-k0) ∧
        Model.holderNorm (fun x => map (u x,v x)-k0) t ≤
          ENNReal.ofReal (C*|Av| * ell⁻¹^t*(1+(2 : ℝ)^((J : ℝ)*t)/m)) := by
  let W : Set (ℝ × ℝ) := Prod.swap ⁻¹' V
  have hW : IsOpen W := hV.preimage continuous_swap
  have hW0 : (0 : ℝ × ℝ) ∈ W := hV0
  have hswap : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => map (p.2,p.1)) W :=
    hmap.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hp => hp)
  obtain ⟨ε,C,hε,hε1,hC,hbound⟩ := source_global_K_holder_first U D Q K
    gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ lo hi hlo hlt
    inner outer hiota hin hout hsmooth hcompact hin01 hsupport t ht hbudget
    (fun p : ℝ × ℝ => map (p.2,p.1)) k0 W hW hW0 hswap (fun u hu => hconstant u hu)
  refine ⟨ε,C,hε,hε1,hC,?_⟩
  intro N offset ell p0 Au Av hell hell1 hAu hAv J M m hm z h hh θ σu σv hσu hσv
  exact hbound N offset ell p0 Av Au hell hell1 hAv hAu J M m hm z h hh θ σv σu hσv hσu

private theorem holderNorm_add_le {d : ℕ} (f g : Model.Covariate d → ℝ) (t A B : ℝ)
    (ht : 0 < t) (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfb : Model.holderNorm f t ≤ ENNReal.ofReal A) (hgb : Model.holderNorm g t ≤ ENNReal.ofReal B) :
    Model.holderNorm (fun x => f x+g x) t ≤ ENNReal.ofReal (2*(A+B)) := by
  have he := Model.holderNorm_sum_le Finset.univ (fun i : Fin 2 => ![f,g] i)
    (fun i : Fin 2 => ![A,B] i) t ht
    (by intro i _; fin_cases i <;> simp [hA,hB])
    (by intro i _; fin_cases i <;> simp [hf,hg])
    (by intro i _; fin_cases i <;> simp [hfb,hgb])
  simpa only [Finset.mem_univ,Finset.sum_const_zero,
    Matrix.cons_val_zero,Matrix.cons_val_one,Finset.sum_eq_single,Fin.sum_univ_two] using he

/-- The unrestricted local smooth-map clause with the sum of both actual
profile amplitudes. -/
theorem source_global_K_holder_general (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
    (hin01 : ∀ y, inner y ∈ Icc (0 : ℝ) 1) (hsupport : tsupport inner ⊆ unitCubeOpen (D+1))
    (t : ℝ) (ht : alpha0 < t) (hbudget : Model.holderOrder t+2 ≤ K)
    (map : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ))
    (hV : IsOpen V) (hV0 : (0 : ℝ × ℝ) ∈ V) (hmap : ContDiffOn ℝ ∞ map V) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧ ∀ N : ℕ, ∀ offset ell p0 Au Av : ℝ,
      0 < ell → ell ≤ 1 → |Au| ≤ ε → |Av| ≤ ε → ∀ J M : ℕ, ∀ m : ℝ,
      (2 : ℝ)^((J : ℝ)*alpha0) ≤ m →
      ∀ z : GridPair D N → (Fin (D+1) × Fin J → ℤ),
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ θ σu σv : GridPair D N → ℝ, (∀ b, |σu b| ≤ 1) → (∀ b, |σv b| ≤ 1) →
      let u := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Au inner outer z θ σu
      let v := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Av inner outer z θ σv
      ContDiff ℝ ∞ (fun x => map (u x,v x)-map (0,0)) ∧
        Model.holderNorm (fun x => map (u x,v x)-map (0,0)) t ≤
          ENNReal.ofReal (C*(|Au|+|Av|) * ell⁻¹^t*(1+(2 : ℝ)^((J : ℝ)*t)/m)) := by
  obtain ⟨r,hr,F,G,hF,hG,hfactor⟩ := local_hadamard_two_factors map V hV hV0 hmap
  obtain ⟨C1,hC1,hcomponent1⟩ := source_global_component_holder_bound U D Q K
    gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ F hF lo hi hlo hlt
    inner outer hiota hin hout hsmooth hcompact hin01 hsupport t ht hbudget
  let Gswap : ℝ × ℝ → ℝ := fun p => G (p.2,p.1)
  have hGs : ContDiff ℝ ∞ Gswap := hG.comp (contDiff_snd.prodMk contDiff_fst)
  obtain ⟨C2,hC2,hcomponent2⟩ := source_global_component_holder_bound U D Q K
    gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ Gswap hGs lo hi hlo hlt
    inner outer hiota hin hout hsmooth hcompact hin01 hsupport t ht hbudget
  refine ⟨min 1 (lo*r),2*(C1+C2),lt_min zero_lt_one (mul_pos hlo hr),min_le_left _ _,by positivity,?_⟩
  intro N offset ell p0 Au Av hell hell1 hAu hAv J M m hm z h hh θ σu σv hσu hσv
  dsimp only
  let u := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Au inner outer z θ σu
  let v := sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h Av inner outer z θ σv
  let L := ell⁻¹^t*(1+(2 : ℝ)^((J : ℝ)*t)/m)
  have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hab (A : ℝ) (σ : GridPair D N → ℝ) (hA : |A| ≤ min 1 (lo*r)) (hσ : ∀ b, |σ b| ≤ 1) (x) :
      |sourceGridProfile U D N Q J M gammaStar lambdaStar alpha0 m offset ell p0 lo hi h A inner outer z θ σ x| ≤ r := by
    apply (globalProfile_normalized_abs_bound offset ell p0 A lo hi h hell hlo hlt hh
      inner outer hin hout hiota hin01 θ _ σ _ hσ (fun b => blockGate_range Q M _ _ (z b)) x).trans
    apply (div_le_iff₀ hlo).mpr
    exact (hA.trans (min_le_right _ _)).trans_eq (mul_comm lo r)
  have heq : (fun x => map (u x,v x)-map (0,0)) =
      fun x => u x*F (u x,v x)+v x*G (u x,v x) := by
    funext x
    have hhf := hfactor (u x,v x) (hab Au σu hAu hσu x) (hab Av σv hAv hσv x)
    dsimp only at hhf
    linarith
  obtain ⟨hf,hfb⟩ := hcomponent1 N offset ell p0 Au Av hell hell1 (hAu.trans (min_le_left _ _))
    (hAv.trans (min_le_left _ _)) J M m hm z h hh θ σu σv hσu hσv
  obtain ⟨hg,hgb⟩ := hcomponent2 N offset ell p0 Av Au hell hell1 (hAv.trans (min_le_left _ _))
    (hAu.trans (min_le_left _ _)) J M m hm z h hh θ σv σu hσv hσu
  change ContDiff ℝ ∞ (fun x => u x*F (u x,v x)) at hf
  have hfb' : Model.holderNorm (fun x => u x*F (u x,v x)) t ≤ ENNReal.ofReal (C1*|Au| * L) := by
    convert hfb using 1
    dsimp [L]
    congr 1
    ring
  change ContDiff ℝ ∞ (fun x => v x*G (u x,v x)) at hg
  have hgb' : Model.holderNorm (fun x => v x*G (u x,v x)) t ≤ ENNReal.ofReal (C2*|Av| * L) := by
    convert hgb using 1
    dsimp [L]
    congr 1
    ring
  change ContDiff ℝ ∞ (fun x => map (u x,v x)-map (0,0)) ∧ _
  rw [heq]
  refine ⟨hf.add hg,(holderNorm_add_le _ _ t _ _ (ha0.trans_lt ht) (by positivity)
    (by positivity) hf hg hfb' hgb').trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hc : C1*|Au|+C2*|Av| ≤ (C1+C2)*(|Au|+|Av|) := by
    nlinarith [mul_nonneg hC1.le (abs_nonneg Av),mul_nonneg hC2.le (abs_nonneg Au)]
  have he := mul_le_mul_of_nonneg_right hc hL
  dsimp [L] at *
  nlinarith

end RoughRegime.LatticePriors
