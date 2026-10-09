module

public import RoughRegime.SourceProfileRescaleFamily
public import RoughRegime.GlobalHolderIdentity


@[expose] public section
open Set
open scoped BigOperators ContDiff

noncomputable section

namespace RoughRegime.LatticePriors

open RoughRegime.Calculus RoughRegime.Upper

/-- The actual two-profile nonlinear component is a disjoint sum of the
Hadamard scalar family, with its first amplitude factored out. -/
theorem global_component_eq_sum {D N : ℕ} (F : ℝ × ℝ → ℝ)
    (offset ell p0 r0 h Au Av : ℝ) (hell : 0 < ell)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
    (σu σv S : GridPair D N → ℝ) :
    (fun x =>
      globalProfile offset ell p0 r0 h Au inner outer θ phase σu S x *
        F (globalProfile offset ell p0 r0 h Au inner outer θ phase σu S x,
          globalProfile offset ell p0 r0 h Av inner outer θ phase σv S x)) =
    fun x => ∑ b : GridBlock D N, (Au*σu b.1) *
      oscillatorProfile (hadamardScalarFamily F (Au*σu b.1,Av*σv b.1)) r0 (S b.1)
        (RoughRegime.Lower.sign b.2*h) (θ b.1) inner (phase b.1) (gridCoords offset ell b x) := by
  funext x
  by_cases hx : ∃ b : GridBlock D N, x ∈ gridBlockOpen offset ell b
  · obtain ⟨b,hb⟩ := hx
    rw [globalProfile_eq_local offset ell p0 r0 h Au hell inner outer hin hout θ phase σu S b x hb,
      globalProfile_eq_local offset ell p0 r0 h Av hell inner outer hin hout θ phase σv S b x hb,
      blockProfile_eq_oscillator Au (σu b.1) (S b.1) p0 r0 h (θ b.1)
        (RoughRegime.Lower.sign b.2) inner outer (phase b.1) hiota,
      blockProfile_eq_oscillator Av (σv b.1) (S b.1) p0 r0 h (θ b.1)
        (RoughRegime.Lower.sign b.2) inner outer (phase b.1) hiota]
    rw [Finset.sum_eq_single b]
    · simp only [oscillatorProfile,oscillatorOuter,phaseInput,Function.comp_apply,id_eq,
        hadamardScalarFamily]
      ring
    · intro a _ hab
      have ha := pulledCutoff_zero_of_other offset ell hell b a (Ne.symm hab) inner hin x hb
      change inner (gridCoords offset ell a x) = 0 at ha
      simp [oscillatorProfile,oscillatorOuter,phaseInput,ha,hadamardScalarFamily]
    · simp
  · rw [globalProfile_outside offset ell p0 r0 h Au inner outer hin θ phase σu S x (not_exists.mp hx)]
    simp only [zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have ha := pulledCutoff_zero offset ell b inner hin x ((not_exists.mp hx) b)
    change inner (gridCoords offset ell b x) = 0 at ha
    simp [oscillatorProfile,oscillatorOuter,phaseInput,ha,hadamardScalarFamily]

/-- Uniform genuine Hölder control of the nonlinear Hadamard component on the
literal source grid. The constant is independent of both profile amplitudes,
the number of blocks, and every phase and lattice realization. -/
theorem source_global_component_holder_bound (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
    (hin01 : ∀ y, inner y ∈ Icc (0 : ℝ) 1) (hsupport : tsupport inner ⊆ unitCubeOpen (D+1))
    (t : ℝ) (ht : alpha0 < t) (hbudget : Model.holderOrder t+2 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ offset ell p0 Au Av : ℝ,
      0 < ell → ell ≤ 1 → |Au| ≤ 1 → |Av| ≤ 1 → ∀ J M : ℕ, ∀ m : ℝ,
      (2 : ℝ)^((J : ℝ)*alpha0) ≤ m →
      ∀ z : GridPair D N → (Fin (D+1) × Fin J → ℤ),
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ θ σu σv : GridPair D N → ℝ, (∀ b, |σu b| ≤ 1) → (∀ b, |σv b| ≤ 1) →
      let u := globalProfile offset ell p0 (intervalCenter lo hi) h Au inner outer θ
        (fun b => sourcePartialPhase U (D+1) J M gammaStar (z b) 0) σu
        (fun b => sourceGate (D+1) J Q M gammaStar lambdaStar alpha0 m (z b))
      let v := globalProfile offset ell p0 (intervalCenter lo hi) h Av inner outer θ
        (fun b => sourcePartialPhase U (D+1) J M gammaStar (z b) 0) σv
        (fun b => sourceGate (D+1) J Q M gammaStar lambdaStar alpha0 m (z b))
      ContDiff ℝ ∞ (fun x => u x*F (u x,v x)) ∧
        Model.holderNorm (fun x => u x*F (u x,v x)) t ≤
          ENNReal.ofReal (C*|Au| * ell⁻¹^t*(1+(2 : ℝ)^((J : ℝ)*t)/m)) := by
  let KP : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  have hKP : IsCompact KP := isCompact_Icc.prod isCompact_Icc
  have hfamily := hadamardScalarFamily_contDiff F hF
  obtain ⟨C,hC,hlocal⟩ := source_profile_holder_bound_rescale_family U (D+1) Q K
    gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ (hadamardScalarFamily F)
    KP hKP hfamily (hadamardScalarFamily_zero F) lo hi hlo hlt
    inner hsmooth hcompact hin01 t ht hbudget
  refine ⟨6*C,by positivity,?_⟩
  intro N offset ell p0 Au Av hell hell1 hAu hAv J M m hm z h hh θ σu σv hσu hσv
  dsimp only
  let SG (b : GridPair D N) := sourceGate (D+1) J Q M gammaStar lambdaStar alpha0 m (z b)
  let phase (b : GridPair D N) := sourcePartialPhase U (D+1) J M gammaStar (z b) 0
  let param (b : GridBlock D N) : ℝ × ℝ := (Au*σu b.1,Av*σv b.1)
  let f (b : GridBlock D N) := (oscillatorProfile (hadamardScalarFamily F (param b))
    (intervalCenter lo hi) (SG b.1) (RoughRegime.Lower.sign b.2*h) (θ b.1) inner (phase b.1)) ∘
      gridCoords offset ell b
  let g (b : GridBlock D N) := fun x => (Au*σu b.1)*f b x
  let H := C*ell⁻¹^t*(1+(2 : ℝ)^((J : ℝ)*t)/m)
  have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hp (b : GridBlock D N) : param b ∈ KP := by
    constructor
    · apply abs_le.mp
      rw [abs_mul]
      exact (mul_le_mul hAu (hσu b.1) (abs_nonneg _) zero_le_one).trans_eq (by ring)
    · apply abs_le.mp
      rw [abs_mul]
      exact (mul_le_mul hAv (hσv b.1) (abs_nonneg _) zero_le_one).trans_eq (by ring)
  have hh' (b : GridBlock D N) : RoughRegime.Lower.sign b.2*h ∈
      Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi) := by
    apply abs_le.mp
    rw [abs_mul]
    have hs : |RoughRegime.Lower.sign b.2| = 1 := by cases b.2 <;> norm_num [RoughRegime.Lower.sign]
    rw [hs,one_mul]
    exact abs_le.mpr hh
  have hf (b : GridBlock D N) : ContDiff ℝ ∞ (f b) :=
    (oscillatorProfile_smooth (hadamardScalarFamily F (param b)) lo hi hlo hlt univ isOpen_univ
      (familyScalar_contDiff _ hfamily (param b)).contDiffOn (subset_univ _)
      (SG b.1) _ (θ b.1) (blockGate_range Q M _ _ (z b.1)) (hh' b) inner _ hsmooth
      (sourcePartialPhase_smooth U (D+1) J M gammaStar hγ hγ1 (z b.1) 0) hin01).comp
      (gridCoords_smooth offset ell b)
  have hfb (b : GridBlock D N) : Model.holderNorm (f b) t ≤ ENNReal.ofReal H :=
    hlocal (param b) (hp b) ell hell hell1 (gridOrigin offset ell b) J M m hm (z b.1)
      _ (hh' b) (θ b.1)
  have hgb (b : GridBlock D N) : Model.holderNorm (g b) t ≤ ENNReal.ofReal (2*|Au| * H) := by
    have he := Model.holderNorm_const_mul_le (f b) t H (Au*σu b.1) (ha0.trans_lt ht) hH (hf b) (hfb b)
    have hab : |Au*σu b.1| ≤ |Au| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hσu b.1) (abs_nonneg Au)).trans_eq (by ring)
    exact he.trans (ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_right hab hH]))
  have hgsupp (b : GridBlock D N) : tsupport (g b) ⊆ gridBlockOpen offset ell b :=
    (tsupport_comp_subset (g := fun y : ℝ => (Au*σu b.1)*y) (by simp) (f b)).trans
      (grid_profile_tsupport_subset offset ell b _ (hadamardScalarFamily_zero F (param b))
        _ _ _ _ inner _ hsupport)
  have hg (b : GridBlock D N) : ContDiff ℝ ∞ (g b) := contDiff_const.mul (hf b)
  have hdis : ((Finset.univ : Finset (GridBlock D N)) : Set (GridBlock D N)).Pairwise
      (fun b c => Disjoint (tsupport (g b)) (tsupport (g c))) := by
    intro b _ c _ hbc
    exact (gridBlockOpen_pairwiseDisjoint D N offset ell hell hbc).mono (hgsupp b) (hgsupp c)
  have he := Model.holderNorm_disjoint_sum_le Finset.univ g t (2*|Au| * H)
    (ha0.trans_lt ht) (by positivity) (fun b _ => hg b) (fun b _ => hgb b) hdis
  have hid := global_component_eq_sum F offset ell p0 (intervalCenter lo hi) h Au Av hell
    inner outer hin hout hiota θ phase σu σv SG
  rw [hid]
  refine ⟨ContDiff.sum (fun b _ => hg b),?_⟩
  convert he using 1
  dsimp [g,f,H,param]
  congr 1
  ring

end RoughRegime.LatticePriors
