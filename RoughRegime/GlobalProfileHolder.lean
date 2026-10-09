module

public import RoughRegime.GlobalHolderIdentity


@[expose] public section
/-! The literal globally glued u/v profiles satisfy the genuine uniform
source Hölder estimate. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper

theorem source_global_profile_holder_bound (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0<gammaStar) (hγ1 : gammaStar≤1/4)
    (hlam : 0<lambdaStar) (ha0 : 0≤alpha0) (ha1 : alpha0<1) (hK : 0<K) (hKQ : K≤2*Q)
    (lo hi : ℝ) (hlo : 0<lo) (hlt : lo<hi)
    (inner outer : Model.Covariate (D+1) → ℝ) (hiota : ∀ y, inner y≠0 → outer y=1)
    (hin : ∀ y, y∉unitCubeOpen (D+1) → inner y=0) (hout : ∀ y, y∉unitCubeOpen (D+1) → outer y=0)
    (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
    (hin01 : ∀ y, inner y∈Icc (0:ℝ) 1) (hsupport : tsupport inner⊆unitCubeOpen (D+1))
    (t : ℝ) (ht : alpha0<t) (hbudget : Model.holderOrder t+2≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ offset ell p0 A : ℝ, 0<ell → ell≤1 → ∀ J M : ℕ, ∀ m : ℝ,
      (2:ℝ)^((J:ℝ)*alpha0) ≤ m → ∀ z : GridPair D N → (Fin (D+1) × Fin J → ℤ),
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ θ σ : GridPair D N → ℝ, (∀ b, |σ b|≤1) →
      Model.holderNorm
        (globalProfile offset ell p0 (intervalCenter lo hi) h A inner outer θ
          (fun b => sourcePartialPhase U (D+1) J M gammaStar (z b) 0) σ
          (fun b => sourceGate (D+1) J Q M gammaStar lambdaStar alpha0 m (z b))) t ≤
      ENNReal.ofReal (C*|A| * ell⁻¹^t*(1+(2:ℝ)^((J:ℝ)*t)/m)) := by
  obtain ⟨C,hC,hlocal⟩ := source_profile_holder_bound_rescale U (D+1) Q K gammaStar lambdaStar alpha0
    hγ hγ1 hlam ha0 ha1 hK hKQ id lo hi hlo hlt Set.univ isOpen_univ contDiff_id.contDiffOn rfl
    (subset_univ _) inner hsmooth hcompact hin01 t ht hbudget
  refine ⟨6*C,by positivity,?_⟩
  intro N offset ell p0 A hell hell1 J M m hm z h hh θ σ hσ
  let SG (b : GridPair D N) := sourceGate (D+1) J Q M gammaStar lambdaStar alpha0 m (z b)
  let phase (b : GridPair D N) := sourcePartialPhase U (D+1) J M gammaStar (z b) 0
  let f (b : GridBlock D N) := (oscillatorProfile id (intervalCenter lo hi) (SG b.1)
    (RoughRegime.Lower.sign b.2*h) (θ b.1) inner (phase b.1)) ∘ gridCoords offset ell b
  let g (b : GridBlock D N) := fun x => (A*σ b.1)*f b x
  let H := C*ell⁻¹^t*(1+(2:ℝ)^((J:ℝ)*t)/m)
  have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
  have hH : 0≤H := by dsimp [H]; positivity
  have hh' (b : GridBlock D N) : RoughRegime.Lower.sign b.2*h∈Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi) := by
    apply abs_le.mp
    rw [abs_mul]
    have hs : |RoughRegime.Lower.sign b.2|=1 := by cases b.2 <;> norm_num [RoughRegime.Lower.sign]
    rw [hs,one_mul]
    exact abs_le.mpr hh
  have hf (b : GridBlock D N) : ContDiff ℝ ∞ (f b) :=
    (oscillatorProfile_smooth id lo hi hlo hlt Set.univ isOpen_univ contDiff_id.contDiffOn (subset_univ _)
      (SG b.1) _ (θ b.1) (blockGate_range Q M _ _ (z b.1)) (hh' b) inner _ hsmooth
      (sourcePartialPhase_smooth U (D+1) J M gammaStar hγ hγ1 (z b.1) 0) hin01).comp (gridCoords_smooth offset ell b)
  have hfb (b : GridBlock D N) : Model.holderNorm (f b) t≤ENNReal.ofReal H :=
    hlocal ell hell hell1 (gridOrigin offset ell b) J M m hm (z b.1) _ (hh' b) (θ b.1)
  have hgb (b : GridBlock D N) : Model.holderNorm (g b) t≤ENNReal.ofReal (2*|A| * H) := by
    have he := Model.holderNorm_const_mul_le (f b) t H (A*σ b.1) (ha0.trans_lt ht) hH (hf b) (hfb b)
    have hab : |A*σ b.1|≤|A| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hσ b.1) (abs_nonneg A)).trans_eq (by ring)
    exact he.trans (ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_right hab hH]))
  have hgsupp (b : GridBlock D N) : tsupport (g b)⊆gridBlockOpen offset ell b :=
    (tsupport_comp_subset (g := fun y : ℝ => (A*σ b.1)*y) (by simp) (f b)).trans
      (grid_profile_tsupport_subset offset ell b id rfl _ _ _ _ inner _ hsupport)
  have hg (b : GridBlock D N) : ContDiff ℝ ∞ (g b) := contDiff_const.mul (hf b)
  have hdis : ((Finset.univ : Finset (GridBlock D N)) : Set (GridBlock D N)).Pairwise
      (fun b c => Disjoint (tsupport (g b)) (tsupport (g c))) := by
    intro b _ c _ hbc
    exact (gridBlockOpen_pairwiseDisjoint D N offset ell hell hbc).mono (hgsupp b) (hgsupp c)
  have he := Model.holderNorm_disjoint_sum_le Finset.univ g t (2*|A| * H) (ha0.trans_lt ht) (by positivity)
    (fun b _ => hg b) (fun b _ => hgb b) hdis
  rw [globalProfile_eq_sum_oscillator offset ell p0 (intervalCenter lo hi) h A hell inner outer hin hout hiota θ phase σ SG]
  convert he using 1 <;> dsimp [g,f,H] <;> congr 1 <;> ring

end RoughRegime.LatticePriors
