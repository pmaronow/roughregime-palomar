module

public import RoughRegime.SourceProfileRescale
public import RoughRegime.ScalarHolder
public import RoughRegime.GlobalLattice


@[expose] public section
/-! Actual disjoint affine gluing of the source lattice profiles. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper

/-- The actual scalar profile has no support beyond the fixed inner cutoff. -/
theorem oscillatorProfile_tsupport_subset {d : ℕ} (κ : ℝ → ℝ) (hκ0 : κ 0=0)
    (center S h θ : ℝ) (cut φ : Model.Covariate d → ℝ) :
    tsupport (oscillatorProfile κ center S h θ cut φ) ⊆ tsupport cut := by
  apply closure_mono
  intro x hx
  by_contra hxc
  have hc : cut x=0 := by simpa only [Function.mem_support,not_not] using hxc
  apply hx
  simp [oscillatorProfile,oscillatorOuter,phaseInput,hc,hκ0]

/-- Genuine strict cutoff support implies disjoint topological support after
pullback to the source Cartesian block grid. -/
theorem grid_profile_tsupport_subset {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N)
    (κ : ℝ → ℝ) (hκ0 : κ 0=0) (center S h θ : ℝ)
    (cut φ : Model.Covariate (D+1) → ℝ) (hc : tsupport cut ⊆ unitCubeOpen (D+1)) :
    tsupport ((oscillatorProfile κ center S h θ cut φ) ∘ gridCoords offset ell b) ⊆
      gridBlockOpen offset ell b := by
  exact (tsupport_comp_subset_preimage _ (gridCoords_smooth offset ell b).continuous).trans
    (Set.preimage_mono ((oscillatorProfile_tsupport_subset κ hκ0 center S h θ cut φ).trans hc))

/-- The source local estimates and actual disjoint grid gluing produce the
uniform ell^(-t) global bound, with no dependence on the number of blocks. -/
theorem source_grid_profiles_holder_bound (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0<gammaStar) (hγ1 : gammaStar≤1/4)
    (hlam : 0<lambdaStar) (ha0 : 0≤alpha0) (ha1 : alpha0<1)
    (hK : 0<K) (hKQ : K≤2*Q)
    (κ : ℝ → ℝ) (lo hi : ℝ) (hlo : 0<lo) (hlt : lo<hi)
    (V : Set ℝ) (hV : IsOpen V) (hκ : ContDiffOn ℝ ∞ κ V) (hκ0 : κ 0=0)
    (hinterval : Icc (0:ℝ) (1/lo) ⊆ V)
    (cut : Model.Covariate (D+1) → ℝ) (hcut : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
    (hcut01 : ∀ x, cut x ∈ Icc (0:ℝ) 1) (hsupport : tsupport cut ⊆ unitCubeOpen (D+1))
    (t : ℝ) (ht : alpha0<t) (hbudget : Model.holderOrder t+2≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ offset ell : ℝ, 0<ell → ell≤1 → ∀ J M : ℕ, ∀ m : ℝ,
      (2:ℝ)^((J:ℝ)*alpha0)≤ m → ∀ z : GridBlock D N → (Fin (D+1) × Fin J → ℤ),
      ∀ h θ : GridBlock D N → ℝ,
      (∀ b, h b ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi)) →
      Model.holderNorm (fun x => ∑ b : GridBlock D N,
        oscillatorProfile κ (intervalCenter lo hi) (sourceGate (D+1) J Q M gammaStar lambdaStar alpha0 m (z b))
          (h b) (θ b) cut (sourcePartialPhase U (D+1) J M gammaStar (z b) 0) (gridCoords offset ell b x)) t ≤
      ENNReal.ofReal (C*ell⁻¹^t*(1+(2:ℝ)^((J:ℝ)*t)/m)) := by
  obtain ⟨C,hC,hlocal⟩ := source_profile_holder_bound_rescale U (D+1) Q K gammaStar lambdaStar alpha0
    hγ hγ1 hlam ha0 ha1 hK hKQ κ lo hi hlo hlt V hV hκ hκ0 hinterval cut hcut hcompact hcut01 t ht hbudget
  refine ⟨3*C,by positivity,?_⟩
  intro N offset ell hell hell1 J M m hm z h θ hh
  let f (b : GridBlock D N) := (oscillatorProfile κ (intervalCenter lo hi)
    (sourceGate (D+1) J Q M gammaStar lambdaStar alpha0 m (z b)) (h b) (θ b) cut
      (sourcePartialPhase U (D+1) J M gammaStar (z b) 0)) ∘ gridCoords offset ell b
  let H := C*ell⁻¹^t*(1+(2:ℝ)^((J:ℝ)*t)/m)
  have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
  have hH : 0≤H := by dsimp [H]; positivity
  have hb (b : GridBlock D N) : Model.holderNorm (f b) t≤ENNReal.ofReal H :=
    hlocal ell hell hell1 (gridOrigin offset ell b) J M m hm (z b) (h b) (hh b) (θ b)
  have hf (b : GridBlock D N) : ContDiff ℝ ∞ (f b) :=
    (oscillatorProfile_smooth κ lo hi hlo hlt V hV hκ hinterval _ (h b) (θ b)
      (blockGate_range Q M _ _ (z b)) (hh b) cut _ hcut
      (sourcePartialPhase_smooth U (D+1) J M gammaStar hγ hγ1 (z b) 0) hcut01).comp (gridCoords_smooth offset ell b)
  have hsupp (b : GridBlock D N) : tsupport (f b)⊆gridBlockOpen offset ell b :=
    grid_profile_tsupport_subset offset ell b κ hκ0 _ _ _ _ cut _ hsupport
  have hdis : ((Finset.univ : Finset (GridBlock D N)) : Set (GridBlock D N)).Pairwise (fun b c => Disjoint (tsupport (f b)) (tsupport (f c))) := by
    intro b _ c _ hbc
    exact (gridBlockOpen_pairwiseDisjoint D N offset ell hell hbc).mono (hsupp b) (hsupp c)
  have he := Model.holderNorm_disjoint_sum_le Finset.univ f t H (ha0.trans_lt ht) hH
    (fun b _ => hf b) (fun b _ => hb b) hdis
  convert he using 1 <;> dsimp [f,H] <;> congr 1 <;> ring

end RoughRegime.LatticePriors
