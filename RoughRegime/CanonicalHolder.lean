module

public import RoughRegime.SourceAmplitude
public import RoughRegime.SourceReindex


@[expose] public section
/-! The actual canonical source profiles, with the literal paper amplitudes,
lie in fixed Hölder balls uniformly in every lattice/grid resolution. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Upper

 theorem stateSignU_abs {D N : ℕ} {ι : Type*} (z : GridPair D N → PairState ι)
     (b : GridPair D N) : |stateSignU z b| = 1 := by
   unfold stateSignU
   cases (z b).2.2.1 <;> norm_num [RoughRegime.Lower.sign]
 theorem stateSignV_abs {D N : ℕ} {ι : Type*} (z : GridPair D N → PairState ι)
     (b : GridPair D N) : |stateSignV z b| = 1 := by
   unfold stateSignV
   cases (z b).2.2.2 <;> norm_num [RoughRegime.Lower.sign]

 theorem canonical_source_profile_holder_bound (U : SmoothStep) (D Q K : ℕ)
     (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
     (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1) (hK : 0 < K) (hKQ : K ≤ 2*Q)
     (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
     (inner outer : Model.Covariate (D+1) → ℝ) (hiota : ∀ y, inner y≠0 → outer y=1)
     (hin : ∀ y, y∉unitCubeOpen (D+1) → inner y=0) (hout : ∀ y, y∉unitCubeOpen (D+1) → outer y=0)
     (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
     (hin01 : ∀ y, inner y∈Icc (0:ℝ) 1) (hsupport : tsupport inner⊆unitCubeOpen (D+1))
     (t : ℝ) (ht : alpha0 < t) (hbudget : Model.holderOrder t+2 ≤ K)
     (v0 : ℝ) (hv : 0 < v0) :
     ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ offset B p0 epsilon : ℝ,
       0 < B → 0 ≤ epsilon → sourceBlockScale v0 B (D+1) ≤ 1 → ∀ J M : ℕ, ∀ m : ℝ,
       (2:ℝ)^((J:ℝ)*alpha0) ≤ m → m ≤ (2:ℝ)^((J:ℝ)*t) →
       ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
       ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
       ∀ σ : GridPair D N → ℝ, (∀ b, |σ b| ≤ 1) →
       Model.holderNorm
         (globalProfile offset (sourceBlockScale v0 B (D+1)) p0 (intervalCenter lo hi) h
           (sourceAmplitude epsilon B J (D+1) t m) inner outer (stateAngles z)
           (statePhases U M (fun i => J-i.1.val) Prod.snd (fun i => sourceGamma gammaStar i.1.val) z) σ
           (stateGates Q M (fun i => sourceEta gammaStar lambdaStar alpha0 m i.1.val)
             (fun i => sourceLambda lambdaStar i.1.val) z)) t ≤ ENNReal.ofReal (C*epsilon) := by
   obtain ⟨C,hC,hbound⟩ := source_global_profile_holder_bound U D Q K gammaStar lambdaStar alpha0
     hγ hγ1 hlam ha0 ha1 hK hKQ lo hi hlo hlt inner outer hiota hin hout hsmooth hcompact hin01 hsupport t ht hbudget
   refine ⟨2*C*v0^(-(t/(D+1:ℕ))),by positivity,?_⟩
   intro N offset B p0 epsilon hB he hell1 J M m hm hm1 z h hh σ hσ
   rw [statePhases_eq_source, stateGates_eq_source]
   have hell := sourceBlockScale_pos hv hB (D+1)
   have hb := hbound N offset (sourceBlockScale v0 B (D+1)) p0
     (sourceAmplitude epsilon B J (D+1) t m) hell hell1 J M m hm
     (fun b => sourceDigitsTranspose (z b).1) h hh (stateAngles z) σ hσ
   apply hb.trans
   apply ENNReal.ofReal_le_ofReal
   have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
   have hs := mul_le_mul_of_nonneg_left
     (sourceAmplitude_scale_le epsilon B v0 J (D+1) t m he hB hv (Nat.succ_pos _) hm0 hm1) hC.le
   convert hs using 1 <;> ring

end RoughRegime.LatticePriors
