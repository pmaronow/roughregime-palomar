module

public import RoughRegime.GridHolder


@[expose] public section
/-! Literal global profiles are the disjointly glued normalized local
reciprocal profiles, including their actual amplitudes and signs. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus

 theorem blockProfile_eq_oscillator {d : ℕ} (A σ S p0 r0 h θ sign : ℝ)
     (inner outer phase : Model.Covariate d → ℝ)
     (hiota : ∀ y, inner y≠0 → outer y=1) :
     blockProfile A σ S inner (blockDensity p0 r0 h θ phase outer sign) =
       fun x => (A*σ)*oscillatorProfile id r0 S (sign*h) θ inner phase x := by
   funext x
   by_cases hx : inner x=0
   · simp [blockProfile,oscillatorProfile,oscillatorOuter,phaseInput,hx]
   · have ho := hiota x hx
     simp only [blockProfile,blockDensity,blockOscillatingDensity,oscillatorProfile,
       Function.comp_apply,oscillatorOuter,phaseInput,id_eq,ho,one_mul]
     ring

 theorem globalProfile_eq_sum_oscillator {D N : ℕ} (offset ell p0 r0 h A : ℝ) (hell : 0<ell)
     (inner outer : Model.Covariate (D+1) → ℝ)
     (hin : ∀ y, y∉unitCubeOpen (D+1) → inner y=0)
     (hout : ∀ y, y∉unitCubeOpen (D+1) → outer y=0)
     (hiota : ∀ y, inner y≠0 → outer y=1)
     (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
     (σ S : GridPair D N → ℝ) :
     globalProfile offset ell p0 r0 h A inner outer θ phase σ S = fun x =>
       ∑ b : GridBlock D N, (A*σ b.1)*oscillatorProfile id r0 (S b.1)
         (RoughRegime.Lower.sign b.2*h) (θ b.1) inner (phase b.1) (gridCoords offset ell b x) := by
   funext x
   by_cases hx : ∃ b : GridBlock D N, x∈gridBlockOpen offset ell b
   · obtain ⟨b,hb⟩ := hx
     rw [globalProfile_eq_local offset ell p0 r0 h A hell inner outer hin hout θ phase σ S b x hb]
     rw [blockProfile_eq_oscillator A (σ b.1) (S b.1) p0 r0 h (θ b.1) (RoughRegime.Lower.sign b.2) inner outer (phase b.1) hiota]
     rw [Finset.sum_eq_single b]
     · intro a _ hab
       have ha := pulledCutoff_zero_of_other offset ell hell b a (Ne.symm hab) inner hin x hb
       change inner (gridCoords offset ell a x)=0 at ha
       simp [oscillatorProfile,oscillatorOuter,phaseInput,ha]
     · simp
   · rw [globalProfile_outside offset ell p0 r0 h A inner outer hin θ phase σ S x (not_exists.mp hx)]
     symm
     apply Finset.sum_eq_zero
     intro b _
     have ha := pulledCutoff_zero offset ell b inner hin x ((not_exists.mp hx) b)
     change inner (gridCoords offset ell b x)=0 at ha
     simp [oscillatorProfile,oscillatorOuter,phaseInput,ha]

 theorem sourcePartialPhase_zero_eq_blockPhase (U : SmoothStep) (d J M : ℕ) (gammaStar : ℝ)
     (z : Fin d × Fin J → ℤ) : sourcePartialPhase U d J M gammaStar z 0 =
       blockPhase U M (fun i => J-i.2.val) Prod.fst (fun i => sourceGamma gammaStar i.2.val) z := by
   funext x
   simp [sourcePartialPhase,partialBlockPhase,sourceLevels,blockPhase]

end RoughRegime.LatticePriors
