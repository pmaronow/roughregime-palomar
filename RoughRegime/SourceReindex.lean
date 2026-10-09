module

public import RoughRegime.GlobalHolderIdentity
public import RoughRegime.CanonicalAdmissibility


@[expose] public section
/-! The coordinate-first hierarchy and the paper's level-first lattice
indexing describe the same concrete phase and gate. -/
noncomputable section
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier
open scoped BigOperators

 def sourceDigitsTranspose {d J : ℕ} (z : Fin J × Fin d → ℤ) : Fin d × Fin J → ℤ :=
   fun i => z (i.2,i.1)

 theorem sourcePhase_reindex (U : SmoothStep) (d J M : ℕ) (gammaStar : ℝ)
     (z : Fin J × Fin d → ℤ) :
     sourcePartialPhase U d J M gammaStar (sourceDigitsTranspose z) 0 =
       blockPhase U M (fun i : Fin J × Fin d => J-i.1.val) Prod.snd
         (fun i => sourceGamma gammaStar i.1.val) z := by
   rw [sourcePartialPhase_zero_eq_blockPhase]
   funext x
   simp only [blockPhase, Fintype.sum_prod_type, sourceDigitsTranspose]
   rw [Finset.sum_comm]

 theorem sourceGate_reindex (d J Q M : ℕ) (gammaStar lambdaStar alpha0 m : ℝ)
     (z : Fin J × Fin d → ℤ) :
     sourceGate d J Q M gammaStar lambdaStar alpha0 m (sourceDigitsTranspose z) =
       jointGate Q M (fun i : Fin J × Fin d => sourceEta gammaStar lambdaStar alpha0 m i.1.val)
         (fun i => sourceLambda lambdaStar i.1.val) z := by
   simp only [sourceGate,blockGate,jointGate,Fintype.prod_prod_type,sourceDigitsTranspose]
   rw [Finset.prod_comm]

 theorem statePhases_eq_source {D N J : ℕ} (U : SmoothStep) (M : ℕ) (gammaStar : ℝ)
     (z : GridPair D N → PairState (Fin J × Fin (D+1))) :
     statePhases U M (fun i => J-i.1.val) Prod.snd (fun i => sourceGamma gammaStar i.1.val) z =
       fun b => sourcePartialPhase U (D+1) J M gammaStar (sourceDigitsTranspose (z b).1) 0 := by
   funext b
   exact (sourcePhase_reindex U (D+1) J M gammaStar (z b).1).symm

 theorem stateGates_eq_source {D N J : ℕ} (Q M : ℕ) (gammaStar lambdaStar alpha0 m : ℝ)
     (z : GridPair D N → PairState (Fin J × Fin (D+1))) :
     stateGates Q M (fun i => sourceEta gammaStar lambdaStar alpha0 m i.1.val)
       (fun i => sourceLambda lambdaStar i.1.val) z =
       fun b => sourceGate (D+1) J Q M gammaStar lambdaStar alpha0 m (sourceDigitsTranspose (z b).1) := by
   funext b
   exact (sourceGate_reindex (D+1) J Q M gammaStar lambdaStar alpha0 m (z b).1).symm

end RoughRegime.LatticePriors
