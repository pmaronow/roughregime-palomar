module

public import RoughRegime.LatticeGamma


@[expose] public section
/-! Exact counting and spatial-frequency identification for the density
likelihood's three-valued Fourier mode patterns. -/
noncomputable section
namespace RoughRegime.LatticePriors
open RoughRegime.Lattice
open scoped BigOperators

 def negativeModes (o : Fin j → Fin 3) : Finset (Fin j) := Finset.univ.filter (fun k => o k = 0)
 def positiveModes (o : Fin j → Fin 3) : Finset (Fin j) := Finset.univ.filter (fun k => o k = 2)
 def patternMinus (ε : Bool) (o : Fin j → Fin 3) : Finset (Fin j) :=
  if ε then negativeModes o else positiveModes o
 def patternPlus (ε : Bool) (o : Fin j → Fin 3) : Finset (Fin j) :=
  if ε then positiveModes o else negativeModes o

 theorem negative_positive_disjoint (o : Fin j → Fin 3) : Disjoint (negativeModes o) (positiveModes o) := by
  apply Finset.disjoint_left.mpr
  intro k hk hn
  simp only [negativeModes, positiveModes, Finset.mem_filter, Finset.mem_univ, true_and] at hk hn
  omega

 theorem patternMinusPlus_disjoint (ε : Bool) (o : Fin j → Fin 3) :
    Disjoint (patternMinus ε o) (patternPlus ε o) := by
  cases ε
  · exact (negative_positive_disjoint o).symm
  · exact negative_positive_disjoint o

 theorem modeFrequency_sum (o : Fin j → Fin 3) :
    (∑ k, modeFrequency (o k)) = (positiveModes o).card - ((negativeModes o).card : ℤ) := by
  have heq (k : Fin j) : modeFrequency (o k) =
      (if o k = 2 then (1 : ℤ) else 0) - (if o k = 0 then 1 else 0) := by
    by_cases h0 : o k = 0
    · simp [h0, modeFrequency]
    · by_cases h1 : o k = 1
      · simp [h1, modeFrequency]
      · have h2 : o k = 2 := by omega
        simp [h2, modeFrequency]
  simp_rw [heq, Finset.sum_sub_distrib]
  simp only [negativeModes, positiveModes, Finset.sum_boole]

 theorem modePattern_card_bound (ε : Bool) (o : Fin j → Fin 3) :
    (patternMinus ε o).card + (patternPlus ε o).card ≤ j := by
  have h := Finset.card_le_card (Finset.subset_univ (negativeModes o ∪ positiveModes o))
  rw [Finset.card_union_of_disjoint (negative_positive_disjoint o)] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  cases ε <;> simpa [patternMinus, patternPlus, add_comm] using h

 theorem patternMinus_card (M : ℕ) (ε : Bool) (o : Fin j → Fin 3)
    (hfreq : patternTotalFrequency M ε o = 0) :
    (patternMinus ε o).card = M + (patternPlus ε o).card := by
  unfold patternTotalFrequency at hfreq
  rw [modeFrequency_sum] at hfreq
  cases ε <;> simp [patternMinus, patternPlus] at hfreq ⊢ <;> omega

 theorem patternPlus_small (M : ℕ) (ε : Bool) (o : Fin j → Fin 3)
    (hfreq : patternTotalFrequency M ε o = 0) (hj : (j : ℝ) < M + Real.sqrt M) :
    2 * ((patternPlus ε o).card : ℝ) < Real.sqrt M := by
  have hcard := modePattern_card_bound ε o
  rw [patternMinus_card M ε o hfreq] at hcard
  have hcardr : (M : ℝ) + ((patternPlus ε o).card : ℝ) + ((patternPlus ε o).card : ℝ) ≤ j := by exact_mod_cast hcard
  linarith

 theorem observationPatternFrequency_as_signedPattern {ι : Type*} [Fintype ι]
    (s : Fin j → ι → ℝ) (ε : Bool) (o : Fin j → Fin 3) (i : ι) :
    observationPatternFrequency s o i =
      signedPatternFrequency ε (patternMinus ε o) (patternPlus ε o) (fun i k => s k i) i := by
  have heq (k : Fin j) : (modeFrequency (o k) : ℝ) * s k i =
      (if o k = 2 then s k i else 0) - (if o k = 0 then s k i else 0) := by
    by_cases h0 : o k = 0
    · simp [h0, modeFrequency]
    · by_cases h1 : o k = 1
      · simp [h1, modeFrequency]
      · have h2 : o k = 2 := by omega
        simp [h2, modeFrequency]
  unfold observationPatternFrequency
  simp_rw [heq, Finset.sum_sub_distrib]
  have hp : (∑ k, if o k = 2 then s k i else 0) = ∑ k ∈ positiveModes o, s k i := by
    simp only [positiveModes, Finset.sum_filter]
  have hn : (∑ k, if o k = 0 then s k i else 0) = ∑ k ∈ negativeModes o, s k i := by
    simp only [negativeModes, Finset.sum_filter]
  rw [hp, hn]
  cases ε <;> simp [signedPatternFrequency, patternFrequency, patternMinus, patternPlus]

end RoughRegime.LatticePriors
