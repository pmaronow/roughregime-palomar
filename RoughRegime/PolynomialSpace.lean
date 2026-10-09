module

public import RoughRegime.HolderTaylorApproximation


@[expose] public section
/-! Concrete finite polynomial spaces with the source binomial dimension bound. -/
noncomputable section
open MvPolynomial Submodule Module
open scoped BigOperators
namespace RoughRegime.Model

def PolynomialIndex (d k : ℕ) := Sym (Option (Fin d)) k

instance (d k : ℕ) : Fintype (PolynomialIndex d k) := by
  unfold PolynomialIndex
  infer_instance

def boundedMonomial {d k : ℕ} (s : PolynomialIndex d k) : MvPolynomial (Fin d) ℝ :=
  monomial ((s.toMultiset.filterMap id).toFinsupp) 1

def polynomialSpace (d k : ℕ) : Submodule ℝ (MvPolynomial (Fin d) ℝ) :=
  span ℝ (Set.range (boundedMonomial (d := d) (k := k)))

instance (d k : ℕ) : FiniteDimensional ℝ (polynomialSpace d k) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

lemma filterMap_card_le {α β : Type*} (g : α → Option β) (s : Multiset α) :
    (s.filterMap g).card ≤ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    cases hg : g a with
    | none => simpa only [Multiset.filterMap_cons_none a s hg, Multiset.card_cons] using ih.trans (Nat.le_succ _)
    | some b => simpa only [Multiset.filterMap_cons_some g a s hg, Multiset.card_cons] using Nat.succ_le_succ ih

theorem boundedMonomial_degree {d k : ℕ} (s : PolynomialIndex d k) :
    (boundedMonomial s).totalDegree ≤ k := by
  apply (totalDegree_monomial_le _ _).trans
  rw [Multiset.toFinsupp_sum_eq]
  exact (filterMap_card_le id s.toMultiset).trans_eq s.property

def paddedPolynomialIndex {d k : ℕ} (a : Fin d →₀ ℕ)
    (ha : a.sum (fun _ => id) ≤ k) : PolynomialIndex d k :=
  ⟨Multiset.replicate (k - a.sum (fun _ => id)) none + a.toMultiset.map some, by
    simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finsupp.card_toMultiset]
    exact Nat.sub_add_cancel ha⟩

lemma filterMap_replicate_none {α : Type*} (n : ℕ) :
    (Multiset.replicate n (none : Option α)).filterMap id = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [Multiset.replicate_succ, Multiset.filterMap_cons_none, ih]

theorem boundedMonomial_padded {d k : ℕ} (a : Fin d →₀ ℕ)
    (ha : a.sum (fun _ => id) ≤ k) :
    boundedMonomial (paddedPolynomialIndex a ha) = monomial a 1 := by
  unfold boundedMonomial paddedPolynomialIndex
  simp only [Sym.toMultiset, Multiset.filterMap_add, filterMap_replicate_none,
    zero_add, Multiset.filterMap_map, Function.id_comp, Multiset.filterMap_some,
    Finsupp.toMultiset_toFinsupp]

theorem mem_polynomialSpace_of_degree {d k : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (hp : p.totalDegree ≤ k) : p ∈ polynomialSpace d k := by
  classical
  rw [p.as_sum]
  apply Submodule.sum_mem
  intro a ha
  have hdeg := (MvPolynomial.le_totalDegree ha).trans hp
  have hm : monomial a (1 : ℝ) ∈ polynomialSpace d k := by
    apply subset_span
    exact ⟨paddedPolynomialIndex a hdeg, boundedMonomial_padded a hdeg⟩
  simpa only [smul_monomial, smul_eq_mul, mul_one] using
    (polynomialSpace d k).smul_mem (p.coeff a) hm

theorem polynomialSpace_degree {d k : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (hp : p ∈ polynomialSpace d k) : p.totalDegree ≤ k := by
  classical
  refine Submodule.span_induction (fun p hp => ?_) (by simp) (fun p q _ _ hp hq => ?_)
    (fun a p _ hp => ?_) hp
  · obtain ⟨s, rfl⟩ := hp
    exact boundedMonomial_degree s
  · exact (totalDegree_add _ _).trans (max_le hp hq)
  · exact (totalDegree_smul_le _ _).trans hp

theorem mem_polynomialSpace_iff {d k : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    p ∈ polynomialSpace d k ↔ p.totalDegree ≤ k :=
  ⟨polynomialSpace_degree p, mem_polynomialSpace_of_degree p⟩

theorem polynomialSpace_mono (d : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    polynomialSpace d k ≤ polynomialSpace d l := by
  intro p hp
  exact mem_polynomialSpace_of_degree p ((polynomialSpace_degree p hp).trans hkl)

theorem polynomialIndex_card (d k : ℕ) : Fintype.card (PolynomialIndex d k) = (d + k).choose d := by
  change Fintype.card (Sym (Option (Fin d)) k) = _
  rw [Sym.card_sym_eq_choose]
  simp only [Fintype.card_option, Fintype.card_fin]
  rw [show d + 1 + k - 1 = d + k by omega]
  have h := Nat.choose_symm (by omega : k ≤ d + k)
  simpa using h.symm

theorem polynomialSpace_finrank_le (d k : ℕ) :
    Module.finrank ℝ (polynomialSpace d k) ≤ (d + k).choose d := by
  classical
  apply (finrank_span_le_card (Set.range (boundedMonomial (d := d) (k := k)))).trans
  rw [Set.toFinset_card, ← polynomialIndex_card]
  exact Fintype.card_range_le _

lemma optionMultiset_decomposition {α : Type*} [DecidableEq α] (s : Multiset (Option α)) :
    s = Multiset.replicate (s.count none) none + (s.filterMap id).map some := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    cases a with
    | none => simpa [Multiset.replicate_succ, Multiset.filterMap_cons_none] using
        congrArg (fun t => none ::ₘ t) ih
    | some a => simpa [Multiset.filterMap_cons_some, Multiset.cons_add,
        Multiset.add_cons] using congrArg (fun t => some a ::ₘ t) ih

theorem polynomialExponent_injective (d k : ℕ) :
    Function.Injective (fun s : PolynomialIndex d k => (s.toMultiset.filterMap id).toFinsupp) := by
  classical
  intro s t h
  have he : s.toMultiset.filterMap id = t.toMultiset.filterMap id := by
    simpa using congrArg Finsupp.toMultiset h
  have hs := optionMultiset_decomposition s.toMultiset
  have ht := optionMultiset_decomposition t.toMultiset
  have hc : s.toMultiset.count none = t.toMultiset.count none := by
    have hsc := congrArg Multiset.card hs
    have htc := congrArg Multiset.card ht
    simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_map] at hsc htc
    rw [he] at hsc
    have hst : s.toMultiset.card = t.toMultiset.card := s.property.trans t.property.symm
    omega
  apply Subtype.ext
  exact hs.trans (by rw [hc, he]; exact ht.symm)

theorem boundedMonomial_linearIndependent (d k : ℕ) :
    LinearIndependent ℝ (boundedMonomial (d := d) (k := k)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he := congrArg (fun p : MvPolynomial (Fin d) ℝ => p.coeff ((i.toMultiset.filterMap id).toFinsupp)) hc
  simpa [boundedMonomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_monomial, (polynomialExponent_injective d k).eq_iff] using he

theorem polynomialSpace_finrank (d k : ℕ) :
    Module.finrank ℝ (polynomialSpace d k) = (d + k).choose d := by
  rw [← polynomialIndex_card]
  exact (linearIndependent_iff_card_eq_finrank_span.mp
    (boundedMonomial_linearIndependent d k)).symm

end RoughRegime.Model
