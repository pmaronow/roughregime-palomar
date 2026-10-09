module

public import RoughRegime.SourceNondegenerate


@[expose] public section
/-! True localization of all smaller positive source weights, with design
volume and score functions fixed before any additional finite restrictions. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.LatticePriors
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

 theorem source_positive_smaller_weights (A0 : Model.Parameters) (D Q K : ℕ)
     {Z : Type*} [MeasurableSpace Z]
     (O : Model.Observables Z (A0.withDimension D)) (π : ProbabilityMeasure Z)
     (S : Scores (π : Measure Z))
     (gammaStar lambdaStar alpha0 v0 rminus rplus : ℝ)
     (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4) (hlam : 0 < lambdaStar)
     (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1) (hK : 0 < K) (hKQ : K ≤ 2*Q)
     (ht : alpha0 < A0.α) (hs : alpha0 < A0.β)
     (hbudgetU : Model.holderOrder A0.α+2 ≤ K) (hbudgetV : Model.holderOrder A0.β+2 ≤ K)
     (hv : 0 < v0) (hv1 : v0 ≤ 1) (hrminus : 0 < rminus) (hlt : rminus < rplus)
     (hden : 0 < 1-v0*sourceOuterIntegral (D+1))
     (hbase : A0.δ < Model.baselineW (A0.withDimension D) O π)
     (hcrossU : residualMomentU (A0.withDimension D) O π S false=0)
     (hcrossV : residualMomentV (A0.withDimension D) O π S true=0)
     (ha : |Model.baselineA (A0.withDimension D) O π| < A0.H)
     (hb : |Model.baselineB (A0.withDimension D) O π| < A0.H)
     (hinterval : A0.gminus ≤ Model.baselineW (A0.withDimension D) O π*rminus ∧
       Model.baselineW (A0.withDimension D) O π*rplus ≤ A0.gplus) :
     ∃ epsilonU epsilonV c : ℝ, 0 < epsilonU ∧ epsilonU ≤ 1 ∧
       0 < epsilonV ∧ epsilonV ≤ 1 ∧ 0 < c ∧
       ∀ (epsilonU' epsilonV' : ℝ), epsilonU' ≤ epsilonU → epsilonV' ≤ epsilonV →
       ∀ (heU : 0 ≤ epsilonU') (heV : 0 ≤ epsilonV') (N J M : ℕ) (hN : 0 < N) (m delta r : ℝ),
       ∀ (hm : 0 < m) (hd : 0 < delta) (_hr : 0 ≤ r)
         (hmargin : delta ≤ sourceMarginBound (D+1) v0 rminus rplus),
       (2:ℝ)^((J:ℝ)*alpha0) ≤ m →
       m ≤ (2:ℝ)^((J:ℝ)*A0.α) → m ≤ (2:ℝ)^((J:ℝ)*A0.β) →
       let F := sourceCanonicalFrame D N J Q M hN gammaStar lambdaStar alpha0 m
         epsilonU' epsilonV' A0.α A0.β v0 rminus rplus delta hγ hγ1 hm
         heU heV hv hv1 hrminus hlt hd hmargin hden
       F.Au+F.Av ≤ c*min delta (min r 1) →
       ∃ hsmall : (F.Au+F.Av)/rminus*S.C ≤ 1/4,
       ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
       (law S (F.field z) hsmall).probabilityMeasure ∈ Model.localClass (A0.withDimension D) O π r := by
   have hw : 0 < Model.baselineW (A0.withDimension D) O π := A0.hδ.trans hbase
   obtain ⟨κ,Cu,Cv,hκ,hCu,hCv,hclass⟩ := source_positive_model_localization A0 D Q K O π S
     gammaStar lambdaStar alpha0 v0 rminus rplus hγ hγ1 hlam ha0 ha1 hK hKQ ht hs hbudgetU hbudgetV
     hv hv1 hrminus hlt hden hw hcrossU hcrossV ha.le hb.le hinterval
   obtain ⟨epsilonU,heU,heU1,heHU⟩ := exists_positive_source_weight Cu _ hCu (sub_pos.mpr ha)
   obtain ⟨epsilonV,heV,heV1,heHV⟩ := exists_positive_source_weight Cv _ hCv (sub_pos.mpr hb)
   obtain ⟨c,hc,hscalar⟩ := exists_source_localization_threshold (A0.withDimension D) O π S
     rminus rplus κ hrminus (hrminus.le.trans hlt.le) hκ hbase
   refine ⟨epsilonU,epsilonV,c,heU,heU1,heV,heV1,hc,?_⟩
   intro epsilonU' epsilonV' hleU hleV heU0 heV0 N J M hN m delta r hm hd hr hmargin hm0 hmU hmV
   have heHU' : Cu*epsilonU' ≤ A0.H-|Model.baselineA (A0.withDimension D) O π| :=
     (mul_le_mul_of_nonneg_left hleU hCu.le).trans heHU
   have heHV' : Cv*epsilonV' ≤ A0.H-|Model.baselineB (A0.withDimension D) O π| :=
     (mul_le_mul_of_nonneg_left hleV hCv.le).trans heHV
   dsimp only
   let F := sourceCanonicalFrame D N J Q M hN gammaStar lambdaStar alpha0 m epsilonU' epsilonV'
     A0.α A0.β v0 rminus rplus delta hγ hγ1 hm heU0 heV0 hv hv1 hrminus hlt hd hmargin hden
   change F.Au+F.Av ≤ c*min delta (min r 1) → _
   intro hamp
   obtain ⟨hKsmall,hsmall,hoverlap,hcollar,hwr,har,hbr⟩ :=
     hscalar delta r (F.Au+F.Av) hd.le hr (add_nonneg F.Au_nonneg F.Av_nonneg) hamp
   refine ⟨hsmall,?_⟩
   exact hclass N J M hN m epsilonU' epsilonV' delta r hm heU0 heV0 hd hmargin
     hm0 hmU hmV heHU' heHV'  hKsmall hsmall hoverlap hcollar hwr har hbr


 theorem source_equal_exponent_smaller_weights (A0 : Model.Parameters) (D Q K : ℕ)
     {Z : Type*} [MeasurableSpace Z]
     (O : Model.Observables Z (A0.withDimension D)) (π : ProbabilityMeasure Z)
     (S : Scores (π : Measure Z))
     (gammaStar lambdaStar alpha0 v0 rminus rplus : ℝ)
     (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4) (hlam : 0 < lambdaStar)
     (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1) (hK : 0 < K) (hKQ : K ≤ 2*Q)
     (ht : alpha0 < A0.α) (hs : alpha0 < A0.β)
     (hbudgetU : Model.holderOrder A0.α+2 ≤ K) (hbudgetV : Model.holderOrder A0.β+2 ≤ K)
     (hv : 0 < v0) (hv1 : v0 ≤ 1) (hrminus : 0 < rminus) (hlt : rminus < rplus)
     (hden : 0 < 1-v0*sourceOuterIntegral (D+1))
     (hbase : A0.δ < Model.baselineW (A0.withDimension D) O π)
     (hαβ : A0.α=A0.β)
     (ha : |Model.baselineA (A0.withDimension D) O π| < A0.H)
     (hb : |Model.baselineB (A0.withDimension D) O π| < A0.H)
     (hinterval : A0.gminus ≤ Model.baselineW (A0.withDimension D) O π*rminus ∧
       Model.baselineW (A0.withDimension D) O π*rplus ≤ A0.gplus) :
     ∃ epsilonU epsilonV c : ℝ, 0 < epsilonU ∧ epsilonU ≤ 1 ∧
       0 < epsilonV ∧ epsilonV ≤ 1 ∧ 0 < c ∧
       ∀ (epsilonU' epsilonV' : ℝ), epsilonU' ≤ epsilonU → epsilonV' ≤ epsilonV →
       ∀ (heU : 0 ≤ epsilonU') (heV : 0 ≤ epsilonV') (N J M : ℕ) (hN : 0 < N) (m delta r : ℝ),
       ∀ (hm : 0 < m) (hd : 0 < delta) (_hr : 0 ≤ r)
         (hmargin : delta ≤ sourceMarginBound (D+1) v0 rminus rplus),
       (2:ℝ)^((J:ℝ)*alpha0) ≤ m →
       m ≤ (2:ℝ)^((J:ℝ)*A0.α) → m ≤ (2:ℝ)^((J:ℝ)*A0.β) →
       let F := sourceCanonicalFrame D N J Q M hN gammaStar lambdaStar alpha0 m
         epsilonU' epsilonV' A0.α A0.β v0 rminus rplus delta hγ hγ1 hm
         heU heV hv hv1 hrminus hlt hd hmargin hden
       F.Au+F.Av ≤ c*min delta (min r 1) →
       ∃ hsmall : (F.Au+F.Av)/rminus*S.C ≤ 1/4,
       ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
       (law S (F.field z) hsmall).probabilityMeasure ∈ Model.localClass (A0.withDimension D) O π r := by
   have hw : 0 < Model.baselineW (A0.withDimension D) O π := A0.hδ.trans hbase
   obtain ⟨κ,Cu,Cv,hκ,hCu,hCv,hclass⟩ := source_equal_exponent_model_localization A0 D Q K O π S
     gammaStar lambdaStar alpha0 v0 rminus rplus hγ hγ1 hlam ha0 ha1 hK hKQ ht hs hbudgetU hbudgetV
     hv hv1 hrminus hlt hden hw hαβ ha.le hb.le hinterval
   obtain ⟨epsilon,he,he1,heH⟩ := exists_positive_source_weight (2*(Cu+Cv))
     (min (A0.H-|Model.baselineA (A0.withDimension D) O π|)
       (A0.H-|Model.baselineB (A0.withDimension D) O π|)) (by positivity)
     (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))
   let epsilonU := epsilon
   let epsilonV := epsilon
   have heU : 0 < epsilonU := he
   have heV : 0 < epsilonV := he
   have heU1 : epsilonU ≤ 1 := he1
   have heV1 : epsilonV ≤ 1 := he1
   have heHU : Cu*(epsilonU+epsilonV) ≤ A0.H-|Model.baselineA (A0.withDimension D) O π| := by
     have hbU := heH.trans (min_le_left _ _)
     dsimp [epsilonU,epsilonV]
     nlinarith only [hbU,mul_nonneg hCv.le he.le]
   have heHV : Cv*(epsilonU+epsilonV) ≤ A0.H-|Model.baselineB (A0.withDimension D) O π| := by
     have hbV := heH.trans (min_le_right _ _)
     dsimp [epsilonU,epsilonV]
     nlinarith only [hbV,mul_nonneg hCu.le he.le]
   obtain ⟨c,hc,hscalar⟩ := exists_source_localization_threshold (A0.withDimension D) O π S
     rminus rplus κ hrminus (hrminus.le.trans hlt.le) hκ hbase
   refine ⟨epsilonU,epsilonV,c,heU,heU1,heV,heV1,hc,?_⟩
   intro epsilonU' epsilonV' hleU hleV heU0 heV0 N J M hN m delta r hm hd hr hmargin hm0 hmU hmV
   have heHU' : Cu*(epsilonU'+epsilonV') ≤ A0.H-|Model.baselineA (A0.withDimension D) O π| :=
     (mul_le_mul_of_nonneg_left (add_le_add hleU hleV) hCu.le).trans heHU
   have heHV' : Cv*(epsilonU'+epsilonV') ≤ A0.H-|Model.baselineB (A0.withDimension D) O π| :=
     (mul_le_mul_of_nonneg_left (add_le_add hleU hleV) hCv.le).trans heHV
   dsimp only
   let F := sourceCanonicalFrame D N J Q M hN gammaStar lambdaStar alpha0 m epsilonU' epsilonV'
     A0.α A0.β v0 rminus rplus delta hγ hγ1 hm heU0 heV0 hv hv1 hrminus hlt hd hmargin hden
   change F.Au+F.Av ≤ c*min delta (min r 1) → _
   intro hamp
   obtain ⟨hKsmall,hsmall,hoverlap,hcollar,hwr,har,hbr⟩ :=
     hscalar delta r (F.Au+F.Av) hd.le hr (add_nonneg F.Au_nonneg F.Av_nonneg) hamp
   refine ⟨hsmall,?_⟩
   exact hclass N J M hN m epsilonU' epsilonV' delta r hm heU0 heV0 hd hmargin
     hm0 hmU hmV heHU' heHV'  hKsmall hsmall hoverlap hcollar hwr har hbr


end RoughRegime.LatticePriors
