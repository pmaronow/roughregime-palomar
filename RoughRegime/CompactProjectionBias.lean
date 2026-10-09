module

public import RoughRegime.CompactDensityParameters


@[expose] public section
/-! A compact family of density intervals admits a common genuine projection
bias constant. We enlarge only the interval used to bound the approximation
norm; every actual law, Gram matrix, weighted projection and rate parameter
retains its own original value. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RoughRegime.Model
universe u
set_option backward.isDefEq.respectTransparency false

 theorem compact_density_envelope (G : Set (ℝ×ℝ)) (hG : IsCompact G)
     (hdom : G⊆densityIntervalDomain) :
     ∃lo hi:ℝ,0<lo ∧ lo<hi ∧ ∀I∈G,lo≤I.1 ∧ I.2≤hi := by
   by_cases hne : G.Nonempty
   · obtain ⟨Il,hIl,hl⟩:=hG.exists_isMinOn hne continuous_fst.continuousOn
     obtain ⟨Iu,hIu,hu⟩:=hG.exists_isMaxOn hne continuous_snd.continuousOn
     exact ⟨Il.1,Iu.2,(hdom hIl).1,(hl hIu).trans_lt (hdom hIu).2,fun I hI=>⟨hl hI,hu hI⟩⟩
   · exact ⟨1,2,by norm_num,by norm_num,fun I hI=>False.elim (hne ⟨I,hI⟩)⟩

 def Observables.rebaseDensity (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) (J : ℝ×ℝ) (hJ : J∈densityIntervalDomain)
     (F : Observables Z (densityParameters A I hI)) : Observables Z (densityParameters A J hJ) where
   D:=F.D
   U:=F.U
   V:=F.V
   W:=F.W
   lam:=F.lam
   hlam:=F.hlam
   measurableD:=F.measurableD
   measurableU:=F.measurableU
   measurableV:=F.measurableV
   measurableW:=F.measurableW
   boundD:=F.boundD
   boundU:=F.boundU
   boundV:=F.boundV
   boundW:=F.boundW

 def ModelWitness.enlargeDensity (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) (J : ℝ×ℝ) (hJ : J∈densityIntervalDomain)
     (hlo : J.1≤I.1) (hhi : I.2≤J.2)
     (F : Observables Z (densityParameters A I hI))
     (P : ProbabilityMeasure (Observation (densityParameters A I hI) Z))
     (W : ModelWitness (densityParameters A I hI) F P) :
     ModelWitness (densityParameters A J hJ) (F.rebaseDensity A I hI J hJ) P where
   p:=W.p
   w:=W.w
   a:=W.a
   b:=W.b
   measurableP:=W.measurableP
   measurableW:=W.measurableW
   measurableA:=W.measurableA
   measurableB:=W.measurableB
   nonnegativeP:=W.nonnegativeP
   marginal:=W.marginal
   momentD:=W.momentD
   momentU:=W.momentU
   momentV:=W.momentV
   overlap:=W.overlap
   smoothA:=W.smoothA
   smoothB:=W.smoothB
   densityBounds:=W.densityBounds.mono (fun _x hx=>⟨hlo.trans hx.1,hx.2.trans hhi⟩)

 theorem compact_uniform_projection_telescope_resolution_bias (A : Parameters) (hαβ : A.α≤A.β)
     (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hdom : G⊆densityIntervalDomain) :
     ∃C:ℝ,0<C ∧ ∀(I:ℝ×ℝ)(hI:I∈G),
       ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z (densityParameters A I (hdom hI)))
       (P:ProbabilityMeasure (Observation (densityParameters A I (hdom hI)) Z))
       (W:ModelWitness (densityParameters A I (hdom hI)) F P)(J:ℕ),
       |W.productTarget-(W.levelProjectionTarget (holderOrder A.β) 0+
         ∑j∈Finset.range J,W.levelProjectionIncrement j)|≤C*((2:ℝ)^J)^(-A.theta) := by
   obtain ⟨lo,hi,hlo,hlt,henvelope⟩:=compact_density_envelope G hG hdom
   let B := densityParameters A (lo,hi) ⟨hlo,hlt⟩
   obtain ⟨C,hC,hbias⟩:=uniform_projection_telescope_resolution_bias.{u} B hαβ
   refine ⟨C,hC,?_⟩
   intro I hI Z mZ F P W J
   let W0 := W.enlargeDensity A I (hdom hI) (lo,hi) ⟨hlo,hlt⟩
     (henvelope I hI).1 (henvelope I hI).2 F P
   have he := hbias Z (F.rebaseDensity A I (hdom hI) (lo,hi) ⟨hlo,hlt⟩) P W0 J
   exact he

end RoughRegime.Model
