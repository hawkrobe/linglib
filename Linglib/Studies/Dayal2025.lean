import Mathlib.Tactic.DeriveFintype
import Linglib.Data.Examples.Dayal2025
import Linglib.Fragments.English.QuestionParticles
import Linglib.Fragments.HindiUrdu.Particles
import Linglib.Fragments.Japanese.Particles
import Linglib.Semantics.Questions.Exhaustivity
import Linglib.Syntax.Minimalist.LeftPeriphery

/-!
# Dayal (2025): The interrogative left periphery

Question meaning is built at three points of the left periphery. At C a
proposition becomes a set of propositions; at PerspP a perspectival center is
introduced for whom the question is potentially active, which presupposes that
the center may not know the answer; at SAP the speaker puts the addressee under
an obligation to answer. Embedding predicates select up to one of the layers,
and the middle one, quasi-subordination with matrix syntax and intonation,
carries a semantic filter: *know* and *remember* assert knowledge of the answer
and so cannot host it, negation or questioning of them and *forget* leave the
center's ignorance open and can, which is McCloskey's shiftiness. Boundary
tones realize the features of the two upper layers, so a declarative question
is biased in English, where C is typed early, and can be neutral in Hindi-Urdu
and Italian, where typing is delayed; and a bare polar clause can only be
subordinated where a complementizer or Q-morpheme types it, which Hindi-Urdu
lacks. Question particles sit at the layer their embedding distribution shows.

## Implementation notes

* Predicates enter through their at-issue content as a set of worlds: *know*
  and *remember* are the center's knowledge of the answer at the evaluation
  time and *forget* its negation (43b), the past presuppositions set aside as
  the paper does.
* Boundary tones stand in for the features they realize: Persp_CQ and SA_ASK
  rise, Persp_CP and SA_ASSERT fall, the combined act of a biased question
  licenses both (§4.3).

## TODO

* The de se requirement of §3.3, disjoined questions (§4.2), imperatives,
  sentience and rhetorical questions (§5), and selection (§6) are not
  formalized. The centering condition alone licenses *Have you forgotten [was
  Henry a communist]*, which the paper marks unacceptable and attributes to
  who is invested in the answer (`possiblyIgnorant_forgets_question_iff`).

## References

* [V. Dayal, *The interrogative left periphery* (2025)][dayal-2025]
* [J. McCloskey, *Questions and questioning in a local English*
  (2006)][mccloskey-2006]
* [R. Bhatt and V. Dayal, *Polar question particles* (2020)][bhatt-dayal-2020]
* [U. Sauerland and K. Yatsushiro, *Remind-me presuppositions and speech-act
  decomposition* (2017)][sauerland-yatsushiro-2017]
* [C. Gunlogson, *True to form* (2004)][gunlogson-2004]
* [D. Büring and C. Gunlogson, *Aren't positive and negative polar questions
  the same?* (2000)][buring-gunlogson-2000]
* [D. Büring, *Intonation and meaning* (2016)][buring-2016]
* [L. Cheng, *On the typology of wh-questions* (1991)][cheng-1991]
* [M. Speas and C. Tenny, *Configurational properties of point of view roles*
  (2003)][speas-tenny-2003]
* [M. Krifka, *Embedding illocutionary acts* (2014)][krifka-2014]
* [V. Dayal, *Locality in WH quantification* (1996)][dayal-1996]
* [X. V. Zu, *Discourse participants and the structural representation of the
  context* (2018)][zu-2018]
-/

namespace Dayal2025

open Minimalist Questions Features Data.Examples Clause
open English.Predicates.Verbal English.QuestionParticles HindiUrdu.Particles Japanese.Particles

/-! ### The three layers (7), (20) -/

/-- The layer an embedding context reaches: subordination CP, quasi-subordination
PerspP, a matrix clause or a quotation SAP. -/
def layerOfContext : EmbeddingContext → QParticleLayer
  | .subordinated => .cp
  | .quasiSubordinated => .perspP
  | .matrix => .sap
  | .quotation => .sap

/-- The height of a layer in (7). -/
def height : QParticleLayer → ℕ
  | .polP => 0
  | .cp => 1
  | .perspP => 2
  | .sap => 3

/-- A class takes an embedding context when the context's layer is within what it
selects. -/
def Selects (cls : SelectionClass) (e : EmbeddingContext) : Prop :=
  match cls.layer with
  | none => False
  | some l => height (layerOfContext e) ≤ height l

instance (cls : SelectionClass) (e : EmbeddingContext) : Decidable (Selects cls e) := by
  unfold Selects
  split <;> infer_instance

/-! ### Question particles (§1.3) -/

/-- A particle's layer, read off its embedding distribution (20): licensed in subordination
CP, otherwise in quasi-subordination PerspP, otherwise in matrix clauses SAP. -/
def layerOf (p : Particle) : Option QParticleLayer :=
  if p.LicensedInEmbed .subordinated then some .cp
  else if p.LicensedInEmbed .quasiSubordinated then some .perspP
  else if p.LicensedInEmbed .matrix then some .sap
  else none

/-- (15)–(19): Japanese *ka* types the clause at CP, Hindi-Urdu *kya:* sits at PerspP, and
the meta question particles *kke* and *quick* at SAP. -/
theorem layers_derived :
    layerOf ka = some .cp ∧ layerOf kya = some .perspP ∧
      layerOf kke = some .sap ∧ layerOf quick = some .sap := by
  decide

/-! ### Centering (25)–(26), (42)–(43) -/

variable {W E : Type*} {c : Set W} (H : Set (Set W)) (R : E → W → W → Prop) (x : E)

/-- The at-issue content of *x knows Q* and of *x remembers Q*: knowledge of the answer at
the evaluation time. -/
def knows : Set W := {w | KnowsAnswer H w R x}

/-- (43b): *x forgets Q* is ignorance of the answer, its past-knowledge presupposition set
aside. -/
def forgets : Set W := (knows H R x)ᶜ

/-- (26d), (42a): bare *know* and *remember* reject quasi-subordination in every context:
the requirement of Persp_CQ fails on the context updated with the assertion. -/
theorem not_possiblyIgnorant_knows : ¬ PossiblyIgnorant H (c ∩ knows H R x) R x :=
  not_possiblyIgnorant_inter_of_subset subset_rfl

/-- (42b), (43): negated *remember* and bare *forget* quasi-subordinate exactly in the
contexts where the center may be ignorant. -/
theorem possiblyIgnorant_forgets_iff :
    PossiblyIgnorant H (c ∩ forgets H R x) R x ↔ PossiblyIgnorant H c R x :=
  possiblyIgnorant_inter_compl_iff

/-- (42c): under a polar question either answer is at issue, so the same holds of
*Does Sue remember?*. -/
theorem possiblyIgnorant_knows_question_iff :
    PossiblyIgnorant H (c ∩ (knows H R x ∪ (knows H R x)ᶜ)) R x ↔ PossiblyIgnorant H c R x :=
  possiblyIgnorant_inter_union_compl_iff

/-- (46b): the same computation licenses *Have you forgotten [was Henry a communist]*,
which the paper marks unacceptable; §3.3 attributes the difference to who is invested in
the answer, not formalized here. -/
theorem possiblyIgnorant_forgets_question_iff :
    PossiblyIgnorant H (c ∩ (forgets H R x ∪ (forgets H R x)ᶜ)) R x ↔
      PossiblyIgnorant H c R x :=
  possiblyIgnorant_inter_union_compl_iff

/-! ### Boundary tones and the features they realize (§4.3–4.4) -/

inductive Tone where
  | rise
  | fall
  deriving DecidableEq, Repr

/-- The feature on Persp: a centered question or a centered proposition. -/
inductive PerspFeature where
  | cq
  | cp
  deriving DecidableEq, Repr, Fintype

/-- The tone a Persp feature is realized as. -/
def PerspFeature.tone : PerspFeature → Tone
  | .cq => .rise
  | .cp => .fall

/-- The illocutionary head: asking, asserting, or the combined act of a biased question
(64b). -/
inductive Illocution where
  | ask
  | assert
  | assertAsk
  deriving DecidableEq, Repr

/-- The tones an illocution licenses. -/
def Illocution.licenses : Illocution → Tone → Prop
  | .ask, .rise => True
  | .assert, .fall => True
  | .assertAsk, _ => True
  | _, _ => False

instance (sa : Illocution) (t : Tone) : Decidable (sa.licenses t) := by
  cases sa <;> cases t <;> simp only [Illocution.licenses] <;> infer_instance

/-- The tone C demands of Persp, if C is typed. -/
def demand : WHFeature → Option Tone
  | .plusWH => some .rise
  | .minusWH => some .fall
  | .alphaWH => none

/-- Persp agrees with C when C, if typed, demands Persp's tone (75). -/
def AgreesC (f : WHFeature) (p : PerspFeature) : Prop :=
  demand f = none ∨ demand f = some p.tone

instance (f : WHFeature) (p : PerspFeature) : Decidable (AgreesC f p) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A full left periphery is derivable when Persp agrees with C and SAP licenses Persp's
tone (75). -/
def Derivable (f : WHFeature) (p : PerspFeature) (sa : Illocution) : Prop :=
  AgreesC f p ∧ sa.licenses p.tone

instance (f : WHFeature) (p : PerspFeature) (sa : Illocution) : Decidable (Derivable f p sa) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- (64): with interrogative syntax a neutral question is derivable; with declarative
syntax only the combined act of a biased question is. -/
theorem english_declarative_biased :
    Derivable .plusWH .cq .ask ∧ Derivable .minusWH .cp .assertAsk ∧
      ∀ p, ¬ Derivable .minusWH p .ask := by
  decide

/-- (66): where C may stay untyped, a declarative question has both readings. -/
theorem delayed_typing_neutral :
    Derivable .alphaWH .cq .ask ∧ Derivable .alphaWH .cp .assertAsk := by
  decide

/-- (67): without SAP a question needs Persp_CQ, which declarative syntax cannot host, so
declarative questions do not quasi-subordinate. -/
theorem no_quasi_declarative_question : ¬ AgreesC .minusWH .cq := by decide

/-- A language's resources for typing a bare polar clause at C (§4.4): a polar
complementizer (*whether*, *se*) or a clause-typing Q-morpheme (*ka*). -/
structure PolarTyping where
  polarComplementizer : Bool
  qMorpheme : Bool
  deriving DecidableEq, Repr, Fintype

/-- A simplex polar clause is clause-typed in a context when a lexical resource types it
or the context supplies Persp_CQ above C ((72)). -/
def Typed (L : PolarTyping) (e : EmbeddingContext) : Prop :=
  L.polarComplementizer = true ∨ L.qMorpheme = true ∨ height .perspP ≤ height (layerOfContext e)

instance (L : PolarTyping) (e : EmbeddingContext) : Decidable (Typed L e) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def english : PolarTyping := ⟨true, false⟩
def italian : PolarTyping := ⟨true, false⟩
def japanese : PolarTyping := ⟨false, true⟩
def hindiUrdu : PolarTyping := ⟨false, false⟩

/-- (69)–(71): English and Italian subordinate simplex polar questions, Hindi-Urdu does
not; every language quasi-subordinates them. -/
theorem simplex_polar :
    (∀ e, Typed english e ∧ Typed italian e ∧ Typed japanese e) ∧
      ¬ Typed hindiUrdu .subordinated ∧ Typed hindiUrdu .quasiSubordinated ∧
        Typed hindiUrdu .matrix := by
  decide

/-- (71): the fragment's *ya: nahĩ:* is obligatory exactly where nothing else types the
clause. -/
theorem ya_nahi_obligatory_iff :
    ∀ e, ya_nahi.distribution .polar e = some .obligatory ↔ ¬ Typed hindiUrdu e := by
  decide

/-! ### The paper's judgments -/

/-- The English predicates of the paper, from the fragment. -/
def verbs : List VerbEntry :=
  [know, believe, wonder, ask, investigate, depend_on, remember_rog, forget_rog]

/-- The embedding context a row's `embedding` feature names. -/
def contextOf : String → Option EmbeddingContext
  | "subordination" => some .subordinated
  | "quasi" => some .quasiSubordinated
  | "quotation" => some .quotation
  | "matrix" => some .matrix
  | _ => none

/-- Whether a judgment counts as licensed: McCloskey's `?` on (40b) is licensed. -/
def Fine (j : Judgment) : Prop := j = .acceptable ∨ j = .marginal

instance (j : Judgment) : Decidable (Fine j) := inferInstanceAs (Decidable (_ ∨ _))

/-- (8)–(9), (11), (24), (84)–(85): outside quasi-subordination an English predicate embeds
an interrogative iff its lexical class, read off the fragment, selects the context's
layer. -/
theorem selection_rows :
    ∀ row ∈ Examples.all, ∀ v ∈ verbs, ∀ e,
      row.feature? "verb" = some v.form → (row.feature? "embedding").bind contextOf = some e →
      e ≠ .quasiSubordinated →
      (Fine row.judgment ↔ Selects (deriveSelectionClass v) e) := by
  decide

/-- The answer relation of a responsive's at-issue content (43b): *know* and *remember*
assert knowledge, *forget* ignorance. -/
def assertsKnowledge : String → Bool
  | "know" => true
  | "remember" => true
  | _ => false

/-- (8)–(9), (38), (40), (43), (45)–(46), (84)–(85): quasi-subordination is licensed iff the
class selects PerspP and, for a responsive, its content does not assert knowledge of the
answer once negation or questioning is taken into account — the instances of
`not_possiblyIgnorant_knows`, `possiblyIgnorant_forgets_iff` and
`possiblyIgnorant_knows_question_iff` in a context where the center may be ignorant. Rows
the paper attributes to who is invested in the answer (§3.3) carry the feature `invested`
and are set aside. -/
theorem quasi_rows :
    ∀ row ∈ Examples.all, ∀ v ∈ verbs,
      row.feature? "verb" = some v.form →
      (row.feature? "embedding").bind contextOf = some .quasiSubordinated →
      row.feature? "invested" = none →
      (Fine row.judgment ↔
        Selects (deriveSelectionClass v) .quasiSubordinated ∧
          (deriveSelectionClass v = .responsive →
            assertsKnowledge v.form = false ∨ row.feature? "negated" = some "true" ∨
              row.feature? "questioned" = some "true")) := by
  decide

/-- The WH-feature a language's declarative syntax leaves on C: typed early in English,
delayable in Hindi-Urdu and Italian (§4.4). -/
def declarativeC : String → Option WHFeature
  | "stan1293" => some .minusWH
  | "hind1269" => some .alphaWH
  | "ital1282" => some .alphaWH
  | _ => none

/-- (62)–(63): a declarative question has a neutral reading iff its language's C may stay
untyped, and always a biased one. -/
theorem declarative_question_rows :
    ∀ row ∈ Examples.all, ∀ f, row.feature? "syntax" = some "declarative" →
      row.feature? "embedding" = some "matrix" → declarativeC row.language = some f →
      (row.readings.lookup "neutral" = some .acceptable ↔ ∃ p, Derivable f p .ask) ∧
        row.readings.lookup "biased" = some .acceptable := by
  decide

/-- A language's polar typing resources, by glottocode. -/
def typingOf : String → Option PolarTyping
  | "stan1293" => some english
  | "ital1282" => some italian
  | "nucl1643" => some japanese
  | "hind1269" => some hindiUrdu
  | _ => none

/-- (69)–(71): a simplex polar clause is acceptable in a context iff it is clause-typed
there. -/
theorem simplex_rows :
    ∀ row ∈ Examples.all, ∀ L e, row.feature? "simplex" = some "true" →
      typingOf row.language = some L → (row.feature? "embedding").bind contextOf = some e →
      (Fine row.judgment ↔ Typed L e) := by
  decide

end Dayal2025
