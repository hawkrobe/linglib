import Linglib.Semantics.Questions.Partition.QUD
import Linglib.Semantics.Focus.ExtractionClash
import Linglib.Semantics.ArgumentStructure.LevinClass
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Data.Examples.LuPanDegen2025

/-!
# Lu, Pan and Degen (2025): Evidence for a Discourse Account of Manner-of-Speaking Islands

This file formalizes the backgroundedness account of manner-of-speaking islands that
[lu-pan-degen-2025] support in five acceptability experiments. A constituent is foregrounded
when its alternatives are alternatives of the question under discussion, Definition 1 after
[roberts-1996] and [roberts-2012], and backgrounded otherwise: a communication event has a
manner and a content, and a question about the one backgrounds the other (`Foregrounded`,
`Backgrounded`, `mannerQUD`, `contentQUD`). Extraction foregrounds the moved element, so
extraction from a backgrounded complement is the information-structural clash of
[erteschik-shir-1973], the substrate's `extractionISClash`. A manner-of-speaking verb carries
a manner component, *whisper* being *say* in a whispering manner, which makes the manner
question the default and backgrounds the complement, while the light *say* leaves its content
foregrounded, so the complement is an island exactly when the matrix predicate carries manner
and no focus on the embedded object overrides the default question (`Island`, `island_iff`).
The experiments' predictions follow: focus on the embedded object ameliorates the island,
Experiments 1, 2a and 3b (`not_island_of_focus`), a manner adverb on *say* recreates it,
Experiment 3a (`island_adverb`), and a backgrounded complement is unaffected by matrix
negation, the negation test (4) (`unaffectedByNegation_iff_island`). The manner component is
read from the verb's Levin class, so the prediction follows from the lexical classification of
`Fragments/English` (`hasManner_of_mannerOfSpeaking`, `island_whisper`, `not_island_say`), and
the stimulus rows of `Data/Examples/LuPanDegen2025` are classified by the same rule
(`rows_classified`).

## Implementation notes

The subjacency and verb-frame-frequency accounts the paper argues against are described in
prose: prosodic focus changes neither structure nor frequency, and the *say* plus adverb
contrast holds the verb constant. The residual difference between manner-of-speaking verbs
and *say* under one prosody, Experiment 2a, the per-verb correlation of backgroundedness with
acceptability, Experiment 2b, and the rating means are not represented; the paper notes that
the account makes no prediction about the obligatory overt complementizer of
manner-of-speaking complements (16).

## References

* [lu-pan-degen-2025]
* [roberts-1996]
* [roberts-2012]
* [erteschik-shir-1973]
* [kratzer-selkirk-2020]
* [levin-1993]
-/

namespace LuPanDegen2025

open Focus Features Focus.ExtractionClash ArgumentStructure English.Predicates.Verbal
open Data.Examples

/-! ### Foreground and background (Definition 1) -/

section Foregrounding

variable {M A : Type*}

/-- A dimension `π` of the events is foregrounded under the question `q`: its alternatives are
alternatives of the question, so two events in one cell agree on it. -/
def Foregrounded (q : QUD M) (π : M → A) : Prop :=
  ∀ e e', q.r e e' → π e = π e'

/-- A dimension varied by `upd` is backgrounded under `q`: varying it never changes the cell. -/
def Backgrounded (q : QUD M) (upd : M → A → M) : Prop :=
  ∀ e a, q.r e (upd e a)

/-- A dimension that can be varied is not both foregrounded and backgrounded. -/
theorem Foregrounded.not_backgrounded {q : QUD M} {π : M → A} {upd : M → A → M}
    (hf : Foregrounded q π) (h : ∃ e a, π (upd e a) ≠ π e) : ¬ Backgrounded q upd :=
  λ hb => let ⟨e, a, hne⟩ := h; hne (hf _ _ (hb e a)).symm

end Foregrounding

/-! ### Communication events -/

/-- A communication event: how it was said and what was said. -/
structure CommEvent (Manner Content : Type*) where
  manner : Manner
  content : Content

namespace CommEvent

variable {Manner Content : Type*}

/-- The event with another content. -/
def withContent (e : CommEvent Manner Content) (c : Content) : CommEvent Manner Content :=
  ⟨e.manner, c⟩

/-- The event with another manner. -/
def withManner (e : CommEvent Manner Content) (m : Manner) : CommEvent Manner Content :=
  ⟨m, e.content⟩

end CommEvent

section Questions

variable {Manner Content : Type*} [DecidableEq Manner] [DecidableEq Content]

/-- The manner question, *how did John say it?*: events in one cell share a manner. -/
def mannerQUD : QUD (CommEvent Manner Content) := QUD.ofDecEq CommEvent.manner

/-- The content question, *what did John say?*: events in one cell share a content. -/
def contentQUD : QUD (CommEvent Manner Content) := QUD.ofDecEq CommEvent.content

omit [DecidableEq Content] in
theorem mannerQUD_r_iff (e e' : CommEvent Manner Content) :
    (mannerQUD (Manner := Manner) (Content := Content)).r e e' ↔ e.manner = e'.manner :=
  Iff.rfl

omit [DecidableEq Manner] in
theorem contentQUD_r_iff (e e' : CommEvent Manner Content) :
    (contentQUD (Manner := Manner) (Content := Content)).r e e' ↔ e.content = e'.content :=
  Iff.rfl

omit [DecidableEq Content] in
/-- The manner question foregrounds the manner. -/
theorem foregrounded_manner_mannerQUD :
    Foregrounded (mannerQUD (Manner := Manner) (Content := Content)) CommEvent.manner :=
  λ _ _ h => h

omit [DecidableEq Content] in
/-- The manner question backgrounds the content. -/
theorem backgrounded_content_mannerQUD :
    Backgrounded (mannerQUD (Manner := Manner) (Content := Content)) CommEvent.withContent :=
  λ _ _ => rfl

omit [DecidableEq Manner] in
/-- The content question foregrounds the content. -/
theorem foregrounded_content_contentQUD :
    Foregrounded (contentQUD (Manner := Manner) (Content := Content)) CommEvent.content :=
  λ _ _ h => h

omit [DecidableEq Manner] in
/-- The content question backgrounds the manner. -/
theorem backgrounded_manner_contentQUD :
    Backgrounded (contentQUD (Manner := Manner) (Content := Content)) CommEvent.withManner :=
  λ _ _ => rfl

omit [DecidableEq Content] in
/-- With two contents to choose from, the manner question does not foreground the content. -/
theorem not_foregrounded_content_mannerQUD (m : Manner) {c c' : Content} (h : c ≠ c') :
    ¬ Foregrounded (mannerQUD (Manner := Manner) (Content := Content)) CommEvent.content :=
  λ hf => hf.not_backgrounded ⟨⟨m, c⟩, c', h.symm⟩ backgrounded_content_mannerQUD

/-! ### Extraction as a content question -/

/-- Extraction from the complement asks after its content; the question is relevant to the
active question only if some change of content changes the cell ([roberts-1996]). -/
def ContentQuestionRelevant (q : QUD (CommEvent Manner Content)) : Prop :=
  ∃ e : CommEvent Manner Content, ∃ c, ¬ q.r e (e.withContent c)

omit [DecidableEq Manner] [DecidableEq Content] in
/-- The content question is relevant exactly when the content is not backgrounded. -/
theorem contentQuestionRelevant_iff (q : QUD (CommEvent Manner Content)) :
    ContentQuestionRelevant q ↔ ¬ Backgrounded q CommEvent.withContent := by
  simp [ContentQuestionRelevant, Backgrounded]

omit [DecidableEq Content] in
/-- Under the manner question the content question is irrelevant: every filler gives the same
answer. -/
theorem not_contentQuestionRelevant_mannerQUD :
    ¬ ContentQuestionRelevant (mannerQUD (Manner := Manner) (Content := Content)) :=
  λ h => (contentQuestionRelevant_iff _).1 h backgrounded_content_mannerQUD

omit [DecidableEq Manner] in
/-- Under the content question it is relevant, given two contents. -/
theorem contentQuestionRelevant_contentQUD (m : Manner) {c c' : Content} (h : c ≠ c') :
    ContentQuestionRelevant (contentQUD (Manner := Manner) (Content := Content)) :=
  ⟨⟨m, c⟩, c', h⟩

end Questions

/-! ### The default question and the island -/

/-- The matrix predicate: a verb of the fragment, and whether a manner adverb modifies it. -/
structure MatrixPredicate where
  verb : VerbEntry
  mannerAdverb : Bool

/-- Whether the verb's Levin class specifies manner, the manner-of-speaking class of
[levin-1993] (`MeaningComponents.mannerSpec`). -/
def MatrixPredicate.lexicalManner (p : MatrixPredicate) : Bool :=
  (p.verb.levinClass.map λ lc => lc.meaningComponents.mannerSpec).getD false

/-- The predicate carries manner, lexically or by a manner adverb. -/
def MatrixPredicate.HasManner (p : MatrixPredicate) : Prop :=
  p.lexicalManner = true ∨ p.mannerAdverb = true

instance : DecidablePred MatrixPredicate.HasManner := λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A verb of the manner-of-speaking class carries manner however it is modified. -/
theorem hasManner_of_mannerOfSpeaking {v : VerbEntry} (h : v.levinClass = some .mannerOfSpeaking)
    (b : Bool) : MatrixPredicate.HasManner ⟨v, b⟩ :=
  Or.inl (by simp [MatrixPredicate.lexicalManner, h, LevinClass.meaningComponents])

/-- A verb of the *say* class carries manner only by an adverb. -/
theorem hasManner_say_iff {v : VerbEntry} (h : v.levinClass = some .say) (b : Bool) :
    MatrixPredicate.HasManner ⟨v, b⟩ ↔ b = true := by
  simp [MatrixPredicate.HasManner, MatrixPredicate.lexicalManner, h, LevinClass.meaningComponents]

/-- The dimension the active question addresses. -/
inductive Dimension where
  | manner
  | content
  deriving DecidableEq

/-- Focus on the embedded object makes the content question active; otherwise a predicate
with manner makes the manner question the default, and one without leaves the content
question. -/
def activeDimension (p : MatrixPredicate) (embeddedFocus : Bool) : Dimension :=
  if embeddedFocus then .content else if p.HasManner then .manner else .content

/-- The complement's status: backgrounded, the given status of [kratzer-selkirk-2020], under
the manner question, and new under the content question. -/
def complementStatus : Dimension → BinaryGivenness
  | .manner => .given
  | .content => .new

/-- The complement is an island: extraction, which foregrounds the moved element, clashes with
the complement's backgrounded status. -/
def Island (p : MatrixPredicate) (embeddedFocus : Bool) : Prop :=
  extractionISClash .focused (complementStatus (activeDimension p embeddedFocus))

instance (p : MatrixPredicate) (f : Bool) : Decidable (Island p f) :=
  inferInstanceAs (Decidable (extractionISClash _ _))

/-- The island arises exactly when the predicate carries manner and no focus on the embedded
object overrides the default question. -/
theorem island_iff (p : MatrixPredicate) (f : Bool) : Island p f ↔ p.HasManner ∧ f = false := by
  unfold Island activeDimension
  cases f <;> by_cases h : p.HasManner <;> simp [h, complementStatus, extractionISClash]

theorem island_of_hasManner {p : MatrixPredicate} (h : p.HasManner) : Island p false :=
  (island_iff p false).2 ⟨h, rfl⟩

theorem not_island_of_not_hasManner {p : MatrixPredicate} (h : ¬ p.HasManner) (f : Bool) :
    ¬ Island p f :=
  λ hi => h ((island_iff p f).1 hi).1

/-- Prosodic amelioration: focus on the embedded object removes the island whatever the
predicate, Experiments 1, 2a and 3b. -/
theorem not_island_of_focus (p : MatrixPredicate) : ¬ Island p true :=
  λ h => Bool.noConfusion ((island_iff p true).1 h).2

/-- A manner adverb makes any verb's complement an island, Experiment 3a. -/
theorem island_adverb (v : VerbEntry) : Island ⟨v, true⟩ false :=
  island_of_hasManner (Or.inr rfl)

/-! ### The negation test (4) -/

/-- Backgrounded content is unaffected by matrix sentential negation
([erteschik-shir-1973]). -/
def UnaffectedByNegation : BinaryGivenness → Prop
  | .given => True
  | .new => False

instance : DecidablePred UnaffectedByNegation := λ s => by
  cases s <;> unfold UnaffectedByNegation <;> infer_instance

/-- The negation test and islandhood coincide, both being the complement's backgrounded
status. -/
theorem unaffectedByNegation_iff_island (p : MatrixPredicate) (f : Bool) :
    UnaffectedByNegation (complementStatus (activeDimension p f)) ↔ Island p f := by
  unfold Island
  cases h : complementStatus (activeDimension p f) <;>
    simp [UnaffectedByNegation, extractionISClash]

/-! ### The fragment's verbs -/

/-- *John whispered that Mary met with the lawyer*: an island by the verb's class. -/
theorem island_whisper : Island ⟨whisper, false⟩ false :=
  island_of_hasManner (hasManner_of_mannerOfSpeaking rfl false)

/-- *John said that Mary met with the lawyer*: no island. -/
theorem not_island_say (f : Bool) : ¬ Island ⟨say, false⟩ f :=
  not_island_of_not_hasManner (λ h => Bool.noConfusion ((hasManner_say_iff rfl false).1 h)) f

/-- *John said softly that Mary met with the lawyer*: an island by the adverb. -/
theorem island_say_softly : Island ⟨say, true⟩ false :=
  island_adverb say

/-! ### The stimulus rows -/

/-- The matrix predicate of a stimulus row: *whisper* for the manner-of-speaking items,
*say* and *say softly* for the others. -/
def rowPredicate (e : LinguisticExample) : Option MatrixPredicate :=
  match e.feature? "verb_type" with
  | some "mos" => some ⟨whisper, false⟩
  | some "say" => some ⟨say, false⟩
  | some "sayAdverb" => some ⟨say, true⟩
  | _ => none

/-- Whether the row's embedded object bears focus. -/
def rowFocus (e : LinguisticExample) : Option Bool :=
  match e.feature? "focus_condition" with
  | some "embeddedFocus" => some true
  | some "verbFocus" | some "adverbFocus" | some "none" => some false
  | _ => none

/-- The rows' judgments follow the rule: the degraded member of each contrast is the island. -/
theorem rows_classified :
    ∀ e ∈ Examples.all, ∀ p ∈ rowPredicate e, ∀ f ∈ rowFocus e,
      (Island p f ↔ e.judgment = .marginal) := by
  decide

end LuPanDegen2025
