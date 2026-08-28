import Linglib.Discourse.Accessibility
import Linglib.Discourse.Centering.Pronominalization
import Linglib.Data.Examples.Ariel2001

/-!
# Ariel 2001: accessibility theory

Referring expressions are accessibility markers: each codes a degree of mental accessibility
of the representation the addressee is to retrieve, and the eighteen classes of the
Accessibility Marking Scale run from full name with modifier down to zero. The scale is
motivated by three partially overlapping criteria — informativity, rigidity, and
attenuation — each anti-correlated with the accessibility a form codes. The accessibility of
a representation is a composite of the antecedent's salience (discourse topics, speaker and
addressee, frame-induced entities), competition among antecedents, distance, and the unity
between antecedent and anaphor; no single factor decides, as when a topical but distant
antecedent takes the higher marker over a recent non-topical one. Against the rival
theories, the Givenness Hierarchy maps many forms of distinct accessibility to one status
and one form to several, and Centering's pronoun rule is silent on lexical anaphors, so it
does not predict the repeated-name penalty.

## Main definitions

* `head`, `modified`, `lexical`, `full`, `deixis`, `stressed`, `bound`: the form features
  the scale's labels name.
* `Factors`: the accessibility factors, with `Factors.Dominates` the factor-wise comparison.
* `givenness`: the Givenness Hierarchy statuses of the scale's forms, as the paper reports
  them.

## References

* [ariel-2001]
* [ariel-1990] — the scale and its distributional basis
* [gundel-hedberg-zacharski-1993] — the Givenness Hierarchy
* [grosz-joshi-weinstein-1995] — Centering's pronoun rule
-/

namespace Ariel2001

open Discourse Features Data.Examples

/-! ### Form-function criteria (§1.1) -/

/-- The head of a form class on the scale. -/
inductive Head
  | name
  | description
  | demonstrative
  | pronoun
  | inflection
  | zero
  deriving DecidableEq, Repr

/-- Demonstrative deixis. -/
inductive Deixis
  | distal
  | proximate
  deriving DecidableEq, Repr

/-- The head named by a scale label. -/
def head : AccessibilityLevel → Head
  | .fullNameMod | .fullName | .lastName | .firstName => .name
  | .longDefDescription | .shortDefDescription => .description
  | .distalDemMod | .proxDemMod | .distalDemNP | .proxDemNP | .distalDem | .proxDem =>
    .demonstrative
  | .stressedPronGesture | .stressedPron | .unstressedPron | .cliticizedPron => .pronoun
  | .verbalAgreement => .inflection
  | .zero => .zero

/-- A modifier, or the long form of a description. -/
def modified : AccessibilityLevel → Bool
  | .fullNameMod | .longDefDescription | .distalDemMod | .proxDemMod => true
  | _ => false

/-- Lexical content beyond the head: a noun or a name. -/
def lexical : AccessibilityLevel → Bool
  | .fullNameMod | .fullName | .lastName | .firstName | .longDefDescription
  | .shortDefDescription | .distalDemMod | .proxDemMod | .distalDemNP | .proxDemNP => true
  | _ => false

/-- A full rather than partial name. -/
def full : AccessibilityLevel → Bool
  | .fullNameMod | .fullName => true
  | _ => false

/-- The deixis of a demonstrative form. -/
def deixis : AccessibilityLevel → Option Deixis
  | .distalDemMod | .distalDemNP | .distalDem => some .distal
  | .proxDemMod | .proxDemNP | .proxDem => some .proximate
  | _ => none

/-- A stressed pronoun. -/
def stressed : AccessibilityLevel → Bool
  | .stressedPronGesture | .stressedPron => true
  | _ => false

/-- A bound pronominal: cliticized, or verbal agreement. -/
def bound : AccessibilityLevel → Bool
  | .cliticizedPron | .verbalAgreement => true
  | _ => false

/-- Informativity: a modifier lowers the accessibility a form codes. -/
theorem informativity_modifier :
    ∀ a b : AccessibilityLevel, head a = head b → deixis a = deixis b →
      modified a → ¬ modified b → a < b := by
  decide

/-- Informativity: a demonstrative with a noun codes lower accessibility than a bare one. -/
theorem informativity_lexical :
    ∀ a b : AccessibilityLevel, head a = head b → deixis a = deixis b →
      ¬ modified a → ¬ modified b → lexical a → ¬ lexical b → a < b := by
  decide

/-- Informativity: a full name codes lower accessibility than a partial one. -/
theorem informativity_partial_name :
    ∀ a b : AccessibilityLevel, head a = .name → head b = .name →
      ¬ modified a → ¬ modified b → full a → ¬ full b → a < b := by
  decide

/-- Rigidity: a full name codes lower accessibility than the description of the same
length. -/
theorem rigidity_full_name :
    ∀ a b : AccessibilityLevel, head a = .name → full a → head b = .description →
      modified a = modified b → a < b := by
  decide

/-- The criteria overlap only partially: a partial name is rigid, yet codes higher
accessibility than a short description. -/
theorem rigidity_not_sufficient :
    AccessibilityLevel.shortDefDescription < AccessibilityLevel.lastName := by
  decide

/-- Attenuation: a stressed pronoun codes lower accessibility than an unstressed one. -/
theorem attenuation_stress :
    ∀ a b : AccessibilityLevel, head a = .pronoun → head b = .pronoun →
      stressed a → ¬ stressed b → a < b := by
  decide

/-- Attenuation: a free pronoun codes lower accessibility than a cliticized one, a pronoun
than verbal agreement, and agreement than zero. -/
theorem attenuation_reduction :
    ∀ a b : AccessibilityLevel,
      (head a = .pronoun ∧ head b = .pronoun ∧ ¬ stressed a ∧ ¬ bound a ∧ bound b) ∨
        (head a = .pronoun ∧ head b = .inflection) ∨ (head a = .inflection ∧ head b = .zero) →
      a < b := by
  decide

/-- The proximate demonstrative codes higher accessibility than the distal one of the same
shape (§5.1 records Kirsner's Dutch data against this). -/
theorem deixis_proximate :
    ∀ a b : AccessibilityLevel, head a = .demonstrative → head b = .demonstrative →
      modified a = modified b → lexical a = lexical b →
      deixis a = some .distal → deixis b = some .proximate → a < b := by
  decide

/-! ### Accessibility as a complex concept (§1.2) -/

/-- The salience of an antecedent by discourse role. -/
inductive Topicality
  | nonTopic
  | localTopic
  | globalTopic
  deriving DecidableEq, Repr

/-- Topicality in increasing order. -/
def Topicality.rank : Topicality → ℕ
  | .nonTopic => 0
  | .localTopic => 1
  | .globalTopic => 2

/-- The factors a degree of accessibility is assessed from: distance since the last mention,
competing antecedents, topicality, and the unity of antecedent and anaphor. -/
structure Factors where
  distance : ℕ
  competitors : ℕ
  topicality : Topicality
  tight : Bool
  deriving DecidableEq, Repr

/-- `a` is at least as accessible as `b` on every factor. -/
def Factors.Dominates (a b : Factors) : Prop :=
  a.distance ≤ b.distance ∧ a.competitors ≤ b.competitors ∧
    b.topicality.rank ≤ a.topicality.rank ∧ (b.tight → a.tight)

instance (a b : Factors) : Decidable (a.Dominates b) := by unfold Factors.Dominates; infer_instance

/-- *Maya kissed Rachel. And then she/SHE …*: the first-mentioned Maya is topical but more
distant, Rachel more recent but not topical. -/
def maya : Factors := ⟨2, 1, .localTopic, false⟩

/-- Rachel's factors in the same example. -/
def rachel : Factors := ⟨1, 1, .nonTopic, false⟩

/-- Neither antecedent dominates the other: the factors pull apart. -/
theorem maya_rachel_incomparable : ¬ maya.Dominates rachel ∧ ¬ rachel.Dominates maya := by
  decide

/-- The scale label of a marker feature. -/
def ofLabel : String → Option AccessibilityLevel
  | "fullNameMod" => some .fullNameMod
  | "fullName" => some .fullName
  | "longDefDescription" => some .longDefDescription
  | "shortDefDescription" => some .shortDefDescription
  | "lastName" => some .lastName
  | "firstName" => some .firstName
  | "distalDemMod" => some .distalDemMod
  | "proxDemMod" => some .proxDemMod
  | "distalDemNP" => some .distalDemNP
  | "proxDemNP" => some .proxDemNP
  | "distalDem" => some .distalDem
  | "proxDem" => some .proxDem
  | "stressedPronGesture" => some .stressedPronGesture
  | "stressedPron" => some .stressedPron
  | "unstressedPron" => some .unstressedPron
  | "cliticizedPron" => some .cliticizedPron
  | "verbalAgreement" => some .verbalAgreement
  | "zero" => some .zero
  | _ => none

/-- The marker a row records under a feature. -/
def marker (r : LinguisticExample) (key : String) : Option AccessibilityLevel :=
  r.feature? key >>= ofLabel

/-- All the markers a row lists, in order. -/
def markers (r : LinguisticExample) : List AccessibilityLevel :=
  r.paperFeatures.filterMap fun p => if p.1 = "marker" then ofLabel p.2 else none

/-- Topicality outranks distance: the topical, more distant Maya takes the higher marker. -/
theorem rows_topicality_over_distance :
    ∀ r ∈ Examples.all, ∀ m ∈ (marker r "maya").toList, ∀ c ∈ (marker r "rachel").toList,
      c < m := by
  decide +kernel

/-- (3) against (4): the entity whose point of view a newspaper takes is coded by the higher
marker — the victim by zero and the rapist by a name in Haaretz, the rapists by zero and the
victim by a demonstrative in Maariv. -/
theorem rows_perspective :
    ∀ r ∈ Examples.all, ∀ v ∈ (marker r "victim").toList, ∀ p ∈ (marker r "rapists").toList,
      (r.feature? "perspective" = some "victim" → p < v) ∧
        (r.feature? "perspective" = some "rapists" → v < p) := by
  decide +kernel

/-- (8): every referring expression of the article's opening sentence codes lower
accessibility than its counterpart in the headline — initial retrievals, but of entities the
headline has just made accessible. -/
theorem rows_headline :
    ∀ a ∈ Examples.all, ∀ b ∈ Examples.all,
      a.source.paperLabel = "(8a)" → b.source.paperLabel = "(8b)" →
        ∀ p ∈ (markers a).zip (markers b), p.2 < p.1 := by
  decide +kernel

/-! ### Competing theories (§4) -/

/-- The Givenness Hierarchy statuses of the scale's forms, as the paper reports them for
English: the pronominal forms are all *in focus*, *that*, *this*, stressed *IT*, and *this
N* all *activated*, and a full name *uniquely identifiable* or *familiar*, a partial name
*familiar* or *activated*. -/
def givenness : AccessibilityLevel → Finset GivennessStatus
  | .zero | .verbalAgreement | .cliticizedPron | .unstressedPron => {.inFocus}
  | .stressedPronGesture | .stressedPron | .proxDem | .distalDem | .proxDemNP
  | .proxDemMod => {.activated}
  | .distalDemNP | .distalDemMod => {.familiar}
  | .longDefDescription | .shortDefDescription => {.uniquelyIdentifiable}
  | .fullNameMod | .fullName => {.uniquelyIdentifiable, .familiar}
  | .lastName | .firstName => {.familiar, .activated}

/-- Many forms, one status: four forms of distinct accessibility are all *activated*. -/
theorem activated_many_forms :
    (∀ l ∈ [AccessibilityLevel.distalDem, .proxDem, .stressedPron, .proxDemNP],
      givenness l = {.activated}) ∧
      ([AccessibilityLevel.distalDem, .proxDem, .stressedPron, .proxDemNP].map
        AccessibilityLevel.rank).Nodup := by
  decide

/-- One form, many statuses: a full name is *uniquely identifiable* or *familiar*. -/
theorem full_name_two_statuses :
    GivennessStatus.uniquelyIdentifiable ∈ givenness .fullName ∧
      GivennessStatus.familiar ∈ givenness .fullName := by
  decide

/-- Zeroes, agreement, cliticized and full pronouns are all *in focus*, though each codes a
different degree of accessibility and has its own distribution. -/
theorem in_focus_collapse :
    (∀ l ∈ [AccessibilityLevel.zero, .verbalAgreement, .cliticizedPron, .unstressedPron],
      givenness l = {.inFocus}) ∧
      ([AccessibilityLevel.zero, .verbalAgreement, .cliticizedPron, .unstressedPron].map
        AccessibilityLevel.rank).Nodup := by
  decide

open Centering in
/-- Centering's pronoun rule says nothing when no pronoun is used, so an entity coded by a
repeated name violates nothing: the repeated-name penalty is not its prediction. -/
theorem pronominalization_vacuous {E R U : Type*} [CfRankerOf E R] [Realizes U E]
    [Pronominalizes U E] (prev : Utterance E R) (cur : U) (h : ∀ e, ¬ pronominalizes cur e) :
    PronominalizationConstraint prev cur :=
  fun ⟨e, _, he⟩ => absurd he (h e)

/-- (12): the discourse topic is pronominal while the subject of two consecutive clauses is
a description — the topic, not the local subject, takes the higher marker. -/
theorem rows_topic_over_subject :
    ∀ r ∈ Examples.all, ∀ t ∈ (marker r "topicMarker").toList,
      ∀ s ∈ (marker r "subjectMarker").toList, s < t := by
  decide +kernel

end Ariel2001
