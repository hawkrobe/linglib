import Linglib.Semantics.ArgumentStructure.ArgumentIntroduction
import Linglib.Syntax.Minimalist.Verbal.Applicative
import Linglib.Data.Examples.Pylkkanen2008

/-!
# Pylkkänen (2008): Introducing Arguments

This file formalizes [pylkkanen-2008]'s inventory of argument-introducing heads (Table 1.1) and
the two typologies built on it. Applicative heads are high or low: a high applicative relates
the applied argument to the event by Event Identification, a low applicative relates it to the
verb's theme by a transfer-of-possession relation, so only a high applicative can attach to a
verb without a theme. Causative heads vary along two parameters: whether Cause is bundled with
Voice into one head, and whether Cause selects a root, a verb, or a phase.

The applicative diagnostics of Table 2.1 are instances of the substrate lemmas
`IntroMode.licenses_unergative_iff` and `IntroMode.licenses_kimian_iff`, checked against the six
languages' rows in `Data.Examples.Pylkkanen2008`. The causative predictions of Tables 3.1 and
3.2 are derived from `Cause.Embeds`, the layers a causative head's complement may contain, and
from the two-step interpretation of the bundled head, `bundledCause`; their joint corollary is
that a root-selecting, Voice-bundling causative leaves no position for a causee.

## Implementation notes

The third applicative diagnostic, the availability of the applied argument for depictive
modification, is a typing fact in the book: a depictive phrase is of type ⟨e,⟨s,t⟩⟩ and combines
by Predicate Modification with constituents of that type, which a high Appl' is and a low Appl'
is not. No proposition asserts that an application fails to typecheck, so that diagnostic is
recorded in the data rows only.

The Voice-bundling status of the Bemba, Luganda, and Venda causatives is unknown (Table 3.1,
note a), so only the English, Japanese, and Finnish heads are given as `Cause` values.

## References

[pylkkanen-2008], [kratzer-1996], [marantz-1993], [marantz-1997], [cuervo-2003]
-/

namespace Pylkkanen2008

open ArgumentStructure Minimalist Data.Examples Examples

variable {Entity : Type*} {T : Type*} [LinearOrder T]

/-! ### Applicatives: high relates to the event, low to the theme -/

/-- The introduction mode of each applicative head (Table 1.1, rows 1–3): a high applicative
relates the applied argument to the event, and both low applicatives relate it to the theme,
differing only in the direction of the transfer-of-possession relation. -/
def introMode : ApplType → IntroMode
  | .high => .toEvent
  | .lowRecipient | .lowSource => .toTheme

theorem introMode_eq_toEvent_iff (a : ApplType) : introMode a = .toEvent ↔ a = .high := by
  cases a <;> simp [introMode]

/-- Table 2.1, test 1: an applicative attaches to an unergative exactly when it is high. -/
theorem licenses_unergative_iff (a : ApplType) (body : Event T → Prop) :
    (introMode a).Licenses (VerbDenot.unergative (Entity := Entity) body) ↔ a = .high := by
  rw [IntroMode.licenses_unergative_iff, introMode_eq_toEvent_iff]

/-- Table 2.1, test 2: an applicative attaches to a static verb exactly when it is high. -/
theorem licenses_kimian_iff (a : ApplType) (rel : Entity → Entity → Prop) :
    (introMode a).Licenses (VerbDenot.kimianStative (T := T) rel) ↔ a = .high := by
  rw [IntroMode.licenses_kimian_iff, introMode_eq_toEvent_iff]

/-- The applicative constructions the book analyzes, with the heads it assigns them
(Table 1.1, together with the Korean and Albanian applicatives of Chapter 2). -/
inductive Construction where
  | chagaBenefactive
  | lugandaBenefactive
  | vendaBenefactive
  | albanianBenefactive
  | japaneseGaplessAdversity
  | englishDOC
  | japaneseDOC
  | koreanDOC
  | hebrewPossessorDative
  | japaneseAdversityCausative
  | japaneseGappedAdversity
  deriving DecidableEq, Repr

/-- The head assigned to each construction. -/
def Construction.head : Construction → ApplType
  | .chagaBenefactive | .lugandaBenefactive | .vendaBenefactive | .albanianBenefactive
  | .japaneseGaplessAdversity => .high
  | .englishDOC | .japaneseDOC | .koreanDOC => .lowRecipient
  | .hebrewPossessorDative | .japaneseAdversityCausative | .japaneseGappedAdversity => .lowSource

/-- Table 2.1: each of the six languages with the construction tested, its unergative test, and
its static-verb test. -/
def table21 : List (Construction × LinguisticExample × LinguisticExample) :=
  [(.englishDOC, ex20a, ex20b), (.japaneseDOC, ex21a, ex21b), (.koreanDOC, ex22a, ex22b),
   (.lugandaBenefactive, ex23a, ex23b), (.vendaBenefactive, ex24a, ex24b),
   (.albanianBenefactive, ex25a, ex25b)]

/-- Tests 1 and 2 come out as `licenses_unergative_iff` and `licenses_kimian_iff` predict: the
applicative attaches to an unergative, and to a static verb, exactly in the languages whose
head is high. -/
theorem table21_tests :
    ∀ t ∈ table21, (t.2.1.judgment = .acceptable ↔ t.1.head = .high) ∧
      (t.2.2.judgment = .acceptable ↔ t.1.head = .high) := by
  decide

/-- Table 2.5: the gapless Japanese adversity passive, a high applicative, attaches to
unergatives, while the gapped one, a low source applicative, requires a theme. -/
theorem adversity_passives (body : Event T → Prop) :
    (introMode Construction.japaneseGaplessAdversity.head).Licenses
        (VerbDenot.unergative (Entity := Entity) body) ∧
      ¬ (introMode Construction.japaneseGappedAdversity.head).Licenses
        (VerbDenot.unergative (Entity := Entity) body) := by
  simp [licenses_unergative_iff, Construction.head]

/-- The transitivity restriction on Hebrew possessor datives (Table 2.2) follows from their
low source analysis. -/
theorem possessor_dative_transitivity (body : Event T → Prop) :
    ¬ (introMode Construction.hebrewPossessorDative.head).Licenses
      (VerbDenot.unergative (Entity := Entity) body) := by
  simp [licenses_unergative_iff, Construction.head]

/-! ### Voice bundling: Cause introduces a causing event, not a causer -/

/-- The Voice-bundling head `[Cause, Voice]` (42), interpreted in two steps with Cause first
(44): it introduces a causing event and then the external argument of that event. -/
def bundledCause (cause : Event T → Event T → Prop) (θExt : ThematicRel Entity T)
    (caused : Event T → Prop) : ThematicRel Entity T :=
  eventIdentification θExt (causeBieventive cause caused)

/-- The bundled head means what the causer-introducing Cause of §3.2 means: bundling packages
Cause and Voice into one head without changing what either contributes. -/
theorem bundledCause_eq_causeThetaRole (cause : Event T → Event T → Prop)
    (θExt : ThematicRel Entity T) (caused : Event T → Prop) :
    bundledCause cause θExt caused = causeThetaRole cause θExt caused := rfl

/-- Table 3.1, first row of every cell: a Voice-bundling causative always has an external
argument, so unaccusative causatives are impossible. An independent Cause introduces none
(`causeBieventive_no_external_arg`), which is what the Japanese adversity causative needs. -/
theorem bundledCause_external {cause : Event T → Event T → Prop} {θExt : ThematicRel Entity T}
    {caused : Event T → Prop} {x : Entity} {e : Event T} (h : bundledCause cause θExt caused x e) :
    θExt x e :=
  h.1

/-! ### Selection: Cause takes a root, a verb, or a phase -/

/-- The layers of the Kratzer/Marantz verbal architecture (12): the category-neutral root, the
verb a category-defining head makes of it, and the phase closed by an external-argument
introducer, Voice or a high applicative. -/
inductive Layer where
  | root
  | verb
  | phase
  deriving DecidableEq, Repr, Fintype

/-- Containment order on layers. -/
def Layer.rank : Layer → ℕ
  | .root => 0
  | .verb => 1
  | .phase => 2

instance : LinearOrder Layer := LinearOrder.lift' Layer.rank (by decide)

/-- A causative head: the largest layer its complement may contain (11) and whether Cause is
bundled with Voice (10). -/
structure Cause where
  selects : Layer
  bundled : Bool
  deriving DecidableEq, Repr

/-- `c.Embeds l`: a constituent of layer `l` can occur between the root and Cause. -/
def Cause.Embeds (c : Cause) (l : Layer) : Prop := l ≤ c.selects

instance (c : Cause) (l : Layer) : Decidable (c.Embeds l) := inferInstanceAs (Decidable (_ ≤ _))

/-- Table 3.2, rows 1 and 2: VP modifiers take scope below Cause, and verbal morphology
intervenes between the root and Cause, exactly when Cause selects at least a verb. The two
rows correlate because both are this one fact. -/
theorem embeds_verb_iff (c : Cause) : c.Embeds .verb ↔ c.selects ≠ .root := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide

/-- Table 3.2, rows 3 and 4: agent-oriented modifiers take scope below Cause, and high
applicative morphology intervenes between the root and Cause, exactly when Cause selects a
phase. -/
theorem embeds_phase_iff (c : Cause) : c.Embeds .phase ↔ c.selects = .phase := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide

/-- A causee position (94): inside Cause's complement when that complement is at least a verb,
or between Cause and Voice when Cause is not bundled with Voice. -/
def Cause.HasCauseePosition (c : Cause) : Prop := c.Embeds .verb ∨ c.bundled = false

instance (c : Cause) : Decidable c.HasCauseePosition := inferInstanceAs (Decidable (_ ∨ _))

/-- Table 3.1, second row: causatives of unergatives and transitives are impossible exactly for
a root-selecting, Voice-bundling head. -/
theorem hasCauseePosition_iff (c : Cause) :
    c.HasCauseePosition ↔ ¬ (c.selects = .root ∧ c.bundled = true) := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide

/-- The English zero-causative: root-selecting and Voice-bundling. -/
def englishZero : Cause := ⟨.root, true⟩

/-- The Japanese lexical causative: root-selecting, with Cause independent of Voice. -/
def japaneseLexical : Cause := ⟨.root, false⟩

/-- The Finnish *-tta* causative: verb-selecting, with Cause independent of Voice. -/
def finnishTta : Cause := ⟨.verb, false⟩

/-- (95) and (96): the English and Japanese root-selecting causatives differ on unergative
bases exactly as `hasCauseePosition_iff` predicts. -/
theorem root_causativized_unergative :
    (ex95.judgment = .acceptable ↔ englishZero.HasCauseePosition) ∧
      (ex96.judgment = .acceptable ↔ japaneseLexical.HasCauseePosition) := by
  decide

end Pylkkanen2008
