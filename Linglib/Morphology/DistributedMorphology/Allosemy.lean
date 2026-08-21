import Mathlib.Algebra.Group.WithOne.Defs
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Morphology.DistributedMorphology.Categorizer.Gender
import Linglib.Morphology.Exponence.Select
import Linglib.Morphology.Realization
import Linglib.Semantics.ArgumentStructure.Root.Classification
import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Allosemy

Allosemy is contextual meaning variation of a single functional head —
the LF analogue of allomorphy. The heads v, n, and Voice each carry
several allosemes, selected by the syntactic context rather than tracked
by morphosyntactic features, and the ambiguity of deverbal
nominalizations between event, result, state, entity, and content
readings is the visible trace of that selection. The alloseme
inventories here compose: the typed denotations of `Verbalizer.Alloseme.denote`
and `Nominalizer.Alloseme.denote` derive the reading typology, and the analytical
choice of where the eventive component lives — v or n — is provably
immaterial for the result and content readings.

## Main definitions

* `Alloseme` — the inventory carrier: contentful allosemes with the
  zero alloseme adjoined (`Option`, in the `WithZero` pattern)
* `Verbalizer.Alloseme`, `Nominalizer.Alloseme`, `Voice.Alloseme` —
  each head's inventory under its own API, from its `Contentful` type;
  Voice's expletive is the shared zero
* `Verbalizer.vocabulary`, `Nominalizer.vocabulary`,
  `Voice.vocabulary` — each head's List-3 vocabulary over the shared
  selection engine
* `NominalizationReading`, `readingFromAllosemes` — the reading typology
  of deverbal nominalizations and its alloseme table
* `NominalizationModel`, `Verbalizer.Alloseme.denote`, `Nominalizer.Alloseme.denote` — typed
  alloseme denotations and their composition

## Main statements

* `result_options_pred_agree`, `content_options_agree` — the two
  analytical options for the result and content readings agree on what
  the nominal describes: the event and result readings are mirror images
* `result_options_disagree_on_arguments`,
  `cen_retains_argument_structure`, `zero_v_no_argument_structure` — the
  internal-argument position exists exactly where eventive v introduced
  it: the argument-structural CEN/RN difference, derived
* `readingFromAllosemes_isSome_iff_denote` — the reading table has a
  reading exactly where the composed denotation is defined
* `Verbalizer.ambiguity`, `Nominalizer.cen_result_ambiguity` — one deverbal context licenses
  both v allosemes and several n allosemes: nominalization ambiguity as
  non-singleton licensing
* `Verbalizer.isAllosemous` — v's contextual meaning variation on the
  shared `Realization.Interpreted` carrier

## Implementation notes

An alloseme is a `VocabularyItem` whose exponent is a denotation, so DM's
List 2 (form) and List 3 (meaning) run on one selection engine
(`subsetPrinciple`, `winner?_isElsewhereWinner`); its specification
conditions on the neighboring terminals, not on features of its own head.
`Voice.Alloseme.fromComplement` is a worked List-3 competition on that
engine; `readingFromAllosemes` is a different object — the composition of
two already-selected allosemes.
Existing infrastructure this module retroactively classifies as
allosemy: `Minimalist.Voice.Flavor` (Voice) and root change-type
conditioning of v.

## References

* [I. Benz, *Structure and interpretation across categories*][benz-2025]
* [J. Wood, *Icelandic nominalizations and allosemy*][wood-2023]
* [A. Kratzer, *Severing the external argument from its verb*][kratzer-1996]
* [N. Myler, *Building and interpreting possession sentences*][myler-2016]
* [L. J. Adamson, *Gender assignment is local*][adamson-2024]
-/

namespace DistributedMorphology.Allosemy

open DistributedMorphology (Categorizer Categorizer.Head)
open scoped DistributedMorphology.VocabularyItem
open Minimalist.Voice (Flavor Head)

/-! ### The alloseme carrier

Every head's inventory contains the zero alloseme trivially
([benz-2025] §2.2), so an inventory is the head's contentful allosemes
with a zero adjoined: `Option`, in the `WithZero` pattern, with `none`
the zero alloseme. Each head contributes only its `Contentful` type. -/

/-- The alloseme inventory over a head's contentful allosemes `C`: the
contentful allosemes together with the zero alloseme every head has —
mathlib's `WithZero C`, with the zero alloseme as its `0` (Benz's Ø).
`zero` and `of` are the pattern-matchable faces of `none` and `some`. -/
def Alloseme (C : Type*) : Type _ := WithZero C

namespace Alloseme

variable {C : Type*}

/-- The zero alloseme: semantically Ø. -/
@[match_pattern] def zero : Alloseme C := none

/-- A contentful alloseme. -/
@[match_pattern] def of (c : C) : Alloseme C := some c

@[simp] theorem zero_def : (zero : Alloseme C) = none := rfl

@[simp] theorem of_def (c : C) : of c = some c := rfl

instance [DecidableEq C] : DecidableEq (Alloseme C) :=
  inferInstanceAs (DecidableEq (Option C))

instance [Repr C] : Repr (Alloseme C) := inferInstanceAs (Repr (Option C))

instance [Fintype C] : Fintype (Alloseme C) :=
  inferInstanceAs (Fintype (Option C))

instance : Zero (Alloseme C) := inferInstanceAs (Zero (WithZero C))

/-- The zero alloseme is `WithZero`'s zero. -/
theorem zero_eq_zero : (zero : Alloseme C) = 0 := rfl

/-- The zero alloseme is not contentful. -/
theorem zero_ne_of (c : C) : (zero : Alloseme C) ≠ of c := nofun

end Alloseme

/-! ### v allosemy -/

/-- The contentful alloseme of v: its verbal-domain interpretation,
introducing the event variable and the Theme requirement alongside it
([benz-2025] §2.2). A single meaning here; verbal-domain flavors would
extend this inventory without touching the zero structure. -/
inductive Verbalizer.Contentful where
  | eventive
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of the verbal categorizer v that the nominalization
typology turns on ([benz-2025] §2.2, after [wood-2023]): v is either
interpreted exactly as in the verbal domain or receives the zero
alloseme, in which case no internal-argument position enters the
denotation. The proposal is symmetric in v and n: *observation* is
eventive when v is interpreted and n vacuous, referential when n is
interpreted and v vacuous — one root, one structure, the readings
differing in which head's alloseme is contentful. -/
def Verbalizer.Alloseme : Type := Allosemy.Alloseme Verbalizer.Contentful

namespace Verbalizer.Alloseme

/-- v interpreted as in the verbal domain (CEN contexts). -/
@[match_pattern] def eventive : Verbalizer.Alloseme :=
  Allosemy.Alloseme.of .eventive

/-- Semantically Ø (SEN/RN contexts). -/
@[match_pattern] def zero : Verbalizer.Alloseme := Allosemy.Alloseme.zero

instance : DecidableEq Verbalizer.Alloseme :=
  inferInstanceAs (DecidableEq (Allosemy.Alloseme Verbalizer.Contentful))

instance : Repr Verbalizer.Alloseme :=
  inferInstanceAs (Repr (Allosemy.Alloseme Verbalizer.Contentful))

instance : Fintype Verbalizer.Alloseme :=
  inferInstanceAs (Fintype (Allosemy.Alloseme Verbalizer.Contentful))

end Verbalizer.Alloseme

/-- Does this v alloseme introduce an event variable? -/
def Verbalizer.Alloseme.introducesEvent : Verbalizer.Alloseme → Bool
  | .eventive => true
  | .zero     => false

/-! ### Allosemic entries

An alloseme is a Vocabulary Item whose exponent is a denotation. Its
specification mentions no feature of its own head — the vocabulary is the
head's — and conditions on the neighbors: the complement below, toward the
root, and the embedding head above ([benz-2025] §2.4: allosemy is
conditioned by the interpreted domain below and the features of the next
head above; the exact locality is open). -/

/-- What an alloseme may require of a neighboring terminal: its category,
or that it denotes an event or a state ([kratzer-1996] §2.3 for the
stative–dynamic split conditioning Voice). -/
inductive Feature where
  | cat (c : Categorizer)
  | eventive
  | stative
  deriving DecidableEq, Repr

/-- A specification on the complement, the terminal below the head. -/
def complement (fs : List Feature) : Neighborhood (List Feature) := ⟨[], [fs], []⟩

/-- A specification on the embedding head, the terminal above. -/
def embedding (fs : List Feature) : Neighborhood (List Feature) := ⟨[], [], [fs]⟩

/-- The denotations a vocabulary licenses in a context — the exponents of
its applicable entries. Ambiguity in a context is non-singleton licensing;
the canonical default among the licensed entries is the Elsewhere winner
(`winner?_isElsewhereWinner`). -/
def licensed {Sem : Type*} (v : List (VocabularyItem Feature Sem))
    (n : Neighborhood (List Feature)) : List Sem :=
  (Morphology.Exponence.applicable v n).map (·.exponent)

/-- v's alloseme vocabulary: the eventive alloseme requires an eventive
complement, while the zero alloseme is the unconditioned elsewhere
option, available trivially in any context ([benz-2025] §2.2). Engine
selection picks the more specific eventive alloseme in eventive
contexts; `licensed` keeps both (`Verbalizer.ambiguity`). -/
def Verbalizer.vocabulary : List (VocabularyItem Feature Verbalizer.Alloseme) :=
  [⟨complement [.eventive], .eventive⟩, [] ⟷ .zero]

/-- Both v allosemes are licensed under an eventive complement — the
zero alloseme is the elsewhere option — so an *observation*-type
nominalization supports the eventive and the referential reading from
one structure ([benz-2025] §2.2's symmetric proposal). -/
theorem Verbalizer.ambiguity :
    Verbalizer.Alloseme.eventive ∈ licensed Verbalizer.vocabulary (complement [.eventive])
      ∧ Verbalizer.Alloseme.zero ∈ licensed Verbalizer.vocabulary (complement [.eventive]) := by
  constructor <;> decide

/-- Root change-type conditions v alloseme selection: result roots,
    which entail a prior change, demand the event variable; property
    concept roots do not ([beavers-etal-2021]'s root typology feeding v
    allosemy). -/
def Verbalizer.Alloseme.fromRootType : Verb.Root.ChangeType → Verbalizer.Alloseme
  | .result          => .eventive
  | .propertyConcept => .zero

/-- The bridge preserves the change entailment: eventive v iff the root
entails change. -/
theorem Verbalizer.fromRootType_iff_entailsChange (rt : Verb.Root.ChangeType) :
    (Verbalizer.Alloseme.fromRootType rt).introducesEvent = rt.entailsChange := by
  cases rt <;> rfl

/-! ### n allosemy -/

/-- The contentful allosemes of the nominal categorizer n: [adamson-2024]'s
three root-attached types — relational (the body-part-of relation of (36)),
sortal ((37)), and the alienator that closes a possessor slot ((43),
`ArgumentStructure.Relational.ExPossessor`) — [benz-2025]'s content
alloseme, and [wood-2023]'s deverbal inventory. The deverbal denotations
live in `Nominalizer.Alloseme.denote`. -/
inductive Nominalizer.Contentful where
  | relational    -- introduces a relation (body-part-of)
  | sortal        -- bare categorization
  | alienator     -- existentially closes a possessor
  | content       -- propositional content (CCN reading)
  | simpleEvent   -- picks out entities equal to an event (SEN)
  | result        -- picks out the entity an event produced
  | state         -- picks out states
  | entity        -- picks out entities, no event connection
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of n: the contentful inventory or the zero alloseme —
Ø / identity, on which the noun inherits the verb meaning (CEN). -/
def Nominalizer.Alloseme : Type := Allosemy.Alloseme Nominalizer.Contentful

namespace Nominalizer.Alloseme

@[match_pattern] def relational : Nominalizer.Alloseme := Allosemy.Alloseme.of .relational
@[match_pattern] def sortal : Nominalizer.Alloseme := Allosemy.Alloseme.of .sortal
@[match_pattern] def alienator : Nominalizer.Alloseme := Allosemy.Alloseme.of .alienator
@[match_pattern] def content : Nominalizer.Alloseme := Allosemy.Alloseme.of .content
@[match_pattern] def simpleEvent : Nominalizer.Alloseme := Allosemy.Alloseme.of .simpleEvent
@[match_pattern] def result : Nominalizer.Alloseme := Allosemy.Alloseme.of .result
@[match_pattern] def state : Nominalizer.Alloseme := Allosemy.Alloseme.of .state
@[match_pattern] def entity : Nominalizer.Alloseme := Allosemy.Alloseme.of .entity

/-- Ø / identity: the noun inherits the verb meaning (CEN). -/
@[match_pattern] def zero : Nominalizer.Alloseme := Allosemy.Alloseme.zero

instance : DecidableEq Nominalizer.Alloseme :=
  inferInstanceAs (DecidableEq (Allosemy.Alloseme Nominalizer.Contentful))

instance : Repr Nominalizer.Alloseme :=
  inferInstanceAs (Repr (Allosemy.Alloseme Nominalizer.Contentful))

instance : Fintype Nominalizer.Alloseme :=
  inferInstanceAs (Fintype (Allosemy.Alloseme Nominalizer.Contentful))

end Nominalizer.Alloseme

/-- n's alloseme vocabulary: the non-deverbal allosemes are
unconditioned (all-wildcard contexts), the deverbal ones require a
verbal complement, with the CEN and result allosemes further demanding
an eventive one. -/
def Nominalizer.vocabulary : List (VocabularyItem Feature Nominalizer.Alloseme) :=
  [[] ⟷ .relational, [] ⟷ .sortal, [] ⟷ .alienator,
    ⟨complement [.cat .v], .content⟩,
    ⟨complement [.cat .v, .eventive], .zero⟩,
    ⟨complement [.cat .v], .simpleEvent⟩,
    ⟨complement [.cat .v, .eventive], .result⟩,
    ⟨complement [.cat .v], .state⟩,
    ⟨complement [.cat .v], .entity⟩]

/-- One eventive deverbal context licenses several n allosemes at once —
the CEN reading (zero n) and the result reading among them. The
ambiguity of a nominalization is non-singleton licensing, not structural
ambiguity ([benz-2025], [wood-2023]). -/
theorem Nominalizer.cen_result_ambiguity :
    Nominalizer.Alloseme.zero ∈ licensed Nominalizer.vocabulary (complement [.cat .v, .eventive])
      ∧ Nominalizer.Alloseme.result
        ∈ licensed Nominalizer.vocabulary (complement [.cat .v, .eventive]) := by
  constructor <;> decide

/-! ### Voice allosemy -/

/-- The contentful (θ-assigning) allosemes of Voice: [kratzer-1996]'s
agent and holder — the severing argument observes that the holder
function cannot combine with an action predicate, nor the agent function
with a stative one, so the thematic role is fixed by the complement —
and [myler-2016]'s engineer role for ECM *have*. -/
inductive Voice.Contentful where
  | agent     -- combines with dynamic action complements
  | holder    -- combines with stative complements
  | engineer  -- ECM *have*: saturated eventive VoiceP complement
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of Voice: a θ-role or the zero alloseme —
[myler-2016]'s expletive identity for relational and light-verb *have*,
where Voice assigns no θ-role. The expletive is the same zero every
head has. -/
def Voice.Alloseme : Type := Allosemy.Alloseme Voice.Contentful

namespace Voice.Alloseme

@[match_pattern] def agent : Voice.Alloseme := Allosemy.Alloseme.of .agent
@[match_pattern] def holder : Voice.Alloseme := Allosemy.Alloseme.of .holder
@[match_pattern] def engineer : Voice.Alloseme := Allosemy.Alloseme.of .engineer

/-- Identity; no θ-role: the zero alloseme of Voice. -/
@[match_pattern] def expletive : Voice.Alloseme := Allosemy.Alloseme.zero

instance : DecidableEq Voice.Alloseme :=
  inferInstanceAs (DecidableEq (Allosemy.Alloseme Voice.Contentful))

instance : Repr Voice.Alloseme :=
  inferInstanceAs (Repr (Allosemy.Alloseme Voice.Contentful))

instance : Fintype Voice.Alloseme :=
  inferInstanceAs (Fintype (Allosemy.Alloseme Voice.Contentful))

end Voice.Alloseme

/-- The alloseme assigns a thematic role to the external argument;
only the expletive identity does not. -/
def Voice.Alloseme.AssignsTheta (a : Voice.Alloseme) : Prop :=
  a ≠ .expletive

instance : DecidablePred Voice.Alloseme.AssignsTheta :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- The Voice allosemes as a competing exponence vocabulary
    ([myler-2016]): engineer for a saturated eventive VoiceP complement
    (most specified), holder for a stative one, expletive elsewhere (the
    all-wildcard default). -/
def Voice.vocabulary : List (VocabularyItem Feature Voice.Alloseme) :=
  [⟨complement [.cat .v, .eventive], .engineer⟩, ⟨complement [.stative], .holder⟩,
    [] ⟷ .expletive]

/-- Voice alloseme selection from complement properties: Elsewhere
    competition over `Voice.vocabulary`, resolved by the shared exponence
    engine ([myler-2016]'s conditioning of the alloseme on the nature of
    *have*'s complement). -/
def Voice.Alloseme.fromComplement
    (complementIsEventiveVoiceP : Prop) [Decidable complementIsEventiveVoiceP]
    (complementIsStative : Prop) [Decidable complementIsStative] : Voice.Alloseme :=
  (subsetPrinciple Voice.vocabulary (complement
    ((if complementIsEventiveVoiceP then [.cat .v, .eventive] else []) ++
      if complementIsStative then [.stative] else []))).getD .expletive

/-- Eventive-VoiceP complement selects engineer ([myler-2016]). -/
example : Voice.Alloseme.fromComplement True False = .engineer := by decide

/-- Stative complement selects holder ([kratzer-1996]). -/
example : Voice.Alloseme.fromComplement False True = .holder := by decide

/-- Neither condition met selects the elsewhere expletive. -/
example : Voice.Alloseme.fromComplement False False = .expletive := by decide

/-- Bridge to the syntactic `Flavor` inventory. Syntactically all four
    allosemes realize the same Voice with a DP specifier; the θ-role
    distinction is resolved at LF ([myler-2016]). The map picks the
    flavor matching each alloseme's syntactic behavior. -/
def Voice.Alloseme.toFlavor : Voice.Alloseme → Flavor
  | .agent    => .agentive
  | .holder   => .experiencer
  | .engineer => .agentive
  | .expletive => .expletive

/-- The bridge respects θ-assignment: an alloseme assigns a thematic
role iff its syntactic flavor does. -/
theorem Voice.theta_consistent (a : Voice.Alloseme) :
    a.AssignsTheta ↔ Head.AssignsTheta { flavor := a.toFlavor, hasD := true } := by
  revert a; decide

/-! ### Nominalization readings -/

/-- Reading types for deverbal nominalizations: [wood-2023]'s five
    terminal readings plus [benz-2025]'s complex content nominal. -/
inductive NominalizationReading where
  | complexEvent   -- CEN: full verbal event reading with argument structure
  | simpleEvent    -- SEN: event reading without argument structure
  | result         -- entity whose existence results from an event
  | simpleState    -- state reading
  | simpleEntity   -- entity reading, no event connection
  | content        -- CCN: propositional content, takes a CP complement
  deriving DecidableEq, Repr, Fintype

/-- The reading of a nominalization from the allosemes of v and n.

    The CEN pairs eventive v with zero n (the noun inherits the verb
    meaning); the simple readings pair zero v with the event, state, and
    entity allosemes of n. For the result and content readings
    [benz-2025] §3.5 notes two analytical options, both already in
    [wood-2023]: either v is vacuous everywhere but the CEN — the option
    the dissertation's denotations adopt, on which the event and result
    readings are mirror images — or the eventive component always comes
    from v. Both derivations are admitted, and `result_options_agree`
    shows the choice is denotationally immaterial. Content does not
    require a verbal source at all: simple content nouns (*Gerücht*
    'rumor', *fact*, *idea*) have the reading with no corresponding verb
    ([benz-2025] §3.5, Table 2). The non-deverbal allosemes yield no
    nominalization reading — their semantics is the relationalizer π and
    its possessor-closing `ExPossessor`. [benz-2025] §2.2 further observes that
    referential readings could instead involve no v at all, a
    root-attached n — a different structure rather than a different
    alloseme, outside this table. -/
def readingFromAllosemes : Verbalizer.Alloseme → Nominalizer.Alloseme → Option NominalizationReading
  | .eventive, .zero        => some .complexEvent
  | .eventive, .result      => some .result   -- both-heads-interpreted option
  | .eventive, .content     => some .content  -- both-heads-interpreted option
  | .zero,     .simpleEvent => some .simpleEvent
  | .zero,     .state       => some .simpleState
  | .zero,     .entity      => some .simpleEntity
  | .zero,     .result      => some .result   -- v-vacuous option
  | .zero,     .content     => some .content  -- v-vacuous option
  | _,         .sortal      => none
  | _,         .relational  => none
  | _,         .alienator   => none
  | .zero,     .zero        => none
  | .eventive, .simpleEvent => none
  | .eventive, .state       => none
  | .eventive, .entity      => none

/-! ### Typed alloseme denotations

The denotations of the deverbal allosemes, after [wood-2023] as taken
over by [benz-2025] Ch. 3: nominalization semantics happens over a
domain in which eventualities are entities, and each n alloseme builds
an entity predicate from what v hands it. The reading typology is then
derived, not tabulated: readings exist exactly where the composition is
defined (`readingFromAllosemes_isSome_iff_denote`), and the analytical
options for the result and content readings compose to identical
denotations (`result_options_agree`, `content_options_agree`). -/

variable {E S : Type*}

/-- A model for nominalization denotations: eventualities embed into the
entity domain (a nominal can describe an event as an entity), split into
stative and dynamic, with `result` relating an entity to the eventuality
that produced it and `hasContent` picking out the entities with
propositional content. -/
structure NominalizationModel (E S : Type*) where
  /-- Eventualities as entities. -/
  ev : S → E
  ev_injective : Function.Injective ev
  /-- Stative eventualities. -/
  stative : S → Prop
  /-- The entity is the result of the eventuality. -/
  result : E → S → Prop
  /-- The entity has propositional content (*rumor*, *idea*, *claim*). -/
  hasContent : E → Prop

/-- A root's contribution to nominalization semantics: what it says of
entities and of eventualities, and its Theme relation — which entity an
eventuality of the root's kind is predicated of. -/
structure RootMeaning (E S : Type*) where
  onEntities : E → Prop
  onEvents : S → Prop
  theme : E → S → Prop

/-- What v hands to n: under the eventive alloseme, verbal event content
together with the Theme position v introduces ([benz-2025] §2.2); under
the zero alloseme, the untouched root — and no argument position, since
none is introduced by v (§3.5). -/
inductive Verbalizer.Denotation (E S : Type*) where
  | eventive (p : S → Prop) (theme : E → S → Prop)
  | zero (ρ : RootMeaning E S)

/-- The v alloseme applied to the root. -/
def Verbalizer.Alloseme.denote (ρ : RootMeaning E S) :
    Verbalizer.Alloseme → Verbalizer.Denotation E S
  | .eventive => .eventive ρ.onEvents ρ.theme
  | .zero     => .zero ρ

/-- A nominal denotation: the entity predicate, together with the
internal-argument relation when the nominal retains one. The relation is
present exactly when v introduced the Theme position — no such position
is part of the denotation unless v contributes it ([benz-2025] §2.2,
§3.5). -/
structure NominalDenotation (E S : Type*) where
  /-- What the nominal describes. -/
  pred : E → Prop
  /-- The internal-argument relation: `internalArg y x` holds when `y`
  saturates the nominal `x`'s Theme position (*the observation of the
  sky*). -/
  internalArg : Option (E → E → Prop) := none

/-- The n alloseme applied to v's output, `none` where the combination
is uninterpretable. The CEN describes the events the verb describes and
retains the Theme position v introduced; the SEN predicates the root's
entity content of an event-entity; the result alloseme picks out what an
event of the root's kind produced ([benz-2025]'s denotation, taken over
from [wood-2023]); the content alloseme ignores the verbal layer
entirely. The non-deverbal allosemes have their semantics in
`Semantics/Possessive/Relational.lean` (π, `ExPossessor`). -/
def Nominalizer.Alloseme.denote (m : NominalizationModel E S) :
    Verbalizer.Denotation E S → Nominalizer.Alloseme →
      Option (NominalDenotation E S)
  | .eventive p θ, .zero =>
      some { pred := fun x => ∃ e, x = m.ev e ∧ p e
           , internalArg := some fun y x => ∃ e, x = m.ev e ∧ p e ∧ θ y e }
  | .eventive p θ, .result =>
      some { pred := fun x => ∃ e, p e ∧ m.result x e
           , internalArg := some fun y x => ∃ e, p e ∧ θ y e ∧ m.result x e }
  | .eventive _ _, .content => some { pred := m.hasContent }
  | .zero ρ, .simpleEvent =>
      some { pred := fun x => ρ.onEntities x ∧ ∃ e, x = m.ev e }
  | .zero ρ, .state =>
      some { pred := fun x => ∃ e, x = m.ev e ∧ m.stative e ∧ ρ.onEvents e }
  | .zero ρ, .result =>
      some { pred := fun x => ∃ e, ρ.onEvents e ∧ m.result x e }
  | .zero ρ, .entity => some { pred := ρ.onEntities }
  | .zero _, .content => some { pred := m.hasContent }
  | _, _ => none

/-- The event and result readings are mirror images at the
entity-predicate level: the two analytical options for the result
reading — eventive v with n's result alloseme, or vacuous v with the
same — agree on what the nominal describes ([benz-2025] §3.5, crediting
[wood-2023]). -/
theorem result_options_pred_agree (m : NominalizationModel E S)
    (ρ : RootMeaning E S) :
    (Nominalizer.Alloseme.denote m
        (Verbalizer.Alloseme.eventive.denote ρ) .result).map (·.pred)
      = (Nominalizer.Alloseme.denote m
          (Verbalizer.Alloseme.zero.denote ρ) .result).map (·.pred) := rfl

/-- ...but not on argument structure: on the both-heads-interpreted
option the result nominal retains the internal-argument position v
introduced, on the v-vacuous option it has none. Since result nominals
cannot saturate an internal argument, this derives [benz-2025]'s reason
for adopting the vacuous option for the RN reading (§3.5, following
[wood-2023]). -/
theorem result_options_disagree_on_arguments (m : NominalizationModel E S)
    (ρ : RootMeaning E S) :
    (∃ r, Nominalizer.Alloseme.denote m
        (Verbalizer.Alloseme.eventive.denote ρ) .result = some r
      ∧ r.internalArg.isSome)
    ∧ ∃ r, Nominalizer.Alloseme.denote m
        (Verbalizer.Alloseme.zero.denote ρ) .result = some r
      ∧ r.internalArg = none :=
  ⟨⟨_, rfl, rfl⟩, _, rfl, rfl⟩

/-- CENs retain argument structure: the complex event nominal carries
the Theme position v introduced (*the observation of the sky*), which is
what separates it from every zero-v reading
(`zero_v_no_argument_structure`). -/
theorem cen_retains_argument_structure (m : NominalizationModel E S)
    (ρ : RootMeaning E S) :
    ∃ r, Nominalizer.Alloseme.denote m
        (Verbalizer.Alloseme.eventive.denote ρ) .zero = some r
      ∧ r.internalArg.isSome :=
  ⟨_, rfl, rfl⟩

/-- No zero-v reading has an internal-argument position: none is
introduced by v, so none is part of the denotation ([benz-2025] §3.5). -/
theorem zero_v_no_argument_structure (m : NominalizationModel E S)
    (ρ : RootMeaning E S) (n : Nominalizer.Alloseme)
    {r : NominalDenotation E S}
    (h : Nominalizer.Alloseme.denote m
        (Verbalizer.Alloseme.zero.denote ρ) n = some r) :
    r.internalArg = none := by
  rcases n with _ | cn
  · simp [Verbalizer.Alloseme.denote, Nominalizer.Alloseme.denote] at h
  · cases cn <;>
      simp only [Verbalizer.Alloseme.denote, Nominalizer.Alloseme.denote,
        Option.some.injEq, reduceCtorEq] at h <;>
      (try subst h) <;> rfl

/-- The content reading likewise ignores the verbal layer: both v
options compose to `hasContent`, which is how simple content nouns can
have the reading with no verbal source at all ([benz-2025] §3.5). -/
theorem content_options_agree (m : NominalizationModel E S) (ρ : RootMeaning E S) :
    Nominalizer.Alloseme.denote m (Verbalizer.Alloseme.eventive.denote ρ) .content
      = Nominalizer.Alloseme.denote m (Verbalizer.Alloseme.zero.denote ρ) .content := rfl

/-- The reading typology tracks denotational definedness: a (v, n) pair
has a reading exactly when its composed denotation is defined. -/
theorem readingFromAllosemes_isSome_iff_denote (m : NominalizationModel E S)
    (ρ : RootMeaning E S) (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    (readingFromAllosemes v n).isSome
      ↔ (Nominalizer.Alloseme.denote m (v.denote ρ) n).isSome := by
  rcases v with _ | cv <;> rcases n with _ | cn <;>
    (try cases cv) <;> (try cases cn) <;>
    simp [readingFromAllosemes, Verbalizer.Alloseme.denote,
      Nominalizer.Alloseme.denote]

/-- A complex event nominal holds only of event-entities: the ground of
its event reading (temporal modification, aspectual behavior). -/
theorem cen_denotes_events (m : NominalizationModel E S) (ρ : RootMeaning E S)
    {r : NominalDenotation E S}
    (h : Nominalizer.Alloseme.denote m
        (Verbalizer.Alloseme.eventive.denote ρ) .zero = some r) :
    ∀ x, r.pred x → ∃ e, x = m.ev e := by
  simp only [Verbalizer.Alloseme.denote, Nominalizer.Alloseme.denote,
    Option.some.injEq] at h
  subst h
  rintro x ⟨e, rfl, -⟩
  exact ⟨e, rfl⟩

/-! ### The `Realization.Interpreted` view

An allosemic head is a List-3 object: a single morpheme whose
interpretation is resolved in context by the shared exponence engine.
`Realization.Interpreted` is exactly that carrier — an opaque index with
a contextual `interp` map — with an empty List-2 form side, since
allosemy is meaning-only. Contextual meaning variation, Benz's core
claim that allosemy is allomorphy's LF analogue, is then literally
`Realization.Interpreted.IsAllosemous`. -/

/-- The allosemy engine as a `Realization.Interpreted` view: one
abstract head whose contextual interpretation is the alloseme the Subset
Principle picks from the vocabulary (a singleton, `∅` at a semantic gap),
with an empty List-2 form side. -/
def toInterpreted {Sem : Type} (v : List (VocabularyItem Feature Sem)) :
    Morphology.Realization.Interpreted Unit (Neighborhood (List Feature)) Unit Sem where
  realize _ _ := ∅
  interp _ n := (subsetPrinciple v n).elim ∅ ({·})

/-- The verbal categorizer's meaning varies with context — eventive
under an eventive complement, zero elsewhere — so v is `IsAllosemous` on
the shared carrier: contextual meaning variation as non-constancy of the
`interp` map ([benz-2025]). -/
theorem Verbalizer.isAllosemous :
    (toInterpreted Verbalizer.vocabulary).IsAllosemous () :=
  ⟨complement [.eventive], ∅, .eventive, by decide, .zero, by decide, by decide⟩

end DistributedMorphology.Allosemy
