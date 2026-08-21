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
readings is the visible trace of that selection. The reading typology
`readingFromAllosemes` is grounded in typed denotations in
`Studies/Benz2025.lean`, where it is shown to track definedness.

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

## Main statements

* `Voice.theta_consistent` — a Voice alloseme assigns a θ-role iff its
  syntactic flavor does
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
* [J. Beavers et al., *States and changes of state*][beavers-etal-2021]
-/

namespace DistributedMorphology.Allosemy

open DistributedMorphology (Categorizer Categorizer.Head)
open scoped DistributedMorphology.VocabularyItem
open Minimalist.Voice (Flavor Head)

/-! ### The alloseme carrier

Every head's inventory contains the zero alloseme trivially, so an
inventory is the head's contentful allosemes with a zero adjoined:
`Option`, in the `WithZero` pattern, with `none` the zero alloseme. Each
head contributes only its `Contentful` type. -/

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

instance [DecidableEq C] : DecidableEq (Alloseme C) :=
  inferInstanceAs (DecidableEq (Option C))

instance [Repr C] : Repr (Alloseme C) := inferInstanceAs (Repr (Option C))

instance [Fintype C] : Fintype (Alloseme C) :=
  inferInstanceAs (Fintype (Option C))

instance : Zero (Alloseme C) := inferInstanceAs (Zero (WithZero C))

end Alloseme

/-! ### v allosemy -/

/-- The contentful alloseme of v: its verbal-domain interpretation,
introducing the event variable and the Theme requirement alongside it. A
single meaning here; verbal-domain flavors would
extend this inventory without touching the zero structure. -/
inductive Verbalizer.Contentful where
  | eventive
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of the verbal categorizer v that the nominalization
typology turns on: v is either
interpreted exactly as in the verbal domain or receives the zero
alloseme, in which case no internal-argument position enters the
denotation. The proposal is symmetric in v and n: *observation* is
eventive when v is interpreted and n vacuous, referential when n is
interpreted and v vacuous — one root, one structure, the readings
differing in which head's alloseme is contentful. -/
abbrev Verbalizer.Alloseme := Allosemy.Alloseme Verbalizer.Contentful

namespace Verbalizer.Alloseme

/-- v interpreted as in the verbal domain (CEN contexts). -/
@[match_pattern] def eventive : Verbalizer.Alloseme :=
  Allosemy.Alloseme.of .eventive

/-- Semantically Ø (SEN/RN contexts). -/
@[match_pattern] def zero : Verbalizer.Alloseme := Allosemy.Alloseme.zero

end Verbalizer.Alloseme

/-- Does this v alloseme introduce an event variable? -/
def Verbalizer.Alloseme.introducesEvent : Verbalizer.Alloseme → Bool
  | .eventive => true
  | .zero     => false

/-! ### Allosemic entries

An alloseme is a Vocabulary Item whose exponent is a denotation. Its
specification mentions no feature of its own head — the vocabulary is the
head's — and conditions on the neighbors: the complement below, toward the
root, and the embedding head above — allosemy is conditioned by the
interpreted domain below and the features of the next head above. The
locality of the conditioning — the first category head's
spell-out domain, across semantically null heads only — is `Spine.Visible`
(`Locality.lean`). -/

/-- What an alloseme may require of a neighboring terminal: its category,
or that it denotes an event or a state — the stative–dynamic split that
conditions Voice. -/
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
option, available trivially in any context. Engine
selection picks the more specific eventive alloseme in eventive
contexts; `licensed` keeps both. -/
def Verbalizer.vocabulary : List (VocabularyItem Feature Verbalizer.Alloseme) :=
  [⟨complement [.eventive], .eventive⟩, [] ⟷ .zero]

/-- Root change-type conditions v alloseme selection: result roots,
    which entail a prior change, demand the event variable; property
    concept roots do not — the root typology feeding v allosemy. -/
def Verbalizer.Alloseme.fromRootType : Verb.Root.ChangeType → Verbalizer.Alloseme
  | .result          => .eventive
  | .propertyConcept => .zero

/-- The bridge preserves the change entailment: eventive v iff the root
entails change. -/
theorem Verbalizer.fromRootType_iff_entailsChange (rt : Verb.Root.ChangeType) :
    (Verbalizer.Alloseme.fromRootType rt).introducesEvent = rt.entailsChange := by
  cases rt <;> rfl

/-! ### n allosemy -/

/-- The contentful allosemes of the nominal categorizer n: the three
root-attached types — relational (the body-part-of relation), sortal, and
the alienator that closes a possessor slot
(`ArgumentStructure.Relational.ExPossessor`) — the content alloseme, and
the deverbal inventory. The deverbal denotations live in
`Studies/Benz2025.lean`. -/
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
abbrev Nominalizer.Alloseme := Allosemy.Alloseme Nominalizer.Contentful

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

/-! ### Voice allosemy -/

/-- The contentful (θ-assigning) allosemes of Voice: agent and holder —
the severing argument observes that the holder function cannot combine
with an action predicate, nor the agent function with a stative one, so
the thematic role is fixed by the complement — and the engineer role for
ECM *have*. -/
inductive Voice.Contentful where
  | agent     -- combines with dynamic action complements
  | holder    -- combines with stative complements
  | engineer  -- ECM *have*: saturated eventive VoiceP complement
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of Voice: a θ-role or the zero alloseme — the expletive
identity for relational and light-verb *have*, where Voice assigns no
θ-role. The expletive is the same zero every
head has. -/
abbrev Voice.Alloseme := Allosemy.Alloseme Voice.Contentful

namespace Voice.Alloseme

@[match_pattern] def agent : Voice.Alloseme := Allosemy.Alloseme.of .agent
@[match_pattern] def holder : Voice.Alloseme := Allosemy.Alloseme.of .holder
@[match_pattern] def engineer : Voice.Alloseme := Allosemy.Alloseme.of .engineer

/-- Identity; no θ-role: the zero alloseme of Voice. -/
@[match_pattern] def expletive : Voice.Alloseme := Allosemy.Alloseme.zero

end Voice.Alloseme

/-- The alloseme assigns a thematic role to the external argument;
only the expletive identity does not. -/
def Voice.Alloseme.AssignsTheta (a : Voice.Alloseme) : Prop :=
  a ≠ .expletive

instance : DecidablePred Voice.Alloseme.AssignsTheta :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- The Voice allosemes as a competing exponence vocabulary: engineer for
    a saturated eventive VoiceP complement (most specified), holder for a
    stative one, expletive elsewhere (the all-wildcard default). -/
def Voice.vocabulary : List (VocabularyItem Feature Voice.Alloseme) :=
  [⟨complement [.cat .v, .eventive], .engineer⟩, ⟨complement [.stative], .holder⟩,
    [] ⟷ .expletive]

/-- Voice alloseme selection from the complement's features: Elsewhere
    competition over `Voice.vocabulary`, resolved by the shared exponence
    engine — the conditioning of the alloseme on the nature of *have*'s
    complement. -/
def Voice.Alloseme.fromComplement (fs : List Feature) : Voice.Alloseme :=
  (subsetPrinciple Voice.vocabulary (complement fs)).getD .expletive

/-- Eventive-VoiceP complement selects engineer. -/
example : Voice.Alloseme.fromComplement [.cat .v, .eventive] = .engineer := by decide

/-- Stative complement selects holder. -/
example : Voice.Alloseme.fromComplement [.stative] = .holder := by decide

/-- Neither condition met selects the elsewhere expletive. -/
example : Voice.Alloseme.fromComplement [] = .expletive := by decide

/-- Bridge to the syntactic `Flavor` inventory. Syntactically all four
    allosemes realize the same Voice with a DP specifier; the θ-role
    distinction is resolved at LF. The map picks the
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

/-- Reading types for deverbal nominalizations: the five terminal readings
    plus the complex content nominal. -/
inductive NominalizationReading where
  | complexEvent   -- CEN: full verbal event reading with argument structure
  | simpleEvent    -- SEN: event reading without argument structure
  | result         -- entity whose existence results from an event
  | simpleState    -- state reading
  | simpleEntity   -- entity reading, no event connection
  | content        -- CCN: propositional content, takes a CP complement
  deriving DecidableEq, Repr, Fintype

/-- The reading of a nominalization from the allosemes of v and n. The CEN
pairs eventive v with zero n, the noun inheriting the verb meaning; the
simple readings pair zero v with the event, state, and entity allosemes of
n. The result and content readings admit both derivations — v vacuous, or
the eventive component from v — and the choice is immaterial for what the
nominal describes (`Benz2025.result_options_pred_agree`,
`Benz2025.content_options_agree`); content needs no verbal source at all.
The non-deverbal allosemes yield no nominalization reading: their
semantics is the relationalizer and its possessor-closing `ExPossessor`. -/
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
`interp` map. -/
theorem Verbalizer.isAllosemous :
    (toInterpreted Verbalizer.vocabulary).IsAllosemous () :=
  ⟨complement [.eventive], ∅, .eventive, by decide, .zero, by decide, by decide⟩

end DistributedMorphology.Allosemy
