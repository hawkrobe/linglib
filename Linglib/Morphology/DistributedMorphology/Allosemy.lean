import Linglib.Morphology.DistributedMorphology.Basic
import Linglib.Morphology.DistributedMorphology.Categorizer.Gender
import Linglib.Morphology.DistributedMorphology.Categorizer.Semantics
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
inventories here compose: the typed denotations of `VAlloseme.denote`
and `NAlloseme.denote` derive the reading typology, and the analytical
choice of where the eventive component lives — v or n — is provably
immaterial for the result and content readings.

## Main definitions

* `VAlloseme`, `NAlloseme`, `VoiceAlloseme` — the alloseme inventories
  of v, n, and Voice
* `vAllosemic`, `nAllosemic` — v and n as `AllosemicHead`s over the
  shared selection engine
* `NominalizationReading`, `readingFromAllosemes` — the reading typology
  of deverbal nominalizations and its alloseme table
* `NominalizationModel`, `VAlloseme.denote`, `NAlloseme.denote` — typed
  alloseme denotations and their composition

## Main statements

* `result_options_agree`, `content_options_agree` — the two analytical
  options for the result and content readings compose to the same
  denotation: the event and result readings are mirror images
* `readingFromAllosemes_isSome_iff_denote` — the reading table has a
  reading exactly where the composed denotation is defined
* `cen_result_ambiguity` — one deverbal context licenses several n
  allosemes: nominalization ambiguity as non-singleton licensing
* `vAllosemic_isAllosemous` — v's contextual meaning variation on the
  shared `Realization.Interpreted` carrier

## Implementation notes

`AllosemicEntry` is a `Morphology.Exponence.Rule` instance, just as
`VI.VocabItem` is, so DM's List 2 (form) and List 3 (meaning) run on one
selection engine: `Exponence.selectBy` on the non-wildcard-field score
(`selectBy_score_isElsewhereWinner`). `VoiceAlloseme.fromComplement` is
a worked List-3 competition on that engine; `readingFromAllosemes` is a
different object — the composition of two already-selected allosemes.
Existing infrastructure this module retroactively classifies as
allosemy: `CategorizerSemantics.NSemanticType` (n), `Minimalist.Voice.Flavor`
(Voice), and root change-type conditioning of v.

## References

* [I. Benz, *Structure and interpretation across categories*][benz-2025]
* [J. Wood, *Icelandic nominalizations and allosemy*][wood-2023]
* [A. Kratzer, *Severing the external argument from its verb*][kratzer-1996]
* [N. Myler, *Building and interpreting possession sentences*][myler-2016]
-/

namespace DistributedMorphology.Allosemy

open DistributedMorphology (Categorizer Categorizer.Head)
open DistributedMorphology.CategorizerSemantics (NSemanticType)
open Minimalist.Voice (Flavor Head)

/-! ### v allosemy -/

/-- Allosemes of the verbal categorizer v ([benz-2025] §2.2;
    [wood-2023]): v either contributes eventive semantics or is
    semantically null, and in nominalization contexts both are available
    for the same root — the CEN vs SEN/RN ambiguity arises from v's
    alloseme, not from the root. -/
inductive VAlloseme where
  | eventive   -- introduces an event variable (CEN contexts)
  | zero       -- semantically Ø / identity (SEN/RN contexts)
  deriving DecidableEq, Repr

/-- Does this v alloseme introduce an event variable? -/
def VAlloseme.introducesEvent : VAlloseme → Bool
  | .eventive => true
  | .zero     => false

/-- v allosemy as an `AllosemicHead`: eventive under an eventive
complement, zero elsewhere. -/
def vAllosemic : AllosemicHead VAlloseme where
  morpheme := .v
  entries := [
    { label := "v_eventive"
    , denotation := .eventive
    , context := { complementIsEventive := true } },
    { label := "v_zero"
    , denotation := .zero
    , context := { complementIsEventive := false } }
  ]

/-- Root change-type conditions v alloseme selection: result roots,
    which entail a prior change, demand the event variable; property
    concept roots do not ([beavers-etal-2021]'s root typology feeding v
    allosemy). -/
def VAlloseme.fromRootType : Verb.Root.ChangeType → VAlloseme
  | .result          => .eventive
  | .propertyConcept => .zero

/-- The bridge preserves the change entailment: eventive v iff the root
entails change. -/
theorem fromRootType_iff_entailsChange (rt : Verb.Root.ChangeType) :
    (VAlloseme.fromRootType rt).introducesEvent = rt.entailsChange := by
  cases rt <;> rfl

/-! ### n allosemy -/

/-- Allosemes of the nominal categorizer n: the three non-deverbal types
    of `CategorizerSemantics.NSemanticType`, [benz-2025]'s content
    alloseme for content nominalizations, and [wood-2023]'s deverbal
    inventory. The deverbal denotations live in `NAlloseme.denote`. -/
inductive NAlloseme where
  | relational    -- introduces a relation (body-part-of)
  | sortal        -- bare categorization
  | alienator     -- existentially closes a possessor
  | content       -- propositional content (CCN reading)
  | zero          -- Ø / identity: noun inherits the verb meaning (CEN)
  | simpleEvent   -- picks out entities equal to an event (SEN)
  | result        -- picks out the entity an event produced
  | state         -- picks out states
  | entity        -- picks out entities, no event connection
  deriving DecidableEq, Repr

/-- The non-deverbal allosemes are `NSemanticType` under another name. -/
def NAlloseme.ofNSemanticType : NSemanticType → NAlloseme
  | .relational => .relational
  | .sortal     => .sortal
  | .alienator  => .alienator

/-- n allosemy as an `AllosemicHead`: the non-deverbal allosemes are
unconditioned (all-wildcard contexts), the deverbal ones require a
verbal complement, with the CEN and result allosemes further demanding
an eventive one. -/
def nAllosemic : AllosemicHead NAlloseme where
  morpheme := .n
  entries := [
    { label := "n_relational"
    , denotation := .relational
    , context := { belowCat := none } },
    { label := "n_sortal"
    , denotation := .sortal
    , context := { belowCat := none } },
    { label := "n_alienator"
    , denotation := .alienator
    , context := { belowCat := none } },
    { label := "n_content"
    , denotation := .content
    , context := { belowCat := some .v } },
    { label := "n_zero"
    , denotation := .zero
    , context := { belowCat := some .v, complementIsEventive := true } },
    { label := "n_simpleEvent"
    , denotation := .simpleEvent
    , context := { belowCat := some .v } },
    { label := "n_result"
    , denotation := .result
    , context := { belowCat := some .v, complementIsEventive := true } },
    { label := "n_state"
    , denotation := .state
    , context := { belowCat := some .v } },
    { label := "n_entity"
    , denotation := .entity
    , context := { belowCat := some .v } }
  ]

/-- One eventive deverbal context licenses several n allosemes at once —
the CEN reading (zero n) and the result reading among them. The
ambiguity of a nominalization is non-singleton licensing, not structural
ambiguity ([benz-2025], [wood-2023]). -/
theorem cen_result_ambiguity :
    NAlloseme.zero ∈ nAllosemic.licensed
        { belowCat := some .v, complementIsEventive := true }
      ∧ NAlloseme.result ∈ nAllosemic.licensed
        { belowCat := some .v, complementIsEventive := true } := by
  constructor <;> decide

/-! ### Voice allosemy -/

/-- Allosemes of Voice: the thematic interpretation of the external
    argument depends on the semantics of the complement.
    [kratzer-1996]'s severing argument observes that the holder function
    cannot combine with an action predicate, nor the agent function with
    a stative one — so the thematic role is fixed by the complement, not
    by the head. [myler-2016] extends the inventory to four, adding the
    engineer role for ECM *have* and an expletive identity alloseme for
    relational and light-verb *have*, where Voice assigns no θ-role. -/
inductive VoiceAlloseme where
  | agent     -- combines with dynamic action complements
  | holder    -- combines with stative complements
  | engineer  -- ECM *have*: saturated eventive VoiceP complement
  | expletive -- identity; no θ-role (relational and light-verb *have*)
  deriving DecidableEq, Repr

/-- The alloseme assigns a thematic role to the external argument;
only the expletive identity does not. -/
def VoiceAlloseme.AssignsTheta (a : VoiceAlloseme) : Prop :=
  a ≠ .expletive

instance : DecidablePred VoiceAlloseme.AssignsTheta :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- The Voice allosemes as a competing exponence vocabulary
    ([myler-2016]): engineer for a saturated eventive VoiceP complement
    (most specified), holder for a stative one, expletive elsewhere (the
    all-wildcard default). -/
def voiceVocabulary : List (AllosemicEntry VoiceAlloseme) :=
  [ { label := "Voice_engineer", denotation := .engineer
    , context := { belowCat := some .v, complementIsEventive := true } },
    { label := "Voice_holder", denotation := .holder
    , context := { complementIsStative := true } },
    { label := "Voice_expletive", denotation := .expletive
    , context := {} } ]

/-- Voice alloseme selection from complement properties: Elsewhere
    competition over `voiceVocabulary`, resolved by the shared exponence
    engine ([myler-2016]'s conditioning of the alloseme on the nature of
    *have*'s complement). -/
def VoiceAlloseme.fromComplement
    (complementIsEventiveVoiceP : Prop) [Decidable complementIsEventiveVoiceP]
    (complementIsStative : Prop) [Decidable complementIsStative] : VoiceAlloseme :=
  let q : SyntacticContext :=
    { belowCat := if complementIsEventiveVoiceP then some .v else none
      complementIsEventive := decide complementIsEventiveVoiceP
      complementIsStative := decide complementIsStative }
  ((Morphology.Exponence.selectBy AllosemicEntry.score voiceVocabulary q).map
    AllosemicEntry.denotation).getD .expletive

/-- Eventive-VoiceP complement selects engineer ([myler-2016]). -/
example : VoiceAlloseme.fromComplement True False = .engineer := by decide

/-- Stative complement selects holder ([kratzer-1996]). -/
example : VoiceAlloseme.fromComplement False True = .holder := by decide

/-- Neither condition met selects the elsewhere expletive. -/
example : VoiceAlloseme.fromComplement False False = .expletive := by decide

/-- Bridge to the syntactic `Flavor` inventory. Syntactically all four
    allosemes realize the same Voice with a DP specifier; the θ-role
    distinction is resolved at LF ([myler-2016]). The map picks the
    flavor matching each alloseme's syntactic behavior. -/
def VoiceAlloseme.toFlavor : VoiceAlloseme → Flavor
  | .agent    => .agentive
  | .holder   => .experiencer
  | .engineer => .agentive
  | .expletive => .expletive

/-- The bridge respects θ-assignment: an alloseme assigns a thematic
role iff its syntactic flavor does. -/
theorem voice_alloseme_theta_consistent (a : VoiceAlloseme) :
    a.AssignsTheta ↔ Head.AssignsTheta { flavor := a.toFlavor, hasD := true } := by
  cases a <;> simp [VoiceAlloseme.AssignsTheta, VoiceAlloseme.toFlavor] <;> decide

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
  deriving DecidableEq, Repr

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
    nominalization reading — their semantics lives in
    `Categorizer/Semantics.lean`. -/
def readingFromAllosemes : VAlloseme → NAlloseme → Option NominalizationReading
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
entities and of eventualities. -/
structure RootMeaning (E S : Type*) where
  onEntities : E → Prop
  onEvents : S → Prop

/-- What v hands to n: verbal event content under the eventive alloseme,
the untouched root under the zero alloseme. -/
inductive VDenotation (E S : Type*) where
  | eventive (p : S → Prop)
  | zero (ρ : RootMeaning E S)

/-- The v alloseme applied to the root. -/
def VAlloseme.denote (ρ : RootMeaning E S) : VAlloseme → VDenotation E S
  | .eventive => .eventive ρ.onEvents
  | .zero     => .zero ρ

/-- The n alloseme applied to v's output: the nominal's entity
predicate, `none` where the combination is uninterpretable. The CEN
describes the events the verb describes; the SEN predicates the root's
entity content of an event-entity; the result alloseme picks out what an
event of the root's kind produced ([benz-2025]'s denotation, taken over
from [wood-2023]); the content alloseme ignores the verbal layer
entirely. The non-deverbal allosemes have their semantics in
`Categorizer/Semantics.lean`. -/
def NAlloseme.denote (m : NominalizationModel E S) :
    VDenotation E S → NAlloseme → Option (E → Prop)
  | .eventive p, .zero        => some fun x => ∃ e, x = m.ev e ∧ p e
  | .eventive p, .result      => some fun x => ∃ e, p e ∧ m.result x e
  | .eventive _, .content     => some m.hasContent
  | .zero ρ,     .simpleEvent => some fun x => ρ.onEntities x ∧ ∃ e, x = m.ev e
  | .zero ρ,     .state       => some fun x => ∃ e, x = m.ev e ∧ m.stative e ∧ ρ.onEvents e
  | .zero ρ,     .result      => some fun x => ∃ e, ρ.onEvents e ∧ m.result x e
  | .zero ρ,     .entity      => some ρ.onEntities
  | .zero _,     .content     => some m.hasContent
  | _,           _            => none

/-- The event and result readings are mirror images: the two analytical
options for the result reading — eventive v with n's result alloseme, or
vacuous v with the same — compose to the same denotation, so the choice
of where the eventive component lives is immaterial ([benz-2025] §3.5,
crediting [wood-2023]). -/
theorem result_options_agree (m : NominalizationModel E S) (ρ : RootMeaning E S) :
    NAlloseme.denote m (VAlloseme.eventive.denote ρ) .result
      = NAlloseme.denote m (VAlloseme.zero.denote ρ) .result := rfl

/-- The content reading likewise ignores the verbal layer: both v
options compose to `hasContent`, which is how simple content nouns can
have the reading with no verbal source at all ([benz-2025] §3.5). -/
theorem content_options_agree (m : NominalizationModel E S) (ρ : RootMeaning E S) :
    NAlloseme.denote m (VAlloseme.eventive.denote ρ) .content
      = NAlloseme.denote m (VAlloseme.zero.denote ρ) .content := rfl

/-- The reading typology tracks denotational definedness: a (v, n) pair
has a reading exactly when its composed denotation is defined. -/
theorem readingFromAllosemes_isSome_iff_denote (m : NominalizationModel E S)
    (ρ : RootMeaning E S) (v : VAlloseme) (n : NAlloseme) :
    (readingFromAllosemes v n).isSome
      ↔ (NAlloseme.denote m (v.denote ρ) n).isSome := by
  cases v <;> cases n <;>
    simp [readingFromAllosemes, VAlloseme.denote, NAlloseme.denote]

/-- A complex event nominal holds only of event-entities: the ground of
its event reading (temporal modification, aspectual behavior). -/
theorem cen_denotes_events (m : NominalizationModel E S) (ρ : RootMeaning E S)
    {p : E → Prop}
    (h : NAlloseme.denote m (VAlloseme.eventive.denote ρ) .zero = some p) :
    ∀ x, p x → ∃ e, x = m.ev e := by
  simp only [VAlloseme.denote, NAlloseme.denote, Option.some.injEq] at h
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

open Morphology.Exponence in
/-- The allosemy engine as a `Realization.Interpreted` view: one
abstract head whose contextual interpretation is the alloseme `selectBy`
picks (a singleton, `∅` at a semantic gap), with an empty List-2 form
side. -/
def AllosemicHead.toInterpreted {Sem : Type} (h : AllosemicHead Sem) :
    Morphology.Realization.Interpreted Unit SyntacticContext Unit Sem where
  realize _ _ := ∅
  interp _ c :=
    match selectBy AllosemicEntry.score h.entries c with
    | some e => {e.denotation}
    | none => ∅

/-- The verbal categorizer's meaning varies with context — eventive
under an eventive complement, zero elsewhere — so v is `IsAllosemous` on
the shared carrier: contextual meaning variation as non-constancy of the
`interp` map ([benz-2025]). -/
theorem vAllosemic_isAllosemous : vAllosemic.toInterpreted.IsAllosemous () :=
  ⟨{ complementIsEventive := true }, { complementIsEventive := false },
   .eventive, by decide, .zero, by decide, by decide⟩

end DistributedMorphology.Allosemy
