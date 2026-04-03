import Linglib.Theories.Semantics.Lexical.CovertQuantifier
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Theories.Semantics.Lexical.Verb.Habituals
import Linglib.Theories.Semantics.Tense.Aspect.Core
import Linglib.Core.Genericity

/-!
# @cite{boneh-doron-2013} — Hab and Gen in the Expression of Habituality

In *Genericity* (Mari, Beyssade, Del Prete eds.), OUP, Oxford Studies in
Theoretical Linguistics 43.

## Core Claim

HAB and GEN are **distinct** covert operators, not a single operator with
different parameters. They share the same quantificational skeleton
(`covertQ` in `CovertQuantifier.lean`) but differ in:

1. **Quantificational force**: HAB is a modalized *existential* quantifier
   over sums of events; GEN is a modalized *universal* quantifier.
2. **Restrictor requirement**: GEN requires an explicit restrictor (e.g.,
   "after dinner" in ex. (4a)); HAB does not — it uses INIT to anchor
   to an initiating event.
3. **Structural position**: HAB sits low as a VP adverb selected by AspP;
   GEN sits high in MoodP (parallel to *would*).

The chapter provides English evidence from three habitual verb forms:
the simple past tense form, the periphrastic *used to*, and *would*.

## English Habitual Forms (Table (41))

| Form        | Viewpoint aspect        | Perspective               |
|-------------|-------------------------|---------------------------|
| simple form | imperfective/perfective | internal/retrospective    |
| *used to*   | imperfective            | retrospective             |
| *would*     | imperfective            | internal                  |

## Connection to Existing Infrastructure

- `CovertQuantifier.lean`: shared skeleton `covertQ`; `gen_is_covertQ`
  and `hab_is_covertQ` show both operators instantiate it.
- `Aspect/Core.lean`: `ViewpointAspectB` — the `aspectCompatibility`
  bridge connects B&D's Table (41) to the aspectual infrastructure.
- `DelPrete2013.lean`: Del Prete's Same-Object Effect (SOE) is the Italian
  analogue of the same-object readings in B&D's exx. (4b), (6b), (7b).
  The `sameObjectParallel` theorem makes this connection explicit.
-/

namespace Phenomena.Generics.Studies.BonehDoron2013

open Semantics.Lexical.CovertQuantifier
open Semantics.Lexical.Noun.Kind.Generics (Situation traditionalGEN)
open Semantics.Lexical.Verb.Habituals (Occasion traditionalHAB)
open Semantics.Tense.Aspect.Core (ViewpointAspectB)

-- ═══ Operator Distinction ═══

/-- Quantificational force of a covert operator.

    @cite{boneh-doron-2013} §6.2.1: HAB is a "modalized existential
    quantifier over sums of events"; GEN is a "modalized universal
    quantifier" (Krifka et al. 1995). -/
inductive QForce where
  /-- Existential: HAB ∃-quantifies over event sums via ITER. -/
  | existential
  /-- Universal: GEN ∀-quantifies over individuals/events meeting
      the restrictor. -/
  | universal
  deriving DecidableEq, Repr

/-- Configuration for a covert quantifier, recording the structural
    differences between GEN and HAB beyond the shared `covertQ` skeleton. -/
structure CovertQConfig where
  /-- Quantificational force (existential vs universal) -/
  force : QForce
  /-- Whether the operator requires an explicit restrictor in the clause.
      GEN requires one (e.g., "after dinner"); HAB uses INIT instead. -/
  requiresExplicitRestrictor : Bool
  /-- Whether the operator is modalized (references a modal base MB).
      Both GEN and HAB reference MB in their denotations (eqs. (13), (21)). -/
  isModal : Bool
  deriving DecidableEq, Repr

/-- GEN configuration: universal, requires explicit restrictor, modal. -/
def genConfig : CovertQConfig :=
  { force := .universal
  , requiresExplicitRestrictor := true
  , isModal := true
  }

/-- HAB configuration: existential, no explicit restrictor needed, modal. -/
def habConfig : CovertQConfig :=
  { force := .existential
  , requiresExplicitRestrictor := false
  , isModal := true
  }

/-- GEN and HAB have distinct configurations despite sharing `covertQ`. -/
theorem gen_hab_distinct : genConfig ≠ habConfig := by decide

/-- GEN and HAB agree on modality (both are modalized) but differ on
    quantificational force and restrictor requirement. -/
theorem gen_hab_modal_agreement :
    genConfig.isModal = habConfig.isModal := rfl

theorem gen_hab_differ_on_force_and_restrictor :
    genConfig.force ≠ habConfig.force ∧
    genConfig.requiresExplicitRestrictor ≠ habConfig.requiresExplicitRestrictor := by
  exact ⟨by decide, by decide⟩

-- ═══ English Habitual Forms ═══

/-- The three English verb forms that express habituality.

    @cite{boneh-doron-2013} §6.1, ex. (1): "In the good old days, people
    dressed/used to dress/would dress elegantly to go to the opera." -/
inductive HabitualForm where
  /-- Simple past tense form: "people dressed elegantly." -/
  | simpleForm
  /-- Periphrastic *used to*: "people used to dress elegantly." -/
  | usedTo
  /-- Periphrastic *would*: "people would dress elegantly." -/
  | would
  deriving DecidableEq, Repr

/-- Whether a habitual form admits perfective aspect.

    @cite{boneh-doron-2013} Table (41): only the simple form admits
    perfective; the periphrastic forms are imperfective only. -/
def admitsPerfective : HabitualForm → Bool
  | .simpleForm => true
  | .usedTo => false
  | .would => false

/-- Whether a habitual form has a retrospective perspective.

    @cite{boneh-doron-2013} Table (41): the simple form can be either,
    *used to* is retrospective, *would* is internal (not retrospective). -/
def hasRetrospective : HabitualForm → Bool
  | .simpleForm => true   -- can be retrospective
  | .usedTo => true       -- always retrospective
  | .would => false       -- internal only

/-- Whether a habitual form requires actualization (habit must be
    instantiated by actual episodes in the world).

    @cite{boneh-doron-2013} §6.3.2, ex. (42): *used to* requires
    actualization; the simple form and *would* do not. -/
def requiresActualization : HabitualForm → Bool
  | .simpleForm => false
  | .usedTo => true
  | .would => false

-- ═══ Bridge to ViewpointAspectB ═══

/-- Which viewpoint aspects each habitual form is compatible with,
    connecting B&D's Table (41) to `ViewpointAspectB` in `Aspect/Core.lean`.

    The simple form admits both imperfective and perfective; the
    periphrastic forms are imperfective only. -/
def aspectCompatibility : HabitualForm → ViewpointAspectB → Bool
  | .simpleForm, _ => true                 -- both aspects
  | .usedTo, .imperfective => true
  | .usedTo, .perfective => false
  | .would, .imperfective => true
  | .would, .perfective => false

/-- Periphrastic forms reject perfective aspect. -/
theorem periphrastic_reject_perfective :
    aspectCompatibility .usedTo .perfective = false ∧
    aspectCompatibility .would .perfective = false := by
  exact ⟨rfl, rfl⟩

/-- The simple form accepts both viewpoint aspects. -/
theorem simple_both_aspects :
    aspectCompatibility .simpleForm .imperfective = true ∧
    aspectCompatibility .simpleForm .perfective = true := by
  exact ⟨rfl, rfl⟩

-- ═══ Data from the Chapter ═══

/-- An English habituality datum. -/
structure EnglishDatum where
  sentence : String
  form : HabitualForm
  felicitous : Bool
  /-- Which operator the chapter's analysis assigns to this reading.
      Under B&D's proposal, the simple form typically involves Hab,
      *would* involves Gen, and *used to* involves Hab + aspectual marking. -/
  operator : String
  exNumber : String
  deriving Repr

-- ── §6.2.1: Restrictor contrast (motivating HAB/GEN split) ──

/-- Ex. (4a): "Mary smokes a cigarette after dinner" — GEN with
    explicit restrictor "after dinner". Felicitous because the restrictor
    supplies Gen's required restriction over events. -/
def maryCigaretteAfterDinner : EnglishDatum :=
  { sentence := "Mary smokes a cigarette after dinner"
  , form := .simpleForm
  , felicitous := true
  , operator := "GEN"
  , exNumber := "(4a)"
  }

/-- Ex. (4b): "#Mary smokes a cigarette" — No explicit restrictor,
    so Gen cannot apply. Hab applies but the singular indefinite
    "a cigarette" scopes over events, forcing a same-object reading
    (smoke the same cigarette repeatedly), which is infelicitous. -/
def maryCigarette : EnglishDatum :=
  { sentence := "#Mary smokes a cigarette"
  , form := .simpleForm
  , felicitous := false
  , operator := "HAB"
  , exNumber := "(4b)"
  }

-- ── §6.2.1: Same-object examples ──

/-- Ex. (6b): "A flower grows out behind the old shed" — singular
    indefinite under Hab forces a same-object reading: the same flower
    grows out repeatedly. This is the same-object phenomenon that
    @cite{del-prete-2013} calls the Same-Object Effect (SOE). -/
def flowerGrows : EnglishDatum :=
  { sentence := "A flower grows out behind the old shed"
  , form := .simpleForm
  , felicitous := true  -- true but only on same-object reading
  , operator := "HAB"
  , exNumber := "(6b)"
  }

/-- Ex. (7b): "#Max killed a rabbit repeatedly" — singular indefinite
    under adverbial *repeatedly* forces same-object (same rabbit killed
    over and over), which is pragmatically absurd. -/
def maxKilledRabbit : EnglishDatum :=
  { sentence := "#Max killed a rabbit repeatedly"
  , form := .simpleForm
  , felicitous := false
  , operator := "HAB"
  , exNumber := "(7b)"
  }

-- ── §6.1: *Would* context requirement ──

/-- Ex. (2c): "#In the good old days, people would dress elegantly" —
    *would* (Gen) is infelicitous even with a discourse context ("At the
    opera"). Gen requires an explicit *in-sentence* restrictor (e.g., a
    purpose clause "to go to the opera"), not just a contextual
    presupposition. -/
def wouldDressNoContext : EnglishDatum :=
  { sentence := "#In the good old days, people would dress elegantly"
  , form := .would
  , felicitous := false
  , operator := "GEN"
  , exNumber := "(2c)"
  }

/-- Ex. (2d): "In the good old days, people would dress elegantly to go
    to the opera" — felicitous because "to go to the opera" provides the
    restrictor for Gen. -/
def wouldDressWithContext : EnglishDatum :=
  { sentence := "In the good old days, people would dress elegantly to go to the opera"
  , form := .would
  , felicitous := true
  , operator := "GEN"
  , exNumber := "(2d)"
  }

-- ── §6.3.2: Actualization contrast ──

/-- Ex. (42a): "She went to work by bus" — simple form, TRUE even
    with a single episode. Can be read episodically or as a one-episode
    habit. -/
def sheWentByBus : EnglishDatum :=
  { sentence := "She went to work by bus"
  , form := .simpleForm
  , felicitous := true
  , operator := "episodic/HAB"
  , exNumber := "(42a)"
  }

/-- Ex. (42b): "She would go to work by bus" — *would* (GEN), TRUE
    even with a single episode. Gen is about what happens in normal
    worlds, not about actual iteration. -/
def sheWouldGoByBus : EnglishDatum :=
  { sentence := "She would go to work by bus"
  , form := .would
  , felicitous := true
  , operator := "GEN"
  , exNumber := "(42b)"
  }

/-- Ex. (42c): "She used to go to work by bus" — *used to*, FALSE
    in single-episode context. *Used to* requires actualization: the
    habit must be instantiated by multiple actual episodes. -/
def sheUsedToGoByBus : EnglishDatum :=
  { sentence := "She used to go to work by bus"
  , form := .usedTo
  , felicitous := false
  , operator := "HAB"
  , exNumber := "(42c)"
  }

-- ── §6.3.3/§6.4: Individual-level predicate contrast ──

/-- Ex. (48a): "The London Bridge used to stand on the Thames" —
    *used to* (Hab) is compatible with individual-level predicates because
    Hab is an aspectual operator that selects for states. -/
def usedToStand : EnglishDatum :=
  { sentence := "The London Bridge used to stand on the Thames, now it stands in Arizona"
  , form := .usedTo
  , felicitous := true
  , operator := "HAB"
  , exNumber := "(48a)"
  }

/-- Ex. (48b): "*The London Bridge would stand on the Thames" —
    *would* (Gen) is incompatible with individual-level predicates when the
    subject is definite. Gen requires a restrictor, but a definite subject
    cannot serve as one, and "stand on the Thames" (individual-level) is
    incompatible with an episodic restrictor. Contrast with (47a), where
    the indefinite singular "a French teacher" provides Gen's restrictor. -/
def wouldStand : EnglishDatum :=
  { sentence := "*The London Bridge would stand on the Thames, now it stands in Arizona"
  , form := .would
  , felicitous := false
  , operator := "GEN"
  , exNumber := "(48b)"
  }

-- ── §6.4: *Would* vs *used to* puzzle ──

/-- Ex. (3a)/(47a): "a French teacher would know Latin" — *would* (GEN)
    accepts an indefinite singular subject because Gen takes a nominal
    restrictor (the indefinite provides it). First introduced as (3a),
    discussed fully in §6.4 as (47a). -/
def wouldKnowLatin : EnglishDatum :=
  { sentence := "a French teacher would know Latin"
  , form := .would
  , felicitous := true
  , operator := "GEN"
  , exNumber := "(3a)/(47a)"
  }

/-- Ex. (3b)/(47b): "*a French teacher used to know Latin" — *used to*
    rejects an indefinite singular subject. *Used to* involves Hab, which
    quantifies over *events* (not individuals). The indefinite singular
    "a French teacher" cannot serve as a restrictor for Hab's event
    quantification, unlike Gen which quantifies over individuals and can
    bind the indefinite as a nominal restrictor. -/
def usedToKnowLatin : EnglishDatum :=
  { sentence := "*a French teacher used to know Latin"
  , form := .usedTo
  , felicitous := false
  , operator := "HAB"
  , exNumber := "(3b)/(47b)"
  }

def englishData : List EnglishDatum :=
  [ maryCigaretteAfterDinner, maryCigarette
  , flowerGrows, maxKilledRabbit
  , wouldDressNoContext, wouldDressWithContext
  , sheWentByBus, sheWouldGoByBus, sheUsedToGoByBus
  , usedToStand, wouldStand
  , wouldKnowLatin, usedToKnowLatin ]

-- ═══ Key Predictions ═══

/-- The restrictor contrast (4): "Mary smokes a cigarette after dinner" (✓)
    vs "#Mary smokes a cigarette" (✗). Gen requires an explicit restrictor;
    without one, Hab applies but the singular indefinite forces same-object. -/
theorem restrictor_contrast :
    maryCigaretteAfterDinner.felicitous = true ∧
    maryCigarette.felicitous = false := by
  exact ⟨rfl, rfl⟩

/-- The *would* restrictor contrast (2c-d): *would* (Gen) is infelicitous
    without an explicit in-sentence restrictor (2c), but felicitous with
    a purpose clause (2d). Same underlying mechanism as the (4a-b) contrast. -/
theorem would_restrictor_contrast :
    wouldDressNoContext.felicitous = false ∧
    wouldDressWithContext.felicitous = true := by
  exact ⟨rfl, rfl⟩

/-- The restrictor requirement is consistent across forms: both the simple
    form (4a-b) and *would* (2c-d) show Gen needs an explicit restrictor. -/
theorem gen_restrictor_across_forms :
    maryCigaretteAfterDinner.felicitous = true ∧
    maryCigarette.felicitous = false ∧
    wouldDressWithContext.felicitous = true ∧
    wouldDressNoContext.felicitous = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The same-object effect (6b, 7b): singular indefinites under Hab force
    a same-object reading. When pragmatically implausible (7b), the sentence
    is infelicitous.

    This is the English counterpart of @cite{del-prete-2013}'s SOE in Italian.
    Del Prete's "Gianni leggeva un libro di filosofia" (HAB blocked, SOE
    implausible) parallels B&D's "#Max killed a rabbit repeatedly." -/
theorem sameObjectParallel :
    flowerGrows.felicitous = true ∧      -- same-object plausible
    maxKilledRabbit.felicitous = false := by  -- same-object implausible
  exact ⟨rfl, rfl⟩

/-- The actualization contrast (42): simple form and *would* are true
    even with a single episode; *used to* requires actualized iteration. -/
theorem actualization_contrast :
    sheWentByBus.felicitous = true ∧
    sheWouldGoByBus.felicitous = true ∧
    sheUsedToGoByBus.felicitous = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Actualization requirement matches function: *used to* requires
    actualization; simple form and *would* do not. -/
theorem actualization_matches_form :
    requiresActualization .usedTo = true ∧
    requiresActualization .simpleForm = false ∧
    requiresActualization .would = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Individual-level predicate contrast (48): *used to* accepts individual-
    level predicates (it selects states); *would* rejects them when the
    subject is definite (Gen needs a restrictor the definite can't provide). -/
theorem individual_level_contrast :
    usedToStand.felicitous = true ∧
    wouldStand.felicitous = false := by
  exact ⟨rfl, rfl⟩

/-- The *would* vs *used to* puzzle (3)/(47): *would* accepts an indefinite
    singular subject; *used to* does not. This follows from *would* involving
    Gen (which can bind the indefinite as a nominal restrictor) while *used to*
    involves Hab (which quantifies over events, not individuals). -/
theorem would_vs_usedTo_puzzle :
    wouldKnowLatin.felicitous = true ∧
    usedToKnowLatin.felicitous = false := by
  exact ⟨rfl, rfl⟩

/-- (47) and (48) together show that *would*'s acceptability depends on
    whether Gen's restrictor can be filled: indefinite singular fills it
    (47a ✓), definite subject with individual-level predicate does not (48b ✗).
    Meanwhile *used to* is the mirror: rejects indefinite singular (47b ✗)
    but accepts individual-level predicates freely (48a ✓). -/
theorem would_usedTo_complementarity :
    wouldKnowLatin.felicitous = true ∧     -- would + indef. sing. ✓
    wouldStand.felicitous = false ∧         -- would + def. + indiv-level ✗
    usedToKnowLatin.felicitous = false ∧   -- used to + indef. sing. ✗
    usedToStand.felicitous = true := by     -- used to + indiv-level ✓
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Only the simple form admits perfective aspect; periphrastic forms
    are imperfective only (Table (41)). -/
theorem perfective_only_simple :
    admitsPerfective .simpleForm = true ∧
    admitsPerfective .usedTo = false ∧
    admitsPerfective .would = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- *Would* lacks retrospective perspective; the other forms have it
    (Table (41)). -/
theorem would_no_retrospective :
    hasRetrospective .would = false ∧
    hasRetrospective .simpleForm = true ∧
    hasRetrospective .usedTo = true := by
  exact ⟨rfl, rfl, rfl⟩

-- ═══ Shared Skeleton ═══

/-- Despite the structural differences, both operators instantiate `covertQ`.
    This is not in tension with distinctness — `covertQ` is the *skeleton*,
    and the two operators differ in what fills its parameters.

    GEN: `covertQ individuals (normal ∧ kind) property`
    HAB: `covertQ occasions characteristic activity`

    The skeleton is shared; the interpretation is different. -/
theorem shared_skeleton :
    (∀ (sits : List Situation) normal restrictor scope,
      traditionalGEN sits normal restrictor scope =
      covertQ sits (λ s => normal s && restrictor s) scope) ∧
    (∀ (occs : List Occasion) characteristic activity,
      traditionalHAB occs characteristic activity =
      covertQ occs characteristic activity) :=
  ⟨λ _ _ _ _ => rfl, λ _ _ _ => rfl⟩

end Phenomena.Generics.Studies.BonehDoron2013
