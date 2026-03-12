import Linglib.Theories.Semantics.Lexical.CovertQuantifier
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Theories.Semantics.Lexical.Verb.Habituals
import Linglib.Core.Genericity

/-!
# @cite{boneh-doron-2013} — Hab and Gen in the Expression of Habituality

In *Genericity* (Mari, Beyssade, Del Prete eds.), OUP, Oxford Studies in
Theoretical Linguistics 43.

## Core Claim

HAB and GEN are **distinct** covert operators, not a single operator with
different parameters. They share the same quantificational skeleton
(`covertQ` in `CovertQuantifier.lean`) but differ in:

1. **Domain of quantification**: GEN quantifies over *individuals* of a kind;
   HAB quantifies over *situations* characteristic of an agent.
2. **Modal profile**: HAB is a modal operator with a *realistic alternatives*
   modal base; GEN is non-modal (normalcy-based restriction).
3. **Morphological realization**: Hebrew distinguishes beinoni (GEN/present)
   from past habitual (HAB) with distinct morphology. This is not
   allomorphic variation — the two forms have different distributions.

## Connection to Existing Infrastructure

`CovertQuantifier.lean` provides the shared skeleton `covertQ`, and the
existing `gen_is_covertQ` / `hab_is_covertQ` theorems show both instantiate
it. This file formalizes the structural *differences* between the two
instantiations, proving they are genuinely distinct operators despite
sharing the same logical form.

## Hebrew Evidence

| Form | Morphology | Operator | Domain |
|------|-----------|----------|--------|
| beinoni (present) | CoCeC/meCaCeC | GEN | individuals of kind |
| haya + beinoni (past hab.) | haya + CoCeC | HAB | situations of agent |

"Dan yodea italkit" (Dan knows-BEINONI Italian) — GEN over individuals
"Dan haya yodea italkit" (Dan HAB-was knowing Italian) — HAB over situations
-/

namespace Phenomena.Generics.Studies.BonehDoron2013

open Semantics.Lexical.CovertQuantifier
open Semantics.Lexical.Noun.Kind.Generics (Situation traditionalGEN)
open Semantics.Lexical.Verb.Habituals (Occasion traditionalHAB)

-- ═══ Domain Distinction ═══

/-- The domain over which a covert quantifier ranges.

    @cite{boneh-doron-2013} argue GEN and HAB quantify over fundamentally
    different domains: GEN over individuals that instantiate a kind,
    HAB over situations characteristic of an agent's behavior. -/
inductive QuantifierDomain where
  /-- GEN: quantifies over individuals of a kind.
      "Dogs bark" → for normal individuals x of the kind DOG, x barks. -/
  | individualBased
  /-- HAB: quantifies over situations characteristic of an agent.
      "Dan smokes" → in characteristic situations s of Dan, Dan smokes in s. -/
  | situationBased
  deriving DecidableEq, Repr, BEq

/-- Configuration for a covert quantifier, recording the structural
    differences between GEN and HAB beyond the shared `covertQ` skeleton. -/
structure CovertQConfig where
  /-- What the quantifier ranges over -/
  domain : QuantifierDomain
  /-- Whether the quantifier has a modal base (realistic alternatives) -/
  isModal : Bool
  /-- Whether the quantifier requires an agentive subject -/
  requiresAgent : Bool
  deriving DecidableEq, Repr, BEq

/-- GEN configuration: individual-based, non-modal, no agent requirement. -/
def genConfig : CovertQConfig :=
  { domain := .individualBased
  , isModal := false
  , requiresAgent := false
  }

/-- HAB configuration: situation-based, modal (realistic alternatives),
    requires agentive subject. -/
def habConfig : CovertQConfig :=
  { domain := .situationBased
  , isModal := true
  , requiresAgent := true
  }

/-- GEN and HAB have distinct configurations despite sharing `covertQ`. -/
theorem gen_hab_distinct : genConfig ≠ habConfig := by decide

/-- GEN and HAB differ on every structural parameter. -/
theorem gen_hab_differ_on_all :
    genConfig.domain ≠ habConfig.domain ∧
    genConfig.isModal ≠ habConfig.isModal ∧
    genConfig.requiresAgent ≠ habConfig.requiresAgent := by
  exact ⟨by decide, by decide, by decide⟩

-- ═══ Hebrew Morphological Evidence ═══

/-- Hebrew verb form relevant to genericity/habituality. -/
inductive HebrewForm where
  /-- Beinoni (present/participial): expresses GEN.
      CoCeC pattern for pa'al, meCaCeC for pi'el, etc. -/
  | beinoni
  /-- Past habitual: haya + beinoni. Expresses HAB. -/
  | hayaBeinoni
  /-- Simple past (avar): episodic, neither GEN nor HAB. -/
  | past
  deriving DecidableEq, Repr, BEq

/-- The operator expressed by each Hebrew form. -/
def formOperator : HebrewForm → Option QuantifierDomain
  | .beinoni => some .individualBased      -- GEN
  | .hayaBeinoni => some .situationBased   -- HAB
  | .past => none                          -- episodic

/-- A Hebrew genericity datum. -/
structure HebrewDatum where
  hebrew : String
  gloss : String
  form : HebrewForm
  reading : String
  source : String

/-- "Dan yodea italkit" — beinoni → GEN (individual-based). -/
def danYodea : HebrewDatum :=
  { hebrew := "Dan yodea italkit"
  , gloss := "Dan knows-BEINONI Italian"
  , form := .beinoni
  , reading := "Dan knows Italian (generic capacity)"
  , source := "Boneh & Doron 2013"
  }

/-- "Dan haya yodea italkit" — haya + beinoni → HAB (situation-based). -/
def danHayaYodea : HebrewDatum :=
  { hebrew := "Dan haya yodea italkit"
  , gloss := "Dan was-HAB knowing Italian"
  , form := .hayaBeinoni
  , reading := "Dan used to know Italian (habitual past)"
  , source := "Boneh & Doron 2013"
  }

/-- "Dan yada italkit" — simple past → episodic. -/
def danYada : HebrewDatum :=
  { hebrew := "Dan yada italkit"
  , gloss := "Dan knew-PAST Italian"
  , form := .past
  , reading := "Dan knew Italian (at a specific time)"
  , source := "Boneh & Doron 2013"
  }

/-- Beinoni and haya+beinoni map to different operators. -/
theorem hebrew_forms_distinguished :
    formOperator danYodea.form ≠ formOperator danHayaYodea.form := by
  decide

/-- Simple past gets no covert quantifier (episodic). -/
theorem past_is_episodic :
    formOperator danYada.form = none := rfl

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
