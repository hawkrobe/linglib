import Linglib.Syntax.Negation
import Linglib.Semantics.Negation.Expletive

/-!
# Januubi Arabic: Negation and Expletive Negation Markers
[jin-koenig-2021]

Januubi is a dialect of Gulf Arabic spoken in the province of Asir in
southwestern Saudi Arabia. It had not been documented for expletive
negation (EN) prior to [jin-koenig-2021].

## Standard Negation

Januubi uses **maa** as its standard negation marker.

## Expletive Negation

EN negators vary by trigger class:

| Trigger class | EN negator  | Gloss            | Form class     |
|---------------|-------------|------------------|----------------|
| FEAR          | maa         | standard NEG     | perfective NEG |
| REGRET        | —           | (no EN for this) |                |
| DENY          | maa         | standard NEG     | perfective NEG |
| FORGET        | maa         | standard NEG     | perfective NEG |
| BEFORE        | maa         | standard NEG     | perfective NEG |
| CANNOT WAIT   | maa         | standard NEG     | perfective NEG |
| IMPOSSIBLE    | maa         | standard NEG     | perfective NEG |

Unlike French and Mandarin, Januubi does not show negator-trigger
covariation: all EN triggers use the same standard negation marker
**maa**. The paper's Januubi consultant reported that REGRET does not
trigger EN due to a dispreference for modal operators in complement
clauses.

## Notable Absences

- COMPARATIVES (MORE THAN, TOO…TO): Januubi only allows NPs as
  complements of comparatives, blocking clausal EN.
- REGRET: disallowed because Januubi disprefers modals in complement
  clauses, and REGRET's EN requires a deontic modal.
-/

namespace Januubi.Negation

open Syntax.Negation

/-! ### Standard negation -/

/-- *maa* — Januubi Arabic's standard sentential negation particle.
    Same form used as the EN marker across all attested EN-trigger
    classes (see § 2 below); Januubi shows no negator-trigger covariation
    unlike French and Mandarin. -/
def maa : NegMarkerEntry :=
  { form := "maa"
  , morphemeType := .particle
  , position := .preverbal }

/-- The standard sentential negation marker in Januubi Arabic. -/
def standardNeg : String := maa.form

/-- The Januubi negation system: a single particle.
    No WALS datapoint for Januubi-specific dialect; the lookup returns
    `none` and the WALS fields stay unset. The Fragment-side joint
    consumed by `Studies/Dryer2013Negation.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "" [maa]

/-! ### Expletive negation markers -/

/-- An expletive negation marker used in a specific trigger context. -/
structure ENNegator where
  /-- The negator form -/
  form : String
  /-- Romanized gloss -/
  gloss : String
  /-- Whether this is the same as the standard negation marker -/
  isStandardNeg : Bool
  deriving Repr, DecidableEq

/-- Januubi uses the standard negator **maa** for all EN contexts. -/
def enNegator : ENNegator where
  form := "maa"
  gloss := "standard NEG (perfective)"
  isStandardNeg := true

/-- Unlike French and Mandarin, Januubi uses the same negator for
    standard and expletive negation. -/
theorem en_negator_is_standard : enNegator.isStandardNeg = true := rfl

/-! ### Trigger-specific examples -/

/-- A glossed EN example from Januubi. -/
structure ENExample where
  triggerClass : String
  triggerForm : String
  triggerGloss : String
  sentence : String
  gloss : String
  translation : String
  enNegator : String
  deriving Repr

/-- BEFORE trigger: *gabl* 'before' ([jin-koenig-2021], ex. 24). -/
def beforeExample : ENExample where
  triggerClass := "BEFORE"
  triggerForm := "gabl"
  triggerGloss := "before"
  sentence := "gabl maa atzawaʒ ʕisht maʕa ahl-ii"
  gloss := "before NEG I.get.married.IPFV I.live.PFV with family-my"
  translation := "Before I got married I lived with my parents."
  enNegator := "maa"

/-- BARELY trigger: *b-il-guwah* 'by force / barely'
    ([jin-koenig-2021], ex. 23). -/
def barelyExample : ENExample where
  triggerClass := "BARELY"
  triggerForm := "b-il-guwah"
  triggerGloss := "with-DET-force"
  sentence := "ta-kallam-na maʕaa-h tˤawaal il-lail wallah b-il-guwah maa waafag"
  gloss := "PFV-talk-we with-he all DET-night really with-DET-force NEG he.agree.PFV"
  translation := "We talked to him all night, and he really barely agreed."
  enNegator := "maa"

def allExamples : List ENExample :=
  [beforeExample, barelyExample]

/-! ### Structural Constraints on EN -/

open Semantics.Negation (ENBlockingReason)

/-- Why REGRET does not trigger EN in Januubi: Januubi speakers disprefer
    modal operators in complement clauses, and REGRET-class EN requires
    a deontic modal (e.g. *should*) ([jin-koenig-2021], §6.1.2, §7). -/
def regretBlocked : ENBlockingReason := .modalRestriction

/-- Why comparatives (MORE THAN, TOO…TO) do not trigger EN in Januubi. -/
def comparativeBlocked : ENBlockingReason := .npOnlyComplement

end Januubi.Negation
