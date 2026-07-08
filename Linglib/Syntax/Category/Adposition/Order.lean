import Linglib.Data.WALS.Features.F85A
import Linglib.Data.UD.Basic
import Linglib.Features.WordOrder

/-!
# Adposition typology: shared substrate type
[dryer-2013-wals] [greenberg-1963] [dryer-1992]

Framework-agnostic enum for storing per-language adposition order
(WALS Ch 85). The adposition-order facet of the bare-root `Adposition`
namespace (sibling of `Syntax/Category/Adposition/Basic.lean`'s PP structure);
both `Fragments/` (per-language profiles) and `Studies/` (cross-linguistic
generalisations) import it.

Sister substrate to `WordOrder` — same shape (enum with
WALS-attested cases plus epistemic-distinction cases, namespaced
`AdpositionOrder.ofWALS{85A,}` converters, classification predicates,
head-direction projection).

## Epistemic distinction: `noDominant` vs `notInWALS`

`AdpositionOrder.noDominant` is the WALS-attested mixed-system code
(language has both pre- and postpositions, neither dominates — *itself
a finding*). `AdpositionOrder.notInWALS` is absence from Ch 85 — the
language was not coded. A consumer that filtered on `≠ .noDominant`
would otherwise silently include unencoded languages as "genuinely
nondominant". The two cases are kept distinct, mirroring
`WordOrder`'s post-refactor design.

## `noAdpositions` as a category

WALS codes ~30 languages as `.noAdpositions` (case-marking alone, no
adposition morphology). This is distinct from `noDominant` (language
has both) and from `notInWALS` (uncoded). All three are framework-
neutral.

## Greenbergian vs Dryerian primacy

The substrate is *neutral* on which classification is theoretically
primary. [greenberg-1963]'s Universals 3 and 4 treat adposition
as the *correlate* of basic constituent order (VSO → Prep, SOV →
Postp). [dryer-1992] explicitly demoted SOV/SVO/VSO in favour of
OV/VO + correlation pairs (Branching Direction Theory), making
adposition a co-primary head-direction phenomenon. Consumers
downstream choose which projection to read; the substrate provides
both `IsPrepositional`/`IsPostpositional` (Greenberg-style
predicates) and `headDirection` (Dryer-style projection).
-/

namespace Adposition

/-- WALS Ch 85 plus the absence-from-WALS case. -/
inductive AdpositionOrder where
  /-- Adposition precedes complement NP (head-initial PP). -/
  | prepositional
  /-- Adposition follows complement NP (head-final PP). -/
  | postpositional
  /-- Adposition appears medially in a complex NP (rare; WALS lists
      ~8 Australian Aboriginal + Cariban + PNG languages). -/
  | inpositional
  /-- Language has no adpositions (case-marking alone; ~30 WALS
      languages). Distinct from `notInWALS`. -/
  | noAdpositions
  /-- WALS-attested mixed system (both pre- and postpositions,
      neither dominates). -/
  | noDominant
  /-- Language not coded in WALS Ch 85 (no information). Distinct
      from `noAdpositions` (which is a substantive WALS finding). -/
  | notInWALS
  deriving DecidableEq, Repr

namespace AdpositionOrder

/-- Convert WALS F85A's `AdpositionNPOrder` to a local `AdpositionOrder`. -/
def ofWALS85A : Data.WALS.F85A.AdpositionNPOrder → AdpositionOrder
  | .prepositions => .prepositional
  | .postpositions => .postpositional
  | .inpositions => .inpositional
  | .noAdpositions => .noAdpositions
  | .noDominantOrder => .noDominant

/-- Look up Ch 85 adposition order for an ISO 639-3 code. Returns
    `.notInWALS` when the language is absent from the chapter. -/
def ofWALS (iso : String) : AdpositionOrder :=
  match Data.WALS.Datapoint.lookupISO Data.WALS.F85A.allData iso with
  | some d => ofWALS85A d.value
  | none => .notInWALS

-- ============================================================================
-- Classification predicates (Greenberg-style)
-- ============================================================================

/-- `a` is prepositional. -/
abbrev IsPrepositional (a : AdpositionOrder) : Prop := a = .prepositional

/-- `a` is postpositional. -/
abbrev IsPostpositional (a : AdpositionOrder) : Prop := a = .postpositional

-- ============================================================================
-- Head-direction projection (Dryer-style)
-- ============================================================================

/-- Project an `AdpositionOrder` to a `HeadDirection`. Theory-neutral:
    prepositional ⇒ head-initial PP, postpositional ⇒ head-final PP.
    Returns `none` for the categories that do not commit to a single
    direction (`.inpositional`, `.noAdpositions`, `.noDominant`,
    `.notInWALS`). Sister of `OVOrder.verbPosition`; consumers needing
    BDT-style head-direction unification can iterate over both
    projections. -/
def headDirection : AdpositionOrder → Option HeadDirection
  | .prepositional => some .headInitial
  | .postpositional => some .headFinal
  | .inpositional | .noAdpositions | .noDominant | .notInWALS => none

end AdpositionOrder

end Adposition
