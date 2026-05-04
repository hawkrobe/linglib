import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Givenness — Cognitive Status of Discourse Referents
@cite{gundel-hedberg-zacharski-1993} @cite{prince-1981} @cite{chafe-1976}

Substrate type for the **Givenness** axis of information structure, one of
the four IS notions identified in @cite{krifka-2008} and adopted as the
unifying definitional baseline in @cite{fery-ishihara-2016} (Oxford
Handbook of Information Structure §1.3).

The handbook §1.3.3 names two interpretive modes for givenness:

- **Scalar / hierarchical** — Prince 1981, Chafe 1976,
  @cite{gundel-hedberg-zacharski-1993} (GHZ), @cite{lambrecht-1994}. The
  cognitive status of a referent in the hearer's mind is graded.
- **Categorical** — Schwarzschild 1999. Binary given vs not given,
  derived from grammatical antecedent presence.

This file provides the substrate for both:

- `GivennessStatus` (GHZ-6): `inFocus | activated | familiar |
  uniquelyIdentifiable | referential | typeIdentifiable`. The full
  hierarchy, promoted from `Phenomena/Reference/Studies/Ariel2001.lean`
  (where it was originally defined for the GHZ-vs-Ariel comparison) so
  it can be consumed across `Theories/` and `Features/`.

- `BinaryGivenness` (Prince 1981 hearer-status): `given | new`. The
  simplest categorical distinction; coarsening of GHZ-6 cutting at
  hearer-knowledge: anything the hearer can identify (`inFocus` through
  `uniquelyIdentifiable`) is `given`; anything brand-new to the hearer
  (`referential`, `typeIdentifiable`) is `new`. This is the cut Prince
  1981 / Strube-Hahn 1999 use; Chafe 1976's *activation*-based binary
  is a different cut (around `activated`/`familiar`) and is not
  provided as a primitive — consumers wanting Chafe's distinction can
  use `GivennessStatus.isActivated`.

## Layer position

`Features/`. Importable from any Theories/, Phenomena/, or Fragments/
consumer that needs to type a discourse referent's cognitive status.
The Centering MEDIATED tier
(`Theories/Discourse/Centering/Instances/InformationStatus.lean`) used
to lack a substrate source for the inferable / containing-inferable /
anchored-brand-new tier; GHZ-6's `familiar` and `uniquelyIdentifiable`
now supply it via `StrubeHahnInfoStatus.ofGivenness`.

## Replaces

`Features.InformationStructure.DiscourseStatus` (the 3-value enum
`focused | given | new`) was the prior catch-all annotation. It
conflated focus and givenness, and the `focused` tier was a category
error (focus is its own axis — `Features.InformationStructure.Focus`).
Consumers needing focus migrate to that type; consumers needing
givenness use `GivennessStatus` or `BinaryGivenness` here.
-/

set_option autoImplicit false

namespace Features

/-- @cite{gundel-hedberg-zacharski-1993} (GHZ): six cognitive statuses
    organized as an implicational hierarchy. Each status implies all
    lower ones (a referent in focus is also activated, familiar, etc.):

        in focus > activated > familiar > uniquely identifiable >
        referential > type identifiable

    The form-mapping documented in the original paper:
    `inFocus`              = unstressed pronoun
    `activated`            = that, this, this N
    `familiar`             = that N
    `uniquelyIdentifiable` = the N
    `referential`          = indefinite this N
    `typeIdentifiable`     = a N

    Promoted from `Phenomena/Reference/Studies/Ariel2001.lean` where it
    was originally defined for the GHZ-vs-Ariel-accessibility
    comparison. The Ariel-specific projection
    (`GivennessStatus.toAccessibility`) stays in `Ariel2001.lean`. -/
inductive GivennessStatus where
  /-- Unstressed pronoun: referent currently in attention. -/
  | inFocus
  /-- Activated: that/this/this-N — referent in working memory. -/
  | activated
  /-- Familiar: that-N — referent in long-term memory. -/
  | familiar
  /-- Uniquely identifiable: the-N — hearer can construct the referent
      from the description alone. -/
  | uniquelyIdentifiable
  /-- Referential: indefinite this-N — speaker has a particular
      referent in mind, hearer doesn't yet. -/
  | referential
  /-- Type identifiable: a-N — hearer can construct a representation
      of the *type* of object described. -/
  | typeIdentifiable
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Numeric rank: `inFocus = 5` (highest), `typeIdentifiable = 0`
    (lowest). Higher rank = more cognitively accessible. -/
def GivennessStatus.rank : GivennessStatus → Nat
  | .inFocus              => 5
  | .activated            => 4
  | .familiar             => 3
  | .uniquelyIdentifiable => 2
  | .referential          => 1
  | .typeIdentifiable     => 0

/-- @cite{prince-1981} hearer-status binary: `given | new`. The simplest
    categorical givenness distinction. `given` covers any referent the
    hearer can identify (regardless of activation state); `new` covers
    referents the hearer doesn't yet know about.

    This is the cut Prince 1981 / Strube-Hahn 1999 use. Chafe 1976's
    activation-based binary is a different cut (around `activated` vs
    `familiar`) and is not provided as a primitive. -/
inductive BinaryGivenness where
  /-- Given: hearer can identify the referent. Covers GHZ's `inFocus`
      through `uniquelyIdentifiable`. -/
  | given
  /-- New: brand-new to the hearer. Covers GHZ's `referential` and
      `typeIdentifiable`. -/
  | new
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Numeric rank: `given = 1`, `new = 0`. Higher rank = more given. -/
def BinaryGivenness.rank : BinaryGivenness → Nat
  | .given => 1
  | .new   => 0

/-- Project GHZ-6 onto Prince's hearer-status binary. The cut is at
    `uniquelyIdentifiable` / `referential`: anything the hearer can
    identify is `given`; brand-new referents are `new`.

    Monotone: higher GHZ rank never maps to lower binary rank
    (verified by `coarsen_monotone`). -/
def GivennessStatus.coarsen : GivennessStatus → BinaryGivenness
  | .inFocus              => .given
  | .activated            => .given
  | .familiar             => .given
  | .uniquelyIdentifiable => .given
  | .referential          => .new
  | .typeIdentifiable     => .new

/-- Chafe 1976 activation-based view: is this referent activated in
    working memory? `inFocus` and `activated` are activated; everything
    else is not. Provided so consumers needing Chafe's cut don't have
    to redefine it.

    Anti-pattern check: this is NOT a third primitive enum — it's a
    derived predicate. If a consumer needs to *parameterize* over
    Chafe-binary instead of Prince-binary, that's a sign the consumer
    should accept a `GivennessStatus → Bool` predicate, not that we
    need a `ChafeGivenness` enum. -/
def GivennessStatus.isActivated : GivennessStatus → Bool
  | .inFocus   => true
  | .activated => true
  | _          => false

/-- The coarsening preserves order: if a GHZ status outranks another,
    its binary projection is at least as given. -/
theorem GivennessStatus.coarsen_monotone (a b : GivennessStatus) :
    a.rank ≥ b.rank → a.coarsen.rank ≥ b.coarsen.rank := by
  cases a <;> cases b <;> decide

private theorem GivennessStatus.rank_injective :
    Function.Injective GivennessStatus.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [GivennessStatus.rank]

private theorem BinaryGivenness.rank_injective :
    Function.Injective BinaryGivenness.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [BinaryGivenness.rank]

/-- Total order on `GivennessStatus` via the rank function. -/
instance : LinearOrder GivennessStatus :=
  LinearOrder.lift' GivennessStatus.rank GivennessStatus.rank_injective

/-- Total order on `BinaryGivenness` via the rank function. -/
instance : LinearOrder BinaryGivenness :=
  LinearOrder.lift' BinaryGivenness.rank BinaryGivenness.rank_injective

end Features
