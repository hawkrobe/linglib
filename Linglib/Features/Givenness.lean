import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Givenness — Cognitive Status of Discourse Referents
@cite{gundel-hedberg-zacharski-1993} @cite{prince-1981} @cite{chafe-1976}
@cite{chafe-1987} @cite{ariel-2001}

Substrate type for the **Givenness** axis of information structure.
@cite{krifka-2008} enumerates four IS notions — focus, givenness,
topic, and **delimitation** (frame-setting). At-issueness (Roberts /
Tonhauser-Beaver-Roberts-Simons / Tonhauser-Beaver-Degen) is a
separate axis from the QUD tradition that the post-2008 literature
treats as orthogonal to Krifka's four. @cite{fery-ishihara-2016}
(Oxford Handbook of Information Structure introduction) adopts
Krifka's definitions as the unifying baseline. Linglib currently
provides substrate for focus, givenness, topic, and at-issueness;
delimitation has no substrate yet.

The handbook section on givenness names two interpretive modes:

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
  1981 / Strube-Hahn 1999 use. Chafe's later activation-based view
  (Chafe 1987, elaborated in Chafe 1994) draws a different cut as a
  three-way active / semi-active / inactive taxonomy; not provided
  here as a primitive.

## Critique: Ariel 2001 on GHZ

@cite{ariel-2001} (pp. 62-65) raises four substantive critiques of the
GHZ-6 hierarchy that consumers should know about:

1. **Limited psychological evidence.** Ariel argues (p. 64) that
   psychological evidence supports the scalar relation between
   `inFocus` and `activated` only — the four lower tiers (`familiar`
   through `typeIdentifiable`) lack independent experimental support
   as a distinct scalar order.
2. **Internally disjunctive tiers.** `uniquelyIdentifiable` and
   `referential` each cover two cognitively different processes
   (retrieve vs construct an existing/new representation; Ariel p. 63).
3. **Many-many form-function.** A given GHZ status maps to many
   surface forms, and a given form maps to many statuses (Mulkern 1996
   on partial vs full proper names; Ariel p. 64).
4. **Implicationality counterexample.** Ziv 1996 — pronouns
   (`inFocus`) are predicted by the implicational hierarchy to also
   be `uniquelyIdentifiable`, but Ziv exhibits cases of unidentified
   inferred role players where this fails.

Ariel's own account uses the 18-tier `Features.AccessibilityLevel`
(see below) which Ariel argues is the better-grounded scale. **GHZ-6 is
nonetheless retained as substrate** because it is what the IS
literature widely cites (Krifka 2008 / Féry-Ishihara 2016 list it as
the canonical scalar givenness theory), and because Centering's
@cite{strube-hahn-1999} information-status taxonomy projects naturally
from GHZ-style categories. Discrete enough for `decide`-based
theorems, where AccessibilityLevel's 18 tiers can be unwieldy.

## Relation to AccessibilityLevel

`Features.AccessibilityLevel` (@cite{ariel-2001}) is the
empirically-better-supported sibling: 18 tiers of NP-form-marking
with informativity, rigidity, and attenuation criteria. Ariel's `toAccessibility` projection from GHZ-6
to AccessibilityLevel lives in `Phenomena/Reference/Studies/Ariel2001.lean`
(Ariel-specific bridge). Use AccessibilityLevel when finer distinctions
matter (proximate vs distal demonstratives; clitic vs unstressed vs zero
pronouns); use GivennessStatus when the IS-literature 6-tier shape is
the right granularity.

## Layer position

`Features/`. Importable from any Theories/, Phenomena/, or Fragments/
consumer that needs to type a discourse referent's cognitive status.
The Centering MEDIATED tier
(`Theories/Discourse/Centering/Instances/InformationStatus.lean`) used
to lack a substrate source for the inferable / containing-inferable /
anchored-brand-new tier; GHZ-6's `familiar` and `uniquelyIdentifiable`
now supply it via `StrubeHahnInfoStatus.ofGivenness`.

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
  /-- Unstressed pronoun: referent currently in attention. Per
      @cite{ariel-2001} p. 64 (citing Ziv 1996), the implicational
      claim that `inFocus` entities are also `uniquelyIdentifiable`
      has counterexamples (unidentified inferred role players); this
      enum's ordinal placement is the GHZ-claimed order, not a proven
      cognitive fact. -/
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

    This is the cut Prince 1981 / Strube-Hahn 1999 use. Chafe's
    activation-based view (Chafe 1987) draws a different
    *three-way* taxonomy (active / semi-active / inactive); not
    provided here as a primitive. -/
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

/-- Distinct GHZ-6 statuses have distinct ranks. -/
theorem GivennessStatus.rank_injective :
    Function.Injective GivennessStatus.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [GivennessStatus.rank]

/-- Distinct binary-givenness values have distinct ranks. -/
theorem BinaryGivenness.rank_injective :
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
