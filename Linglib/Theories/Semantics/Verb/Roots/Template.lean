import Linglib.Theories.Semantics.Verb.Roots.Basic

/-!
# Templatic Heads and Event Structure Composition

@cite{beavers-koontz-garboden-2020} @cite{rappaport-hovav-levin-1998}

The B&K-G architecture decomposes event structure into **templatic
heads** that combine with **roots**. The three primitive heads are:

- `v_act`    — activity (Davidsonian event predicate)
- `v_become` — change of state ([BECOME [x ⟨STATE⟩]])
- `v_cause`  — causation ([e₁ CAUSE e₂])

A root attaches to a head in one of two structural positions:

- **adjoined** — modifier of a head (typical of manner roots)
- **complement** — argument of a head (typical of state roots)

The familiar @cite{rappaport-hovav-levin-1998} templates (state,
activity, achievement, accomplishment) are *compositions* of these
primitives — see `EventStructure.toTemplate`.
-/

namespace Semantics.Verb.Roots

-- ════════════════════════════════════════════════════
-- § 1. Templatic Heads
-- ════════════════════════════════════════════════════

/-- The three primitive event-structural heads
    (@cite{beavers-koontz-garboden-2020} ch. 1, ch. 5). -/
inductive TemplaticHead where
  | v_act     -- activity: λxλe. P(x, e)
  | v_become  -- BECOME:   λPλxλe. ∃s. become(s, e) ∧ P(x, s)
  | v_cause   -- CAUSE:    λPλQλxλe. ∃e'. P(x, e) ∧ Q(e') ∧ cause(e, e')
  deriving DecidableEq, Repr

/-- Structural position at which a root attaches to a head. -/
inductive RootPosition where
  | adjoined    -- modifier (typical of manner roots)
  | complement  -- argument (typical of state roots)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Composed Event Structures
-- ════════════════════════════════════════════════════

/-- An event structure: a list of templatic heads (outermost first)
    composed with a root in a specific structural position.

    Examples:
    - `⟨[v_act], jog, adjoined⟩`           — pure activity (jog)
    - `⟨[v_become], blossom, complement⟩`  — achievement
    - `⟨[v_cause, v_become], crack, complement⟩` — accomplishment
    - `⟨[v_cause, v_become], hand, adjoined⟩`    — caused result with
      manner root in adjoined position -/
structure EventStructure where
  heads : List TemplaticHead
  root : Root
  position : RootPosition
  deriving Repr

namespace EventStructure

/-- Does the event structure include a particular head? -/
def hasHead (es : EventStructure) (h : TemplaticHead) : Bool :=
  es.heads.contains h

/-- Has activity head. -/
def hasAct (es : EventStructure) : Bool := es.hasHead .v_act

/-- Has BECOME head. -/
def hasBecome (es : EventStructure) : Bool := es.hasHead .v_become

/-- Has CAUSE head. -/
def hasCause (es : EventStructure) : Bool := es.hasHead .v_cause

end EventStructure

-- ════════════════════════════════════════════════════
-- § 3. Canonical Compositions
-- ════════════════════════════════════════════════════

/-- A pure activity: `[v_act]` with manner root adjoined.
    [x ACT⟨manner⟩] -/
def activityOf (r : Root) : EventStructure :=
  ⟨[.v_act], r, .adjoined⟩

/-- An achievement: `[v_become]` with state root as complement.
    [BECOME [x ⟨STATE⟩]] -/
def achievementOf (r : Root) : EventStructure :=
  ⟨[.v_become], r, .complement⟩

/-- An accomplishment: `[v_cause, v_become]` with state root as
    complement to BECOME. [[x ACT] CAUSE [BECOME [y ⟨STATE⟩]]] -/
def accomplishmentOf (r : Root) : EventStructure :=
  ⟨[.v_cause, .v_become], r, .complement⟩

end Semantics.Verb.Roots
