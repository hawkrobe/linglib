import Linglib.Semantics.Lexical.Roots.Basic

/-!
# Templatic Heads and Event Structure Composition

The event-structural architecture of [beavers-koontz-garboden-2020]
(ch. 1): **templatic heads** combine with **roots**, and a root
attaches in one of two structural positions (adjoined to a head, or as
its complement). The familiar [rappaport-hovav-levin-1998] templates
(state, activity, achievement, accomplishment) are *compositions* of
these primitives.

Scope: the three verbal heads `v_act`/`v_become`/`v_cause` of the
change-of-state and manner fragment (chs. 1–2, 4–5). The ditransitive
prepositional heads P_loc and P_have and the modalized causative of
ch. 3 are not modeled.

## Main declarations

* `TemplaticHead` — the three primitive heads
* `Verb.Root.Position` — complement vs adjoined attachment
* `Verb.Root.EventStructure` — heads composed with a positioned root
-/

/-! ### Templatic heads -/

/-- The three primitive event-structural heads of
    [beavers-koontz-garboden-2020] ch. 1. The book glosses
    `v_become` as `λPλxλe. ∃s. become′(s, e) ∧ P(x, s)` and `v_cause`
    as `λQλyλv. ∃e. effector′(y, v) ∧ cause′(v, e) ∧ Q(e)` — one
    event-predicate argument, introducing the effector. -/
inductive TemplaticHead where
  | v_act     -- activity (Davidsonian event predicate)
  | v_become  -- change of state into the root's state
  | v_cause   -- causation by an effector
  deriving DecidableEq, Repr

/-! ### Root position -/

/-- Structural attachment position of a verb root, following the
    Distributed-Morphology tradition (Marantz; systematized by
    [beavers-koontz-garboden-2020]):

    - **complement**: root merges as complement of v (inside VP),
      filling the result/state slot (√flat, √crack, √blossom, √drown);
    - **adjoined**: root merges as adjunct to v (outside VP), modifying
      the event (√jog, √toss, √hand).

    The distinction matters beyond root typology: it conditions vVPE
    eligibility ([kalyakin-2026]), result-state modifier scope, and the
    restitutive/repetitive *again* ambiguity
    ([beavers-koontz-garboden-2020], [merchant-2013]). -/
inductive Verb.Root.Position where
  | complement
  | adjoined
  deriving DecidableEq, Repr

/-! ### Composed event structures -/

namespace Verb.Root

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
  root : Verb.Root
  position : Verb.Root.Position

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

/-! ### Canonical compositions -/

/-- A pure activity: `[v_act]` with manner root adjoined.
    [x ACT⟨manner⟩] -/
def activityOf (r : Verb.Root) : EventStructure :=
  ⟨[.v_act], r, .adjoined⟩

/-- An achievement: `[v_become]` with state root as complement.
    [BECOME [x ⟨STATE⟩]] -/
def achievementOf (r : Verb.Root) : EventStructure :=
  ⟨[.v_become], r, .complement⟩

/-- An accomplishment: `[v_cause, v_become]` with state root as
    complement to BECOME. [[x ACT] CAUSE [BECOME [y ⟨STATE⟩]]] -/
def accomplishmentOf (r : Verb.Root) : EventStructure :=
  ⟨[.v_cause, .v_become], r, .complement⟩

end Verb.Root
