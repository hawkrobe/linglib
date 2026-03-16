import Linglib.Theories.Syntax.ConstructionGrammar.ArgumentStructure
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Typed Slot-Filler Representation

@cite{dunn-2026} @cite{kay-fillmore-1999} @cite{dunn-2025} @cite{fillmore-kay-oconnor-1988} @cite{goldberg-1995}

Constructions are sequences of slots, where each slot is either fixed
(a specific lexeme), open (any word of a given syntactic category),
or headed (a phrase headed by a specific lexeme). @cite{dunn-2025}'s variationist CxG treats abstraction as continuous (the proportion of
open slots). @cite{kay-fillmore-1999} add grammatical functions,
coreference indices, and syntactic constraints to the slot representation.

## Architecture

`Slot Lex` combines six pieces of information into one type:

| Field | Type | Source |
|-------|------|--------|
| `filler` | `SlotFiller Lex` | @cite{dunn-2025} + @cite{kay-fillmore-1999} (fixed/open/headed) |
| `role` | `Option String` | @cite{goldberg-1995} (semantic role) |
| `isHead` | `Bool` | ArgumentStructure.lean |
| `gf` | `Option GramFunction` | @cite{kay-fillmore-1999} (grammatical function) |
| `refIdx` | `Option RefIndex` | @cite{kay-fillmore-1999} (coreference index) |
| `constraints` | `List SlotConstraint` | @cite{kay-fillmore-1999} (syntactic constraints) |

`TypedForm Lex := List (Slot Lex)` is the typed form side of a construction.

The existing `ConstructionSlot` (which only represents open slots) embeds
into `Slot String` via `ConstructionSlot.toSlot` (§3).

## Key definitions

- `abstractionLevel`: continuous [0,1] proportion of open slots (ℚ)
- `derivedSpecificity`: derives `Specificity` from slot structure
- `hasConstraint` / `refGroupCount`: cross-slot constraint queries
- `ConstructionSlot.toSlot`: embeds existing all-open slots

Verification theorems live in `Phenomena/Constructions/Bridge/SlotVerification.lean`.

-/

namespace ConstructionGrammar

-- ============================================================================
-- §1. Core Types
-- ============================================================================

/-- A slot's filler: the representation level of slot content.

@cite{dunn-2025} distinguishes three representation levels for slot content:
- **LEX** (lexeme): a specific word form → `fixed "must"`
- **SYN** (syntactic): any word of a given POS category → `open_.VERB`
- **SEM+** (semantic): any expression satisfying a semantic constraint →
  `semantic "animate"` (any animate NP)

@cite{kay-fillmore-1999} add headed phrases: `headed "doing".VERB` (a VP
headed by *doing*). These are LEX-level (they fix the head lexeme).

Parameterized over `Lex` (the lexeme type) so the same representation
works for strings, morphemes, or phonological forms. -/
inductive SlotFiller (Lex : Type) where
  | fixed : Lex → SlotFiller Lex
  | open_ : UD.UPOS → SlotFiller Lex
  /-- A phrase headed by a specific lexeme.
      `headed "doing".VERB` means "a VP headed by *doing*" — the slot
      is phrasal, not the bare word. Contrast with `fixed "doing"`. -/
  | headed : Lex → UD.UPOS → SlotFiller Lex
  /-- A semantically constrained slot (@cite{dunn-2025}, SEM+ level).
      `semantic "animate"` means any expression satisfying the semantic
      property "animate". More abstract than SYN (category-based): the
      filler is constrained by meaning, not by syntactic category. -/
  | semantic : String → SlotFiller Lex
  deriving DecidableEq, BEq, Repr

/-- Is this slot open (not lexically fixed)?

Both `open_` (SYN) and `semantic` (SEM+) slots count as open for
abstraction level computation. `headed` slots do not: they fix the
head lexeme even though the phrase is open. -/
def SlotFiller.isOpen {Lex : Type} : SlotFiller Lex → Bool
  | .fixed _ => false
  | .open_ _ => true
  | .headed _ _ => false
  | .semantic _ => true

/-- Grammatical function of a valence member (@cite{kay-fillmore-1999}, Figure 12).
    Distinct from semantic role: a subject (gf) can be an agent, theme,
    or experiencer (role). -/
inductive GramFunction where
  | subj   -- subject
  | comp   -- complement (clausal/verbal)
  | obj    -- direct object
  | pred   -- predicative complement / secondary predicate
  deriving DecidableEq, BEq, Repr

/-- Referential index for cross-slot coreference constraints.
    Slots sharing the same RefIndex must have their semantic values
    unified. @cite{kay-fillmore-1999} use #1, #2, etc. to
    express identity between a construction's semantic arguments
    and its valence members' semantic values. -/
abbrev RefIndex := Nat

/-- Syntactic constraint on a slot (@cite{kay-fillmore-1999}, Figure 12). -/
inductive SlotConstraint where
  | locMinus   -- [loc -]: must occur left-isolated, not VP-internal
  | negMinus   -- [neg -]: cannot be negated
  | refEmpty   -- [ref ∅]: nonreferential (no variable-binding function)
  deriving DecidableEq, BEq, Repr

/-- A slot in a construction: filler content + semantic role + headedness.

Subsumes `ConstructionSlot` (which only represents open slots) by adding
the fixed/open distinction via `SlotFiller`. Fixed slots (like "let" in
*let alone*) have `role := none` since they carry no independent semantic
role. -/
structure Slot (Lex : Type) where
  /-- What fills this slot: a specific lexeme, open category, or headed phrase -/
  filler : SlotFiller Lex
  /-- Semantic role label (agent, theme, etc.), if any -/
  role : Option String := none
  /-- Whether this slot is the head of the construction -/
  isHead : Bool := false
  /-- Grammatical function (subj, comp, obj, pred) — @cite{kay-fillmore-1999} -/
  gf : Option GramFunction := none
  /-- Coreference index: slots sharing an index have unified semantics -/
  refIdx : Option RefIndex := none
  /-- Syntactic constraints on this slot ([loc -], [neg -], [ref ∅]) -/
  constraints : List SlotConstraint := []
  deriving DecidableEq, BEq, Repr

/-- A typed form: the form side of a construction as a sequence of slots.

This replaces `Construction.form : String` with a structured representation
that supports computation (abstraction level, specificity derivation). -/
abbrev TypedForm (Lex : Type) := List (Slot Lex)

-- ============================================================================
-- §2. Abstraction Level and Derived Specificity
-- ============================================================================

section AbstractionLevel
variable {Lex : Type}

/-- Proportion of open slots: a continuous [0,1] measure of abstraction.

This computes the fraction of slots that are open (SYN or SEM+).
@cite{dunn-2025} defines four discrete abstraction *orders* based on
which representation levels appear (1st = all LEX, 2nd = mostly LEX,
3rd = mixed, 4th = all abstract). This function computes the continuous
proportion underlying those orders; `derivedSpecificity` (below)
maps to the three-way `Specificity` enum. -/
def abstractionLevel (form : TypedForm Lex) : ℚ :=
  if form.isEmpty then 0
  else
    let openCount := (form.filter (·.filler.isOpen)).length
    (openCount : ℚ) / (form.length : ℚ)

/-- Derive `Specificity` from the slot structure.

| Condition | Result |
|-----------|--------|
| All slots open | `.fullyAbstract` |
| No slots open | `.lexicallySpecified` |
| Mix of fixed and open | `.partiallyOpen` |

This makes `Specificity` a derived property rather than a stipulated one:
changing a slot from open to fixed automatically changes the specificity. -/
def derivedSpecificity (form : TypedForm Lex) : Specificity :=
  let openCount := (form.filter (·.filler.isOpen)).length
  if openCount = form.length then .fullyAbstract
  else if openCount = 0 then .lexicallySpecified
  else .partiallyOpen

end AbstractionLevel

-- ============================================================================
-- §3. Embedding of ConstructionSlot
-- ============================================================================

/-- Embed an all-open `ConstructionSlot` as a `Slot String`.

Every `ConstructionSlot` is an open slot (it only specifies `cat : UPOS`).
The embedding preserves category, role, and headedness. -/
def ConstructionSlot.toSlot (s : ConstructionSlot) : Slot String :=
  { filler := .open_ s.cat
  , role := some s.role
  , isHead := s.isHead }

/-- Convert an `ArgStructureConstruction`'s slot list to a `TypedForm`. -/
def ArgStructureConstruction.toTypedForm (asc : ArgStructureConstruction) :
    TypedForm String :=
  asc.slots.map ConstructionSlot.toSlot

/-- All-open slots are always open (by construction). -/
theorem ConstructionSlot.toSlot_isOpen (s : ConstructionSlot) :
    (s.toSlot).filler.isOpen = true := rfl

-- ============================================================================
-- §4. Cross-Slot Constraints (@cite{kay-fillmore-1999})
-- ============================================================================

section CrossSlotConstraints
variable {Lex : Type}

/-- Does any slot in the form bear a given constraint? -/
def hasConstraint (form : TypedForm Lex) (c : SlotConstraint) : Bool :=
  form.any (·.constraints.any (· == c))

/-- Count of distinct coreference groups in a form. -/
def refGroupCount (form : TypedForm Lex) : Nat :=
  (form.filterMap (·.refIdx)).eraseDups.length

end CrossSlotConstraints

end ConstructionGrammar
