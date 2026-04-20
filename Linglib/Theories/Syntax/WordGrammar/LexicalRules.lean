import Linglib.Core.Dependency.Basic

/-!
# Lexical Rules for Word Grammar @cite{hudson-2010}

Lexical rules derive new lexical entries from existing ones, following
Word Grammar and HPSG @cite{pollard-sag-1994}. The two rules formalised
here are central to the @cite{hudson-2010} treatment of English auxiliaries
(also discussed in @cite{gibson-2025}):

1. Auxiliary Inversion: `V+aux → V+aux,+inv` (subject moves from left to
   right — Hudson treats this as a word-class subtype, not a movement rule;
   see `WordGrammar.Network.englishAuxNet`'s `inverted_auxiliary` node).
2. Passive: `VN → V+passive` (object promoted, subject demoted to by-phrase).

A third rule — Dative Alternation — is mentioned in the literature but not
formalised here.
-/

namespace WordGrammar

open DepGrammar (ArgStr ArgSlot Dir)

-- ============================================================================
-- Lexical Entries with Argument Structures
-- ============================================================================

/-- A lexical entry: word form + category + features + argument structure.
    Uses the shared `Features` bundle from Core/Basic.lean.
    The `inv` field is DG-specific (auxiliary inversion state). -/
structure LexEntry where
  form : String
  cat : UD.UPOS
  features : Features
  argStr : ArgStr
  inv : Bool := false
  deriving Repr

-- ============================================================================
-- Auxiliary Argument Structures (DG-specific, used with LexEntry/lexical rules)
-- Standard frames (argStr_V0, argStr_VN, argStr_VNN, argStr_VPassive) and
-- satisfiesArgStr are in Core/Basic.lean.
-- ============================================================================

/-- Auxiliary verb (non-inverted): subject left, main verb right -/
def argStr_Aux : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩,
              ⟨.aux, .right, true, some .VERB⟩] }

/-- Auxiliary verb (inverted): subject right, main verb right -/
def argStr_AuxInv : ArgStr :=
  { slots := [⟨.nsubj, .right, true, some .DET⟩,
              ⟨.aux, .right, true, some .VERB⟩] }

-- ============================================================================
-- Lexical Rules
-- ============================================================================

/-- A lexical rule transforms one lexical entry into another -/
structure LexRule where
  name : String
  /-- Condition for the rule to apply -/
  applies : LexEntry → Bool
  /-- Transform the entry -/
  transform : LexEntry → LexEntry

/-- Auxiliary Inversion Rule: V+aux,-inv → V+aux,+inv
    The subject moves from left to right position -/
def auxInversionRule : LexRule :=
  { name := "Auxiliary Inversion"
    applies := λ e =>
      e.cat == .AUX && !e.inv
    transform := λ e =>
      let newSlots := e.argStr.slots.map λ slot =>
        if slot.depType == .nsubj then
          { slot with dir := .right }  -- subject now goes to the right
        else slot
      { e with
        inv := true
        argStr := { slots := newSlots } } }

/-- Passive Rule: VN → V+passive
    Object is removed (promoted to subject), by-phrase added as optional -/
def passiveRule : LexRule :=
  { name := "Passive"
    applies := λ e =>
      e.cat == .VERB && e.features.voice != some Voice.passive &&
      e.argStr.slots.any (·.depType == .obj)
    transform := λ e =>
      let newSlots := e.argStr.slots.filter (·.depType != .obj)
      let withByPhrase := newSlots ++ [⟨.obl, .right, false, some .ADP⟩]
      { e with
        features := { e.features with voice := some Voice.passive }
        argStr := { slots := withByPhrase } } }

-- ============================================================================
-- Applying Lexical Rules
-- ============================================================================

/-- Apply a lexical rule if it matches -/
def applyRule (rule : LexRule) (entry : LexEntry) : Option LexEntry :=
  if rule.applies entry then some (rule.transform entry)
  else none

/-- Apply all applicable rules to generate derived entries -/
def deriveEntries (rules : List LexRule) (entry : LexEntry) : List LexEntry :=
  entry :: rules.filterMap (applyRule · entry)

end WordGrammar
