import Linglib.Syntax.DependencyGrammar.Valency

/-!
# Lexical Rules for Word Grammar [hudson-2010]

Lexical rules derive new lexical entries from existing ones, following
Word Grammar and HPSG [pollard-sag-1994]. The two rules formalised
here are central to the [hudson-2010] treatment of English auxiliaries
(also discussed in [gibson-2025]):

1. Auxiliary Inversion: `V+aux → V+aux,+inv` (subject moves from left to
   right — Hudson treats this as a word-class subtype, not a movement rule;
   see `WordGrammar.Network.englishAuxNet`'s `inverted_auxiliary` node).
2. Passive: `VN → V+passive` (object promoted, subject demoted to by-phrase).

A third rule — Dative Alternation — is mentioned in the literature but not
formalised here.
-/

namespace WordGrammar

open DependencyGrammar (ArgStr ArgSlot Dir)

-- ============================================================================
-- Lexical Entries with Argument Structures
-- ============================================================================

/-- A lexical entry: word form + category + features + argument structure.
    Uses the shared `Features` bundle from Core/Basic.lean.
    The `inv` field is DG-specific (auxiliary inversion state). -/
structure LexEntry where
  form : String
  cat : UD.UPOS
  features : UD.MorphFeatures
  argStr : ArgStr
  inv : Bool := false
  deriving Repr

-- ============================================================================
-- Auxiliary Argument Structures (DG-specific, used with LexEntry/lexical rules)
-- Standard frames (argStrV0, argStrVN, argStrVNN, argStrVPassive) and
-- satisfiesArgStr are in Syntax/DependencyGrammar/Valency.lean.
-- ============================================================================

/-- Auxiliary verb (non-inverted): subject left, main verb right -/
def argStrAux : ArgStr := [⟨.nsubj, .left, true⟩, ⟨.aux, .right, true⟩]

/-- Auxiliary verb (inverted): subject right, main verb right -/
def argStrAuxInv : ArgStr := [⟨.nsubj, .right, true⟩, ⟨.aux, .right, true⟩]

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
      { e with
        inv := true
        argStr := e.argStr.map λ slot =>
          if slot.depType == .nsubj then
            { slot with dir := .right }  -- subject now goes to the right
          else slot } }

/-- Passive Rule: VN → V+passive
    Object is removed (promoted to subject), by-phrase added as optional -/
def passiveRule : LexRule :=
  { name := "Passive"
    applies := λ e =>
      e.cat == .VERB && e.features.voice != some .Pass &&
      e.argStr.any (·.depType == .obj)
    transform := λ e =>
      { e with
        features := { e.features with voice := some .Pass }
        argStr := e.argStr.filter (·.depType != .obj) ++ [⟨.obl, .right, false⟩] } }

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
