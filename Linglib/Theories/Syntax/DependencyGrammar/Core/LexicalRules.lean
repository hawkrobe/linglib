/-
# Lexical Rules for Dependency Grammar

Lexical rules derive new lexical entries from existing ones.
Following Word Grammar (Hudson 1984, 1990) and HPSG (Pollard & Sag 1994).

Key lexical rules:
1. Auxiliary Inversion: V+aux → V+aux,+inv (subject moves from left to right)
2. Passive: VN → V+passive (object promoted, subject demoted to by-phrase)
3. Dative Alternation: VN,N → VN,PP (double object ↔ prepositional dative)

References:
- Gibson (2025) "Syntax", MIT Press, Section 3.9
- Pollard & Sag (1994) "Head-Driven Phrase Structure Grammar"
-/

import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.Syntax.DependencyGrammar.Core.Basic

namespace DepGrammar

-- ============================================================================
-- Lexical Entries with Argument Structures
-- ============================================================================

/-- Features for lexical entries -/
structure LexFeatures where
  inv : Bool := false      -- inverted (for auxiliaries)
  passive : Bool := false  -- passive voice
  finite : Bool := true
  number : Option Number := none
  person : Option Person := none
  deriving Repr, DecidableEq

/-- A lexical entry: word form + category + features + argument structure -/
structure LexEntry where
  form : String
  cat : UD.UPOS
  features : LexFeatures
  argStr : ArgStr
  deriving Repr

-- ============================================================================
-- Standard Argument Structures
-- ============================================================================

/-- Intransitive verb: subject to the left -/
def argStr_V0 : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩] }

/-- Transitive verb: subject left, object right -/
def argStr_VN : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩,
              ⟨.obj, .right, true, some .DET⟩] }

/-- Ditransitive verb: subject left, indirect object right, object right -/
def argStr_VNN : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩,
              ⟨.iobj, .right, true, some .DET⟩,
              ⟨.obj, .right, true, some .DET⟩] }

/-- Auxiliary verb (non-inverted): subject left, main verb right -/
def argStr_Aux : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩,
              ⟨.aux, .right, true, some .VERB⟩] }

/-- Auxiliary verb (inverted): subject right, main verb right -/
def argStr_AuxInv : ArgStr :=
  { slots := [⟨.nsubj, .right, true, some .DET⟩,
              ⟨.aux, .right, true, some .VERB⟩] }

/-- Passive transitive: subject left (was patient), optional by-phrase right -/
def argStr_VPassive : ArgStr :=
  { slots := [⟨.nsubj, .left, true, some .DET⟩,
              ⟨.obl, .right, false, some .ADP⟩] }  -- by-phrase is optional

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
      e.cat == .AUX && !e.features.inv
    transform := λ e =>
      let newSlots := e.argStr.slots.map λ slot =>
        if slot.depType == .nsubj then
          { slot with dir := .right }  -- subject now goes to the right
        else slot
      { e with
        features := { e.features with inv := true }
        argStr := { slots := newSlots } } }

/-- Passive Rule: VN → V+passive
    Object is removed (promoted to subject), by-phrase added as optional -/
def passiveRule : LexRule :=
  { name := "Passive"
    applies := λ e =>
      e.cat == .VERB && !e.features.passive &&
      e.argStr.slots.any (·.depType == .obj)
    transform := λ e =>
      let newSlots := e.argStr.slots.filter (·.depType != .obj)
      let withByPhrase := newSlots ++ [⟨.obl, .right, false, some .ADP⟩]
      { e with
        features := { e.features with passive := true }
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

-- ============================================================================
-- Example Lexical Entries
-- ============================================================================

/-- "can" - modal auxiliary (non-inverted) -/
def lex_can : LexEntry :=
  { form := "can"
    cat := .AUX
    features := { inv := false, finite := true }
    argStr := argStr_Aux }

/-- "can" - modal auxiliary (inverted, derived) -/
def lex_can_inv : LexEntry :=
  auxInversionRule.transform lex_can

/-- "does" - do-support auxiliary (non-inverted) -/
def lex_does : LexEntry :=
  { form := "does"
    cat := .AUX
    features := { inv := false, finite := true, number := some .sg, person := some .third }
    argStr := argStr_Aux }

/-- "kicked" - transitive verb -/
def lex_kicked : LexEntry :=
  { form := "kicked"
    cat := .VERB
    features := { passive := false, finite := true }
    argStr := argStr_VN }

/-- "kicked" - passive (derived) -/
def lex_kicked_passive : LexEntry :=
  passiveRule.transform lex_kicked

-- ============================================================================
-- Tests
-- ============================================================================

-- Auxiliary inversion
#eval lex_can.features.inv           -- false
#eval lex_can_inv.features.inv       -- true

-- Check subject direction changes
#eval lex_can.argStr.slots.map (·.dir)      -- [left, right]
#eval lex_can_inv.argStr.slots.map (·.dir)  -- [right, right]

-- Passive
#eval lex_kicked.features.passive           -- false
#eval lex_kicked_passive.features.passive   -- true

-- Check object removed in passive
#eval lex_kicked.argStr.slots.map (·.depType)         -- [subj, obj]
#eval lex_kicked_passive.argStr.slots.map (·.depType) -- [subj, obl]

-- ============================================================================
-- Building Dependency Trees from Argument Structures
-- ============================================================================

/-- Check if a dependency tree satisfies an argument structure -/
def satisfiesArgStr (t : DepTree) (headIdx : Nat) (argStr : ArgStr) : Bool :=
  argStr.slots.all λ slot =>
    if slot.required then
      -- Required slot: must have a matching dependency
      t.deps.any λ d =>
        d.headIdx == headIdx &&
        d.depType == slot.depType &&
        -- Check direction
        (match slot.dir with
         | .left => d.depIdx < headIdx
         | .right => d.depIdx > headIdx)
    else
      -- Optional slot: if present, must be in correct direction
      t.deps.all λ d =>
        if d.headIdx == headIdx && d.depType == slot.depType then
          match slot.dir with
          | .left => d.depIdx < headIdx
          | .right => d.depIdx > headIdx
        else true

-- ============================================================================
-- Example: Declarative vs Interrogative Trees
-- ============================================================================

private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev can := Fragments.English.FunctionWords.can.toWord
private abbrev sleep := Fragments.English.Predicates.Verbal.sleep.toWordPl

/-- "John can sleep" - declarative (subject left of aux)
    John ←subj─ can ─aux→ sleep
-/
def johnCanSleepTree : DepTree :=
  { words := [john, can, sleep]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .aux⟩]
    rootIdx := 1 }

/-- "Can John sleep?" - interrogative (subject right of aux)
    can ─subj→ John
     └──aux→ sleep
-/
def canJohnSleepTree : DepTree :=
  { words := [can, john, sleep]
    deps := [⟨0, 1, .nsubj⟩, ⟨0, 2, .aux⟩]
    rootIdx := 0 }

-- Check argument structure satisfaction
#eval satisfiesArgStr johnCanSleepTree 1 argStr_Aux     -- true (subj left)
#eval satisfiesArgStr johnCanSleepTree 1 argStr_AuxInv  -- false (subj should be right)
#eval satisfiesArgStr canJohnSleepTree 0 argStr_AuxInv  -- true (subj right)
#eval satisfiesArgStr canJohnSleepTree 0 argStr_Aux     -- false (subj should be left)

-- ============================================================================
-- Formal Proofs
-- ============================================================================

/-- Auxiliary inversion rule applies to non-inverted auxiliaries -/
theorem aux_inv_applies :
    auxInversionRule.applies lex_can = true := rfl

/-- Auxiliary inversion sets the inv feature -/
theorem aux_inv_sets_inv :
    lex_can_inv.features.inv = true := rfl

/-- Auxiliary inversion moves subject from left to right -/
theorem aux_inv_moves_subj :
    lex_can.argStr.slots.head?.map (·.dir) = some .left ∧
    lex_can_inv.argStr.slots.head?.map (·.dir) = some .right :=
  ⟨rfl, rfl⟩

/-- Passive rule applies to transitive verbs -/
theorem passive_applies :
    passiveRule.applies lex_kicked = true := rfl

/-- Passive rule sets the passive feature -/
theorem passive_sets_passive :
    lex_kicked_passive.features.passive = true := rfl

/-- Passive rule removes object, adds oblique -/
theorem passive_removes_obj :
    (lex_kicked.argStr.slots.any (·.depType == .obj) = true) ∧
    (lex_kicked_passive.argStr.slots.any (·.depType == .obj) = false) ∧
    (lex_kicked_passive.argStr.slots.any (·.depType == .obl) = true) :=
  ⟨rfl, rfl, rfl⟩

/-- Declarative satisfies non-inverted arg structure -/
theorem declarative_argstr :
    satisfiesArgStr johnCanSleepTree 1 argStr_Aux = true := rfl

/-- Declarative does NOT satisfy inverted arg structure -/
theorem declarative_not_inv :
    satisfiesArgStr johnCanSleepTree 1 argStr_AuxInv = false := rfl

/-- Interrogative satisfies inverted arg structure -/
theorem interrogative_argstr :
    satisfiesArgStr canJohnSleepTree 0 argStr_AuxInv = true := rfl

/-- Interrogative does NOT satisfy non-inverted arg structure -/
theorem interrogative_not_decl :
    satisfiesArgStr canJohnSleepTree 0 argStr_Aux = false := rfl

/-- Key theorem: Inversion rule correctly distinguishes declarative from interrogative -/
theorem inversion_distinguishes_clause_types :
    -- Declarative matches non-inverted, not inverted
    (satisfiesArgStr johnCanSleepTree 1 argStr_Aux = true ∧
     satisfiesArgStr johnCanSleepTree 1 argStr_AuxInv = false) ∧
    -- Interrogative matches inverted, not non-inverted
    (satisfiesArgStr canJohnSleepTree 0 argStr_AuxInv = true ∧
     satisfiesArgStr canJohnSleepTree 0 argStr_Aux = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end DepGrammar
