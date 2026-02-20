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

-- ============================================================================
-- Lexical Entries (derived from Fragment)
-- ============================================================================

/-- "can" - modal auxiliary (non-inverted).
    Features derived from Fragment FunctionWords.can. -/
def lex_can : LexEntry :=
  { form := Fragments.English.FunctionWords.can.toWord.form
    cat := .AUX
    features := Fragments.English.FunctionWords.can.toWord.features
    argStr := argStr_Aux }

/-- "can" - modal auxiliary (inverted, derived) -/
def lex_can_inv : LexEntry :=
  auxInversionRule.transform lex_can

/-- "does" - do-support auxiliary (non-inverted).
    Features derived from Fragment FunctionWords.does. -/
def lex_does : LexEntry :=
  { form := Fragments.English.FunctionWords.does.toWord.form
    cat := .AUX
    features := Fragments.English.FunctionWords.does.toWord.features
    argStr := argStr_Aux }

/-- "kicked" - transitive verb.
    Features derived from Fragment kick.toWordPast. -/
def lex_kicked : LexEntry :=
  { form := Fragments.English.Predicates.Verbal.kick.toWordPast.form
    cat := .VERB
    features := Fragments.English.Predicates.Verbal.kick.toWordPast.features
    argStr := argStr_VN }

/-- "kicked" - passive (derived) -/
def lex_kicked_passive : LexEntry :=
  passiveRule.transform lex_kicked

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

-- ============================================================================
-- Formal Proofs
-- ============================================================================

/-- Auxiliary inversion rule applies to non-inverted auxiliaries -/
theorem aux_inv_applies :
    auxInversionRule.applies lex_can = true := rfl

/-- Auxiliary inversion sets the inv feature -/
theorem aux_inv_sets_inv :
    lex_can_inv.inv = true := rfl

/-- Auxiliary inversion moves subject from left to right -/
theorem aux_inv_moves_subj :
    lex_can.argStr.slots.head?.map (·.dir) = some .left ∧
    lex_can_inv.argStr.slots.head?.map (·.dir) = some .right :=
  ⟨rfl, rfl⟩

/-- Passive rule applies to transitive verbs -/
theorem passive_applies :
    passiveRule.applies lex_kicked = true := rfl

/-- Passive rule sets passive voice -/
theorem passive_sets_voice :
    lex_kicked_passive.features.voice = some Voice.passive := rfl

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

-- ============================================================================
-- Fragment Grounding
-- ============================================================================

/-- lex_kicked's argument structure matches the standard transitive frame,
    and the Fragment's valence maps to that frame via valenceToArgStr. -/
theorem lex_kicked_from_fragment :
    lex_kicked.argStr = argStr_VN ∧
    Fragments.English.Predicates.Verbal.kick.toWordPast.features.valence = some .transitive ∧
    valenceToArgStr .transitive = some argStr_VN :=
  ⟨rfl, rfl, rfl⟩

end DepGrammar
