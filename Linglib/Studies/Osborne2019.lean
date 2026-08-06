import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Auxiliaries
import Linglib.Fragments.English.FunctionWords
import Linglib.Syntax.WordGrammar.LexicalRules
import Linglib.Syntax.DependencyGrammar.Formal.Catena

open Morphology (Word)

/-!
# DG Valency Bridge: [osborne-2019]
[tesniere-1959]

Full derivation chain from DG valency theory to subcategorization and
passive contrasts, grounded in the English Fragment lexicon.

Each verb's DG frame is DERIVED from its Fragment entry's `complementType`
field via `complementToArgStr`, not stipulated independently. The DG
analysis then verifies that trees built with these Fragment-derived words
satisfy the corresponding valency frames.

## Derivation Chain

```
Fragment VerbEntry.complementType ← lexical data (sleep=.none, kick=.np, give=.np_np)
    ↓ complementToArgStr
ArgStr frames (argStrV0/VN/VNN) → Tree.frames premises
    ↓
Tree instances ← concrete parse trees
    ↓
satisfiesArgStr / checkVerbSubcat ← frame satisfaction + subcat verification
    ↓
passiveRule (LexRule) ← valency change derivation
    ↓
isCatena / isConstituent ← structural analysis (Ch 4)
    ↓
grammaticality contrasts ← predictions for the example sentences
```

-/

namespace Osborne2019


open DependencyGrammar WordGrammar Catena

-- ============================================================================
-- §1: Words from the Fragment Lexicon
-- Each frame is DERIVED from a VerbEntry's complementType, not stipulated.
-- ============================================================================

-- Nouns (from Fragments/English/Nouns.lean)
private abbrev john := English.Nouns.john.toWordSg
private abbrev mary := English.Nouns.mary.toWordSg
private abbrev ball := English.Nouns.ball.toWordSg
private abbrev book := English.Nouns.book.toWordSg
private abbrev pizza := English.Nouns.pizza.toWordSg

-- Determiner, auxiliary, preposition (from Fragments/English/)
private abbrev the_ := Word.mk' English.Determiners.the.form .DET
private abbrev was_ := English.Auxiliaries.was.toWord
private abbrev by_ := English.FunctionWords.by_.toWord

-- Active verbs in 3sg present (valence from Fragment complementType)
private abbrev sleeps := English.Predicates.Verbal.sleep.toWord3sg
private abbrev devours := English.Predicates.Verbal.devour.toWord3sg
private abbrev gives := English.Predicates.Verbal.give.toWord3sg

-- Active "kicked" in past tense (valence derived from Fragment complementType)
private abbrev kicked := English.Predicates.Verbal.kick.toWordPast

-- Passive "kicked" (past participle + passive valence change)
private abbrev kicked_pass := English.Predicates.Verbal.kick.toWordPassive

/-- "kicked" - transitive verb as a DG lexical entry.
    Features derived from Fragment kick.toWordPast. -/
private def lex_kicked : LexEntry :=
  { form := kicked.form
    cat := .VERB
    features := kicked.features
    argStr := argStrVN }

-- ============================================================================
-- §2: Fragment Grounding Theorems
-- The Fragment's complementType determines the DG frame.
-- ============================================================================

/-- sleep.complementType =.none → intransitive frame (V0). -/
theorem sleep_frame_from_fragment :
    complementToArgStr English.Predicates.Verbal.sleep.complementType = some argStrV0 := rfl

/-- devour.complementType =.np → transitive frame (VN). -/
theorem devour_frame_from_fragment :
    complementToArgStr English.Predicates.Verbal.devour.complementType = some argStrVN := rfl

/-- give.complementType =.np_np → ditransitive frame (VNN). -/
theorem give_frame_from_fragment :
    complementToArgStr English.Predicates.Verbal.give.complementType = some argStrVNN := rfl

/-- kick.complementType =.np → transitive frame (VN, active). -/
theorem kick_frame_from_fragment :
    complementToArgStr English.Predicates.Verbal.kick.complementType = some argStrVN := rfl

/-- The passive frame carried on `passiveTree.frames` is consistent with the
    passive rule: the rule removes the obj slot from kick's transitive frame. -/
theorem passive_valence_consistent :
    complementToArgStr English.Predicates.Verbal.kick.complementType = some argStrVN ∧
    passiveRule.applies lex_kicked = true ∧
    (passiveRule.transform lex_kicked).argStr.any (·.depType == .obj) = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §3: Grammatical Trees
-- ============================================================================

/-- SV fixture: subject → verb. -/
private def mkSVTree (subj verb : Word) (frame : Option ArgStr := none) : Tree :=
  { words := [subj, verb]
    deps := [⟨1, 0, .nsubj⟩]
    rootIdx := 1
    frames := [none, frame] }

/-- SVO fixture: subject → verb ← object. -/
private def mkSVOTree (subj verb obj : Word) (frame : Option ArgStr := none) : Tree :=
  { words := [subj, verb, obj]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1
    frames := [none, frame, none] }

/-- Ditransitive fixture: subj → verb ← iobj, obj. -/
private def mkDitransTree (subj verb iobj obj : Word) (frame : Option ArgStr := none) : Tree :=
  { words := [subj, verb, iobj, obj]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .iobj⟩, ⟨1, 3, .obj⟩]
    rootIdx := 1
    frames := [none, frame, none, none] }

/-- "John sleeps" — intransitive, no object. -/
def intransTree :=
  mkSVTree john sleeps (complementToArgStr English.Predicates.Verbal.sleep.complementType)

/-- "John devours pizza" — transitive with object. -/
def transTree :=
  mkSVOTree john devours pizza (complementToArgStr English.Predicates.Verbal.devour.complementType)

/-- "John gives Mary book" — ditransitive with two objects. -/
def ditransTree :=
  mkDitransTree john gives mary book
    (complementToArgStr English.Predicates.Verbal.give.complementType)

/-- "John kicked the ball" — active transitive (for passive derivation). -/
def activeTree : Tree :=
  { words := [john, kicked, the_, ball]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .obj⟩, ⟨3, 2, .det⟩]
    rootIdx := 1
    frames := [none, complementToArgStr English.Predicates.Verbal.kick.complementType,
               none, none] }

/-- "The ball was kicked" — short passive; the passive analysis derives
    `argStrVPassive` from kick's transitive frame (`passive_frame_matches`). -/
def passiveTree : Tree :=
  { words := [the_, ball, was_, kicked_pass]
    deps := [⟨1, 0, .det⟩, ⟨3, 1, .nsubj⟩, ⟨3, 2, .auxPass⟩]
    rootIdx := 3
    frames := [none, none, none, some argStrVPassive] }

/-- "The ball was kicked by John" — long passive with agent by-phrase. -/
def longPassiveTree : Tree :=
  { words := [the_, ball, was_, kicked_pass, by_, john]
    deps := [⟨1, 0, .det⟩, ⟨3, 1, .nsubj⟩, ⟨3, 2, .auxPass⟩,
             ⟨3, 5, .obl⟩, ⟨5, 4, .case_⟩]
    rootIdx := 3
    frames := [none, none, none, some argStrVPassive, none, none] }

-- ============================================================================
-- §4: Ungrammatical Trees
-- ============================================================================

/-- "*John sleeps book" — intransitive with spurious object. -/
def intrans_with_obj : Tree :=
  { words := [john, sleeps, book]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1
    frames := [none, complementToArgStr English.Predicates.Verbal.sleep.complementType,
               none] }

/-- "*John devours" — transitive missing required object. -/
def trans_no_obj :=
  mkSVTree john devours (complementToArgStr English.Predicates.Verbal.devour.complementType)

/-- "*John gives Mary" — ditransitive missing direct object. -/
def ditrans_no_obj : Tree :=
  { words := [john, gives, mary]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .iobj⟩]
    rootIdx := 1
    frames := [none, complementToArgStr English.Predicates.Verbal.give.complementType,
               none] }

/-- "*The ball was kicked the ball" — passive with spurious object. -/
def passive_with_obj : Tree :=
  { words := [the_, ball, was_, kicked_pass, the_, ball]
    deps := [⟨1, 0, .det⟩, ⟨3, 1, .nsubj⟩, ⟨3, 2, .auxPass⟩,
             ⟨3, 5, .obj⟩, ⟨5, 4, .det⟩]
    rootIdx := 3
    frames := [none, none, none, some argStrVPassive, none, none] }

-- ============================================================================
-- LEVEL 1: Valency Frame Satisfaction
-- [osborne-2019]: each verb selects a specific argument frame
-- ============================================================================

/-- Intransitive tree satisfies intransitive frame (V0). -/
theorem intrans_satisfies_V0 :
    satisfiesArgStr intransTree 1 argStrV0 = true := rfl

/-- Transitive tree satisfies transitive frame (VN). -/
theorem trans_satisfies_VN :
    satisfiesArgStr transTree 1 argStrVN = true := rfl

/-- Ditransitive tree satisfies ditransitive frame (VNN). -/
theorem ditrans_satisfies_VNN :
    satisfiesArgStr ditransTree 1 argStrVNN = true := rfl

-- Cross-frame mismatches: wrong frame → fails

/-- Intransitive tree does NOT satisfy transitive frame (missing obj). -/
theorem intrans_not_VN :
    satisfiesArgStr intransTree 1 argStrVN = false := rfl

/-- Transitive-minus-object tree does NOT satisfy transitive frame. -/
theorem trans_noobj_not_VN :
    satisfiesArgStr trans_no_obj 1 argStrVN = false := rfl

-- ============================================================================
-- LEVEL 2: Subcategorization Verification
-- checkVerbSubcat validates each verb against its Fragment-derived frame
-- ============================================================================

-- Grammatical trees pass
theorem intrans_subcat_ok : checkVerbSubcat intransTree = true := rfl
theorem trans_subcat_ok : checkVerbSubcat transTree = true := rfl
theorem ditrans_subcat_ok : checkVerbSubcat ditransTree = true := rfl

-- Ungrammatical trees fail
theorem intrans_obj_subcat_fail : checkVerbSubcat intrans_with_obj = false := rfl
theorem trans_noobj_subcat_fail : checkVerbSubcat trans_no_obj = false := rfl
theorem ditrans_noobj_subcat_fail : checkVerbSubcat ditrans_no_obj = false := rfl

-- ============================================================================
-- LEVEL 3: Passive Lexical Rule Derivation
-- [osborne-2019]: passive changes valency
-- ============================================================================

/-- The passive rule applies to transitive "kicked". -/
theorem passive_applies_to_kicked :
    passiveRule.applies lex_kicked = true := rfl

/-- The derived entry removes the obj slot and adds optional obl. -/
theorem passive_removes_obj_adds_obl :
    (passiveRule.transform lex_kicked).argStr.any (·.depType == .obj) = false ∧
    (passiveRule.transform lex_kicked).argStr.any (·.depType == .obl) = true :=
  ⟨rfl, rfl⟩

/-- The passive rule output matches argStrVPassive. -/
theorem passive_frame_matches :
    (passiveRule.transform lex_kicked).argStr =
    argStrVPassive := by native_decide

-- Passive trees validate
theorem passive_subcat_ok : checkVerbSubcat passiveTree = true := rfl
theorem long_passive_subcat_ok : checkVerbSubcat longPassiveTree = true := rfl
theorem passive_obj_subcat_fail : checkVerbSubcat passive_with_obj = false := rfl

-- Passive frame satisfaction
theorem passive_satisfies_VPassive :
    satisfiesArgStr passiveTree 3 argStrVPassive = true := rfl

theorem long_passive_satisfies_VPassive :
    satisfiesArgStr longPassiveTree 3 argStrVPassive = true := rfl

-- ============================================================================
-- LEVEL 4: Catena vs Constituent Analysis
-- [osborne-2019]: verb + ALL args = constituent;
--                        verb + SUBSET = catena (not constituent)
-- ============================================================================

/-- SVO tree: verb + all args {0, 1, 2} is a constituent (complete subtree). -/
theorem svo_complete_is_constituent :
    isConstituent transTree.deps 3 [0, 1, 2] = true := by native_decide

/-- SVO tree: verb + subject {0, 1} is a catena (connected via nsubj). -/
theorem svo_verb_subj_is_catena :
    isCatena transTree.deps [0, 1] = true := by native_decide

/-- SVO tree: verb + subject {0, 1} is NOT a constituent (missing obj). -/
theorem svo_verb_subj_not_constituent :
    isConstituent transTree.deps 3 [0, 1] = false := by native_decide

/-- Ditransitive: verb + all args {0, 1, 2, 3} is a constituent. -/
theorem ditrans_complete_is_constituent :
    isConstituent ditransTree.deps 4 [0, 1, 2, 3] = true := by native_decide

/-- Ditransitive: verb + just obj {1, 3} is a catena but not constituent. -/
theorem ditrans_verb_obj_catena_not_constituent :
    isCatena ditransTree.deps [1, 3] = true ∧
    isConstituent ditransTree.deps 4 [1, 3] = false := by
  constructor <;> native_decide

-- ============================================================================
-- LEVEL 5: Complete Derivation Chain
-- Fragment → DG theory → lexical rule → tree → prediction
-- ============================================================================

/-- **Full valency derivation chain**: from Fragment lexicon through DG
    theory to grammaticality predictions.

    1. Fragment kick.complementType =.np → transitive frame (argStrVN)
    2. Active tree satisfies transitive frame (argStrVN) ✓
    3. checkVerbSubcat validates the active tree ✓
    4. Passive rule applies and removes obj slot ✓
    5. Passive tree satisfies derived frame (argStrVPassive) ✓
    6. checkVerbSubcat validates the passive tree ✓
    7. Passive + spurious obj correctly rejected ✗ -/
theorem valency_derivation_chain :
    -- Fragment grounding
    complementToArgStr English.Predicates.Verbal.kick.complementType = some argStrVN ∧
    -- Active: frame ✓, subcat ✓
    satisfiesArgStr activeTree 1 argStrVN = true ∧
    checkVerbSubcat activeTree = true ∧
    -- Passive rule applies, removes obj
    passiveRule.applies lex_kicked = true ∧
    (passiveRule.transform lex_kicked).argStr.any (·.depType == .obj) = false ∧
    -- Passive tree: derived frame ✓, subcat ✓
    satisfiesArgStr passiveTree 3 argStrVPassive = true ∧
    checkVerbSubcat passiveTree = true ∧
    -- Passive with obj: correctly rejected
    checkVerbSubcat passive_with_obj = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- LEVEL 6: Grammaticality Contrasts
-- ============================================================================

/-- DG subcategorization predictions capture the textbook contrasts:

    | Grammatical          | Ungrammatical         | Frame      |
    |---------------------|-----------------------|------------|
    | "John sleeps"       | "*John sleeps book"   | argStrV0  |
    | "John devours pizza"| "*John devours"       | argStrVN  |
    | "John gives Mary …" | "*John gives Mary"    | argStrVNN | -/
theorem subcategorization_contrasts :
    checkVerbSubcat intransTree = true ∧
    checkVerbSubcat intrans_with_obj = false ∧
    checkVerbSubcat transTree = true ∧
    checkVerbSubcat trans_no_obj = false ∧
    checkVerbSubcat ditransTree = true ∧
    checkVerbSubcat ditrans_no_obj = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- DG passive prediction captures the contrast
    "the ball was kicked" / "*the ball was kicked the ball". -/
theorem passive_contrasts :
    checkVerbSubcat passiveTree = true ∧
    checkVerbSubcat passive_with_obj = false :=
  ⟨rfl, rfl⟩

/-
## Summary

```
Fragments/English/Predicates/Verbal
    sleep.complementType =.none → argStrV0
    devour.complementType =.np → argStrVN
    kick.complementType =.np → argStrVN
    give.complementType =.np_np → argStrVNN
        ↓ VerbEntry.toWord3sg / complementToArgStr
Tree instances (trees carry Fragment-derived frames)
        ↓ satisfiesArgStr / checkVerbSubcat
grammatical ✓ / ungrammatical ✗
        ↓ passiveRule.transform
obj removed → argStrVPassive surface frame
```

Each level is independently verifiable by `rfl` or `native_decide`.
The chain is cumulative: changing a Fragment verb's `complementType`
propagates through frames, trees, verification, and breaks exactly
the affected theorems.
-/

end Osborne2019
