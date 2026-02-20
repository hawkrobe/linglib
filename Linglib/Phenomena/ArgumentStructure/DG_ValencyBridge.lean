import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.Syntax.DependencyGrammar.Core.LexicalRules
import Linglib.Theories.Syntax.DependencyGrammar.Formal.Catena
import Linglib.Phenomena.ArgumentStructure.Subcategorization
import Linglib.Phenomena.ArgumentStructure.Passive

/-!
# DG Valency Bridge: Osborne (2019, Ch 6) @cite{osborne-2019}

Full derivation chain from DG valency theory to argument structure
phenomena, grounded in the English Fragment lexicon.

## Three-Way Connection

```
Fragments/English/Predicates/Verbal   (complementType → valence)
    ↓                                    ↑
DG ArgStr / LexRule / checkVerbSubcat   ↔   Phenomena/ArgumentStructure data
```

Verb valence is DERIVED from each Fragment entry's `complementType` field
via `complementToValence`, not stipulated independently. The DG analysis
then verifies that trees built with these Fragment-derived words satisfy
the corresponding valency frames.

## Derivation Chain

```
Fragment VerbEntry.complementType      ← lexical data (sleep=.none, kick=.np, give=.np_np)
    ↓  complementToValence
VerbEntry.toWord3sg.features.valence   ← intransitive / transitive / ditransitive
    ↓
DepTree instances                      ← concrete parse trees
    ↓
satisfiesArgStr (ArgStr frames)        ← frame satisfaction
    ↓
checkVerbSubcat                        ← subcategorization verification
    ↓
passiveRule (LexRule)                   ← valency change derivation
    ↓
isCatena / isConstituent               ← structural analysis (Ch 4)
    ↓
Phenomena data match                   ← grammaticality predictions
```

## References

- Osborne, T. (2019). *A Dependency Grammar of English*, Ch 6: Valency.
  Amsterdam: John Benjamins.
- Tesnière, L. (1959). *Éléments de syntaxe structurale*. Paris: Klincksieck.
-/

namespace DepGrammar.ValencyBridge

open DepGrammar Catena

-- ============================================================================
-- §1: Words from the Fragment Lexicon
-- Valence is DERIVED from each VerbEntry's complementType, not stipulated.
-- ============================================================================

-- Nouns (from Fragments/English/Nouns.lean)
private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev mary := Fragments.English.Nouns.mary.toWordSg
private abbrev ball := Fragments.English.Nouns.ball.toWordSg
private abbrev book := Fragments.English.Nouns.book.toWordSg
private abbrev pizza := Fragments.English.Nouns.pizza.toWordSg

-- Determiner, auxiliary, preposition (from Fragments/English/)
private abbrev the_ := Fragments.English.Determiners.the.toWord
private abbrev was_ := Fragments.English.FunctionWords.was.toWord
private abbrev by_ := Fragments.English.FunctionWords.by_.toWord

-- Active verbs in 3sg present (valence from Fragment complementType)
private abbrev sleeps := Fragments.English.Predicates.Verbal.sleep.toWord3sg
private abbrev devours := Fragments.English.Predicates.Verbal.devour.toWord3sg
private abbrev gives := Fragments.English.Predicates.Verbal.give.toWord3sg

-- Active "kicked" in past tense (valence derived from Fragment complementType)
private abbrev kicked := Fragments.English.Predicates.Verbal.kick.toWordPast

-- Passive "kicked" (past participle + passive valence change)
private abbrev kicked_pass := Fragments.English.Predicates.Verbal.kick.toWordPastPart.asPassive

-- ============================================================================
-- §2: Fragment Grounding Theorems
-- The Fragment's complementType determines the DG valence.
-- ============================================================================

/-- sleep.complementType = .none → intransitive. -/
theorem sleep_valence_from_fragment :
    sleeps.features.valence = some .intransitive := rfl

/-- devour.complementType = .np → transitive. -/
theorem devour_valence_from_fragment :
    devours.features.valence = some .transitive := rfl

/-- give.complementType = .np_np → ditransitive. -/
theorem give_valence_from_fragment :
    gives.features.valence = some .ditransitive := rfl

/-- kick.complementType = .np → transitive (active). -/
theorem kick_valence_from_fragment :
    kicked.features.valence = some .transitive := rfl

/-- The passive valence (intransitive) is consistent with the passive rule:
    the rule removes the obj slot from the transitive frame. -/
theorem passive_valence_consistent :
    kicked_pass.features.valence = some .intransitive ∧
    kicked.features.valence = some .transitive ∧
    passiveRule.applies lex_kicked = true ∧
    (passiveRule.transform lex_kicked).argStr.slots.any (·.depType == .obj) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §3: Grammatical Trees
-- ============================================================================

/-- "John sleeps" — intransitive, no object.
    Matches `Subcategorization.data` pair 1. -/
def intransTree := mkSVTree john sleeps

/-- "John devours pizza" — transitive with object.
    Matches `Subcategorization.data` pair 3. -/
def transTree := mkSVOTree john devours pizza

/-- "John gives Mary book" — ditransitive with two objects.
    Matches `Subcategorization.data` pair 5. -/
def ditransTree := mkDitransTree john gives mary book

/-- "John kicked the ball" — active transitive (for passive derivation). -/
def activeTree : DepTree :=
  { words := [john, kicked, the_, ball]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .obj⟩, ⟨3, 2, .det⟩]
    rootIdx := 1 }

/-- "The ball was kicked" — short passive.
    Matches `Passive.data` pair 1. -/
def passiveTree : DepTree :=
  { words := [the_, ball, was_, kicked_pass]
    deps := [⟨1, 0, .det⟩, ⟨3, 1, .nsubj⟩, ⟨3, 2, .auxPass⟩]
    rootIdx := 3 }

/-- "The ball was kicked by John" — long passive with agent by-phrase. -/
def longPassiveTree : DepTree :=
  { words := [the_, ball, was_, kicked_pass, by_, john]
    deps := [⟨1, 0, .det⟩, ⟨3, 1, .nsubj⟩, ⟨3, 2, .auxPass⟩,
             ⟨3, 5, .obl⟩, ⟨5, 4, .case_⟩]
    rootIdx := 3 }

-- ============================================================================
-- §4: Ungrammatical Trees
-- ============================================================================

/-- "*John sleeps book" — intransitive with spurious object.
    Matches `Subcategorization.data` pair 1. -/
def intrans_with_obj : DepTree :=
  { words := [john, sleeps, book]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1 }

/-- "*John devours" — transitive missing required object.
    Matches `Subcategorization.data` pair 3. -/
def trans_no_obj := mkSVTree john devours

/-- "*John gives Mary" — ditransitive missing direct object.
    Matches `Subcategorization.data` pair 5. -/
def ditrans_no_obj : DepTree :=
  { words := [john, gives, mary]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .iobj⟩]
    rootIdx := 1 }

/-- "*The ball was kicked the ball" — passive with spurious object.
    Matches `Passive.data` pair 1. -/
def passive_with_obj : DepTree :=
  { words := [the_, ball, was_, kicked_pass, the_, ball]
    deps := [⟨1, 0, .det⟩, ⟨3, 1, .nsubj⟩, ⟨3, 2, .auxPass⟩,
             ⟨3, 5, .obj⟩, ⟨5, 4, .det⟩]
    rootIdx := 3 }

-- ============================================================================
-- LEVEL 1: Valency Frame Satisfaction
-- Osborne (2019, Ch 6): each verb selects a specific argument frame
-- ============================================================================

/-- Intransitive tree satisfies intransitive frame (V0). -/
theorem intrans_satisfies_V0 :
    satisfiesArgStr intransTree 1 argStr_V0 = true := rfl

/-- Transitive tree satisfies transitive frame (VN). -/
theorem trans_satisfies_VN :
    satisfiesArgStr transTree 1 argStr_VN = true := rfl

/-- Ditransitive tree satisfies ditransitive frame (VNN). -/
theorem ditrans_satisfies_VNN :
    satisfiesArgStr ditransTree 1 argStr_VNN = true := rfl

-- Cross-frame mismatches: wrong frame → fails

/-- Intransitive tree does NOT satisfy transitive frame (missing obj). -/
theorem intrans_not_VN :
    satisfiesArgStr intransTree 1 argStr_VN = false := rfl

/-- Transitive-minus-object tree does NOT satisfy transitive frame. -/
theorem trans_noobj_not_VN :
    satisfiesArgStr trans_no_obj 1 argStr_VN = false := rfl

-- ============================================================================
-- LEVEL 2: Subcategorization Verification
-- checkVerbSubcat validates each verb against its Fragment-derived valence
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
-- Osborne (2019, Ch 6 §6.7): passive changes valency
-- ============================================================================

/-- The passive rule applies to transitive "kicked". -/
theorem passive_applies_to_kicked :
    passiveRule.applies lex_kicked = true := rfl

/-- The derived entry removes the obj slot and adds optional obl. -/
theorem passive_removes_obj_adds_obl :
    (passiveRule.transform lex_kicked).argStr.slots.any (·.depType == .obj) = false ∧
    (passiveRule.transform lex_kicked).argStr.slots.any (·.depType == .obl) = true :=
  ⟨rfl, rfl⟩

/-- The passive rule output matches argStr_VPassive. -/
theorem passive_frame_matches :
    (passiveRule.transform lex_kicked).argStr.slots =
    argStr_VPassive.slots := by native_decide

-- Passive trees validate
theorem passive_subcat_ok : checkVerbSubcat passiveTree = true := rfl
theorem long_passive_subcat_ok : checkVerbSubcat longPassiveTree = true := rfl
theorem passive_obj_subcat_fail : checkVerbSubcat passive_with_obj = false := rfl

-- Passive frame satisfaction
theorem passive_satisfies_VPassive :
    satisfiesArgStr passiveTree 3 argStr_VPassive = true := rfl

theorem long_passive_satisfies_VPassive :
    satisfiesArgStr longPassiveTree 3 argStr_VPassive = true := rfl

-- ============================================================================
-- LEVEL 4: Catena vs Constituent Analysis
-- Osborne (2019, Ch 4): verb + ALL args = constituent;
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

    1. Fragment kick.complementType = .np → valence = transitive
    2. Active tree satisfies transitive frame (argStr_VN) ✓
    3. checkVerbSubcat validates the active tree ✓
    4. Passive rule applies and removes obj slot ✓
    5. Passive tree satisfies derived frame (argStr_VPassive) ✓
    6. checkVerbSubcat validates the passive tree ✓
    7. Passive + spurious obj correctly rejected ✗ -/
theorem valency_derivation_chain :
    -- Fragment grounding
    kicked.features.valence = some .transitive ∧
    -- Active: frame ✓, subcat ✓
    satisfiesArgStr activeTree 1 argStr_VN = true ∧
    checkVerbSubcat activeTree = true ∧
    -- Passive rule applies, removes obj
    passiveRule.applies lex_kicked = true ∧
    (passiveRule.transform lex_kicked).argStr.slots.any (·.depType == .obj) = false ∧
    -- Passive tree: derived frame ✓, subcat ✓
    satisfiesArgStr passiveTree 3 argStr_VPassive = true ∧
    checkVerbSubcat passiveTree = true ∧
    -- Passive with obj: correctly rejected
    checkVerbSubcat passive_with_obj = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- LEVEL 6: Bridge to Phenomena Data
-- ============================================================================

/-- DG subcategorization predictions match all data pairs in
    `Phenomena.ArgumentStructure.Subcategorization.data`:

    | Data pair | Grammatical          | Ungrammatical         | Valence      |
    |-----------|---------------------|-----------------------|--------------|
    | 1         | "John sleeps"       | "*John sleeps book"   | intransitive |
    | 3         | "John devours pizza"| "*John devours"       | transitive   |
    | 5         | "John gives Mary …" | "*John gives Mary"    | ditransitive | -/
theorem subcategorization_data_match :
    checkVerbSubcat intransTree = true ∧
    checkVerbSubcat intrans_with_obj = false ∧
    checkVerbSubcat transTree = true ∧
    checkVerbSubcat trans_no_obj = false ∧
    checkVerbSubcat ditransTree = true ∧
    checkVerbSubcat ditrans_no_obj = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- DG passive predictions match `Phenomena.ArgumentStructure.Passive.data`:

    | Data pair | Grammatical             | Ungrammatical                    |
    |-----------|------------------------|----------------------------------|
    | 1         | "the ball was kicked"  | "*the ball was kicked the ball"  | -/
theorem passive_data_match :
    checkVerbSubcat passiveTree = true ∧
    checkVerbSubcat passive_with_obj = false :=
  ⟨rfl, rfl⟩

/-
## Summary: Three-Way Connection

```
Fragments/English/Predicates/Verbal
    sleep.complementType = .none          →  valence = .intransitive
    devour.complementType = .np           →  valence = .transitive
    kick.complementType = .np             →  valence = .transitive
    give.complementType = .np_np          →  valence = .ditransitive
        ↓  VerbEntry.toWord3sg / complementToValence
DepTree instances (words carry Fragment-derived valence)
        ↓  satisfiesArgStr
argStr_V0 / argStr_VN / argStr_VNN / argStr_VPassive
        ↓  checkVerbSubcat
grammatical ✓  /  ungrammatical ✗
        ↓  passiveRule.transform
obj removed → intransitive surface valence
        ↓  matches
Phenomena.ArgumentStructure.Subcategorization.data
Phenomena.ArgumentStructure.Passive.data
```

Each level is independently verifiable by `rfl` or `native_decide`.
The chain is cumulative: changing a Fragment verb's `complementType`
propagates through valence, trees, verification, and breaks exactly
the affected theorems.
-/

end DepGrammar.ValencyBridge
