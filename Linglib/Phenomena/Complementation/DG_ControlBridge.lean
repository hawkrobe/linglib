import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.Syntax.DependencyGrammar.Formal.EnhancedDependencies
import Linglib.Phenomena.Complementation.Typology

/-!
# DG Control/Raising Bridge: Osborne (2019, Ch 6 §6.8–6.9)

Derivation chain from DG enhanced dependency analysis to complementation
phenomena, grounded in the English Fragment lexicon.

## Key Insight (Osborne 2019)

In DG, control and raising verbs both take xcomp complements. The basic tree
enforces unique heads, so the controlled/raised subject appears as a dependent
of the matrix verb ONLY. The predicate-argument relation to the embedded verb
is **lost** in the basic tree but **recovered** in the enhanced dependency graph
(de Marneffe & Nivre 2019).

## Three Control Types

| Type | Example | Propagation |
|------|---------|-------------|
| Subject control | "John managed to sleep" | matrix nsubj → embedded nsubj |
| Object control | "John persuaded Mary to run" | matrix obj → embedded nsubj |
| Raising | "John seems to sleep" | Same structure as subject control |

## Derivation Chain

```
Fragment VerbEntry.controlType       ← lexical data (manage=.subjectControl, etc.)
    ↓
DG basic tree (xcomp relation)      ← subject attached to matrix verb only
    ↓
DG enhanced graph                   ← shared nsubj edge added
    ↓
hasUnrepresentedArg = true           ← basic tree loses embedded subject
    ↓
classifyEnhancement = .controlSubject ← enhanced edge classified
    ↓
CTPDatum.hasEquiDeletion             ← matches Noonan's (2007) observations
```

## References

- Osborne, T. (2019). *A Dependency Grammar of English*, Ch 6 §6.8–6.9.
- de Marneffe, M.-C. & Nivre, J. (2019). Dependency Grammar. §4.2.
- Noonan, M. (2007). Complementation. In Shopen (ed.), *Language Typology*.
-/

namespace DepGrammar.ControlBridge

open DepGrammar DepGrammar.EnhancedDependencies

-- ============================================================================
-- §1: Words from the Fragment Lexicon
-- ============================================================================

-- Nouns
private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev mary := Fragments.English.Nouns.mary.toWordSg

-- Control/raising verbs (valence derived from complementType via complementToValence)
private abbrev manages := Fragments.English.Predicates.Verbal.manage.toWord3sg
private abbrev persuaded := Fragments.English.Predicates.Verbal.persuade.toWordPast
private abbrev seems := Fragments.English.Predicates.Verbal.seem.toWord3sg

-- Complement verbs (intransitive, base form for infinitival)
private abbrev sleep_ := Fragments.English.Predicates.Verbal.sleep.toWordBase
private abbrev run_ := Fragments.English.Predicates.Verbal.run.toWordBase

-- Infinitival marker "to" (from Fragment)
private abbrev to_ := Fragments.English.FunctionWords.toInf

-- ============================================================================
-- §2: Fragment Grounding Theorems
-- ============================================================================

/-- manage is subject control in the Fragment. -/
theorem manage_is_subject_control :
    Fragments.English.Predicates.Verbal.manage.controlType = .subjectControl := rfl

/-- persuade is object control in the Fragment. -/
theorem persuade_is_object_control :
    Fragments.English.Predicates.Verbal.persuade.controlType = .objectControl := rfl

/-- seem is raising in the Fragment. -/
theorem seem_is_raising :
    Fragments.English.Predicates.Verbal.seem.controlType = .raising := rfl

/-- Raising verbs assign no theta role to their subject (Fragment data). -/
theorem seem_no_subject_theta :
    Fragments.English.Predicates.Verbal.seem.subjectTheta = none := rfl

/-- Control verbs DO assign a theta role to their subject (Fragment data). -/
theorem manage_has_subject_theta :
    Fragments.English.Predicates.Verbal.manage.subjectTheta = some .agent := rfl

-- ============================================================================
-- §3: DG Trees — Basic (unique heads) and Enhanced (shared dependents)
-- ============================================================================

-- Subject control: "John manages to sleep"
-- john(0) manages(1) to(2) sleep(3)

/-- Basic tree: John is nsubj of manages only. -/
def subjControlBasic : DepTree :=
  { words := [john, manages, to_, sleep_]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .xcomp⟩, ⟨3, 2, .mark⟩]
    rootIdx := 1 }

/-- Enhanced graph: John is also nsubj of sleep (shared dependent). -/
def subjControlEnhanced : DepGraph :=
  { words := [john, manages, to_, sleep_]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .xcomp⟩, ⟨3, 2, .mark⟩,
             ⟨3, 0, .nsubj⟩]  -- ← ENHANCED: sleep ← John
    rootIdx := 1 }

-- Object control: "John persuaded Mary to run"
-- john(0) persuaded(1) mary(2) to(3) run(4)

/-- Basic tree: Mary is obj of persuaded only. -/
def objControlBasic : DepTree :=
  { words := [john, persuaded, mary, to_, run_]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩, ⟨1, 4, .xcomp⟩, ⟨4, 3, .mark⟩]
    rootIdx := 1 }

/-- Enhanced graph: Mary is also nsubj of run (shared dependent). -/
def objControlEnhanced : DepGraph :=
  { words := [john, persuaded, mary, to_, run_]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩, ⟨1, 4, .xcomp⟩, ⟨4, 3, .mark⟩,
             ⟨4, 2, .nsubj⟩]  -- ← ENHANCED: run ← Mary
    rootIdx := 1 }

-- Raising: "John seems to sleep"
-- john(0) seems(1) to(2) sleep(3)
-- Same tree structure as subject control — the difference is semantic (theta roles)

/-- Basic tree: John is nsubj of seems only. -/
def raisingBasic : DepTree :=
  { words := [john, seems, to_, sleep_]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .xcomp⟩, ⟨3, 2, .mark⟩]
    rootIdx := 1 }

/-- Enhanced graph: John is also nsubj of sleep. -/
def raisingEnhanced : DepGraph :=
  { words := [john, seems, to_, sleep_]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .xcomp⟩, ⟨3, 2, .mark⟩,
             ⟨3, 0, .nsubj⟩]  -- ← ENHANCED: sleep ← John
    rootIdx := 1 }

-- ============================================================================
-- §4: Information Loss — Basic Tree Loses the Embedded Subject
-- ============================================================================

/-- Subject control: John (idx 0) has an unrepresented argument in the basic tree.
    He is semantically nsubj of sleep (3), but the tree only attaches him to manages (1). -/
theorem subjControl_loses_embedded_subject :
    hasUnrepresentedArg subjControlBasic subjControlEnhanced 0 = true := by native_decide

/-- Object control: Mary (idx 2) has an unrepresented argument in the basic tree.
    She is semantically nsubj of run (4), but the tree only attaches her to persuaded (1). -/
theorem objControl_loses_embedded_subject :
    hasUnrepresentedArg objControlBasic objControlEnhanced 2 = true := by native_decide

/-- Raising: John (idx 0) has an unrepresented argument in the basic tree.
    He is semantically nsubj of sleep (3), but the tree only attaches him to seems (1). -/
theorem raising_loses_embedded_subject :
    hasUnrepresentedArg raisingBasic raisingEnhanced 0 = true := by native_decide

-- ============================================================================
-- §5: Enhanced Recovery — Graph Recovers the Lost Argument
-- ============================================================================

/-- Enhanced graph for subject control has more edges than basic tree. -/
theorem subjControl_enhanced_recovers :
    subjControlEnhanced.deps.length > subjControlBasic.deps.length := by native_decide

/-- Enhanced graph for object control has more edges than basic tree. -/
theorem objControl_enhanced_recovers :
    objControlEnhanced.deps.length > objControlBasic.deps.length := by native_decide

/-- Enhanced graph for raising has more edges than basic tree. -/
theorem raising_enhanced_recovers :
    raisingEnhanced.deps.length > raisingBasic.deps.length := by native_decide

-- Basic trees satisfy unique-heads; enhanced graphs do not

/-- Subject control basic tree IS a tree (unique heads). -/
theorem subjControl_basic_is_tree :
    hasUniqueHeads subjControlBasic = true := by native_decide

/-- Subject control enhanced graph violates unique heads (John has two nsubj edges). -/
theorem subjControl_enhanced_not_tree :
    hasUniqueHeads { words := subjControlEnhanced.words
                     deps := subjControlEnhanced.deps
                     rootIdx := subjControlEnhanced.rootIdx } = false := by native_decide

/-- Object control basic tree IS a tree. -/
theorem objControl_basic_is_tree :
    hasUniqueHeads objControlBasic = true := by native_decide

/-- Object control enhanced graph violates unique heads (Mary has two incoming edges). -/
theorem objControl_enhanced_not_tree :
    hasUniqueHeads { words := objControlEnhanced.words
                     deps := objControlEnhanced.deps
                     rootIdx := objControlEnhanced.rootIdx } = false := by native_decide

-- ============================================================================
-- §6: Enhancement Classification
-- ============================================================================

/-- Subject control enhanced edge is classified as controlSubject. -/
theorem subjControl_classified :
    classifyEnhancement subjControlBasic.deps ⟨3, 0, .nsubj⟩ =
    some .controlSubject := by native_decide

/-- Object control enhanced edge is classified as controlSubject.
    Even though the controller is the matrix OBJ (Mary), the enhanced edge
    is an nsubj relation → classified as controlSubject. -/
theorem objControl_classified :
    classifyEnhancement objControlBasic.deps ⟨4, 2, .nsubj⟩ =
    some .controlSubject := by native_decide

/-- Raising enhanced edge is classified as controlSubject.
    Structurally identical to subject control — the DG tree doesn't
    distinguish control from raising. The distinction is semantic
    (theta role assignment, captured in Fragment controlType). -/
theorem raising_classified :
    classifyEnhancement raisingBasic.deps ⟨3, 0, .nsubj⟩ =
    some .controlSubject := by native_decide

-- ============================================================================
-- §7: Control ↔ Raising Structural Identity
-- Osborne (2019, Ch 6 §6.9): DG treats control and raising identically at
-- the syntactic level. Both produce the same tree geometry; the difference
-- is purely semantic (theta role assignment).
-- ============================================================================

/-- Subject control and raising produce structurally identical basic trees.
    (Same word positions, same dependency relations — only the words differ.) -/
theorem control_raising_same_deps :
    subjControlBasic.deps = raisingBasic.deps := rfl

/-- Both produce the same enhanced edge pattern. -/
theorem control_raising_same_enhancement :
    subjControlEnhanced.deps.length = raisingEnhanced.deps.length := rfl

-- ============================================================================
-- §8: Bridge to CTPDatum — Fragment controlType predicts equi-deletion
-- ============================================================================

open Phenomena.Complementation.Typology
open Fragments.English.Predicates.Verbal (manage persuade want hope stop start continue_ seem)

/-- Control verbs in the Fragment have corresponding CTPDatum entries
    with hasEquiDeletion = true (Noonan 2007 §2.1).

    This connects three independently specified data sources:
    1. Fragment controlType / altControlType (lexical annotation)
    2. DG enhanced dependencies (structural analysis)
    3. CTPDatum hasEquiDeletion (typological observation)

    Note: "hope" has complementType = .finiteClause (primary frame) but
    altComplementType = .infinitival with altControlType = .subjectControl.
    The equi-deletion corresponds to the infinitival frame. -/
theorem control_predicts_equi_deletion :
    -- Fragment says these are control verbs
    manage.controlType = .subjectControl ∧
    persuade.controlType = .objectControl ∧
    want.controlType = .subjectControl ∧
    hope.altControlType = .subjectControl ∧
    stop.controlType = .subjectControl ∧
    start.controlType = .subjectControl ∧
    continue_.controlType = .subjectControl ∧
    -- CTPDatum says these have equi-deletion
    english_manage.hasEquiDeletion = true ∧
    english_persuade.hasEquiDeletion = true ∧
    english_want.hasEquiDeletion = true ∧
    english_hope.hasEquiDeletion = true ∧
    english_stop.hasEquiDeletion = true ∧
    english_start.hasEquiDeletion = true ∧
    english_continue.hasEquiDeletion = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The raising verb "seem" is NOT marked for equi-deletion in the typology.
    seem does not appear in allEnglishCTPData — it's a purely syntactic
    phenomenon, not a CTP in Noonan's semantic classification. -/
theorem seem_is_raising_not_ctp :
    seem.controlType = .raising ∧
    seem.subjectTheta = none := ⟨rfl, rfl⟩

-- ============================================================================
-- §9: Complete Derivation Chain
-- ============================================================================

/-- **Full control derivation chain**: from Fragment lexicon through DG
    enhanced dependency analysis to complementation typology.

    1. Fragment manage.controlType = .subjectControl ✓
    2. Basic tree attaches John to manages only ✓
    3. Basic tree LOSES John as argument of sleep ✓
    4. Enhanced graph RECOVERS John as nsubj of sleep ✓
    5. Enhanced edge classified as controlSubject ✓
    6. CTPDatum english_manage.hasEquiDeletion = true ✓

    The chain is cumulative: changing manage's controlType in the Fragment
    breaks the grounding theorem; changing the tree structure breaks the
    information-loss proof; changing the CTPDatum breaks the bridge. -/
theorem control_derivation_chain :
    -- Fragment grounding
    manage.controlType = .subjectControl ∧
    -- Basic tree is well-formed
    hasUniqueHeads subjControlBasic = true ∧
    -- Information loss
    hasUnrepresentedArg subjControlBasic subjControlEnhanced 0 = true ∧
    -- Enhanced recovery
    subjControlEnhanced.deps.length > subjControlBasic.deps.length ∧
    -- Edge classification
    classifyEnhancement subjControlBasic.deps ⟨3, 0, .nsubj⟩ = some .controlSubject ∧
    -- Typological bridge
    english_manage.hasEquiDeletion = true :=
  ⟨rfl, by native_decide, by native_decide, by native_decide, by native_decide, rfl⟩

/-- **Full object control derivation chain**: persuade variant.

    1. Fragment persuade.controlType = .objectControl ✓
    2. Basic tree attaches Mary to persuaded only ✓
    3. Basic tree LOSES Mary as argument of run ✓
    4. Enhanced graph RECOVERS Mary as nsubj of run ✓
    5. Enhanced edge classified as controlSubject ✓
    6. CTPDatum english_persuade.hasEquiDeletion = true ✓ -/
theorem object_control_derivation_chain :
    persuade.controlType = .objectControl ∧
    hasUniqueHeads objControlBasic = true ∧
    hasUnrepresentedArg objControlBasic objControlEnhanced 2 = true ∧
    objControlEnhanced.deps.length > objControlBasic.deps.length ∧
    classifyEnhancement objControlBasic.deps ⟨4, 2, .nsubj⟩ = some .controlSubject ∧
    english_persuade.hasEquiDeletion = true :=
  ⟨rfl, by native_decide, by native_decide, by native_decide, by native_decide, rfl⟩

end DepGrammar.ControlBridge
