import Linglib.Theories.Syntax.ConstructionGrammar.Slot
import Linglib.Theories.Syntax.ConstructionGrammar.Studies.FillmoreKayOConnor1988
import Linglib.Theories.Syntax.ConstructionGrammar.Studies.GoldbergShirtz2025

/-!
# Slot/Filler Verification

@cite{dunn-2026} @cite{kay-fillmore-1999} @cite{goldberg-shirtz-2025}

Per-datum verification that `derivedSpecificity` (computed from the typed
slot structure) matches the `Specificity` values stipulated in existing
construction definitions.

Concrete `TypedForm` instantiations for six constructions verify:
1. `abstractionLevel` computes the correct open-slot proportion
2. `derivedSpecificity` agrees with stipulated `Specificity`
3. `ConstructionSlot.toSlot` round-trips through embedding
4. `refGroupCount` and `hasConstraint` detect WXDY's structural properties
5. WXDY coinstantiation: X and Y share refIdx 2 (subject control)
-/

namespace Phenomena.Constructions.Studies.Dunn2026

open ConstructionGrammar

-- ============================================================================
-- § 1. Basic Constructions
-- ============================================================================

/-- Ditransitive typed form: [Subj_NP V Obj1_NP Obj2_NP].

All four slots are open — the construction constrains categories
and roles but not specific lexemes. -/
def ditransitiveForm : TypedForm String :=
  [ { filler := .open_ .NOUN, role := some "agent" }
  , { filler := .open_ .VERB, role := some "predicate", isHead := true }
  , { filler := .open_ .NOUN, role := some "recipient" }
  , { filler := .open_ .NOUN, role := some "theme" } ]

/-- must-VERB typed form: [fixed("must") V N].

"must" is a fixed lexeme; the verb and noun slots are open.
"a must-see movie", "a must-read book". -/
def mustVerbForm : TypedForm String :=
  [ { filler := .fixed "must" }
  , { filler := .open_ .VERB, role := some "predicate", isHead := true }
  , { filler := .open_ .NOUN, role := some "theme" } ]

/-- *Let alone* typed form: [A_NP fixed("let") fixed("alone") B_NP].

Simplified from the full form F⟨X A Y let alone B⟩ to highlight the
fixed/open distinction. "let" and "alone" are fixed; the focus positions
are open. -/
def letAloneForm : TypedForm String :=
  [ { filler := .open_ .NOUN, role := some "focusA" }
  , { filler := .fixed "let" }
  , { filler := .fixed "alone" }
  , { filler := .open_ .NOUN, role := some "focusB" } ]

/-- Veggie-wrap: a fully lexically specified compound (@cite{goldberg-2003}:220). -/
def veggieWrapForm : TypedForm String :=
  [ { filler := .fixed "veggie" }
  , { filler := .fixed "wrap", isHead := true } ]

-- ============================================================================
-- § 2. Abstraction Levels
-- ============================================================================

/-- Ditransitive: 4/4 open slots → abstraction level 1. -/
theorem ditransitive_abstraction :
    abstractionLevel ditransitiveForm = 1 := by native_decide

/-- must-VERB: 2/3 open slots → abstraction level 2/3. -/
theorem mustVerb_abstraction :
    abstractionLevel mustVerbForm = 2 / 3 := by native_decide

/-- *Let alone*: 2/4 open slots → abstraction level 1/2. -/
theorem letAlone_abstraction :
    abstractionLevel letAloneForm = 1 / 2 := by native_decide

/-- Veggie-wrap: 0/2 open slots → abstraction level 0. -/
theorem veggieWrap_abstraction :
    abstractionLevel veggieWrapForm = 0 := by native_decide

-- ============================================================================
-- § 3. Specificity Consistency
-- ============================================================================

/-! These theorems verify that `derivedSpecificity` (computed from slot
structure) matches the `Specificity` values stipulated in the existing
construction definitions. This makes the connection true by verification
rather than by construction. -/

/-- Ditransitive: derived `.fullyAbstract` matches stipulated. -/
theorem ditransitive_specificity_consistent :
    derivedSpecificity ditransitiveForm =
      ditransitive.construction.specificity := by native_decide

/-- *Let alone*: derived `.partiallyOpen` matches stipulated. -/
theorem letAlone_specificity_consistent :
    derivedSpecificity letAloneForm =
      Studies.FillmoreKayOConnor1988.letAloneConstruction.specificity := by
  native_decide

/-- must-VERB: derived `.partiallyOpen` matches stipulated. -/
theorem mustVerb_specificity_consistent :
    derivedSpecificity mustVerbForm =
      Studies.GoldbergShirtz2025.mustVerbConstruction.specificity := by
  native_decide

/-- Veggie-wrap: derived `.lexicallySpecified` (all fixed). -/
theorem veggieWrap_is_lexicallySpecified :
    derivedSpecificity veggieWrapForm = .lexicallySpecified := by native_decide

-- ============================================================================
-- § 4. Embedding Consistency
-- ============================================================================

/-- The ditransitive `TypedForm` matches the existing `ArgStructureConstruction`'s
slots projected through `toTypedForm`. -/
theorem ditransitive_embedding_consistent :
    ditransitive.toTypedForm = ditransitiveForm := by native_decide

-- ============================================================================
-- § 5. WXDY (@cite{kay-fillmore-1999}, Figure 12)
-- ============================================================================

/-! @cite{kay-fillmore-1999} formalize the WXDY construction
    as a hierarchical AVM with valence sets, grammatical functions,
    coreference indices (#1, #2), and feature constraints ([loc -],
    [neg -], [ref ∅]). This flat projection captures the key structural
    properties while losing the nesting.

    **Coinstantiation** (Figure 13, §4.2) is a general construction
    expressing subject control: the matrix subject and the complement's
    subject share a coreference index. WXDY's X–Y coindexation is an
    instance of this pattern. -/

/-- WXDY construction typed form (@cite{kay-fillmore-1999}, Figure 12).

    Flat projection of the hierarchical AVM. The five positions:
    - X (subject of BE): open NP, coindexed with Y via refIdx 2
    - BE (head): auxiliary headed by *be*
    - doing (complement): VP headed by *doing*, cannot be negated
    - what (object of doing): fixed, left-isolated, nonreferential
    - Y (secondary predicate): open, coindexed with X via refIdx 2

    The coindexation (refIdx 2) captures the paper's #2: X is the
    understood subject of Y (coinstantiation / subject control). -/
def wxdyForm : TypedForm String :=
  [ { filler := .open_ .NOUN, role := some "subject", gf := some .subj
    , refIdx := some 2 }
  , { filler := .headed "be" .AUX, isHead := true }
  , { filler := .headed "doing" .VERB, gf := some .comp
    , constraints := [.negMinus] }
  , { filler := .fixed "what", gf := some .obj
    , constraints := [.locMinus, .refEmpty] }
  , { filler := .open_ .X, role := some "predicate", gf := some .pred
    , refIdx := some 2 } ]

/-- Coinstantiation construction (@cite{kay-fillmore-1999}, Figure 13, §4.2).

    A general pattern for subject control: the matrix subject and
    the complement's subject share a coreference index.

    "She tried to leave": the subject of *try* (#1) = the understood
    subject of *leave* (#1). This is the mechanism underlying
    WXDY's X–Y coindexation. -/
def coinstantiationForm : TypedForm String :=
  [ { filler := .open_ .NOUN, role := some "subject", gf := some .subj
    , refIdx := some 1 }
  , { filler := .open_ .VERB, role := some "predicate", isHead := true }
  , { filler := .open_ .VERB, role := some "complement", gf := some .comp
    , refIdx := some 1 } ]

/-! ### Abstraction and specificity -/

/-- WXDY: 2/5 open slots → abstraction level 2/5. -/
theorem wxdy_abstraction :
    abstractionLevel wxdyForm = 2 / 5 := by native_decide

/-- WXDY is partiallyOpen: mix of open, headed, and fixed slots. -/
theorem wxdy_specificity :
    derivedSpecificity wxdyForm = .partiallyOpen := by native_decide

/-- Coinstantiation is fully abstract (all slots open). -/
theorem coinstantiation_specificity :
    derivedSpecificity coinstantiationForm = .fullyAbstract := by native_decide

/-! ### Coreference constraints -/

/-- WXDY has exactly one coreference group (the X–Y coinstantiation). -/
theorem wxdy_coreference_count :
    refGroupCount wxdyForm = 1 := by native_decide

/-- X (first slot) and Y (last slot) share coreference index 2:
    X is the understood subject of Y. -/
theorem wxdy_coinstantiation :
    wxdyForm.head?.bind (·.refIdx) = some 2 ∧
    wxdyForm.getLast?.bind (·.refIdx) = some 2 := ⟨rfl, rfl⟩

/-- Coinstantiation has exactly one coreference group. -/
theorem coinstantiation_coreference :
    refGroupCount coinstantiationForm = 1 := by native_decide

/-! ### Syntactic constraints -/

/-- WXDY-what is left-isolated ([loc -]) and nonreferential ([ref ∅]).
    These two constraints together explain why WXDY-what cannot take
    *else* modification and is not a true interrogative pronoun. -/
theorem wxdy_what_constraints :
    hasConstraint wxdyForm .locMinus = true ∧
    hasConstraint wxdyForm .refEmpty = true := ⟨rfl, rfl⟩

/-- WXDY-doing cannot be negated ([neg -]): "*What's X not doing Y?"
    is ungrammatical on the incredulity reading. -/
theorem wxdy_doing_negMinus :
    hasConstraint wxdyForm .negMinus = true := rfl

/-- Neither the ditransitive nor *let alone* bear any slot constraints —
    the enriched constraint machinery is specific to constructions like
    WXDY that have fine-grained syntactic restrictions. -/
theorem basic_forms_no_constraints :
    hasConstraint ditransitiveForm .locMinus = false ∧
    hasConstraint ditransitiveForm .negMinus = false ∧
    hasConstraint letAloneForm .locMinus = false := ⟨rfl, rfl, rfl⟩

end Phenomena.Constructions.Studies.Dunn2026
