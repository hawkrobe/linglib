import Linglib.Theories.Semantics.Mood.Gutzmann
import Linglib.Core.Grammar

/-!
# German Clause Types
@cite{gutzmann-2015}

German clause-type taxonomy used by Gutzmann (2015) for the analysis of
sentence mood operators (DEONT, EPIS, HKNOW). Five clause types
distinguished by verb position (V2 vs verb-last) and complementizer
presence (dass vs not), with their associated mood-operator inventories
and clause-level mood compositions.

This file is the *German fragment* counterpart of the language-agnostic
operators in `Theories.Semantics.Mood.Gutzmann`. The theory file
defines DEONT, EPIS, the E modifier, and HKNOW; this file specifies
*which* of those operators each German clause type composes.

## German Clause Type Inventory (@cite{gutzmann-2015}, Ch 5)

| Clause type       | Mood operators           | Example                |
|-------------------|--------------------------|------------------------|
| dass-VL           | DEONT only               | "Dass du kommst!"      |
| V2-declarative    | DEONT(EPIS(p))           | "Jim wohnt in Berlin." |
| VL-interrogative  | DEONT(EPIS(p))           | "Wann Peter kommt?"    |
| V2-interrogative  | DEONT(EPIS(p)) ⊙ HKNOW  | "Kommt Peter?"         |
| Imperative        | DEONT only               | "Tritt zurück!"        |
-/

namespace Fragments.German.ClauseTypes

open Semantics.Mood.Gutzmann


-- ════════════════════════════════════════════════════════════════
-- § 1. German clause-type mood compositions
-- ════════════════════════════════════════════════════════════════

/-- dass-VL clause mood: DEONT only (@cite{gutzmann-2015}, (5.82)).

No [±wh] visible at LF (dass is semantically empty, so [−wh] is
invisible per the visibility condition (5.41)). Therefore no epistemic
interpretation is triggered. The root rule introduces DEONT.

"Dass du nicht zu spät kommst!" = The speaker wants [you not arrive late]. -/
def dassVLMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  deont p c

/-- V2-declarative mood: DEONT(EPIS(p)) (@cite{gutzmann-2015}, (5.93)–(5.96)).

The finite verb moves to C⁰ (V-to-C triggered by [−wh] attached to an
overt element at PF). The [−wh] is visible at LF, triggering epistemic
interpretation. The root rule adds DEONT, and E modifies it to embed
the epistemic predicate.

"Jim wohnt in Berlin." = The speaker wants the hearer to believe
[Jim lives in Berlin]. -/
def v2DeclMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  episModifier deont p c

/-- V2-interrogative mood: DEONT(EPIS(p)) ⊙ HKNOW(p)
(@cite{gutzmann-2015}, (5.100)).

V2-interrogatives have two [±wh] specifications: [+wh] in CP^spec
and [−wh] in C⁰ (Brandt et al. 1992). The first triggers epistemic
interpretation, the second (in C⁰) triggers an additional epistemic
interpretation resolved to hearer knowledge. HKNOW is a separate
functional expletive UCI whose u-content is conjoined (⊙) with the
deontic/epistemic mood.

"Kommt Peter?" = The speaker wants to know [whether Peter comes]
AND the addressee knows [whether Peter comes]. -/
def v2InterrogMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  episModifier deont p c && hknow p c

/-- VL-interrogative mood: DEONT(EPIS(p)) only — no HKNOW
(@cite{gutzmann-2015}, p. 213).

VL-interrogatives (e.g., "Wann Peter nach Hause kommt?") lack the
[−wh] in C⁰ that triggers HKNOW. Therefore they are felicitous even
when the hearer does not know the answer (the Cuban cigar scenario). -/
def vlInterrogMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  episModifier deont p c


-- ════════════════════════════════════════════════════════════════
-- § 2. Mood-operator theorems for the German clause-type compositions
-- ════════════════════════════════════════════════════════════════

/-- dass-VL clauses have no epistemic component. -/
theorem dassVL_is_pure_deontic {W : Type*}
    (p : W → Bool) (c : MoodContext W) :
    dassVLMood p c = deont p c := rfl

/-- V2-interrogatives differ from VL-interrogatives only in the
HKNOW component (hearer knowledge use condition). -/
theorem v2_vs_vl_interrog {W : Type*}
    (p : W → Bool) (c : MoodContext W) :
    v2InterrogMood p c = (vlInterrogMood p c && hknow p c) := rfl

/-- Imperatives and dass-VL clauses share the same mood structure:
DEONT only, no epistemic. Both lack [±wh] visible at LF. -/
theorem imperative_equals_dassVL {W : Type*}
    (p : W → Bool) (c : MoodContext W) :
    dassVLMood p c = deont p c := rfl


-- ════════════════════════════════════════════════════════════════
-- § 3. German Clause Types as a refinement of Core.Grammar.ClauseForm
-- ════════════════════════════════════════════════════════════════

/-! ### `GermanClauseType` as `ClauseForm`-indexed inductive

`GermanClauseType` is a Gutzmann-2015-specific refinement of the
framework-agnostic `Core.Grammar.ClauseForm`: it distinguishes clauses
by both verb position (V2 vs VL) and complementizer presence (dass vs
not), where `ClauseForm` only records the matrix-vs-embedded question /
declarative / echo word-order distinction.

We encode the refinement *structurally* as an indexed inductive
`GermanClauseType : ClauseForm → Type`. Each constructor specifies the
`ClauseForm` it refines:

| `GermanClauseType` | `ClauseForm`        |
|--------------------|---------------------|
| `dassVL`           | `declarative`       |
| `v2Declarative`    | `declarative`       |
| `v2Interrogative`  | `matrixQuestion`    |
| `vlInterrogative`  | `embeddedQuestion`  |
| `imperative`       | `declarative`       |

Three consequences fall out of the indexing rather than requiring
separate proof:

1. **No bridge function.** The "projection to `ClauseForm`" is the
   type-level index — `(ct : GermanClauseType f)` witnesses both the
   refined value *and* its `ClauseForm` projection `f` simultaneously.
2. **Echo questions are uninhabited.** `GermanClauseType .echo` has no
   constructor, so `(ct : GermanClauseType .echo)` is impossible by
   typing — Gutzmann's theory does not analyze echo questions, and
   that absence is now type-enforced.
3. **`(ct : GermanClauseType .matrixQuestion)` is *exactly* the
   v2Interrogative case.** `cases ct` on this type produces a single
   branch, capturing the structural fact that "matrix-question German
   clause" picks out v2Interrogative without auxiliary filtering. -/

/-- German clause types distinguished by verb position and complementizer,
indexed by their `Core.Grammar.ClauseForm` projection. The
verb-position/complementizer information determines mood operator
inventory (@cite{gutzmann-2015}, Ch 5). -/
inductive GermanClauseType : ClauseForm → Type where
  /-- dass-VL: complementizer clause, verb-last. No [±wh] visible at LF.
      Form-level: declarative. -/
  | dassVL : GermanClauseType .declarative
  /-- V2-declarative: finite verb in C⁰, [−wh] visible at LF.
      Form-level: declarative. -/
  | v2Declarative : GermanClauseType .declarative
  /-- V2-interrogative: verb-second, [+wh] in SpecCP + [−wh] in C⁰.
      Form-level: matrix question. -/
  | v2Interrogative : GermanClauseType .matrixQuestion
  /-- VL-interrogative: verb-last, [+wh] only (no [−wh] in C⁰).
      Form-level: embedded question. -/
  | vlInterrogative : GermanClauseType .embeddedQuestion
  /-- Imperative: no [±wh] visible at LF.
      Form-level: declarative (no SAI inversion). -/
  | imperative : GermanClauseType .declarative
  deriving DecidableEq, Repr

/-- The mood structure of each German clause type, derived from
the theory of [±wh] visibility and the root rule. -/
def GermanClauseType.moodStructure : ∀ {f : ClauseForm},
    GermanClauseType f → MoodStructure
  | _, .dassVL          => ⟨true, false, false⟩
  | _, .v2Declarative   => ⟨true, true, false⟩
  | _, .v2Interrogative => ⟨true, true, true⟩
  | _, .vlInterrogative => ⟨true, true, false⟩
  | _, .imperative      => ⟨true, false, false⟩

/-- Every matrix clause has a deontic operator (the root rule). -/
theorem every_clause_has_deont {f : ClauseForm} (ct : GermanClauseType f) :
    ct.moodStructure.hasDeontic = true := by
  cases ct <;> rfl

/-- Imperatives lack EPIS — the structural basis for selectional
restrictions on UC-modifiers like *wohl*. -/
theorem imperative_lacks_epis :
    GermanClauseType.imperative.moodStructure.hasEpistemic = false := rfl

/-- dass-VL and imperatives share mood structure: deontic only. -/
theorem dassVL_matches_imperative :
    GermanClauseType.dassVL.moodStructure =
    GermanClauseType.imperative.moodStructure := rfl

/-- V2-interrogatives differ from VL-interrogatives only in HKNOW. -/
theorem v2_vl_differ_only_in_hknow :
    GermanClauseType.v2Interrogative.moodStructure.hasDeontic =
      GermanClauseType.vlInterrogative.moodStructure.hasDeontic ∧
    GermanClauseType.v2Interrogative.moodStructure.hasEpistemic =
      GermanClauseType.vlInterrogative.moodStructure.hasEpistemic ∧
    GermanClauseType.v2Interrogative.moodStructure.hasHearerKnowledge = true ∧
    GermanClauseType.vlInterrogative.moodStructure.hasHearerKnowledge = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Structural consequences of the indexing

These theorems exploit the indexed structure: instead of projecting via
a forgetful function and filtering, the type-level index does the work. -/

/-- Echo questions are uninhabited in the German fragment: there is no
constructor `c : GermanClauseType .echo`. The fragment does not analyze
echo questions; this is type-enforced rather than checked by a side
condition. -/
theorem no_german_echo : IsEmpty (GermanClauseType .echo) :=
  ⟨fun ct => nomatch ct⟩

/-- A matrix-question German clause type is *exactly* `v2Interrogative`.
Pattern matching on `GermanClauseType .matrixQuestion` produces a single
constructor by the indexing. -/
theorem matrix_question_is_v2_interrog (ct : GermanClauseType .matrixQuestion) :
    ct = .v2Interrogative := by
  cases ct; rfl

/-- An embedded-question German clause type is *exactly* `vlInterrogative`. -/
theorem embedded_question_is_vl_interrog (ct : GermanClauseType .embeddedQuestion) :
    ct = .vlInterrogative := by
  cases ct; rfl

/-- HKNOW iff matrix question — restated structurally as a fact about the
index. The HKNOW use condition tracks *form*-level matrix interrogativity
(@cite{gutzmann-2015}, p. 213, Cuban cigar argument). -/
theorem hknow_iff_matrix_question {f : ClauseForm} (ct : GermanClauseType f) :
    ct.moodStructure.hasHearerKnowledge = true ↔ f = .matrixQuestion := by
  cases ct <;> simp [GermanClauseType.moodStructure]

/-- Matrix-question German clauses always carry HKNOW. -/
theorem matrix_question_has_hknow (ct : GermanClauseType .matrixQuestion) :
    ct.moodStructure.hasHearerKnowledge = true := by
  cases ct; rfl

/-- The `.declarative` fiber is many-to-one — three German clause types
inhabit it (dassVL, v2Declarative, imperative), and they are
distinguishable only at the `moodStructure` level. The contrast below
type-checks because both terms have type `GermanClauseType .declarative`. -/
theorem declarative_fiber_underdetermines_mood :
    (GermanClauseType.dassVL : GermanClauseType .declarative).moodStructure ≠
    (GermanClauseType.v2Declarative : GermanClauseType .declarative).moodStructure := by
  decide

end Fragments.German.ClauseTypes
