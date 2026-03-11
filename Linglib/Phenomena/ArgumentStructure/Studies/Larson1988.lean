import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Derivation
import Linglib.Theories.Syntax.Minimalism.Core.Applicative
import Linglib.Theories.Syntax.Minimalism.VoiceAppl
import Linglib.Phenomena.ArgumentStructure.DativeAlternation
import Linglib.Core.Lexical.ThetaRole

/-!
# Larson (1988): On the Double Object Construction
@cite{larson-1988}

*Linguistic Inquiry* 19(3): 335–391.

## Core Claims

1. **VP shells**: Ditransitive verbs project binary-branching VP structures
   with an outer VP shell whose head is initially empty. V raises from
   the inner VP to the outer V position (V Raising).

2. **Dative Shift = PASSIVE**: The double object construction (DOC) is
   derived from the oblique dative by Internal Merge — the same operation
   as Passive — applied within the VP domain rather than the IP domain.
   Both operations are `Step.im` in the `Derivation` infrastructure.

3. **@cite{barss-lasnik-1986} asymmetries**: In the derived DOC, the
   indirect object (NP1) asymmetrically c-commands the direct object
   (NP2), deriving six asymmetries: anaphor binding, quantifier-pronoun
   binding, weak crossover, superiority, *each...the other*, NPI licensing.

4. **Recoverability**: Dative Shift requires that *to*'s semantic content
   be recoverable from V's θ-role assignment. *Give/send* alternate
   because V's Goal role subsumes *to*'s contribution; *donate/distribute*
   do not because *to* contributes non-redundant directional semantics.

## Infrastructure Integration

This file uses the `Derivation` type (`Core/Derivation.lean`) to formalize
Dative Shift as a `Step.im` (Internal Merge) step. This enforces Larson's
central thesis at the type level: Passive and Dative Shift are both
instances of `Step.im`, differing only in which argument moves and when
the step is applied in the derivation.

The c-command predictions are verified on `Derivation.final` trees using
`cCommandsInB`, connecting to the same infrastructure used for binding
verification in `ColeHermon2008.lean` and tree-based derivations in
`VoiceAppl.lean` § 6.

## Cross-references

- `Theories.Syntax.Minimalism.Core.Derivation`: `Step.im` = Internal Merge
- `Theories.Syntax.Minimalism.VoiceAppl` § 6: Modern tree-based ditransitive
  with c-command verification (same predictions, different decomposition)
- `Phenomena.WordOrder.Studies.ColeHermon2008`: English passive derivation
  using the same `Derivation` infrastructure
-/

namespace Phenomena.ArgumentStructure.Studies.Larson1988

open Minimalism

-- ============================================================================
-- § 1: Lexical Items
-- ============================================================================

def V_send    := mkLeafPhon .V [.D]    "send"    300
def P_to      := mkLeafPhon .P [.D]   "to"       301
def DP_john   := mkLeafPhon .D []     "John"      302
def DP_mary   := mkLeafPhon .D []     "Mary"      303
def DP_letter := mkLeafPhon .D []     "a letter"  304

def V_kick    := mkLeafPhon .V [.D]   "kicked"    310
def DP_ball   := mkLeafPhon .D []     "the ball"  311

-- ============================================================================
-- § 2: Oblique Dative Derivation
-- ============================================================================

/-! The oblique dative "John sent a letter to Mary" is built bottom-up:

    1. EM-R the PP complement `[PP to Mary]`
    2. EM-L the direct object `a letter` (inner VP-subject)
    3. EM-L the agent `John` (outer VP-subject / Spec-VP)

    The direct object (a letter) c-commands the goal (Mary), but not
    vice versa — Mary is buried inside PP. -/

def obliqueDative : Derivation :=
  { initial := V_send
    steps := [
      .emR (merge P_to DP_mary),   -- [V' send [PP to Mary]]
      .emL DP_letter,               -- [VP a_letter [V' send [PP to Mary]]]
      .emL DP_john                  -- [VP John [VP a_letter [V' send [PP to Mary]]]]
    ] }

-- Oblique dative c-command predictions

theorem oblique_do_ccommands_goal :
    cCommandsInB obliqueDative.final DP_letter DP_mary = true := by native_decide

theorem oblique_goal_not_ccommands_do :
    cCommandsInB obliqueDative.final DP_mary DP_letter = false := by native_decide

theorem oblique_agent_ccommands_both :
    cCommandsInB obliqueDative.final DP_john DP_letter = true ∧
    cCommandsInB obliqueDative.final DP_john DP_mary = true := by
  constructor <;> native_decide

-- ============================================================================
-- § 3: DOC Derivation — Dative Shift as Step.im
-- ============================================================================

/-! The DOC "John sent Mary a letter" extends the oblique dative with
one additional step: **Internal Merge of the indirect object** (`Step.im`).

This is Larson's central insight: Dative Shift = PASSIVE within VP.
The `Step.im` constructor is the same one used for standard Passive
(cf. `ColeHermon2008.lean`'s `englishPassive` derivation). The only
difference is *which* argument moves and *when* in the derivation.

Derivation steps:
1. EM-R the PP complement `[PP to Mary]`
2. EM-L the direct object `a letter`
3. **IM the IO `Mary`** — Dative Shift. Mary is extracted from inside
   `[PP to Mary]`, leaving a trace, and re-merged at the left edge.
   This promotes Mary above the direct object.
4. EM-L the agent `John` -/

def docDativeShift : Derivation :=
  { initial := V_send
    steps := [
      .emR (merge P_to DP_mary),   -- [V' send [PP to Mary]]
      .emL DP_letter,               -- [VP a_letter [V' send [PP to Mary]]]
      .im DP_mary 0,               -- DATIVE SHIFT: Mary moves to Spec
      .emL DP_john                  -- [VP John [VP Mary_i [VP a_letter ...]]]
    ] }

-- DOC c-command predictions: the asymmetries are REVERSED

/-- In the DOC, the indirect object (Mary) c-commands the direct object
    (a letter). Mary has been promoted above the DO by Internal Merge.
    This derives all six @cite{barss-lasnik-1986} asymmetries:
    - Anaphor binding: "I showed Mary herself" vs *"I showed herself Mary"
    - Quantifier binding: "I gave every worker his paycheck"
    - Weak crossover, superiority, *each...the other*, NPI licensing -/
theorem doc_io_ccommands_do :
    cCommandsInB docDativeShift.final DP_mary DP_letter = true := by native_decide

/-- The direct object does NOT c-command the indirect object in the DOC. -/
theorem doc_do_not_ccommands_io :
    cCommandsInB docDativeShift.final DP_letter DP_mary = false := by native_decide

theorem doc_agent_ccommands_both :
    cCommandsInB docDativeShift.final DP_john DP_mary = true ∧
    cCommandsInB docDativeShift.final DP_john DP_letter = true := by
  constructor <;> native_decide

-- ============================================================================
-- § 4: PASSIVE — Same Step.im, Different Domain
-- ============================================================================

/-! Standard Passive ("The ball was kicked by John") is also `Step.im`:
the object moves to subject position. By using the same `Step.im`
constructor, the type system enforces Larson's thesis that Passive
and Dative Shift share the same structural operation. -/

def standardPassive : Derivation :=
  { initial := V_kick
    steps := [
      .emR DP_ball,                 -- [V' kicked [DP the ball]]
      .emL DP_john,                 -- [VP John [V' kicked [DP the ball]]]
      .im DP_ball 0                 -- PASSIVE: ball promoted to Spec
    ] }

-- Passive c-command: promoted object c-commands demoted subject

theorem passive_object_ccommands_subject :
    cCommandsInB standardPassive.final DP_ball DP_john = true := by native_decide

theorem passive_subject_not_ccommands_object :
    cCommandsInB standardPassive.final DP_john DP_ball = false := by native_decide

-- ============================================================================
-- § 5: Structural Parallel — Passive and Dative Shift
-- ============================================================================

/-! Both Passive and Dative Shift use `Step.im`. We can extract the
movement steps and verify they share the same structure. -/

/-- Dative Shift involves exactly one Internal Merge (of the IO). -/
theorem dativeShift_has_one_im :
    docDativeShift.movedItems = [DP_mary] := by native_decide

/-- Standard Passive involves exactly one Internal Merge (of the object). -/
theorem passive_has_one_im :
    standardPassive.movedItems = [DP_ball] := by native_decide

/-- Both operations promote an argument by Internal Merge, reversing
    the c-command relation between the two internal arguments.

    Oblique dative:  DO > IO  (letter c-commands Mary)
    DOC:             IO > DO  (Mary c-commands letter)  [reversed by Step.im]
    Active:          Subj > Obj (John c-commands ball)
    Passive:         Obj > Subj (ball c-commands John)  [reversed by Step.im] -/
theorem passive_dativeShift_parallel :
    -- Both reverse c-command via the same Step.im mechanism
    cCommandsInB obliqueDative.final DP_letter DP_mary = true ∧
    cCommandsInB docDativeShift.final DP_mary DP_letter = true ∧
    cCommandsInB standardPassive.final DP_ball DP_john = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § 6: Recoverability Condition
-- ============================================================================

/-! Dative Shift is possible only when *to*'s semantic content is
recoverable from V's θ-role assignment. When V independently assigns
a Goal role, *to*'s contribution reduces to Case marking and can be
absorbed. When *to* contributes non-redundant directional semantics,
its suppression would cause irrecoverable loss, blocking Dative Shift.

This explains the contrast:
- *give/send*: V assigns Goal → *to* is redundant → Dative Shift ✓
- *donate/distribute*: V assigns only Beneficiary → *to* is
  non-redundant → Dative Shift ✗ -/

structure DativeVerbEntry where
  verb : String
  /-- Does V's θ-assignment to the IO subsume *to*'s role? -/
  verbSubsumesToRole : Bool
  /-- Dative Shift permitted? -/
  allowsDativeShift : Bool
  deriving Repr, BEq

def give_entry : DativeVerbEntry :=
  { verb := "give", verbSubsumesToRole := true, allowsDativeShift := true }

def send_entry : DativeVerbEntry :=
  { verb := "send", verbSubsumesToRole := true, allowsDativeShift := true }

def donate_entry : DativeVerbEntry :=
  { verb := "donate", verbSubsumesToRole := false, allowsDativeShift := false }

def distribute_entry : DativeVerbEntry :=
  { verb := "distribute", verbSubsumesToRole := false, allowsDativeShift := false }

def recoverability (e : DativeVerbEntry) : Bool :=
  e.verbSubsumesToRole

theorem recoverability_predicts_dative_shift :
    ∀ e ∈ [give_entry, send_entry, donate_entry, distribute_entry],
      recoverability e = e.allowsDativeShift := by
  intro e he
  simp at he
  rcases he with rfl | rfl | rfl | rfl <;> rfl

-- ============================================================================
-- § 7: Bridge — Larson VP Shell ↔ Modern Voice/Appl
-- ============================================================================

/-! Larson's VP shell (1988) is the precursor of the modern Voice/v* +
Applicative decomposition. While the tree shapes differ (Larson uses
one VP-shell layer; modern theory uses Voice, v, Appl heads), the
c-command hierarchy among DP arguments is identical:
agent > goal/IO > theme/DO.

The modern derivation with tree-based c-command verification is in
`VoiceAppl.lean` § 6. -/

open Minimalism.Phenomena.VoiceAppl in

/-- Larson's DOC and the modern Voice + low-Appl derivation produce
    the same c-command hierarchy: IO asymmetrically c-commands DO.

    This proves that the Larson 1988 analysis and the Pylkkänen 2008
    analysis, despite different decompositions, converge on the same
    structural prediction for @cite{barss-lasnik-1986} asymmetries. -/
theorem larson_modern_same_hierarchy :
    -- Larson's DOC: IO > DO
    cCommandsInB docDativeShift.final DP_mary DP_letter = true ∧
    cCommandsInB docDativeShift.final DP_letter DP_mary = false ∧
    -- Modern Voice/Appl: goal > theme (same asymmetry)
    cCommandsInB ditransitiveTree DP_mary_t DP_letter_t = true ∧
    cCommandsInB ditransitiveTree DP_letter_t DP_mary_t = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end Phenomena.ArgumentStructure.Studies.Larson1988
