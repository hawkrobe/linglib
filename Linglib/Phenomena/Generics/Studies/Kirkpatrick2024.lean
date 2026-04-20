import Linglib.Theories.Semantics.Dynamic.Generics

/-!
# @cite{kirkpatrick-2024}: The Dynamics of Generics

James Ravi Kirkpatrick, "The Dynamics of Generics."
*Journal of Semantics* 40(4), 2024. 523–548.

## Core Contribution

Explains the asymmetry between generic Sobel sequences and their reverses
using a dynamic semantic theory where generics expand a "modal horizon."

- **Sobel sequence**: "Ravens are black; but albino ravens aren't." (felicitous)
- **Reverse Sobel**: "#Albino ravens aren't black; but ravens are." (infelicitous)

Existing static theories (Cohen's probabilistic account, @cite{cohen-1999a};
Greenberg's normality-based account; Sterken's indexical approach) assign
equivalent truth conditions to both orders and cannot explain the asymmetry.

The key mechanism is that generics **expand** the set of salient individuals
(the modal horizon) as a side effect of assertion. The first generic in a
discourse excludes exceptional individuals from the horizon; subsequent
generics are evaluated against the expanded horizon. Reversing the order
makes exceptional individuals salient before the general claim is assessed.

## Key predictions (verified below)

1. Generic Sobel sequences are consistent (`sobel_consistent`)
2. Reverse generic Sobel sequences are inconsistent (`reverse_sobel_inconsistent`)
3. Mixed generic sequences with non-overlapping contextual variables
   are consistent (`mixed_consistent`)

## Connection to other Generics studies

- @cite{cohen-1999a} (`Studies/Cohen1999.lean`): static probabilistic GEN
  with threshold 0.5 — cannot explain order effects
- @cite{tessler-goodman-2019} (`Studies/TesslerGoodman2019.lean`): RSA model
  explaining prevalence-based judgments — complementary, not competing
-/

namespace Kirkpatrick2024

open Semantics.Dynamic.Generics


-- ═══ Toy Model: Ravens ═══

/-- Three entities: two normal ravens and one albino raven. -/
inductive Raven where
  | normal1 | normal2 | albino
  deriving DecidableEq, Repr

/-- All entities are ravens. -/
def isRaven : Raven → Prop := fun _ => True

instance : DecidablePred isRaven := fun _ => isTrue trivial

/-- Only the albino raven is an albino raven. -/
def isAlbinoRaven : Raven → Prop
  | .albino => True
  | _ => False

instance : DecidablePred isAlbinoRaven :=
  fun e => by cases e <;> unfold isAlbinoRaven <;> infer_instance

/-- Normal ravens are black; the albino is not. -/
def isBlack : Raven → Prop
  | .normal1 => True
  | .normal2 => True
  | .albino => False

instance : DecidablePred isBlack :=
  fun e => by cases e <;> unfold isBlack <;> infer_instance

/-- Normal ravens for the "raven" restrictor class: the non-albino ones.
    These are the output of `NormalityOrder.optimal` applied to ravens. -/
def normalRavens : List Raven := [.normal1, .normal2]

/-- Normal albino ravens: all albino ravens are "normal" for their subkind.
    (Albino is not abnormal *qua albino raven* — it's abnormal qua raven.) -/
def normalAlbinoRavens : List Raven := [.albino]


-- ═══ Generic Sentences ═══

/-- "Ravens are black" -/
def ravensAreBlack : GenericSentence Raven :=
  ⟨isRaven, isBlack, normalRavens⟩

/-- "Albino ravens aren't black" -/
def albinoRavensArentBlack : GenericSentence Raven :=
  ⟨isAlbinoRaven, fun e => ¬ isBlack e, normalAlbinoRavens⟩


-- ═══ Sobel Sequence ═══
-- "Ravens are black; but albino ravens aren't."

def sobelSequence : List (GenericSentence Raven) :=
  [ravensAreBlack, albinoRavensArentBlack]

-- The full Sobel sequence is consistent.
theorem sobel_consistent : isConsistent sobelSequence := by decide


-- ═══ Reverse Sobel Sequence ═══
-- "#Albino ravens aren't black; but ravens are."

def reverseSobelSequence : List (GenericSentence Raven) :=
  [albinoRavensArentBlack, ravensAreBlack]

-- This is the key prediction: the albino raven, made salient by the
-- first generic, poisons the evaluation of the second generic.

theorem reverse_sobel_inconsistent :
    ¬ isConsistent reverseSobelSequence := by decide


-- ═══ Mixed Generic Sequences ═══
-- "Lions have manes and lions give birth to live young."

/-- Two entities: a male lion and a female lion. -/
inductive Animal where
  | maleLion | femaleLion
  deriving DecidableEq, Repr

def hasMane : Animal → Prop
  | .maleLion => True
  | .femaleLion => False

instance : DecidablePred hasMane :=
  fun e => by cases e <;> unfold hasMane <;> infer_instance

def givesLiveBirth : Animal → Prop
  | .maleLion => False
  | .femaleLion => True

instance : DecidablePred givesLiveBirth :=
  fun e => by cases e <;> unfold givesLiveBirth <;> infer_instance

/-- "Lions have manes" — restrictor incorporates Kirkpatrick's contextual
    variable C = alternatives to having a mane (sexually-selected traits).
    Only male lions are in the domain of "mane alternatives." -/
def lionsHaveManes : GenericSentence Animal :=
  ⟨fun e => e = .maleLion, hasMane, [.maleLion]⟩

/-- "Lions give birth to live young" — restrictor incorporates C =
    alternatives to giving birth (modes of reproduction).
    Only female lions are in the domain of "reproduction alternatives." -/
def lionsGiveBirth : GenericSentence Animal :=
  ⟨fun e => e = .femaleLion, givesLiveBirth, [.femaleLion]⟩

/-- Mixed sequence: both generics use different contextual variables C,
    so the first generic's salient individuals don't satisfy the second
    generic's restrictor. No mutual interference. -/
def mixedSequence : List (GenericSentence Animal) :=
  [lionsHaveManes, lionsGiveBirth]

/-- Mixed generic sequences are consistent: the two generics don't
    interfere because they have non-overlapping restrictors (different
    contextual variables C). -/
theorem mixed_consistent : isConsistent mixedSequence := by decide

/-- The reverse mixed sequence is also consistent — mixed sequences
    are symmetric because the restrictors don't overlap. -/
theorem mixed_reverse_consistent :
    isConsistent [lionsGiveBirth, lionsHaveManes] := by decide


-- ═══ General Theorem Instantiations ═══

/-- The raven Sobel pair satisfies the general consistency theorem.
    This derives `sobel_consistent` from the paper's general argument (§5.1)
    rather than finite model checking. -/
theorem sobel_consistent_general :
    isConsistent sobelSequence :=
  sobel_pair_consistent ravensAreBlack albinoRavensArentBlack
    (by decide) (by decide) (by decide) (by decide)

/-- The raven reverse Sobel pair satisfies the general inconsistency theorem.
    This derives `reverse_sobel_inconsistent` from the general argument (§5.2). -/
theorem reverse_sobel_inconsistent_general :
    ¬ isConsistent reverseSobelSequence :=
  reverse_sobel_pair_inconsistent ravensAreBlack albinoRavensArentBlack
    (by decide) (by intro e he; cases e <;> simp [albinoRavensArentBlack, ravensAreBlack,
        isAlbinoRaven, isRaven] at he ⊢)
    (by decide) (by decide)


-- ═══ Additional Data from §2 ═══

/-- Example (4): "Teachers care for their students; but bad teachers don't."
    Another Sobel pair demonstrating the generality of the phenomenon. -/
inductive Person where
  | goodTeacher1 | goodTeacher2 | badTeacher
  deriving DecidableEq, Repr

def isTeacher : Person → Prop := fun _ => True

instance : DecidablePred isTeacher := fun _ => isTrue trivial

def isBadTeacher : Person → Prop
  | .badTeacher => True
  | _ => False

instance : DecidablePred isBadTeacher :=
  fun e => by cases e <;> unfold isBadTeacher <;> infer_instance

def caresForStudents : Person → Prop
  | .goodTeacher1 => True
  | .goodTeacher2 => True
  | .badTeacher => False

instance : DecidablePred caresForStudents :=
  fun e => by cases e <;> unfold caresForStudents <;> infer_instance

def teachersCare : GenericSentence Person :=
  ⟨isTeacher, caresForStudents, [.goodTeacher1, .goodTeacher2]⟩
def badTeachersDontCare : GenericSentence Person :=
  ⟨isBadTeacher, fun e => ¬ caresForStudents e, [.badTeacher]⟩

theorem teachers_sobel_consistent :
    isConsistent [teachersCare, badTeachersDontCare] := by decide
theorem teachers_reverse_inconsistent :
    ¬ isConsistent [badTeachersDontCare, teachersCare] := by decide


-- ═══ Static-Dynamic Bridge ═══

/-- In discourse-initial position, Kirkpatrick's dynamic semantics
    reduces to static truth conditions. Both "Ravens are black" and
    "Albino ravens aren't black" are true when evaluated against an
    empty horizon — matching the predictions of static GEN.

    The dynamic theory diverges from statics only in multi-sentence
    discourse, where prior generics have expanded the horizon. -/
theorem static_both_true_independently :
    (evalGeneric [] ravensAreBlack).2 ∧
    (evalGeneric [] albinoRavensArentBlack).2 := by
  exact ⟨by decide, by decide⟩

/-- The static-dynamic bridge instantiated for the raven model:
    discourse-initial evaluation of "Ravens are black" reduces to a
    restricted universal over normal ravens. -/
theorem ravens_static_dynamic_bridge :
    (evalGeneric [] ravensAreBlack).2 ↔
    ∀ e ∈ ravensAreBlack.normalInstances,
      ravensAreBlack.restrictor e → ravensAreBlack.scope e :=
  evalGeneric_empty_eq_static ravensAreBlack

/-- Yet the order matters for the dynamic evaluation. -/
theorem order_matters :
    isConsistent sobelSequence ∧ ¬ isConsistent reverseSobelSequence := by
  exact ⟨by decide, by decide⟩


-- ═══ Horizon Evolution: Raven Model ═══

/-- Forward Sobel: the raven model instantiates the structural
    horizon theorem. Both expansions fire — normal ravens first,
    then the albino raven. -/
theorem raven_forward_horizons :
    horizonStep albinoRavensArentBlack (horizonStep ravensAreBlack []) =
    normalRavens ++ normalAlbinoRavens :=
  sobel_forward_horizons ravensAreBlack albinoRavensArentBlack (by decide)

/-- Reverse Sobel: the general's expansion is blocked because the
    albino raven (made salient by the first generic) satisfies the
    "is a raven" restrictor. The final horizon contains only [albino]. -/
theorem raven_reverse_horizons :
    horizonStep ravensAreBlack (horizonStep albinoRavensArentBlack []) =
    normalAlbinoRavens :=
  sobel_reverse_horizons ravensAreBlack albinoRavensArentBlack
    (by decide)
    (by intro e he; cases e <;> simp [albinoRavensArentBlack, ravensAreBlack,
         isAlbinoRaven, isRaven] at he ⊢)
    (by decide)

/-- The raven model witnesses horizon non-commutativity:
    the forward horizon [normal1, normal2, albino] differs from
    the reverse horizon [albino]. -/
theorem raven_horizon_noncommutative :
    horizonStep albinoRavensArentBlack (horizonStep ravensAreBlack []) ≠
    horizonStep ravensAreBlack (horizonStep albinoRavensArentBlack []) :=
  sobel_horizon_noncommutative ravensAreBlack albinoRavensArentBlack
    (by decide) (by decide)
    (by intro e he; cases e <;> simp [albinoRavensArentBlack, ravensAreBlack,
         isAlbinoRaven, isRaven] at he ⊢)
    (by decide) (by decide)


-- ═══ Algebraic Properties: Raven Model ═══

/-- The raven generic is idempotent: processing "Ravens are black" twice
    against any horizon gives the same result as processing it once.
    This instantiates the general `horizonStep_idempotent`. -/
theorem raven_idempotent (horizon : List Raven) :
    horizonStep ravensAreBlack (horizonStep ravensAreBlack horizon) =
    horizonStep ravensAreBlack horizon :=
  horizonStep_idempotent ravensAreBlack (by decide) (by decide) horizon

/-- The albino raven generic is also idempotent. -/
theorem albino_idempotent (horizon : List Raven) :
    horizonStep albinoRavensArentBlack (horizonStep albinoRavensArentBlack horizon) =
    horizonStep albinoRavensArentBlack horizon :=
  horizonStep_idempotent albinoRavensArentBlack (by decide) (by decide) horizon

/-- The mixed lion sequence derives from the structural non-interference
    theorem rather than finite model checking. -/
theorem mixed_consistent_structural :
    isConsistent [lionsHaveManes, lionsGiveBirth] ∧
    isConsistent [lionsGiveBirth, lionsHaveManes] :=
  disjoint_pair_consistent lionsHaveManes lionsGiveBirth
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)


-- ═══ Appendix A: Veltman Comparison ═══

/-! The structural horizon theorems above explain WHY the asymmetry
arises: the subset relation between restrictors (albino raven ⊆ raven)
creates asymmetric blocking in horizon evolution. The abstract
impossibility theorem (`commutative_implies_equal_verdicts` in
`Generics.lean`) then rules out ANY commutative framework — including
@cite{veltman-1996}'s `normallyUpdate` — from modeling this asymmetry.

@cite{veltman-1996}'s `normallyUpdate` is commutative
(`normallyUpdate_comm` in `UpdateSemantics/Default.lean`), meaning that
processing "normally (ravens are black)" then "normally (albino ravens
aren't black)" produces the same expectation state as the reverse order.
Since the state is identical, any consistency test must give the same
verdict for both orders — predicting the reverse Sobel is also felicitous,
contrary to empirical judgment. -/


-- ═══ Normality Grounding ═══

/-- The full raven domain. -/
def allRavens : List Raven := [.normal1, .normal2, .albino]

/-- Normality ordering on ravens: normal ravens are equally normal;
    the albino raven is less normal than both. This encodes the
    normality intuition that @cite{kirkpatrick-2024}'s theory relies on:
    normal-colored ravens are the "default" for raven-kind.

    `ravenNormality e₁ e₂` means `e₁` is at least as normal as `e₂`. -/
def ravenNormality : Raven → Raven → Prop
  | .albino, .normal1 => False
  | .albino, .normal2 => False
  | _, _ => True

instance : DecidableRel ravenNormality :=
  fun a b => by cases a <;> cases b <;> unfold ravenNormality <;> infer_instance

/-- The stipulated `normalRavens` are exactly the optimal ravens under
    `ravenNormality`. This grounds the raven model: the normal instances
    are derived from a normality ordering, not ad hoc. -/
theorem ravensAreBlack_grounded :
    (GenericSentence.fromOrder isRaven isBlack allRavens ravenNormality).normalInstances =
    normalRavens := by decide

/-- The stipulated `normalAlbinoRavens` are the optimal albino ravens.
    Within the albino-restricted domain, the albino raven is trivially
    optimal (it's the only member). -/
theorem albinoRavensArentBlack_grounded :
    (GenericSentence.fromOrder isAlbinoRaven (fun e => ¬ isBlack e)
      allRavens ravenNormality).normalInstances =
    normalAlbinoRavens := by decide


-- ═══ Binary Normalcy Grounding (fromPredicate) ═══

/-- Binary normalcy predicate: normal ravens are not albino. -/
def isNormalRaven : Raven → Prop
  | .albino => False
  | _ => True

instance : DecidablePred isNormalRaven :=
  fun e => by cases e <;> unfold isNormalRaven <;> infer_instance

/-- `fromPredicate` constructs the same generic sentence as the hand-stipulated
    `ravensAreBlack`, grounding `normalInstances` via a binary normalcy predicate
    rather than a normality ordering. -/
theorem ravensAreBlack_fromPredicate :
    (GenericSentence.fromPredicate isRaven isBlack allRavens isNormalRaven).normalInstances =
    normalRavens := by decide

/-- `fromPredicate` and `fromOrder` agree on the raven model: both constructors
    derive the same normal instances from their respective primitives.

    This demonstrates that binary normalcy (traditional GEN) and normality
    orderings (Kirkpatrick/Greenberg) coincide when the ordering has exactly
    two equivalence classes. -/
theorem fromPredicate_agrees_fromOrder :
    (GenericSentence.fromPredicate isRaven isBlack allRavens isNormalRaven).normalInstances =
    (GenericSentence.fromOrder isRaven isBlack allRavens ravenNormality).normalInstances := by
  decide


-- ═══ Static Theory Impossibility (§3) ═══

/-! @cite{kirkpatrick-2024} §3 argues that static theories — @cite{cohen-1999a}'s
probabilistic account, @cite{greenberg-2003}'s normality-based account,
@cite{sterken-2015}'s indexical approach — all fail to predict the Sobel
asymmetry. The formal reason: static theories evaluate each generic
independently (no state threading), so the conjunction of truth values
is commutative. If both generics are independently true, both orders
yield `true ∧ true = true`.

This is a special case of `commutative_implies_equal_verdicts` from
`Generics.lean`: any evaluation where each generic's truth value is
determined independently of discourse position is trivially commutative. -/

/-- Any state-independent evaluation assigns the same conjunction
    truth value regardless of presentation order. -/
theorem static_order_irrelevant {α : Type} (truth : α → Prop) (g₁ g₂ : α) :
    (truth g₁ ∧ truth g₂) ↔ (truth g₂ ∧ truth g₁) :=
  And.comm

/-- Both raven generics are true when evaluated discourse-initially
    (= statically), yet the dynamic theory distinguishes the orders.

    Static theories predict `true ∧ true` for both orders and therefore
    cannot model the asymmetry that @cite{kirkpatrick-2024}'s dynamic
    theory captures via horizon expansion and blocking. -/
theorem static_vs_dynamic_divergence :
    -- Both true in isolation (static prediction: both orders felicitous)
    (evalGeneric [] ravensAreBlack).2 ∧
    (evalGeneric [] albinoRavensArentBlack).2 ∧
    -- Dynamic: forward Sobel is consistent
    isConsistent sobelSequence ∧
    -- Dynamic: reverse Sobel is inconsistent
    ¬ isConsistent reverseSobelSequence :=
  ⟨by decide, by decide, by decide, by decide⟩


end Kirkpatrick2024
