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
- `CompareModality.lean`: GEN as modal necessity — the static structure
  that Kirkpatrick's dynamic theory wraps in a CCP
-/

namespace Phenomena.Generics.Studies.Kirkpatrick2024

open Semantics.Dynamic.Generics


-- ═══ Toy Model: Ravens ═══

/-- Three entities: two normal ravens and one albino raven. -/
inductive Raven where
  | normal1 | normal2 | albino
  deriving DecidableEq, BEq, Repr

/-- All entities are ravens. -/
def isRaven : Raven → Bool := λ _ => true

/-- Only the albino raven is an albino raven. -/
def isAlbinoRaven : Raven → Bool
  | .albino => true
  | _ => false

/-- Normal ravens are black; the albino is not. -/
def isBlack : Raven → Bool
  | .normal1 => true
  | .normal2 => true
  | .albino => false

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
  ⟨isAlbinoRaven, λ e => !isBlack e, normalAlbinoRavens⟩


-- ═══ Sobel Sequence ═══
-- "Ravens are black; but albino ravens aren't."

def sobelSequence : List (GenericSentence Raven) :=
  [ravensAreBlack, albinoRavensArentBlack]

-- Step 1: "Ravens are black" against empty horizon.
-- Horizon is empty → expand with normal ravens [normal1, normal2].
-- All ravens on horizon are black → TRUE.
#guard (evalGeneric [] ravensAreBlack).2 = true

-- Step 2: "Albino ravens aren't black" against [normal1, normal2].
-- No albino ravens on horizon → expand with [albino].
-- albino is not black → TRUE.
#guard (evalGeneric [.normal1, .normal2] albinoRavensArentBlack).2 = true

-- The full Sobel sequence is consistent.
#guard isConsistent sobelSequence = true

theorem sobel_consistent : isConsistent sobelSequence = true := by native_decide


-- ═══ Reverse Sobel Sequence ═══
-- "#Albino ravens aren't black; but ravens are."

def reverseSobelSequence : List (GenericSentence Raven) :=
  [albinoRavensArentBlack, ravensAreBlack]

-- Step 1: "Albino ravens aren't black" against empty horizon.
-- No albino ravens → expand with [albino].
-- albino is not black → TRUE.
#guard (evalGeneric [] albinoRavensArentBlack).2 = true

-- Step 2: "Ravens are black" against [albino].
-- albino IS a raven → hasRestrictor = true → NO expansion.
-- Is albino black? NO → FALSE.
-- This is the key prediction: the albino raven, made salient by the
-- first generic, poisons the evaluation of the second generic.
#guard (evalGeneric [.albino] ravensAreBlack).2 = false

-- The reverse Sobel sequence is inconsistent.
#guard isConsistent reverseSobelSequence = false

theorem reverse_sobel_inconsistent :
    isConsistent reverseSobelSequence = false := by native_decide


-- ═══ Mixed Generic Sequences ═══
-- "Lions have manes and lions give birth to live young."

/-- Two entities: a male lion and a female lion. -/
inductive Animal where
  | maleLion | femaleLion
  deriving DecidableEq, BEq, Repr

def hasMane : Animal → Bool
  | .maleLion => true
  | .femaleLion => false

def givesLiveBirth : Animal → Bool
  | .maleLion => false
  | .femaleLion => true

/-- "Lions have manes" — restrictor incorporates Kirkpatrick's contextual
    variable C = alternatives to having a mane (sexually-selected traits).
    Only male lions are in the domain of "mane alternatives." -/
def lionsHaveManes : GenericSentence Animal :=
  ⟨λ e => e == .maleLion, hasMane, [.maleLion]⟩

/-- "Lions give birth to live young" — restrictor incorporates C =
    alternatives to giving birth (modes of reproduction).
    Only female lions are in the domain of "reproduction alternatives." -/
def lionsGiveBirth : GenericSentence Animal :=
  ⟨λ e => e == .femaleLion, givesLiveBirth, [.femaleLion]⟩

/-- Mixed sequence: both generics use different contextual variables C,
    so the first generic's salient individuals don't satisfy the second
    generic's restrictor. No mutual interference. -/
def mixedSequence : List (GenericSentence Animal) :=
  [lionsHaveManes, lionsGiveBirth]

#guard isConsistent mixedSequence = true

/-- Mixed generic sequences are consistent: the two generics don't
    interfere because they have non-overlapping restrictors (different
    contextual variables C). -/
theorem mixed_consistent : isConsistent mixedSequence = true := by native_decide

/-- The reverse mixed sequence is also consistent — mixed sequences
    are symmetric because the restrictors don't overlap. -/
theorem mixed_reverse_consistent :
    isConsistent [lionsGiveBirth, lionsHaveManes] = true := by native_decide


-- ═══ General Theorem Instantiations ═══

/-- The raven Sobel pair satisfies the general consistency theorem.
    This derives `sobel_consistent` from the paper's general argument (§5.1)
    rather than finite model checking. -/
theorem sobel_consistent_general :
    isConsistent sobelSequence = true :=
  sobel_pair_consistent ravensAreBlack albinoRavensArentBlack
    (by decide) (by decide) (by decide) (by decide)

/-- The raven reverse Sobel pair satisfies the general inconsistency theorem.
    This derives `reverse_sobel_inconsistent` from the general argument (§5.2). -/
theorem reverse_sobel_inconsistent_general :
    isConsistent reverseSobelSequence = false :=
  reverse_sobel_pair_inconsistent ravensAreBlack albinoRavensArentBlack
    (by decide) (by decide)
    (by intro e; cases e <;> simp [albinoRavensArentBlack, ravensAreBlack, isAlbinoRaven, isRaven])
    (by decide) (by decide)


-- ═══ Additional Data from §2 ═══

/-- Example (4): "Teachers care for their students; but bad teachers don't."
    Another Sobel pair demonstrating the generality of the phenomenon. -/
inductive Person where
  | goodTeacher1 | goodTeacher2 | badTeacher
  deriving DecidableEq, BEq, Repr

def isTeacher : Person → Bool := fun _ => true
def isBadTeacher : Person → Bool
  | .badTeacher => true
  | _ => false
def caresForStudents : Person → Bool
  | .goodTeacher1 => true
  | .goodTeacher2 => true
  | .badTeacher => false

def teachersCare : GenericSentence Person :=
  ⟨isTeacher, caresForStudents, [.goodTeacher1, .goodTeacher2]⟩
def badTeachersDontCare : GenericSentence Person :=
  ⟨isBadTeacher, fun e => !caresForStudents e, [.badTeacher]⟩

-- (4a) "Teachers care for their students; but bad teachers don't." — felicitous
#guard isConsistent [teachersCare, badTeachersDontCare] = true
-- (4b) "#Bad teachers don't care for their students; but teachers do." — infelicitous
#guard isConsistent [badTeachersDontCare, teachersCare] = false

theorem teachers_sobel_consistent :
    isConsistent [teachersCare, badTeachersDontCare] = true := by native_decide
theorem teachers_reverse_inconsistent :
    isConsistent [badTeachersDontCare, teachersCare] = false := by native_decide


-- ═══ Static-Dynamic Bridge ═══

/-- In discourse-initial position, Kirkpatrick's dynamic semantics
    reduces to static truth conditions. Both "Ravens are black" and
    "Albino ravens aren't black" are true when evaluated against an
    empty horizon — matching the predictions of static GEN.

    The dynamic theory diverges from statics only in multi-sentence
    discourse, where prior generics have expanded the horizon. -/
theorem static_both_true_independently :
    (evalGeneric [] ravensAreBlack).2 = true ∧
    (evalGeneric [] albinoRavensArentBlack).2 = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- The static-dynamic bridge instantiated for the raven model:
    discourse-initial evaluation of "Ravens are black" equals the
    static truth condition (all normal ravens satisfy the scope). -/
theorem ravens_static_dynamic_bridge :
    (evalGeneric [] ravensAreBlack).2 =
    (normalRavens.filter isRaven).all isBlack :=
  evalGeneric_empty_eq_static ravensAreBlack

/-- Yet the order matters for the dynamic evaluation. -/
theorem order_matters :
    isConsistent sobelSequence ≠ isConsistent reverseSobelSequence := by
  native_decide


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
    (by intro e; cases e <;> simp [albinoRavensArentBlack, ravensAreBlack,
         isAlbinoRaven, isRaven])
    (by decide)

/-- The raven model witnesses horizon non-commutativity:
    the forward horizon [normal1, normal2, albino] differs from
    the reverse horizon [albino]. -/
theorem raven_horizon_noncommutative :
    horizonStep albinoRavensArentBlack (horizonStep ravensAreBlack []) ≠
    horizonStep ravensAreBlack (horizonStep albinoRavensArentBlack []) :=
  sobel_horizon_noncommutative ravensAreBlack albinoRavensArentBlack
    (by decide) (by decide)
    (by intro e; cases e <;> simp [albinoRavensArentBlack, ravensAreBlack,
         isAlbinoRaven, isRaven])
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
    isConsistent [lionsHaveManes, lionsGiveBirth] = true ∧
    isConsistent [lionsGiveBirth, lionsHaveManes] = true :=
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


end Phenomena.Generics.Studies.Kirkpatrick2024
