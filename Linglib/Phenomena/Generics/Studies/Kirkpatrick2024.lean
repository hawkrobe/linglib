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


-- ═══ Comparison with Static Theories ═══

/-- Static theories assign the same truth conditions to both orders.
    In the static view, both "Ravens are black" and "Albino ravens aren't
    black" are independently true. The conjunction should be consistent
    regardless of order. But speakers judge the reverse order as infelicitous.

    The dynamic theory explains this: the truth value of each generic
    depends on which individuals were made salient by prior discourse. -/
theorem static_both_true_independently :
    (evalGeneric [] ravensAreBlack).2 = true ∧
    (evalGeneric [] albinoRavensArentBlack).2 = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- Yet the order matters for the dynamic evaluation. -/
theorem order_matters :
    isConsistent sobelSequence ≠ isConsistent reverseSobelSequence := by
  native_decide


end Phenomena.Generics.Studies.Kirkpatrick2024
