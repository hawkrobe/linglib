/-!
# Generic Containment and the *ABA Pattern
@cite{bobaljik-2012} @cite{caha-2009}

## Overview

A widely-discussed cross-linguistic generalization across several
domains of inflectional morphology: when a list of form-class indices
along an ordered hierarchy of paradigm positions is read off a
suppletion pattern, the configuration A–B–A — outer positions sharing
a form that the intervening position lacks — is systematically
unattested. Contiguity (`A–A–B`, `A–B–B`, `A–B–C`) is the modal
pattern.

This module supplies framework-neutral substrate: a contiguity
predicate over `List Nat` (a list of form-class indices), with both a
computable `Bool` decision procedure and a `Prop` wrapper carrying a
`Decidable` instance. Domain-specific instantiations live elsewhere:

- Case allomorphy (`Core/Case/Allomorphy.lean`)
- Degree morphology (`Core/Morphology/DegreeContainment.lean`)

What *explains* the gap is theory-laden and contested. The DM
tradition (`@cite{bobaljik-2012}`) derives it from post-syntactic
Vocabulary Insertion + Elsewhere ordering on a containment hierarchy.
The Nanosyntax tradition (`@cite{caha-2009}`, `@cite{starke-2009}`)
derives it from phrasal spellout + the Superset Principle on the same
containment hierarchy interpreted as syntactic structure. The two
disagree on whether the locus of explanation is morphology or syntax;
this module takes no position.
-/

namespace Morphology.Containment

-- ============================================================================
-- § 1: Generic *ABA Detection (Bool decision procedure)
-- ============================================================================

/-- Helper: does any value `vk` in the remaining list create an ABA
    pattern with a fixed outer value `vi` and inner value `vj`?
    True when vi = vk and vi ≠ vj for some vk in the tail. -/
private def checkRest (vi vj : Nat) : List Nat → Bool
  | [] => false
  | vk :: rest => (vi == vk && vi != vj) || checkRest vi vj rest

/-- Helper: for a fixed position with value `vi`, check whether
    any pair (vj, vk) drawn from the remaining list produces an
    ABA violation. -/
private def checkFromI (vi : Nat) : List Nat → Bool
  | [] => false
  | vj :: rest => checkRest vi vj rest || checkFromI vi rest

/-- Does a list of form-class indices contain an ABA violation?
    An ABA violation occurs at positions i < j < k when
    pattern[i] = pattern[k] ≠ pattern[j] — the same form class
    appears at two non-adjacent positions while the intervening
    position has a different form.

    Works for any hierarchy length: 3-position (degree), 4-position
    (case), or longer. -/
def violatesABA : List Nat → Bool
  | [] => false
  | vi :: rest => checkFromI vi rest || violatesABA rest

/-- Is a pattern contiguous (Bool)? Each form class occupies a
    contiguous span of positions on the hierarchy. Equivalent to
    ¬violatesABA. -/
def isContiguous (pattern : List Nat) : Bool :=
  !violatesABA pattern

-- ============================================================================
-- § 2: Prop Wrappers + Decidable Instances
-- ============================================================================

/-- A list violates the *ABA pattern (Prop). Bridge to the Bool
    decision procedure; downstream files that prefer Prop+`Decidable`
    over `= true` boilerplate use this. -/
def ViolatesABA (l : List Nat) : Prop := violatesABA l = true

instance (l : List Nat) : Decidable (ViolatesABA l) :=
  inferInstanceAs (Decidable (violatesABA l = true))

/-- A list is contiguous (Prop). -/
def IsContiguous (l : List Nat) : Prop := ¬ ViolatesABA l

instance (l : List Nat) : Decidable (IsContiguous l) :=
  inferInstanceAs (Decidable (¬ _))

/-- The Bool and Prop forms of contiguity agree. -/
theorem isContiguous_iff_not_violatesABA (l : List Nat) :
    isContiguous l = true ↔ ¬ ViolatesABA l := by
  unfold isContiguous ViolatesABA
  cases violatesABA l <;> decide

-- ============================================================================
-- § 3: Closed-Form Lemmas for Small Lists
-- ============================================================================

/-- *ABA on a 3-position hierarchy (degree: POS, CMPR, SPRL).
    The only possible violation is positions (0,1,2): a = c ∧ a ≠ b. -/
theorem violatesABA_three (a b c : Nat) :
    violatesABA [a, b, c] = (a == c && a != b) := by
  simp only [violatesABA, checkFromI, checkRest, Bool.or_false]

/-- *ABA on a 4-position hierarchy (case: NOM, ACC, GEN, DAT).
    Four possible triples: (0,1,2), (0,1,3), (0,2,3), (1,2,3). -/
theorem violatesABA_four (a b c d : Nat) :
    violatesABA [a, b, c, d] =
      ((a == c && a != b) ||
       (a == d && a != b) ||
       (a == d && a != c) ||
       (b == d && b != c)) := by
  simp only [violatesABA, checkFromI, checkRest, Bool.or_false]

-- ============================================================================
-- § 4: Verification on Concrete Patterns
-- ============================================================================

/-- ABA: the canonical violation. -/
theorem aba_violates : violatesABA [0, 1, 0] = true := by decide

/-- AAA: regular throughout. -/
theorem aaa_contiguous : isContiguous [0, 0, 0] = true := by decide

/-- ABB: suppletive at CMPR+SPRL. -/
theorem abb_contiguous : isContiguous [0, 1, 1] = true := by decide

/-- ABC: three distinct forms. -/
theorem abc_contiguous : isContiguous [0, 1, 2] = true := by decide

/-- AAB: contiguous (but excluded by VI locality in the degree domain;
    see `Theories/Morphology/DegreeContainment.lean`). -/
theorem aab_contiguous : isContiguous [0, 0, 1] = true := by decide

/-- ABAB: violates on 4-position hierarchy. -/
theorem abab_violates : violatesABA [0, 1, 0, 1] = true := by decide

/-- AABB: contiguous on 4-position hierarchy. -/
theorem aabb_contiguous : isContiguous [0, 0, 1, 1] = true := by decide

end Morphology.Containment
