/-!
# Generic Containment and the *ABA Constraint
@cite{bobaljik-2012} @cite{caha-2009}

## Overview

Many morphological hierarchies obey a **contiguity** constraint: if two
positions X and Z on the hierarchy share a suppletive form A, then every
position Y between them also has form A. The pattern A–B–A — with B ≠ A —
is systematically unattested. This is the **\*ABA constraint**.

The constraint arises whenever three conditions hold:
1. **Containment**: each position's representation properly contains
   all lower positions' representations.
2. **Late Insertion** (Vocabulary Insertion): exponents are inserted
   post-syntactically based on feature matching.
3. **Elsewhere ordering**: among competing VI rules, the most specific
   match wins.

This module provides **domain-independent** contiguity predicates on
`List Nat` (lists of form-class indices), which are then instantiated
by domain-specific modules:

- **Degree containment**: POS ⊂ CMPR ⊂ SPRL
  (`DegreeContainment.lean`, @cite{bobaljik-2012})
- **Case containment**: NOM ⊂ ACC ⊂ GEN ⊂ DAT
  (`CaseContainment.lean`, @cite{caha-2009})

The structural isomorphism between these domains is made explicit
via bridge theorems in each domain module.
-/

namespace Morphology.Containment

-- ============================================================================
-- § 1: Generic *ABA Detection
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

/-- Is a pattern contiguous? Each form class occupies a contiguous
    span of positions on the hierarchy. Equivalent to ¬violatesABA. -/
def isContiguous (pattern : List Nat) : Bool :=
  !violatesABA pattern

-- ============================================================================
-- § 2: Closed-Form Lemmas for Small Lists
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
-- § 3: Verification on Concrete Patterns
-- ============================================================================

/-- ABA: the canonical violation. -/
theorem aba_violates : violatesABA [0, 1, 0] = true := by decide

/-- AAA: regular throughout. -/
theorem aaa_contiguous : isContiguous [0, 0, 0] = true := by decide

/-- ABB: suppletive at CMPR+SPRL. -/
theorem abb_contiguous : isContiguous [0, 1, 1] = true := by decide

/-- ABC: three distinct forms. -/
theorem abc_contiguous : isContiguous [0, 1, 2] = true := by decide

/-- AAB: contiguous (but excluded by VI locality in degree domain). -/
theorem aab_contiguous : isContiguous [0, 0, 1] = true := by decide

/-- ABAB: violates on 4-position hierarchy. -/
theorem abab_violates : violatesABA [0, 1, 0, 1] = true := by decide

/-- AABB: contiguous on 4-position hierarchy. -/
theorem aabb_contiguous : isContiguous [0, 0, 1, 1] = true := by decide

-- ============================================================================
-- § 4: Exhaustive 3-Position Check
-- ============================================================================

/-- All 27 patterns over 3 positions with indices {0, 1, 2}. -/
def allPatterns3 : List (List Nat) :=
  (List.map (λ a =>
    (List.map (λ b =>
      List.map (λ c => [a, b, c]) [0, 1, 2]
    ) [0, 1, 2]).flatten
  ) [0, 1, 2]).flatten

/-- Exactly 6 of the 27 three-position patterns violate *ABA.
    (3 choices for the "A" value × 2 choices for the "B" value.) -/
theorem six_aba_violations :
    (allPatterns3.filter violatesABA).length = 6 := by decide

/-- The remaining 21 patterns are contiguous. -/
theorem twentyone_contiguous :
    (allPatterns3.filter isContiguous).length = 21 := by decide

/-- No pattern is both ABA-violating and contiguous. -/
theorem no_aba_contiguous :
    (allPatterns3.filter (λ p => violatesABA p && isContiguous p)).length = 0 := by
  decide

end Morphology.Containment
