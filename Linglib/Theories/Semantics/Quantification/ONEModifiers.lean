import Linglib.Theories.Semantics.Quantification.UnifiedUniversal

/-!
# ONE Modifiers for Distributive Universal Quantifiers
@cite{haslinger-etal-2025-nllt}

In 2-form languages (English, German, Hindi, ...), distributive [+dist]
UQ forms contain an additional syntactic head ONE below Q_∀ that
restricts the complement to atomic or non-overlapping individuals.

Two variants:
- **ONE_∅**: presupposes non-overlap among restrictor elements.
  English *every* = Q_∀[ONE_∅].
- **ONE_AT**: presupposes atomicity (stronger than non-overlap).
  English *each* = Q_∀[ONE_∅[ONE_AT]].

Non-distributive [−dist] forms like *all* are bare Q_∀ with no ONE.

The ONE_AT atomicity presupposition explains why *each ten minutes*
is ungrammatical: intervals are not atoms, so ONE_AT fails.
-/

namespace Semantics.Quantification.ONEModifiers

open Mereology
open Semantics.Quantification.UnifiedUniversal

-- ════════════════════════════════════════════════════
-- § 1. ONE Presuppositional Modifiers
-- ════════════════════════════════════════════════════

/--
**ONE_∅**: presupposes that the restrictor contains at least two
elements and that no two distinct elements overlap.

@cite{haslinger-etal-2025-nllt} eq. (75a): blocks plural complements
(which contain overlapping sums) and forces [+dist] readings.
-/
structure ONE_empty {α : Type*} [PartialOrder α] (P : α → Prop) : Prop where
  /-- At least two distinct elements in P -/
  has_two : ∃ (x y : α), P x ∧ P y ∧ x ≠ y
  /-- Pairwise non-overlap: distinct P-elements share no part -/
  pairwise_disjoint : ∀ (x y : α), P x → P y → Overlap x y → x = y

/--
**ONE_AT**: presupposes that the restrictor contains at least two
elements and that all elements are atoms.

@cite{haslinger-etal-2025-nllt} eq. (75b): additionally blocks
degree-interval predicates like *ten minutes* (which are non-atomic).
This distinguishes *each* from *every*.
-/
structure ONE_AT {α : Type*} [PartialOrder α] (P : α → Prop) : Prop where
  /-- At least two distinct elements in P -/
  has_two : ∃ (x y : α), P x ∧ P y ∧ x ≠ y
  /-- All P-elements are atoms -/
  all_atomic : ∀ (x : α), P x → Atom x

/-- ONE_AT implies ONE_∅: atoms are pairwise non-overlapping.

    If x and y are both atoms and Overlap(x, y), then ∃z, z ≤ x ∧ z ≤ y.
    By atomicity of x: z = x. By atomicity of y: z = y. Hence x = y. -/
theorem ONE_AT_implies_ONE_empty {α : Type*} [PartialOrder α]
    {P : α → Prop} (h : ONE_AT P) : ONE_empty P where
  has_two := h.has_two
  pairwise_disjoint := λ x y hPx hPy ⟨z, hzx, hzy⟩ =>
    let hzx_eq := h.all_atomic x hPx z hzx  -- z = x
    let hzy_eq := h.all_atomic y hPy z hzy  -- z = y
    hzx_eq.symm.trans hzy_eq

-- ════════════════════════════════════════════════════
-- § 2. English UQ Decomposition
-- ════════════════════════════════════════════════════

/--
**all = Q_∀**: bare universal quantifier, no ONE modifier.
Non-distributive with PL complements, distributive with SG complements.
@cite{haslinger-etal-2025-nllt} eq. (79a).
-/
abbrev allSem {α : Type*} [PartialOrder α] := @QForall α _

/--
**every = Q_∀ + ONE_∅**: universal quantifier with non-overlap presupposition.
Always distributive (since ONE_∅ ensures all elements are maxNonOverlap).
@cite{haslinger-etal-2025-nllt} eq. (79b).
-/
def everyPresup {α : Type*} [PartialOrder α]
    (P : α → Prop) (Q : α → Prop) : Prop :=
  ONE_empty P ∧ QForall P Q

/--
**each = Q_∀ + ONE_∅ + ONE_AT**: universal quantifier with atomicity
presupposition. Always distributive, and restricted to atomic predicates.
@cite{haslinger-etal-2025-nllt} eq. (79c).
-/
def eachPresup {α : Type*} [PartialOrder α]
    (P : α → Prop) (Q : α → Prop) : Prop :=
  ONE_AT P ∧ QForall P Q

/-- *each* entails *every*: ONE_AT is stronger than ONE_∅. -/
theorem each_entails_every {α : Type*} [PartialOrder α]
    {P Q : α → Prop} (h : eachPresup P Q) : everyPresup P Q :=
  ⟨ONE_AT_implies_ONE_empty h.1, h.2⟩

/-- When ONE_empty holds, QForall reduces to pointwise universal.
    This is the core semantic consequence of the ONE_∅ presupposition. -/
theorem every_distributes {α : Type*} [PartialOrder α]
    {P Q : α → Prop} (hONE : ONE_empty P) :
    QForall P Q ↔ ∀ (x : α), P x → Q x := by
  constructor
  · intro hQ x hPx
    apply hQ
    exact ⟨hPx, λ y hy hov => le_of_eq (hONE.pairwise_disjoint y x hy hPx (Overlap.symm hov))⟩
  · intro hAll x ⟨hPx, _⟩
    exact hAll x hPx

end Semantics.Quantification.ONEModifiers
