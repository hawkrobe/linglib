import Linglib.Semantics.Mereology

/-!
# Unified Semantics for Universal Quantification
[haslinger-etal-2025-nllt]

A single lexical meaning for universal quantifiers across languages,
from "A unified semantics for distributive and non-distributive universal
quantifiers across languages" (NLLT 43, 2025).

## Core Idea

The morpheme Q_∀ applies its scope predicate to every **maximal
non-overlapping** element of the restrictor denotation. Whether the
result is distributive or non-distributive falls out from the
algebraic structure of the noun denotation:

- **Singular NP** (atoms only): every element is maximal and
  non-overlapping → Q_∀ distributes over each atom. **[+dist]**
- **Plural NP** (closed under sum): one maximal element = the sum
  → Q_∀ applies scope to the sum. **[−dist]**

This is the **Distributivity-Number Generalization (DNG)**.

## Architecture

Q_∀ is defined abstractly over `PartialOrder` using `Mereology.Overlap`,
`Mereology.Atom`, and `Mereology.Maximal`. A decidable `Finset`-based
variant is provided for computational verification.

The connection to the standard GQ `every_sem` (in `Quantifier.lean`) and
to the tolerance-based `distMaximal` (in `Distributivity.lean`) is
established via bridge theorems, not by replacement.
-/

namespace Quantification.UnifiedUniversal

open _root_.Mereology

/-! ### Maximal Non-Overlapping Elements -/

/--
An element x is **maximal non-overlapping** in P iff x ∈ P and every
P-element that overlaps x is a part of x.

This is the condition in [haslinger-etal-2025-nllt] eq. (70):
P(x) ∧ ¬∃y[P(y) ∧ ∃z[z ⊑ x ∧ z ⊑ y] ∧ y ⊄ x].

Equivalently: x absorbs all overlapping P-elements. In a singular
NP denotation (atoms only), every atom satisfies this. In a plural
NP denotation (closed under sum), only the maximal sum does.
-/
def maxNonOverlap {α : Type*} [PartialOrder α] (P : α → Prop) (x : α) : Prop :=
  P x ∧ ∀ (y : α), P y → Overlap x y → y ≤ x

/-! ### The Unified Universal Quantifier -/

/--
**Q_∀**: the unified universal quantifier.

⟦Q_∀⟧ = λP.λQ.∀x[maxNonOverlap(P, x) → Q(x)]

Q_∀ applies the scope predicate Q to every maximal non-overlapping
element of the restrictor P. [haslinger-etal-2025-nllt] eq. (70).

When P = ⟦student⟧ (atoms {a,b,c}):
  Q_∀(P)(Q) = Q(a) ∧ Q(b) ∧ Q(c)  — distributive

When P = ⟦student-PL⟧ (closed under ⊔, max = a⊔b⊔c):
  Q_∀(P)(Q) = Q(a⊔b⊔c)  — non-distributive (maximization)
-/
def QForall {α : Type*} [PartialOrder α]
    (P : α → Prop) (Q : α → Prop) : Prop :=
  ∀ (x : α), maxNonOverlap P x → Q x

/-! ### Properties of maxNonOverlap -/

/-- maxNonOverlap implies Maximal: if x absorbs all overlapping
    P-elements, it is certainly maximal (no proper P-extension). -/
theorem maxNonOverlap_imp_maximal {α : Type*} [PartialOrder α]
    {P : α → Prop} {x : α} (h : maxNonOverlap P x) :
    Maximal P x :=
  ⟨h.1, λ y hy hle => h.2 y hy ⟨x, le_refl x, hle⟩⟩

/-- For atoms with a disjointness property, maxNonOverlap reduces to
    membership in P.

    The hypothesis `hDisj` says distinct P-atoms don't overlap. This
    holds in any atomic Boolean algebra (or distributive lattice where
    atoms are join-prime). -/
theorem maxNonOverlap_of_atom {α : Type*} [PartialOrder α]
    {P : α → Prop} {x : α}
    (hPx : P x) (_hAtom : Atom x)
    (hDisj : ∀ (y : α), P y → Overlap x y → y = x) :
    maxNonOverlap P x :=
  ⟨hPx, λ y hy hov => le_of_eq (hDisj y hy hov)⟩

/-- In a CUM predicate, an element that is Maximal is also
    maxNonOverlap. CUM ensures all P-elements join into the max,
    so any P-element overlapping max is necessarily ≤ max.

    Proof: if y ∈ P overlaps x, then x ⊔ y ∈ P (by CUM), and
    x ≤ x ⊔ y, so x = x ⊔ y (by maximality), hence y ≤ x. -/
theorem maxNonOverlap_of_cum_maximal {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (hCum : CUM P)
    {x : α} (hMax : Maximal P x) :
    maxNonOverlap P x :=
  ⟨hMax.1, λ y hy _hov => le_trans le_sup_right (hMax.2 (hCum hMax.1 hy) le_sup_left)⟩

/-! ### The Distributivity-Number Generalization (DNG) -/

/--
**DNG for singular complements** (atoms).

When every P-element is an atom and distinct P-atoms don't overlap,
Q_∀(P)(Q) reduces to universal quantification: ∀x, P(x) → Q(x).

This is the **[+dist]** case: [haslinger-etal-2025-nllt] eq. (30b).
-/
theorem dng_atoms {α : Type*} [PartialOrder α]
    {P Q : α → Prop}
    (hAtoms : ∀ (x : α), P x → Atom x)
    (hDisj : ∀ (x y : α), P x → P y → Overlap x y → x = y) :
    QForall P Q ↔ ∀ (x : α), P x → Q x := by
  constructor
  · intro hQ x hPx
    have hMNO : maxNonOverlap P x :=
      maxNonOverlap_of_atom hPx (hAtoms x hPx) (λ y hy hov => hDisj y x hy hPx (Overlap.symm hov))
    exact hQ x hMNO
  · intro hAll x ⟨hPx, _⟩
    exact hAll x hPx

/--
**DNG for plural complements** (CUM with a maximal element).

When P is CUM and has a maximal element m, Q_∀(P)(Q) reduces to Q(m).

This is the **[−dist]** case: [haslinger-etal-2025-nllt] eq. (30a).
The unique maximal element of a CUM predicate is the join of all
P-elements — the "maximal plurality."
-/
theorem dng_cum {α : Type*} [SemilatticeSup α]
    {P Q : α → Prop} (hCum : CUM P)
    {m : α} (hMax : Maximal P m)
    (hOnly : ∀ (x' : α), maxNonOverlap P x' → x' = m) :
    QForall P Q ↔ Q m := by
  constructor
  · intro hQ
    exact hQ m (maxNonOverlap_of_cum_maximal hCum hMax)
  · intro hQm x hMNO
    have heq := hOnly x hMNO
    exact heq ▸ hQm

/-- In a CUM predicate, maxNonOverlap elements are unique (= the max).

    This derives `hOnly` for `dng_cum`: if P is CUM, any two
    maxNonOverlap elements must be equal (both are Maximal,
    and CUM predicates have at most one maximal element). -/
theorem maxNonOverlap_unique_of_cum {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (hCum : CUM P)
    {x y : α} (hx : maxNonOverlap P x) (hy : maxNonOverlap P y) :
    x = y :=
  cum_maximal_unique hCum
    (maxNonOverlap_imp_maximal hx)
    (maxNonOverlap_imp_maximal hy)

/-- Combined DNG-PL: for CUM predicates with a maximal element,
    Q_∀(P)(Q) ↔ Q(m), without needing to supply `hOnly` separately. -/
theorem dng_cum' {α : Type*} [SemilatticeSup α]
    {P Q : α → Prop} (hCum : CUM P)
    {m : α} (hMax : Maximal P m) :
    QForall P Q ↔ Q m :=
  dng_cum hCum hMax (λ _x hx =>
    maxNonOverlap_unique_of_cum hCum hx (maxNonOverlap_of_cum_maximal hCum hMax))

/-! ### Bridge to Standard GQ (every_sem) -/

/--
Q_∀ on an atomic restrictor is equivalent to the standard generalized
quantifier ∀x[P(x) → Q(x)], which is the denotation of `every_sem`
in `Quantifier.lean`.

This theorem bridges the mereological Q_∀ to the flat-domain GQ:
the two coincide when the restrictor has no mereological structure
(all elements are atoms with no overlap).
-/
theorem QForall_eq_standardGQ {α : Type*} [PartialOrder α]
    {P Q : α → Prop}
    (hAtoms : ∀ (x : α), P x → Atom x)
    (hDisj : ∀ (x y : α), P x → P y → Overlap x y → x = y) :
    QForall P Q ↔ ∀ (x : α), P x → Q x :=
  dng_atoms hAtoms hDisj

/-! ### Decidable Finset Variant -/

section Decidable

variable {α : Type*} [DecidableEq α] [Fintype α] [PartialOrder α]
         [DecidableRel ((· ≤ ·) : α → α → Prop)]

/-- Decidable overlap on a finite type with decidable ≤. -/
instance decidableOverlap (x y : α) : Decidable (Overlap x y) :=
  Fintype.decidableExistsFintype

/-- Bool-valued maxNonOverlap for computation. -/
def maxNonOverlapB (P : α → Bool) (x : α) : Bool :=
  P x && decide (∀ (y : α), P y = true → Overlap x y → y ≤ x)

/-- Computable Q_∀ over a Fintype. -/
def QForallDec (P : α → Bool) (Q : α → Bool) : Bool :=
  decide (∀ (x : α), maxNonOverlapB P x = true → Q x = true)

end Decidable

end Quantification.UnifiedUniversal
