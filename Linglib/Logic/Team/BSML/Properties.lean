module

public import Linglib.Logic.Team.BSML.Defs
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Definability

/-!
# BSML formula closure properties (Anttila 2021 Proposition 2.2.8)

[anttila-2021] [aloni-2022]

For BSML's `support` relation, this file proves the three constituent
properties from Anttila 2021 Proposition 2.2.8 (specialised to a logic
without global disjunction ⨼) plus the flatness corollary from Anttila
2.2.16.

## Main declarations

* `supClosed_support` — every BSML formula has sup-closed support
  (Anttila 2.2.8 part 2; BSML's connective set has no ⨼, so the
  union-closure obstruction is absent).
* `support_empty_of_neFree` — NE-free BSML formulas are supported on
  the empty team (Anttila 2.2.8 part 1).
* `isLowerSet_support_of_neFree` — NE-free BSML formulas are
  downward-closed (Anttila 2.2.8 part 1).
* `isFlat_support_of_neFree` — NE-free BSML formulas are flat
  (Anttila 2.2.16), derived via Anttila
  Proposition 2.2.2 from the three properties above.

## Implementation notes

The negation case needs bilateral mutual induction (support of `¬φ` is
anti-support of `φ`), so each property is proved as a *joint* statement
over support + anti-support via a `private` helper, then the public form
projects the support component.

Proposition 2.2.16 itself, `support t ↔ ∀ w ∈ t, Realize w` with `Realize`
classical Kripke truth, is proved directly in `Classical.lean`
(`support_iff_forall_realize`); this file's proof routes through the
foundational decomposition instead.

The decomposition through Anttila 2.2.8 + 2.2.2 is reusable: any future
team-semantic logic in linglib (QBSML, inquisitive, dependence logic)
needs the same structural argument — proving the three closure properties
separately and composing them via `Team.isFlat_iff`.
-/

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)

open Team

variable {W : Type*} [DecidableEq W] {Atom : Type*}

/-! ### Closure properties by induction over the connectives

Each case is the closure lemma of its connective from `Team/Operations.lean`, and
negation swaps the two polarities. -/

/-- Joint union closure for both polarities (Anttila 2.2.8 part 2). -/
private theorem support_and_antiSupport_supClosed (φ : Formula Atom) (M : KripkeModel W Atom) :
    SupClosed {t | support M φ t} ∧ SupClosed {t | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨supClosed_flat _, supClosed_flat _⟩
  | ne => exact ⟨supClosed_ne, supClosed_singleton_empty⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.inter ih₂.1, ih₁.2.tensor ih₂.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.tensor ih₂.1, ih₁.2.inter ih₂.2⟩
  | poss ψ _ => exact ⟨supClosed_flat _, supClosed_flat _⟩

/-- BSML support is sup-closed (Anttila Proposition 2.2.8 part 2). BSML's
    connective set lacks the global disjunction ⨼, so the union-closure
    obstruction is absent and all formulas satisfy the property. -/
theorem supClosed_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    SupClosed { t : Finset W | support M φ t } :=
  (support_and_antiSupport_supClosed φ M).1

/-- Joint empty-team property for NE-free formulas (Anttila 2.2.8 part 1). -/
private theorem support_and_antiSupport_empty_of_neFree
    (φ : Formula Atom) (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    support M φ ∅ ∧ antiSupport M φ ∅ := by
  induction φ with
  | atom p => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨⟨(ih₁ hNE.1).1, (ih₂ hNE.2).1⟩, empty_mem_tensor (ih₁ hNE.1).2 (ih₂ hNE.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨empty_mem_tensor (ih₁ hNE.1).1 (ih₂ hNE.2).1, ⟨(ih₁ hNE.1).2, (ih₂ hNE.2).2⟩⟩
  | poss ψ _ => exact ⟨empty_mem_flat _, empty_mem_flat _⟩

/-- NE-free BSML formulas are supported on the empty team. The only
    obstruction is NE itself, which fails on ∅ by definition. -/
theorem support_empty_of_neFree {φ : Formula Atom}
    (hNE : φ.NEFree) (M : KripkeModel W Atom) : support M φ ∅ :=
  (support_and_antiSupport_empty_of_neFree φ hNE M).1

/-- Joint downward closure for NE-free formulas (Anttila 2.2.8 part 1). -/
private theorem support_and_antiSupport_isLowerSet_of_neFree
    (φ : Formula Atom) (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    IsLowerSet {t | support M φ t} ∧ IsLowerSet {t | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.inter (ih₂ hNE.2).1, (ih₁ hNE.1).2.tensor (ih₂ hNE.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.tensor (ih₂ hNE.2).1, (ih₁ hNE.1).2.inter (ih₂ hNE.2).2⟩
  | poss ψ _ => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩

/-- NE-free BSML formulas are downward-closed: support survives under
    taking subsets of the team. -/
theorem isLowerSet_support_of_neFree {φ : Formula Atom}
    (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    IsLowerSet { t : Finset W | support M φ t } :=
  (support_and_antiSupport_isLowerSet_of_neFree φ hNE M).1

/-- Joint order-convexity for both polarities ([anttila-2025] Proposition
    3.3.1). The split cases need union closure of the subformulas
    (`Set.OrdConnected.tensor`), which is exactly why split disjunction
    preserves convexity only in a union-closed setting ([anttila-2025] Fact
    3.2.7 vs Proposition 3.3.1). -/
private theorem support_and_antiSupport_ordConnected
    (φ : Formula Atom) (M : KripkeModel W Atom) :
    Set.OrdConnected {t | support M φ t} ∧ Set.OrdConnected {t | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨ordConnected_flat _, ordConnected_flat _⟩
  | ne => exact ⟨ordConnected_ne, ordConnected_singleton_empty⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨ih₁.1.inter ih₂.1, ih₁.2.tensor ih₂.2 (support_and_antiSupport_supClosed ψ₁ M).2
      (support_and_antiSupport_supClosed ψ₂ M).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨ih₁.1.tensor ih₂.1 (support_and_antiSupport_supClosed ψ₁ M).1
      (support_and_antiSupport_supClosed ψ₂ M).1, ih₁.2.inter ih₂.2⟩
  | poss ψ _ => exact ⟨ordConnected_flat _, ordConnected_flat _⟩

/-- **BSML support is order-convex** for every formula — NE-bearing included
    ([anttila-2025] Proposition 3.3.1): `{ t | support M φ t }` is
    `Set.OrdConnected`, i.e. `s ⊆ t ⊆ u` with `support M φ s` and
    `support M φ u` forces `support M φ t`.

    Generalizes `isLowerSet_support_of_neFree`: for NE-free `φ` the empty-team
    property holds, and `Team.isLowerSet_iff_ordConnected_of_empty`
    recovers downward closure from convexity. Together with `supClosed_support`,
    this is the convex-and-union-closed property for which BSML is expressively
    complete ([anttila-2025]). -/
theorem ordConnected_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    Set.OrdConnected { t : Finset W | support M φ t } :=
  (support_and_antiSupport_ordConnected φ M).1

/-! ### Flatness corollary (Anttila 2.2.16) -/

/-- **Anttila Proposition 2.2.16**, flatness form: NE-free BSML formulas
    are flat — team support equals pointwise support at each world in the
    team.

    Derived from Anttila 2.2.2 (`Team.isFlat_iff`) applied to
    the three closure properties proved above. The same conclusion follows
    from the classical-truth form `support_iff_forall_realize` in
    `Classical.lean`. -/
theorem isFlat_support_of_neFree {φ : Formula Atom}
    (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    IsFlat { t : Finset W | support M φ t } :=
  isFlat_of_isLowerSet_supClosed_empty
    (isLowerSet_support_of_neFree hNE M)
    (supClosed_support M φ)
    (support_empty_of_neFree hNE M)

/-! ### Soundness for the closure cell (Definability bridge) -/

open Team in
/-- **The NE-free fragment of BSML defines flat properties** (Anttila Proposition 2.2.16), the
    fragment being the subtype of `NE`-free formulas. `NE` is exactly what moves a formula off
    the flat properties into the convex, union-closed ones (`definableClass_support_subset` in
    `BSML/ExpressiveCompleteness.lean`). -/
theorem definableClass_support_neFree_subset (M : KripkeModel W Atom) :
    definableClass (fun φ : {φ : Formula Atom // φ.NEFree} ↦ support M φ.1) ⊆ {P | IsFlat P} :=
  definableClass_subset fun φ ↦ isFlat_support_of_neFree φ.2 M

end BSML
