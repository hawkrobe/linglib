import Linglib.Core.Logic.Modal.BSML.Properties
import Linglib.Core.Logic.Modal.BSML.Bisimulation

/-!
# Expressive completeness for BSML

@cite{anttila-2025} @cite{aloni-anttila-yang-2024} @cite{aloni-2022}

@cite{anttila-2025} Chapter 3 proves that BSML is **expressively complete** for
the class of convex, union-closed, bounded-bisimulation-invariant modal team
properties — solving the BSML expressive-power problem left open in
@cite{aloni-anttila-yang-2024}. In the `Team/Definability.lean` vocabulary this
is `ExpressivelyCompleteFor (support M)` for the cell
`convexProperties ∩ unionClosedProperties ∩ bisimClosedProperties M`.

The theorem splits into two halves:

* **Soundness** (`⟦BSML⟧ ⊆ cell`) — every definable property lies in the cell.
  Fully proved here, assembling the three closure pillars:
  `ordConnected_support` (convexity, Proposition 3.3.1), `supClosed_support`
  (union closure), and `bisimClosed_definedBy` (Theorem 3.8 / bisimulation
  invariance, `BSML/Bisimulation.lean`).
* **Completeness** (`cell ⊆ ⟦BSML⟧`) — the hard converse: every property in the
  cell is BSML-definable. Stated here as `expressiveCompleteness_converse` with
  a `sorry`; it is the within-model specialisation of @cite{anttila-2025} Ch 3
  and requires the characteristic-formula machinery (see the TODO there).

## Main declarations

* `BisimClosed M P`, `bisimClosedProperties M` — bounded-bisimulation closure of
  a team property within `M` (the third soundness pillar as a closure cell).
* `bisimInvariant_support` — Theorem 3.8 specialised to one model.
* `bisimClosed_definedBy` — every BSML-definable property is bisim-closed.
* `expressiveSoundness` — `⟦BSML⟧ ⊆` the convex/union-closed/bisim-closed cell.
* `expressiveCompleteness_converse` — the open converse (`sorry`).
* `expressivelyComplete` — the headline equality (inherits the converse `sorry`).
-/

namespace Core.Logic.Modal.BSML

open Core.Logic.Team Core.Logic.Modal

variable {W : Type*} [DecidableEq W] [Fintype W] {Atom : Type*}

/-! ### Bounded-bisimulation closure (the third soundness pillar) -/

/-- A team property is **bounded-bisimulation-closed** in `M` if for some depth
    `k` it is closed under `k`-bisimulation of teams within `M`. This is the
    closure invariant — alongside convexity and union closure — that
    characterises BSML-definability (@cite{anttila-2025} Ch 3). -/
def BisimClosed (M : BSMLModel W Atom) (P : TeamProperty W) : Prop :=
  ∃ k : ℕ, ∀ s s' : Finset W, StateBisim k M s M s' → (s ∈ P ↔ s' ∈ P)

/-- The class of bounded-bisimulation-closed team properties of `M`. -/
def bisimClosedProperties (M : BSMLModel W Atom) : Set (TeamProperty W) :=
  { P | BisimClosed M P }

/-- **BSML support is bounded-bisimulation invariant within a model**: if
    `s ⇌_k s'` and `k ≥ φ.modalDepth`, then `s` and `s'` agree on `φ`. Immediate
    from Theorem 3.8 (`bisim_invariant_eval`) at `M' := M`. -/
theorem bisimInvariant_support (M : BSMLModel W Atom) (φ : BSMLFormula Atom)
    {k : ℕ} (hd : φ.modalDepth ≤ k) {s s' : Finset W}
    (h : StateBisim k M s M s') : support M φ s ↔ support M φ s' :=
  bisim_invariant_eval φ hd h true

/-- Every BSML-definable team property is bounded-bisimulation-closed, with
    witnessing depth the formula's modal depth. -/
theorem bisimClosed_definedBy (M : BSMLModel W Atom) (φ : BSMLFormula Atom) :
    BisimClosed M (definedBy (support M) φ) :=
  ⟨φ.modalDepth, fun _ _ h => bisimInvariant_support M φ le_rfl h⟩

/-! ### Expressive completeness -/

/-- **Soundness half** (@cite{anttila-2025} Ch 3): every BSML-definable team
    property is convex, union-closed, and bounded-bisimulation-closed. Assembles
    `ordConnected_support`, `supClosed_support`, and `bisimClosed_definedBy`. -/
theorem expressiveSoundness (M : BSMLModel W Atom) :
    definableClass (support M) ⊆
      convexProperties ∩ unionClosedProperties ∩ bisimClosedProperties M := by
  intro P hP
  simp only [mem_definableClass] at hP
  obtain ⟨φ, rfl⟩ := hP
  exact ⟨⟨ordConnected_support M φ, supClosed_support M φ⟩, bisimClosed_definedBy M φ⟩

/-- **Completeness half** (@cite{anttila-2025} Ch 3 — the hard direction, the
    BSML expressive-power problem left open by @cite{aloni-anttila-yang-2024}
    and solved via Knudstorp's convexity machinery): every convex, union-closed,
    bounded-bisimulation-closed team property is BSML-definable.

    TODO: prove via characteristic formulas. The prerequisite is the
    Hennessy-Milner direction (Theorem 3.3, deferred in `BSML/Bisimulation.lean`):
    for `[Fintype Atom]`, build NE-free Hintikka formulas `χ_w^k` satisfying
    `{v} ⊨ χ_w^k ↔ WorldBisim k M w M v`, lift them to characteristic formulas
    for teams, then assemble `P` as a split disjunction over the
    inclusion-minimal teams of `P` of their characteristic formulas conjoined
    with `NE` (the convex + union-closed normal form — the converse of
    Proposition 3.3.1). This is the within-model specialisation of Anttila's
    cross-model theorem. -/
theorem expressiveCompleteness_converse (M : BSMLModel W Atom) :
    convexProperties ∩ unionClosedProperties ∩ bisimClosedProperties M ⊆
      definableClass (support M) := by
  sorry

/-- **BSML is expressively complete** for the convex, union-closed,
    bounded-bisimulation-closed team properties (@cite{anttila-2025} Ch 3).
    Inherits the `sorry` of `expressiveCompleteness_converse`. -/
theorem expressivelyComplete (M : BSMLModel W Atom) :
    ExpressivelyCompleteFor (support M)
      (convexProperties ∩ unionClosedProperties ∩ bisimClosedProperties M) :=
  Set.Subset.antisymm (expressiveSoundness M) (expressiveCompleteness_converse M)

end Core.Logic.Modal.BSML
