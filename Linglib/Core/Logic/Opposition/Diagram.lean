import Linglib.Core.Logic.Opposition.Aristotelian
import Mathlib.Data.Fintype.Card

/-!
# Aristotelian diagrams (skeleton)

Per @cite{demey-smessaert-2018} (and the broader Logica Universalis tradition
of Béziau, Pellissier, Smessaert and collaborators):

An *Aristotelian diagram* is a finite indexed family of formulas together with
the matrix of Aristotelian relations between them. The classical Square is the
simplest non-trivial case (4 corners); other notable instances include:

- **Hexagons** (6 corners, 3 contradiction diagonals) — Jacoby–Sesmat–Blanché,
  Sherwood–Czeżowski, Unconnected-4
- **Cubes / octagons** (8 corners) — Smessaert 2009 logical cube,
  Buridan's octagon
- **Rhombic dodecahedron** (14 contingent corners) — the Boolean closure
  of any 4-formula fragment in classical propositional logic

This file provides the bare structural skeleton — full development of
specializations (hexagon shapes, cube generators) is deferred. The goal here
is to anchor the Square (`Square.lean`) and any future hexagons as instances
of one general structure rather than parallel ad-hoc definitions.

## Design

A `Diagram` is parameterized by:
- `ι : Type` — the index set of corners (e.g., `Fin 4` for Square, `Fin 6` for hexagon)
- `W : Type*` — the model class
- `φ : ι → W → Bool` — the corner-to-formula map

The relation matrix `relation : ι → ι → AristotelianRel` is *derived* from
`φ` (one of the four `Contradictory`/`Contrary`/`Subcontrary`/`Subaltern`
predicates from `Aristotelian.lean` holds, or `unconnected`).
-/

namespace Core.Opposition

variable {W : Type*}

/-- An Aristotelian diagram: a finite indexed family of formulas with their
    Aristotelian relations.

    The `relation_correct` field asserts that the labeled relation matrix
    matches the actual Aristotelian relations between the indexed formulas.
    Since the four relations + unconnected partition all formula-pairs (per
    Demey & Smessaert §2.1), this matrix is uniquely determined by `φ` —
    `relation` is convenience data, `relation_correct` enforces consistency. -/
structure Diagram (ι : Type) [Fintype ι] (W : Type*) where
  /-- The corner-to-formula assignment. -/
  φ : ι → W → Bool
  /-- The labeled relation between any two corners. -/
  relation : ι → ι → AristotelianRel
  /-- Soundness: the labels match the actual Aristotelian relations.
      Stated only for `contradictory`/`contrary`/`subcontrary`/`subaltern`;
      `unconnected` is the residual when none of the others holds. -/
  relation_correct : ∀ i j,
    (relation i j = AristotelianRel.contradictory → Contradictory (φ i) (φ j)) ∧
    (relation i j = AristotelianRel.contrary → Contrary (φ i) (φ j)) ∧
    (relation i j = AristotelianRel.subcontrary → Subcontrary (φ i) (φ j)) ∧
    (relation i j = AristotelianRel.subaltern → Subaltern (φ i) (φ j))

namespace Diagram

variable {ι : Type} [Fintype ι]

/-- The number of corners in the diagram. -/
def size (_ : Diagram ι W) : ℕ := Fintype.card ι

/-- A diagram corner satisfying its formula at a particular world. -/
def trueAt (D : Diagram ι W) (i : ι) (w : W) : Prop := D.φ i w = true

end Diagram

-- ============================================================================
-- §1. Specialization tags (planned home for Square / Hexagon / Cube)
-- ============================================================================

/-! Specializations live in sibling files:

- `Square.lean` — `Diagram (Fin 4)` with the canonical CD/CD/C/SC/SA/SA pattern
- `Hexagon.lean` — `Diagram (Fin 6)` (TODO; 3 Aristotelian families per
  @cite{demey-smessaert-2018} Fig. 2: JSB, SC, U4. The strong/weak JSB
  distinction within JSB is Aristotelian-iso but not Boolean-iso, p. 350-352)
- `Cube.lean` — `Diagram (Fin 8)` (TODO; Smessaert 2009 "On the 3D visualisation
  of logical relations," Logica Universalis 3, 303-332 — bib entry deferred
  pending verified DOI)

Adding a specialization is a matter of (a) picking an `ι` enum, (b) writing
the `relation` matrix, (c) discharging `relation_correct`. The bitstring
machinery in `Bitstring.lean` makes (c) automatic for Boolean-closed fragments.
-/

end Core.Opposition
