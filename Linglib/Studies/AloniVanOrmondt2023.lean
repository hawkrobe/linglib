import Linglib.Studies.AloniVanOrmondt2023.FreeChoice
import Linglib.Core.Logic.Modal.QBSML.Properties
import Linglib.Phenomena.FreeChoice.Atoms
import Linglib.Phenomena.FreeChoice.Worlds

/-!
# [aloni-vanormondt-2023]: QBSML applied to modified numerals + split disjunction

[aloni-vanormondt-2023] [aloni-2022]

Aloni & van Ormondt 2023 introduces QBSML, the first-order extension of
Aloni 2022's BSML, and applies it to a battery of inferences arising from
modified numerals analysed as disjunctions:
  `at least n φ ↦ n ∨ more`,  `at most n φ ↦ n ∨ less`.

The framework's central facts (paper §5):

| Fact | Statement |
|------|-----------|
| 3   | `[Pa ∨ Pb]⁺ ⊨_epi ◇Pa ∧ ◇Pb` (ignorance, R state-based) |
| 4   | `[∀xPx ∨ Qx]⁺ ⊭ ∀x(◇Px ∧ ◇Qx)` (obviation; counterexample on paper Fig. 14) |
| 5   | `card(s)=1 ⇒ M, s ⊨ [∀x(Px ∨ Qx)]⁺ ⇒ M, s ⊨ ∃xPx ∧ ∃xQx` (distribution under full information) |
| 6   | `[∀x(Px ∨ Qx)]⁺ ⊨_epi ∃x◇Px ∧ ∃x◇Qx` (distribution° on epistemic models) |
| 7   | `[□(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (□-free choice) |
| 8   | `[◇(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (◇-free choice; ≡ Aloni 2022 NS FC at first-order) |
| 9   | `[∀x◇(Px ∨ Qx)]⁺ ⊨ ∀x◇Px ∧ ∀x◇Qx` (universal FC; [chemla-2009]) |
| 10  | `[¬(Pa ∨ Pb)]⁺ ⊨ ¬Pa ∧ ¬Pb` (negation behaviour; ignorance disappears) |

## What this file proves

The QBSML substrate carries the universal forms of Facts 5, 6, 8, 9, 10
(in `Studies/AloniVanOrmondt2023/FreeChoice.lean`). This file instantiates
the unconditional ones at a concrete model — paralleling `Aloni2022.lean`'s
pattern of substrate-theorem invocation:

- **Fact 10 (negation)** at `avoModel`: one-line invocation of
  `negationStrip_Q`.
- **Fact 8 (narrow-scope ◇-FC)** at `avoModel`: one-line invocation of
  `narrowScopeFC_Q`.
- **Fact 9 (universal FC)** at `avoModel`: one-line invocation of
  `universalFC_Q`.
- **Fact 5 (distribution at maximal information)** at `avoModel` on any
  singleton state: one-line invocation of `distribution_Q`.

Fact 6 (`distributionEpi_Q`) requires a state-based `R`, which `avoModel`'s
universal access deliberately is not — it stays substrate-level here.

## Concrete model

- 4 worlds (parallel to Aloni 2022): `PowerSet2World.{nothing, onlyA, onlyB, both}`.
- 2-element domain: `FCAtom.{a, b}` (reused from `Phenomena.FreeChoice.Atoms`).
- Two unary predicates `P`, `Q` so that `Pa ∨ Qa` is a non-degenerate
  disjunction (the audit's "duplicate-disjunct collapse" objection
  motivated adding `Q`).
- Single variable `x` (the variable language is monadic; this is the
  paper's setup).

## What is deferred

- **Ignorance (Fact 3)**: needs individual constants in the term language
  (see `Studies/AloniVanOrmondt2023/FreeChoice.lean`).
- **Obviation (Fact 4)**: a non-entailment; the counter-example (paper
  Fig. 14, a single-index state whose universal extension splits
  horizontally) needs hand-proved non-support or a `Decidable` instance
  for `eval`.
- **□-FC (Fact 7)**: needs a primitive `□` or a bridge between the
  derived-`□` enrichment and the paper's.
- **`Decidable` instance for `QBSML.eval`**: would let `decide` close
  premise-supported checks on concrete teams (BSML has this; QBSML
  doesn't yet).

## Atoms and worlds

This file reuses `Phenomena.FreeChoice.{FCAtom, PowerSet2World}` from
the existing FreeChoice substrate, ensuring AvO 2023 + Aloni 2022 both
target the same world space.
-/

namespace AloniVanOrmondt2023

open Core.Logic.Modal.QBSML
open Phenomena.FreeChoice (FCAtom PowerSet2World)

-- ============================================================================
-- §1 Predicates and variables
-- ============================================================================

/-- Two unary predicates `P` and `Q`: provides the non-degenerate disjunction
    `Pa ∨ Qa` matching the paper's `Pa ∨ Pb` schema (where the `a, b` are
    domain elements rather than predicate-instances). With monadic predicates
    over a 2-element domain, `Pa ∨ Qa` and `Pa ∨ Pb` are equally non-trivial
    instantiations of split disjunction. -/
inductive QPred | P | Q
  deriving DecidableEq, Repr

instance : Fintype QPred where
  elems := {.P, .Q}
  complete := by intro p; cases p <;> simp

/-- Single variable `x`. -/
inductive QVar | x
  deriving DecidableEq, Repr

instance : Fintype QVar where
  elems := {.x}
  complete := by intro v; cases v; simp

-- ============================================================================
-- §2 Concrete QBSML model
-- ============================================================================

/-- Universal-access deontic-style model on `PowerSet2World`.

    The interpretation is the `monadicStructure` of the valuation
    `V w P d := w.holds d`: both predicates hold of `d` at `w` iff `w`
    models the atom `d`. The disjunction `Px ∨ Qx` is non-degenerate at the
    *formula* level even though at this model the two interpretations
    coincide. A model with divergent P and Q extensions would discriminate
    further; this minimal model suffices for the substrate-instantiation
    tests below.

    Universal access (`access _ = univ`) means R is indisputable on every
    state but **not** state-based — same shape as `Aloni2022.deonticModel`. -/
def avoModel : QBSMLModel PowerSet2World FCAtom QPred where
  access := λ _ => Finset.univ
  interp := λ w => monadicStructure (λ _ d => w.holds d)

-- ============================================================================
-- §3 Formulas
-- ============================================================================

/-- The atomic formula `Px`. -/
def Px : QBSMLFormula QVar QPred := .pred .P .x

/-- The atomic formula `Qx`. -/
def Qx : QBSMLFormula QVar QPred := .pred .Q .x

/-- Disjunction `Px ∨ Qx` — paper's `Pa ∨ Pb`-shape with two distinct
    predicate-instances. -/
def PxOrQx : QBSMLFormula QVar QPred := .disj Px Qx

/-- The negation premise `¬(Px ∨ Qx)` corresponding to the paper's
    `¬(Pa ∨ Pb)` schema. -/
def negPxOrQx : QBSMLFormula QVar QPred := .neg PxOrQx

/-- The narrow-scope FC premise `◇(Px ∨ Qx)` corresponding to the paper's
    `◇(Pa ∨ Pb)` schema. -/
def possPxOrQx : QBSMLFormula QVar QPred := .poss PxOrQx

/-- The universal-FC premise `∀x◇(Px ∨ Qx)` (paper's Fact 9 schema). -/
def univPossPxOrQx : QBSMLFormula QVar QPred := .univ .x possPxOrQx

/-- The distribution premise `∀x(Px ∨ Qx)` (paper's Facts 5–6 schema). -/
def univPxOrQx : QBSMLFormula QVar QPred := .univ .x PxOrQx

-- ============================================================================
-- §4 Substrate facts: Px, Qx are NE-free
-- ============================================================================

theorem Px_isNEFree : Px.IsNEFree := .pred _ _
theorem Qx_isNEFree : Qx.IsNEFree := .pred _ _

-- ============================================================================
-- §5 Fact 10 (Negation): `[¬(Pa ∨ Pb)]⁺ ⊨ ¬Pa ∧ ¬Pb`
-- ============================================================================

/-- **Fact 10 (Negation behaviour)** at `avoModel`:

    Enriched negation `[¬(Px ∨ Qx)]⁺` entails the conjunction of negated
    disjuncts `¬Px ∧ ¬Qx`. One-line invocation of the substrate's
    `negationStrip_Q` (`Studies/AloniVanOrmondt2023/FreeChoice.lean`).
    Mirrors `Aloni2022.aloni2022_fact11_dual_prohibition` style — substrate
    theorem, model + NE-free witnesses applied. -/
theorem fact10_negation
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel negPxOrQx.enrich s) :
    support avoModel (.neg Px) s ∧ support avoModel (.neg Qx) s :=
  negationStrip_Q avoModel Px Qx s Px_isNEFree Qx_isNEFree h

-- ============================================================================
-- §6 Fact 8 (Narrow-Scope FC): `[◇(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb`
-- ============================================================================

/-- **Fact 8 (Narrow-Scope free choice / ◇-FC)** at `avoModel`:

    Enriched possibility-disjunction `[◇(Px ∨ Qx)]⁺` entails `◇Px ∧ ◇Qx`.
    One-line invocation of `narrowScopeFC_Q`. The first-order analogue of
    `Aloni2022.aloni2022_fact4_NS_FC` — same template, lifted to QBSML's
    monadic predicate language. -/
theorem fact8_narrowScopeFC
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel possPxOrQx.enrich s) :
    support avoModel (.poss Px) s ∧ support avoModel (.poss Qx) s :=
  narrowScopeFC_Q avoModel Px Qx s Px_isNEFree Qx_isNEFree h

-- ============================================================================
-- §6b Fact 9 (Universal FC) and Fact 5 (Distribution)
-- ============================================================================

/-- **Fact 9 (Universal free choice)** at `avoModel`:

    `[∀x◇(Px ∨ Qx)]⁺` entails `∀x◇Px ∧ ∀x◇Qx`. One-line invocation of
    `universalFC_Q` — the [chemla-2009]-attested pattern. -/
theorem fact9_universalFC
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel univPossPxOrQx.enrich s) :
    support avoModel (.univ .x (.poss Px)) s ∧
    support avoModel (.univ .x (.poss Qx)) s :=
  universalFC_Q avoModel Px Qx .x s Px_isNEFree Qx_isNEFree h

/-- **Fact 5 (Distribution at maximal information)** at `avoModel`: on any
    singleton state, `[∀x(Px ∨ Qx)]⁺` entails `∃xPx ∧ ∃xQx`. One-line
    invocation of `distribution_Q`. -/
theorem fact5_distribution
    (i : Index PowerSet2World QVar FCAtom)
    (h : support avoModel univPxOrQx.enrich {i}) :
    support avoModel (.exi .x Px) {i} ∧ support avoModel (.exi .x Qx) {i} :=
  distribution_Q avoModel Px Qx .x i Px_isNEFree Qx_isNEFree h

-- ============================================================================
-- §7 Frame condition: avoModel is indisputable on every state
-- ============================================================================

/-- `avoModel`'s universal accessibility makes R indisputable on every state
    (every world sees the same `Finset.univ`). Mirrors
    `Aloni2022.deonticModel_indisputable_on_team` for the QBSML carrier.

    Indisputability vs state-basedness (paper §4.1.1, Definition 4.10):
    - Indisputable: all worlds in s↓ see the same accessible set (R constant).
    - State-based: every w ∈ s↓ sees exactly s↓ (R(w) = s↓).

    State-basedness is strictly stronger and is the precondition for the
    epistemic facts: Fact 3 (ignorance), Fact 6 (epistemic distribution).
    Facts 8 and 10 (formalised above) need no frame condition at all —
    they hold on every model. -/
theorem avoModel_indisputable
    (s : Finset (Index PowerSet2World QVar FCAtom)) :
    avoModel.IsIndisputable s := by
  intro _ _ _ _; rfl

end AloniVanOrmondt2023
