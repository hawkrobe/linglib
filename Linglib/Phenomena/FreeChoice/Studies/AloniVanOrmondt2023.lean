import Linglib.Theories.Semantics.QBSML.Enrichment
import Linglib.Theories.Semantics.QBSML.Properties
import Linglib.Phenomena.FreeChoice.Atoms
import Linglib.Phenomena.FreeChoice.Worlds

/-!
# @cite{aloni-vanormondt-2023}: QBSML applied to modified numerals + split disjunction

@cite{aloni-vanormondt-2023} @cite{aloni-2022}

Aloni & van Ormondt 2023 introduces QBSML, the first-order extension of
Aloni 2022's BSML, and applies it to a battery of inferences arising from
modified numerals analysed as disjunctions:
  `at least n φ ↦ n ∨ more`,  `at most n φ ↦ n ∨ less`.

The framework's central facts (paper §5):

| Fact | Statement |
|------|-----------|
| 3   | `[Pa ∨ Pb]⁺ ⊨_epi ◇Pa ∧ ◇Pb` (ignorance, R state-based) |
| 4   | `[∀x(Px ∨ Qx)]⁺ ⊭ ∀x(◇Px ∧ ◇Qx)` (obviation; counterexample exists) |
| 5   | `card(s)=1 ⇒ M, s ⊨ [∀x(Px ∨ Qx)]⁺ ⇒ M, s ⊨ ∃xPx ∧ ∃xQx` (distribution under full info) |
| 6   | `[∀x(Px ∨ Qx)]⁺ ⊨_epi ∃x◇Px ∧ ∃x◇Qx` (distribution° with epistemic R) |
| 7   | `[□(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (□-free choice) |
| 8   | `[◇(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (◇-free choice; ≡ Aloni 2022 NS FC at first-order) |
| 9   | `[∀x◇(Px ∨ Qx)]⁺ ⊨ ∀x◇Px ∧ ∀x◇Qx` (universal FC; @cite{chemla-2009}) |
| 10  | `[¬(Pa ∨ Pb)]⁺ ⊨ ¬Pa ∧ ¬Pb` (negation behaviour; ignorance disappears) |

## Scope of this file

This study file proves the **negation fact (Fact 10)** directly on a
concrete QBSML model with:
- 4 worlds (parallel to Aloni 2022's `PowerSet2World`),
- 2-element domain `{a, b}` (reusing `Phenomena.FreeChoice.FCAtom`),
- single unary predicate `P` and single variable `x`.

The negation fact is the simplest QBSML-substantive result that exercises
the substrate's bilateral evaluation + split-disjunction + NE-enrichment
pipeline on first-order syntax. It also instantiates the paper's "negation
behaves classically" desideratum.

## What is deferred

A universal-substrate `Theories/Semantics/QBSML/FreeChoice.lean` paralleling
`BSML/FreeChoice.lean` is not yet written. It would carry the universal
forms of Facts 7, 8, 9, plus an `enrichment_strengthens_support` lemma
(QBSML analogue of `BSML/Enrichment.lean`'s). Once landed, this file
would invoke those theorems by name (per the `Aloni2022.lean` pattern in
the same directory) rather than proving Fact 10 inline.

The propositional analogues of Facts 3-5, 11-12 already live in
`Aloni2022.lean` via the BSML substrate; they can be lifted to QBSML
formulas but the lifting itself is the deferred substrate work.

## Atoms and worlds

This file reuses `Phenomena.FreeChoice.{FCAtom, PowerSet2World}` from
`Aloni2022.lean` for:
- the domain (`FCAtom.{a, b}` ≡ Aloni & van Ormondt 2023's `D = {a, b}`)
- the world space (`PowerSet2World.{nothing, onlyA, onlyB, both}`).

A new lightweight `QPred` enum encodes the single predicate `P`. The QBSML
model interprets `P` at a world as the Finset of domain elements that
satisfy `P` there, matching `PowerSet2World.holds` from Aloni 2022.
-/

namespace Phenomena.FreeChoice.Studies.AloniVanOrmondt2023

open Semantics.QBSML
open Phenomena.FreeChoice (FCAtom PowerSet2World)

-- ============================================================================
-- §1 Predicates and variables
-- ============================================================================

/-- Single unary predicate `P` (extensional reading: "is P at world w"). -/
inductive QPred | P
  deriving DecidableEq, Repr

instance : Fintype QPred where
  elems := {.P}
  complete := by intro p; cases p; simp

/-- Single variable `x`. -/
inductive QVar | x
  deriving DecidableEq, Repr

instance : Fintype QVar where
  elems := {.x}
  complete := by intro v; cases v; simp

-- ============================================================================
-- §2 Concrete QBSML model
-- ============================================================================

/-- Universal-access deontic-style model on `PowerSet2World`. The interpretation
    of `P` at a world `w` is the Finset of `FCAtom`s that satisfy `P` at `w`,
    routed through `PowerSet2World.holds` from Aloni 2022's substrate.

    - `pInterp P .both = {a, b}`
    - `pInterp P .onlyA = {a}`
    - `pInterp P .onlyB = {b}`
    - `pInterp P .nothing = ∅`

    Universal access (`access _ = univ`) means R is indisputable on every
    state but **not** state-based — same shape as `Aloni2022.deonticModel`. -/
def avoModel : QBSMLModel PowerSet2World FCAtom QPred where
  access := λ _ => Finset.univ
  pInterp := λ _ w => (Finset.univ : Finset FCAtom).filter (λ d => w.holds d)

-- ============================================================================
-- §3 Formulas
-- ============================================================================

/-- The atomic formula `Px`. -/
def Px : QBSMLFormula QVar QPred := .pred .P .x

/-- Disjunction `Px ∨ Px`. The paper writes `Pa ∨ Pb` for two distinct
    predicate-instances; with our single-variable + monadic-predicate
    setup, the structurally equivalent shape is `Px ∨ Px`, since QBSML's
    `disj` is split disjunction (Aloni & van Ormondt §3.1) — its support
    requires the team to be partitioned into two sub-teams each supporting
    the corresponding disjunct, even when the two disjuncts coincide
    syntactically. The Fact 10 proof below depends only on the
    antiSupport-disj clause + NE-stripping; the duplicate-disjunct
    formulation suffices. -/
def PxOrPx : QBSMLFormula QVar QPred := .disj Px Px

/-- The negation premise `¬(Px ∨ Px)` corresponding to the paper's
    `¬(Pa ∨ Pb)` schema. -/
def negPxOrPx : QBSMLFormula QVar QPred := .neg PxOrPx

-- ============================================================================
-- §4 Fact 10 (Negation): `[¬(Pa ∨ Pb)]⁺ ⊨ ¬Pa ∧ ¬Pb`
-- ============================================================================

/-- **Fact 10 (Negation behaviour)** at the AvO 2023 model:

    Enriched negation `[¬(Px ∨ Px)]⁺` entails the conjunction of the negated
    disjuncts `¬Px ∧ ¬Px` (which collapses to `¬Px` since both disjuncts
    are the same formula, but the proof structure exhibits the paper's
    Fact 10 pattern: NE-stripping on the antiSupport-conj clause forces
    each part of the split to anti-support its disjunct on the **whole**
    state, recovering classical negation behaviour).

    The paper's full statement uses `Pa ∨ Pb` with two distinct predicate
    instances; here we use `Px ∨ Px` to keep the model + formula language
    minimal. The structural proof — antiSupport-conj split + antiSupport-NE
    stripping + antiSupport-disj conjunction — is identical. -/
theorem fact10_negation
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel negPxOrPx.enrich s) :
    antiSupport avoModel Px s ∧ antiSupport avoModel Px s := by
  -- Unfold enrich (¬φ) = (¬enrich φ) ∧ NE; the outer NE conjunct is `h.2`.
  have hNeg := h.1  -- support (¬enrich (Px ∨ Px)) s = antiSupport (enrich (Px ∨ Px)) s
  -- Stripping NE three times: antiSupport-conj split + antiSupport-NE = empty.
  -- Helper: any conj-with-NE antiSupport on s collapses its left-conjunct
  -- antiSupport onto the whole state s.
  -- Outer split: antiSupport ((enrich Px ∨ enrich Px) ∧ NE) on s
  obtain ⟨t₁, t₂, hsplit, hDisj, hNEt₂⟩ := hNeg
  have heqOuter : t₁ = s := by
    have hnow : t₁ ∪ t₂ = s := hsplit
    rw [show t₂ = ∅ from hNEt₂, Finset.union_empty] at hnow
    exact hnow
  rw [heqOuter] at hDisj
  -- antiSupport disj at s gives antiSupport on each disjunct (paper §4.1, antiSupport-disj clause)
  obtain ⟨hL, hR⟩ := hDisj
  -- Strip NE inside enrich Px on the left disjunct
  obtain ⟨t₃, t₄, hsplit', haPx, hNEt₄⟩ := hL
  have heqLeft : t₃ = s := by
    have hnow : t₃ ∪ t₄ = s := hsplit'
    rw [show t₄ = ∅ from hNEt₄, Finset.union_empty] at hnow
    exact hnow
  rw [heqLeft] at haPx
  -- Strip NE inside enrich Px on the right disjunct
  obtain ⟨t₅, t₆, hsplit'', haPx', hNEt₆⟩ := hR
  have heqRight : t₅ = s := by
    have hnow : t₅ ∪ t₆ = s := hsplit''
    rw [show t₆ = ∅ from hNEt₆, Finset.union_empty] at hnow
    exact hnow
  rw [heqRight] at haPx'
  exact ⟨haPx, haPx'⟩

-- ============================================================================
-- §5 Frame condition fact: avoModel is indisputable on every state
-- ============================================================================

/-- `avoModel`'s universal accessibility makes R indisputable on every state
    (every world sees the same `Finset.univ`). Mirrors
    `Aloni2022.deonticModel_indisputable_on_team` for the QBSML carrier.

    Indisputability is the frame condition for Fact 5 (Wide Scope FC) and
    Fact 6 (epistemic distribution); state-basedness (strictly stronger)
    is the precondition for Facts 3 and 7. The paper distinguishes the two
    in §4.1.1. -/
theorem avoModel_indisputable
    (s : Finset (Index PowerSet2World QVar FCAtom)) :
    avoModel.isIndisputable s := by
  intro _ _ _ _; rfl

-- ============================================================================
-- §6 Substrate-flatness corollary applied to `avoModel`
-- ============================================================================

/-- **Application of Anttila Prop 2.2.16 / QBSML Proposition 4.1**:

    For the NE-free formula `Px`, the substrate's
    `flat_support_of_isNEFree` (in `QBSML/Properties.lean`) gives that
    `support avoModel Px s ↔ ∀ i ∈ s, support avoModel Px {i}`.

    This is the QBSML analogue of the BSML/classical reduction Aloni 2022
    Proposition 2.2.16 + Aloni & van Ormondt 2023 Proposition 4.1: NE-free
    QBSML formulas reduce to classical first-order modal logic on
    singleton states. The substrate built in `QBSML/Properties.lean`
    delivers it. -/
theorem Px_flat (s : Finset (Index PowerSet2World QVar FCAtom)) :
    support avoModel Px s ↔ ∀ i ∈ s, support avoModel Px {i} := by
  exact flat_support_of_isNEFree (W := PowerSet2World) (Domain := FCAtom)
    (φ := Px) rfl avoModel s

end Phenomena.FreeChoice.Studies.AloniVanOrmondt2023
