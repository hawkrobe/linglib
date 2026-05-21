import Linglib.Core.Logic.Modal.Kripke
import Linglib.Core.Logic.Bilateral.Defs
import Linglib.Core.Logic.Team.Algebra
import Linglib.Core.Logic.Team.Closure

/-!
# Modal Dependence Logic (MDL)

@cite{vaananen-2008} @cite{vaananen-2007}

MDL is the modal extension of dependence logic introduced in
@cite{vaananen-2008} ("Modal Dependence Logic", in Apt & van Rooij eds.
*New Perspectives on Games and Interaction*, pp. 237-254). It adds a
*dependence atom* `=(p₁,...,pₙ; q)` to classical modal logic, meaning
"the value of `q` is functionally determined by the values of
`p₁,...,pₙ` across the team."

The framework is grounded in Väänänen's foundational
@cite{vaananen-2007} (the *Dependence Logic* book, Cambridge University
Press 2007), which develops the first-order team-semantic apparatus
that MDL adapts to modal logic. Where the book's quantifiers range
over assignments, MDL's modalities range over Kripke worlds — but the
team-semantic skeleton (formulas as predicates of teams, downward
closure, dependence atoms) transfers directly.

MDL is studied for its computational and model-theoretic properties
(satisfiability complexity in @cite{lohmann-vollmer-2013} and Sevenster's
earlier expressive-power work; bisimulation invariance), with
applications in database theory, knowledge representation, and AI
rather than primarily in linguistic semantics — hence the placement in
`Core/Logic/` rather than `Theories/Semantics/`, alongside the other
team-semantic primitives (`Core/Logic/Team/`, `Core/Logic/Bilateral/`).

## What changes from BSML

MDL and BSML share a bilateral semantics (Player II = support, Player
I = anti-support, negation flips polarity per @cite{vaananen-2008}
clause (T5)) and the same Kripke-model carrier. The structural
differences:

* **Atom**: BSML's `NE` becomes MDL's `dep`. `=(x⃗; y)` is supported by
  a team iff any two worlds agreeing on `x⃗` also agree on `y`.
* **Modal operator clauses**: MDL's ◇-support uses a **single witness**
  `Y` (@cite{vaananen-2008} clause (T8)) — `∃ Y, (∀ w ∈ s, ∃ y ∈ Y,
  y ∈ R[w]) ∧ support φ Y` — rather than BSML's per-world witnesses.
  Similarly, ◇-anti-support uses the union of accessibility images
  (T9) rather than per-world checks. The two formulations are
  equivalent under union-closure but diverge for MDL since dep atoms
  break it.

## Closure profile

MDL's closure profile differs from BSML's, placing it in a different
cell of the closure-property lattice:

| Property            | BSML (NE-free) | BSML (with NE) | MDL              |
|---------------------|----------------|----------------|------------------|
| `IsLowerSet`        | ✓              | broken by NE   | ✓ (Lemma 4.2)    |
| `SupClosed`         | ✓              | ✓              | broken by `dep`  |
| `∅ ∈ support`       | ✓              | ✓              | ✓                |

The dep atom is downward-closed (subteam of a functionally-dependent
team is functionally dependent) but breaks union-closure (two
functionally-dependent teams may have conflicting `y` values at
worlds with matching `x⃗`).

## Main declarations

* `Formula` — MDL syntax (Definition 1.1).
* `eval` — bilateral semantics (Definition 4.1), parametric in polarity.
* `support` / `antiSupport` — convenience abbreviations.
* `Formula.modalDepth` — depth of nested ◇.
* `isBilateral` — `Core.Logic.Bilateral.IsBilateral` instance.
* `isLowerSet_support` — Lemma 4.2's downward-closure property.
* `support_empty` — every formula is supported on the empty team.
* `not_supClosed_dep_of_witness` — the witness that `dep` breaks
  union-closure: in any model with two worlds sharing a `p`-value but
  differing on `q`, the singleton teams support `=(p; q)` but their
  union does not.

## Implementation notes

The MDL eval uses Väänänen's exact clauses, not BSML's. The disjunction
clause is the under-DC simplified form `X = Y ∪ Z` (paper's (T6)'
under Lemma 4.2 part 1) rather than the literal `X ⊆ Y ∪ Z` from
(T6); under downward closure they are equivalent.

The `KripkeModel` carrier from `Core/Logic/Modal/Kripke.lean` is the
shared substrate; BSML, QBSML, and the AAY-2024 extensions
(BSMLOr/BSMLEmpty) alias `BSMLModel := KripkeModel` for literature
compatibility.

## Sibling logics in `Core/Logic/Modal/`

This directory houses modal-logic variants that share Kripke-model
infrastructure but differ in atom flavor:

* `Modal/Kripke.lean` — the carrier type, shared.
* `Modal/Dependence.lean` (this file) — MDL with dependence atoms.
* `Modal/Inclusion.lean` (future) — modal inclusion logic ML(⊆),
  introduced by Galliani; axiomatized in @cite{anttila-2025} Ch 5.
* `Modal/Independence.lean` (future) — modal independence logic
  (Grädel and Väänänen).
* `Modal/Bilateral.lean` (future, after BSML's eventual Core/
  graduation) — BSML's bilateral negation + NE atom.

The bisimulation substrate currently lives at
`Theories/Semantics/BSML/Bisimulation.lean` for historical reasons; a
future refactor lifts it to `Core/Logic/Modal/Bisimulation.lean`.

## Todo

* @cite{lohmann-vollmer-2013} — adds classical disjunction `⓿` (the
  BSML∨ analogue) and complete satisfiability complexity classification.
  Natural second consumer paper, with a Studies file anchored on it.
* Bisim invariance for MDL — same shape as BSML/BSMLOr/BSMLEmpty
  proofs in `BSML/Bisimulation.lean` and `Studies/AloniAnttilaYang2024`,
  but the modal-case argument differs because MDL's ◇ uses single-
  witness semantics rather than per-world.
* Modal independence logic (Grädel and Väänänen's independence atoms) —
  sibling at `Core/Logic/Modal/Independence.lean`.
-/

namespace Core.Logic.Modal.Dependence

variable {W : Type*} [DecidableEq W] [Fintype W] {Atom : Type*}

open Core.Logic.Modal (KripkeModel)

/-! ### Syntax (Definition 1.1) -/

/-- MDL syntax (Definition 1.1 of @cite{vaananen-2008}): classical modal
    logic extended with the dependence atom `=(p₁,...,pₙ; q)`.

    `□` and binary `∧` are abbreviations (the paper's `□A := ¬◇¬A` and
    `A ∧ B := ¬(¬A ∨ ¬B)`). We include `conj` as a primitive constructor
    here for ergonomic parallelism with BSML, with the semantic clauses
    matching what the abbreviations would yield. -/
inductive Formula (Atom : Type*) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Dependence atom `=(x⃗; y)`: values of `y` in the team are
      functionally determined by values of `x⃗`. -/
  | dep (xs : List Atom) (y : Atom)
  /-- Bilateral negation: swap support/anti-support. -/
  | neg (φ : Formula Atom)
  /-- Conjunction. -/
  | conj (φ ψ : Formula Atom)
  /-- Tensor disjunction (team-split form under downward closure). -/
  | disj (φ ψ : Formula Atom)
  /-- Possibility modal `◇`. -/
  | poss (φ : Formula Atom)
  deriving Repr

/-! ### Semantics (Definition 4.1) -/

/-- Bilateral evaluation for MDL (Definition 4.1 of @cite{vaananen-2008}).
    `eval M true φ t` is support (Player II); `eval M false φ t` is
    anti-support (Player I). Negation flips polarity (clause (T5)).

    The ◇ clauses (T8), (T9) use Väänänen's single-witness form, not
    BSML's per-world form; the two formulations diverge for non-union-
    closed logics like MDL. -/
def eval (M : KripkeModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true,  .atom p,        t => ∀ w ∈ t, M.val p w = true
  | false, .atom p,        t => ∀ w ∈ t, M.val p w = false
  | true,  .dep xs y,      t => ∀ w₁ ∈ t, ∀ w₂ ∈ t,
                                  (∀ x ∈ xs, M.val x w₁ = M.val x w₂) →
                                  M.val y w₁ = M.val y w₂
  | false, .dep _ _,       t => t = ∅
  | true,  .neg ψ,         t => eval M false ψ t
  | false, .neg ψ,         t => eval M true ψ t
  | true,  .conj ψ₁ ψ₂,    t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂,    t => ∃ t₁ t₂ : Finset W,
                                  Core.Logic.Team.splitsAs t t₁ t₂ ∧
                                  eval M false ψ₁ t₁ ∧ eval M false ψ₂ t₂
  | true,  .disj ψ₁ ψ₂,    t => ∃ t₁ t₂ : Finset W,
                                  Core.Logic.Team.splitsAs t t₁ t₂ ∧
                                  eval M true ψ₁ t₁ ∧ eval M true ψ₂ t₂
  | false, .disj ψ₁ ψ₂,    t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true,  .poss ψ,        t => ∃ Y : Finset W,
                                  (∀ w ∈ t, ∃ y ∈ Y, y ∈ M.access w) ∧
                                  eval M true ψ Y
  | false, .poss ψ,        t => eval M false ψ (t.biUnion M.access)

/-- Support: positive evaluation. -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M true φ t

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M false φ t

@[simp] lemma support_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    support M (.atom p) t ↔ ∀ w ∈ t, M.val p w = true := Iff.rfl

@[simp] lemma antiSupport_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    antiSupport M (.atom p) t ↔ ∀ w ∈ t, M.val p w = false := Iff.rfl

@[simp] lemma support_dep (M : KripkeModel W Atom) (xs : List Atom) (y : Atom)
    (t : Finset W) :
    support M (.dep xs y) t ↔
      ∀ w₁ ∈ t, ∀ w₂ ∈ t,
        (∀ x ∈ xs, M.val x w₁ = M.val x w₂) → M.val y w₁ = M.val y w₂ := Iff.rfl

@[simp] lemma antiSupport_dep (M : KripkeModel W Atom) (xs : List Atom) (y : Atom)
    (t : Finset W) :
    antiSupport M (.dep xs y) t ↔ t = ∅ := Iff.rfl

@[simp] lemma support_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl

@[simp] lemma antiSupport_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl

@[simp] lemma support_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma antiSupport_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.conj φ ψ) t ↔
      ∃ t₁ t₂ : Finset W, Core.Logic.Team.splitsAs t t₁ t₂ ∧
        antiSupport M φ t₁ ∧ antiSupport M ψ t₂ := Iff.rfl

@[simp] lemma support_disj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.disj φ ψ) t ↔
      ∃ t₁ t₂ : Finset W, Core.Logic.Team.splitsAs t t₁ t₂ ∧
        support M φ t₁ ∧ support M ψ t₂ := Iff.rfl

@[simp] lemma antiSupport_disj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl

@[simp] lemma support_poss (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.poss φ) t ↔
      ∃ Y : Finset W, (∀ w ∈ t, ∃ y ∈ Y, y ∈ M.access w) ∧ support M φ Y :=
  Iff.rfl

@[simp] lemma antiSupport_poss (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.poss φ) t ↔ antiSupport M φ (t.biUnion M.access) := Iff.rfl

/-- MDL's `support`/`antiSupport` form a paraconsistent bilateral logic
    under `Formula.neg`. -/
theorem isBilateral (M : KripkeModel W Atom) :
    Core.Logic.Bilateral.IsBilateral
      (support M) (antiSupport M) Formula.neg :=
  Core.Logic.Bilateral.IsBilateral.of_iff (support_neg M) (antiSupport_neg M)

/-! ### Modal depth -/

/-- Modal depth of an MDL formula. Atoms and dep atoms are 0; `neg`
    preserves depth; `conj` and `disj` take max; `poss` increments. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ => 0
  | .dep _ _ => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-! ### Lemma 4.2: Downward closure -/

/-- Joint downward closure for both polarities. Mirrors the BSML pattern:
    each clause preserves the ⊆-direction, including the new dep clause
    (subteam of functionally-dependent is functionally dependent). -/
private theorem support_and_antiSupport_downward (φ : Formula Atom)
    (M : KripkeModel W Atom) :
    (∀ s t : Finset W, t ⊆ s → support M φ s → support M φ t) ∧
    (∀ s t : Finset W, t ⊆ s → antiSupport M φ s → antiSupport M φ t) := by
  induction φ with
  | atom p =>
    refine ⟨?_, ?_⟩
    · intro s t hsub hsupp w hw; exact hsupp w (hsub hw)
    · intro s t hsub hsupp w hw; exact hsupp w (hsub hw)
  | dep xs y =>
    refine ⟨?_, ?_⟩
    · -- support .dep s = functional dependence in s. Subteams inherit.
      intro s t hsub hsupp w₁ hw₁ w₂ hw₂ hagree
      exact hsupp w₁ (hsub hw₁) w₂ (hsub hw₂) hagree
    · -- antiSupport .dep s = s = ∅. Subteam of ∅ is ∅.
      intro s t hsub hsupp
      show t = ∅
      rw [hsupp] at hsub
      exact Finset.subset_empty.mp hsub
  | neg ψ ih =>
    have ⟨ihs, iha⟩ := ih
    exact ⟨iha, ihs⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have ⟨ihs₁, iha₁⟩ := ih₁
    have ⟨ihs₂, iha₂⟩ := ih₂
    refine ⟨?_, ?_⟩
    · -- support: conjunction of supports, both halves survive ⊆
      intro s t hsub ⟨hs₁, hs₂⟩
      exact ⟨ihs₁ s t hsub hs₁, ihs₂ s t hsub hs₂⟩
    · -- antiSupport: ∃ split, restrict t-intersect
      intro s t hsub ⟨t₁, t₂, hsplit, ha₁, ha₂⟩
      refine ⟨t₁ ∩ t, t₂ ∩ t, ?_, ?_, ?_⟩
      · show (t₁ ∩ t) ∪ (t₂ ∩ t) = t
        rw [(Finset.union_inter_distrib_right t₁ t₂ t).symm]
        have heq : t₁ ∪ t₂ = s := hsplit
        rw [heq]; exact Finset.inter_eq_right.mpr hsub
      · exact iha₁ t₁ (t₁ ∩ t) Finset.inter_subset_left ha₁
      · exact iha₂ t₂ (t₂ ∩ t) Finset.inter_subset_left ha₂
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have ⟨ihs₁, iha₁⟩ := ih₁
    have ⟨ihs₂, iha₂⟩ := ih₂
    refine ⟨?_, ?_⟩
    · -- support: ∃ split, restrict t-intersect
      intro s t hsub ⟨t₁, t₂, hsplit, hs₁, hs₂⟩
      refine ⟨t₁ ∩ t, t₂ ∩ t, ?_, ?_, ?_⟩
      · show (t₁ ∩ t) ∪ (t₂ ∩ t) = t
        rw [(Finset.union_inter_distrib_right t₁ t₂ t).symm]
        have heq : t₁ ∪ t₂ = s := hsplit
        rw [heq]; exact Finset.inter_eq_right.mpr hsub
      · exact ihs₁ t₁ (t₁ ∩ t) Finset.inter_subset_left hs₁
      · exact ihs₂ t₂ (t₂ ∩ t) Finset.inter_subset_left hs₂
    · -- antiSupport: conjunction, both halves survive ⊆
      intro s t hsub ⟨ha₁, ha₂⟩
      exact ⟨iha₁ s t hsub ha₁, iha₂ s t hsub ha₂⟩
  | poss ψ ih =>
    have ⟨_ihs, iha⟩ := ih
    refine ⟨?_, ?_⟩
    · -- support .poss: ∃ Y, (∀ w ∈ s, ∃ y ∈ Y, y ∈ R[w]) ∧ support ψ Y.
      -- Same Y witnesses for subteam t ⊆ s (the per-world condition holds
      -- vacuously for w ∈ s \ t, and unchanged for w ∈ t).
      intro s t hsub ⟨Y, hwit, hsupp⟩
      refine ⟨Y, ?_, hsupp⟩
      intro w hw; exact hwit w (hsub hw)
    · -- antiSupport .poss s = antiSupport ψ (s.biUnion R). For t ⊆ s,
      -- (t.biUnion R) ⊆ (s.biUnion R), so by IH (downward closure on ψ).
      intro s t hsub hsupp
      apply iha (s.biUnion M.access) (t.biUnion M.access) ?_ hsupp
      exact Finset.biUnion_subset_biUnion_of_subset_left M.access hsub

/-- **Lemma 4.2 of @cite{vaananen-2008}**: every MDL formula's support
    is downward-closed. The defining closure property of the dependence
    family — what BSML loses when it adds NE. -/
theorem isLowerSet_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    IsLowerSet { t : Finset W | support M φ t } :=
  fun _ _ hab hb =>
    (support_and_antiSupport_downward φ M).1 _ _ hab hb

/-! ### Empty team property -/

/-- Joint empty-team property: every MDL formula has both empty support
    and empty anti-support. Proved by structural induction; differs
    from BSML in that no `NE` constructor breaks it. -/
private theorem support_and_antiSupport_empty
    (φ : Formula Atom) (M : KripkeModel W Atom) :
    support M φ ∅ ∧ antiSupport M φ ∅ := by
  induction φ with
  | atom p =>
    exact ⟨fun w hw => absurd hw (Finset.notMem_empty w),
           fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | dep xs y =>
    refine ⟨?_, rfl⟩
    -- support .dep ∅ = ∀ w₁ w₂ ∈ ∅, ... — vacuously true
    intro w₁ hw₁; exact absurd hw₁ (Finset.notMem_empty w₁)
  | neg ψ ih =>
    have ⟨hs, ha⟩ := ih
    exact ⟨ha, hs⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have ⟨hs₁, ha₁⟩ := ih₁
    have ⟨hs₂, ha₂⟩ := ih₂
    refine ⟨⟨hs₁, hs₂⟩, ?_⟩
    refine ⟨∅, ∅, ?_, ha₁, ha₂⟩
    show ∅ ∪ ∅ = ∅
    simp
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have ⟨hs₁, ha₁⟩ := ih₁
    have ⟨hs₂, ha₂⟩ := ih₂
    refine ⟨?_, ⟨ha₁, ha₂⟩⟩
    refine ⟨∅, ∅, ?_, hs₁, hs₂⟩
    show ∅ ∪ ∅ = ∅
    simp
  | poss ψ ih =>
    have ⟨_hs, ha⟩ := ih
    refine ⟨?_, ?_⟩
    · -- support .poss ψ ∅ = ∃ Y, (∀ w ∈ ∅, ...) ∧ support ψ Y. Take Y = ∅.
      refine ⟨∅, ?_, _hs⟩
      intro w hw; exact absurd hw (Finset.notMem_empty w)
    · -- antiSupport .poss ψ ∅ = antiSupport ψ (∅.biUnion M.access) = antiSupport ψ ∅
      show antiSupport M ψ ((∅ : Finset W).biUnion M.access)
      rw [Finset.biUnion_empty]
      exact ha

/-- Every MDL formula is supported on the empty team. -/
theorem support_empty (M : KripkeModel W Atom) (φ : Formula Atom) :
    support M φ ∅ :=
  (support_and_antiSupport_empty φ M).1

/-! ### Dep breaks union closure (the defining feature) -/

/-- **The dep atom is not union-closed**: a constructive counterexample.
    Take a model with at least two worlds `w₁, w₂` where `M.val p w₁ =
    M.val p w₂` but `M.val q w₁ ≠ M.val q w₂`. Then `{w₁}` and `{w₂}`
    each support `=(p; q)` vacuously (each is a singleton, so the
    functional-dependence condition is trivial), but `{w₁, w₂}` does not. -/
theorem not_supClosed_dep_of_witness {p q : Atom} {w₁ w₂ : W}
    {M : KripkeModel W Atom}
    (_hp : M.val p w₁ = M.val p w₂)
    (hq : M.val q w₁ ≠ M.val q w₂) :
    ¬ SupClosed { t : Finset W | support M (.dep [p] q) t } := by
  intro hSC
  have h₁ : support M (.dep [p] q) ({w₁} : Finset W) := by
    intro u₁ hu₁ u₂ hu₂ _
    rw [Finset.mem_singleton] at hu₁ hu₂
    rw [hu₁, hu₂]
  have h₂ : support M (.dep [p] q) ({w₂} : Finset W) := by
    intro u₁ hu₁ u₂ hu₂ _
    rw [Finset.mem_singleton] at hu₁ hu₂
    rw [hu₁, hu₂]
  -- SupClosed gives support on {w₁} ⊔ {w₂} = {w₁, w₂}
  have hSC' : support M (.dep [p] q) (({w₁} : Finset W) ⊔ ({w₂} : Finset W)) :=
    hSC h₁ h₂
  -- But this requires q-values to match on {w₁, w₂}, contradicting hq
  have hmem₁ : w₁ ∈ ({w₁} : Finset W) ⊔ ({w₂} : Finset W) := by
    show w₁ ∈ ({w₁} ∪ ({w₂} : Finset W))
    simp
  have hmem₂ : w₂ ∈ ({w₁} : Finset W) ⊔ ({w₂} : Finset W) := by
    show w₂ ∈ ({w₁} ∪ ({w₂} : Finset W))
    simp
  have hagree : ∀ x ∈ [p], M.val x w₁ = M.val x w₂ := by
    intro x hx
    rw [List.mem_singleton] at hx
    rw [hx]
    exact _hp
  exact hq (hSC' w₁ hmem₁ w₂ hmem₂ hagree)

end Core.Logic.Modal.Dependence
