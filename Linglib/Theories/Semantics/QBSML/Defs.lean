import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Union
import Linglib.Core.Logic.Team.Algebra
import Linglib.Core.Logic.Bilateral.Defs

/-!
# Quantified Bilateral State-based Modal Logic (QBSML) — Core Definitions

@cite{aloni-vanormondt-2023} @cite{aloni-2022} @cite{anttila-2021}

QBSML is the first-order extension of Aloni's BSML, presented in Aloni & van
Ormondt 2023 (J Logic Lang Inf 32:539-567) "Modified Numerals and Split
Disjunction: The First-Order Case".

## What changes from BSML

The propositional BSML (Aloni 2022) is recovered when assignments are empty.
QBSML extends along three axes:

1. **Indices replace worlds**: `Index = W × Assignment` (Aloni & van Ormondt
   §3, Definition 4.2). A state is `Finset Index` rather than `Finset W`.
2. **Predicates with variables** (no constants for now; monadic predicates
   sufficient for free-choice scenarios).
3. **Quantifiers**: `∀x` and `∃x` evaluated via state extensions.

## What stays the same

Everything else carries over from BSML:
- Bilateral evaluation (support + anti-support, polarity flip via negation)
- Split disjunction via `Core.Logic.Team.splitsAs`
- NE atom (`s ≠ ∅`)
- Pragmatic enrichment recursion (NE conjuncts in each clause; deferred to a
  follow-up file)
- Frame conditions on accessibility (state-based, indisputable) via the `s↓`
  projection — Aloni & van Ormondt Definition 4.10

The point of this file is **substrate validation**: QBSML's `support` should
fit into `Core.Logic.Team.flat_iff_downwardClosed_unionClosed_emptyTeam`'s
shape exactly as BSML's does — same template, different `Point` type.

## Scope

This file: types, state operations, support relation. No Anttila 2.2.8 proofs
(those go in `Properties.lean` to validate the substrate). No pragmatic
enrichment (separate `Enrichment.lean`). No free-choice theorems (separate
study files under `Phenomena/FreeChoice/Studies/`).

## Simplifications vs the paper

- **Monadic predicates only**: `pred : Pred → Var → Formula`. The paper's
  general `Pⁿ(t₁, ..., tₙ)` with arbitrary arity and term language (constants +
  variables) is more general. Monadic suffices for Universal FC, Distribution,
  Obviation. Higher arities and constants can be added later; the substrate
  abstraction doesn't change.
- **Single fixed domain `D`**: the paper's `M = ⟨W, D, R, I⟩` has D as part of
  the model. We use `Domain : Type*` as a parameter on the model and require
  `[Fintype Domain]` for the universal extension. Polymorphic + finite.
- **Predicate interpretation is per-world**: `pInterp : Pred → W → Finset Domain`
  — at world w, predicate p picks out a Finset of Domain elements. This is
  the "rigid" predicate semantics; the paper's slightly more general setup
  uses an interpretation function `I : (W × Const ∪ Pⁿ) → D ∪ 𝒫(Dⁿ)`.
-/

namespace Semantics.QBSML

-- ============================================================================
-- §1 Assignments and indices
-- ============================================================================

/-- An assignment is a partial function from variables to domain values.
    Aloni & van Ormondt §4 Definition 4.2: `gᵢ : V → D`. We use `Option D`
    to represent the partiality.

    The paper enforces that all indices in a state share the same domain
    (`dom(gᵢ) = dom(gⱼ)`). We don't enforce this at the type level; instead,
    state operations preserve the invariant. -/
abbrev Assignment (Var Domain : Type*) := Var → Option Domain

/-- An index is a (world, assignment) pair. Aloni & van Ormondt §4 Definition
    4.2: `i = ⟨wᵢ, gᵢ⟩`. -/
abbrev Index (W Var Domain : Type*) := W × Assignment Var Domain

/-- The world component of an index. -/
abbrev Index.world {W Var Domain : Type*} (i : Index W Var Domain) : W := i.1

/-- The assignment component of an index. -/
abbrev Index.assign {W Var Domain : Type*} (i : Index W Var Domain) :
    Assignment Var Domain := i.2

/-- The "world projection" `s↓` of a state of indices: the set of worlds
    appearing in some index. Aloni & van Ormondt §4 Definition 4.10:
    `s↓ := {w | ∃g, (w, g) ∈ s}`.

    Frame conditions on `R` (state-based, indisputable) are defined relative
    to `s↓` rather than `s`, so QBSML reuses BSML's notions via this
    projection. -/
def State.worldProj {W Var Domain : Type*} [DecidableEq W]
    (s : Finset (Index W Var Domain)) : Finset W :=
  s.image Prod.fst

-- ============================================================================
-- §2 Assignment update + state extension operations
-- ============================================================================

variable {Var Domain : Type*} [DecidableEq Var] [Fintype Var]

/-- Update an assignment at a single variable: `g[x/d](y) = d` if `y = x`,
    else `g(y)`. -/
def Assignment.update (g : Assignment Var Domain) (x : Var) (d : Domain) :
    Assignment Var Domain :=
  fun y => if y = x then some d else g y

/-- Update an index's assignment. Aloni & van Ormondt §4 Definition 4.4:
    `i[x/d] := ⟨wᵢ, gᵢ[x/d]⟩`. -/
def Index.update {W : Type*} (i : Index W Var Domain) (x : Var) (d : Domain) :
    Index W Var Domain :=
  (i.world, i.assign.update x d)

variable {W : Type*} [DecidableEq W] [DecidableEq Domain]

/-- DecidableEq on assignments follows from Fintype on the variable space
    plus DecidableEq on the codomain (Option Domain via Domain). -/
instance : DecidableEq (Assignment Var Domain) :=
  fun _ _ => decEq _ _

/-- DecidableEq on indices: pair of decidable types. -/
instance : DecidableEq (Index W Var Domain) :=
  inferInstance

/-- **Individual extension** `s[x/d]`: assign x to d in every index.
    Aloni & van Ormondt §4 Definition 4.5: `s[x/d] := {i[x/d] | i ∈ s}`. -/
def State.extendIndividual (s : Finset (Index W Var Domain))
    (x : Var) (d : Domain) : Finset (Index W Var Domain) :=
  s.image (fun i => i.update x d)

/-- **Universal extension** `s[x]`: extend with every domain value at x.
    Aloni & van Ormondt §4 Definition 4.6: `s[x] := {i[x/d] | i ∈ s, d ∈ D}`.

    Requires `[Fintype Domain]` to range over the entire domain. -/
def State.extendUniversal [Fintype Domain] (s : Finset (Index W Var Domain))
    (x : Var) : Finset (Index W Var Domain) :=
  Finset.univ.biUnion (fun d : Domain => State.extendIndividual s x d)

/-- **Functional extension** `s[x/h]`: for each i in s, extend with d's drawn
    from `h(i)` (a non-empty subset of D).
    Aloni & van Ormondt §4 Definition 4.7: `s[x/h] := {i[x/d] | i ∈ s,
    d ∈ h(i)}`.

    Used to interpret existential quantification: `∃x φ` iff `M, s[x/h] ⊨ φ`
    for some functional `h`. -/
def State.extendFunctional (s : Finset (Index W Var Domain))
    (x : Var) (h : Index W Var Domain → Finset Domain) :
    Finset (Index W Var Domain) :=
  s.biUnion (fun i => (h i).image (fun d => i.update x d))

/-- **Modal pairing** `R(wᵢ)[gᵢ]`: pair each accessible world with the
    assignment of the original index. Used in modal evaluation
    (Aloni & van Ormondt §4 Definition 4.9). -/
def State.modalLift (X : Finset W) (g : Assignment Var Domain) :
    Finset (Index W Var Domain) :=
  X.image (fun v => (v, g))

-- ============================================================================
-- §2b State-extension distributive lemmas
-- ============================================================================

/-- Universal extension of empty team is empty. -/
theorem State.extendUniversal_empty [Fintype Domain] (x : Var) :
    State.extendUniversal (∅ : Finset (Index W Var Domain)) x = ∅ := by
  unfold State.extendUniversal State.extendIndividual
  ext; simp

/-- Functional extension of empty team is empty. -/
theorem State.extendFunctional_empty (x : Var)
    (h : Index W Var Domain → Finset Domain) :
    State.extendFunctional (∅ : Finset (Index W Var Domain)) x h = ∅ := by
  unfold State.extendFunctional
  simp

/-- Universal extension is monotone in the team. -/
theorem State.extendUniversal_subset_mono [Fintype Domain]
    {s t : Finset (Index W Var Domain)} (x : Var) (hsub : s ⊆ t) :
    State.extendUniversal s x ⊆ State.extendUniversal t x := by
  unfold State.extendUniversal State.extendIndividual
  intro i hi
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨d, j, hj, hupd⟩ := hi
  exact ⟨d, j, hsub hj, hupd⟩

/-- Universal extension distributes over union. -/
theorem State.extendUniversal_union_distrib [Fintype Domain]
    (s t : Finset (Index W Var Domain)) (x : Var) :
    State.extendUniversal (s ∪ t) x =
      State.extendUniversal s x ∪ State.extendUniversal t x := by
  unfold State.extendUniversal State.extendIndividual
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_image,
             Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, j, hj, hupd⟩
    cases hj with
    | inl hjs => exact Or.inl ⟨d, j, hjs, hupd⟩
    | inr hjt => exact Or.inr ⟨d, j, hjt, hupd⟩
  · rintro (⟨d, j, hjs, hupd⟩ | ⟨d, j, hjt, hupd⟩)
    · exact ⟨d, j, Or.inl hjs, hupd⟩
    · exact ⟨d, j, Or.inr hjt, hupd⟩

/-- Functional extension distributes over union of teams. -/
theorem State.extendFunctional_union_distrib (s t : Finset (Index W Var Domain))
    (x : Var) (h : Index W Var Domain → Finset Domain) :
    State.extendFunctional (s ∪ t) x h =
      State.extendFunctional s x h ∪ State.extendFunctional t x h := by
  unfold State.extendFunctional
  exact Finset.union_biUnion

/-- Functional extension is monotone in the team (for fixed `h`). -/
theorem State.extendFunctional_subset_mono {s t : Finset (Index W Var Domain)}
    (x : Var) (h : Index W Var Domain → Finset Domain) (hsub : s ⊆ t) :
    State.extendFunctional s x h ⊆ State.extendFunctional t x h := by
  unfold State.extendFunctional
  exact Finset.biUnion_subset_biUnion_of_subset_left _ hsub

end Semantics.QBSML

-- ============================================================================
-- §3 Formula language
-- ============================================================================

namespace Semantics.QBSML

/-- QBSML formula language (Aloni & van Ormondt §4 Definition 4.1).

    Parameterized over variable type `Var` and predicate type `Pred`. We use
    monadic predicates (`Pred → Var → Formula`) — sufficient for free-choice
    scenarios. Higher arities (`Pred → List Var → Formula`) and a term
    language (constants + variables) can be added without changing the
    substrate abstraction.

    □ is NOT primitive — defined as `□φ := ¬◇¬φ` (`QBSMLFormula.nec`). -/
inductive QBSMLFormula (Var : Type*) (Pred : Type*) where
  /-- Monadic predicate application. -/
  | pred : Pred → Var → QBSMLFormula Var Pred
  /-- Non-emptiness atom: state is non-empty. -/
  | ne : QBSMLFormula Var Pred
  /-- Bilateral negation: swap support/anti-support. -/
  | neg : QBSMLFormula Var Pred → QBSMLFormula Var Pred
  /-- Conjunction. -/
  | conj : QBSMLFormula Var Pred → QBSMLFormula Var Pred → QBSMLFormula Var Pred
  /-- Split (tensor) disjunction. -/
  | disj : QBSMLFormula Var Pred → QBSMLFormula Var Pred → QBSMLFormula Var Pred
  /-- Possibility modal. -/
  | poss : QBSMLFormula Var Pred → QBSMLFormula Var Pred
  /-- Existential quantifier. -/
  | exi : Var → QBSMLFormula Var Pred → QBSMLFormula Var Pred
  /-- Universal quantifier. -/
  | univ : Var → QBSMLFormula Var Pred → QBSMLFormula Var Pred
  deriving Repr

variable {Var Pred : Type*}

/-- □φ := ¬◇¬φ — necessity as an abbreviation, mirroring BSML. -/
def QBSMLFormula.nec (φ : QBSMLFormula Var Pred) : QBSMLFormula Var Pred :=
  .neg (.poss (.neg φ))

/-- A formula is NE-free if it does not contain the NE atom.
    For NE-free formulas, QBSML reduces to classical first-order modal logic
    on singleton states (Aloni & van Ormondt analogue of Anttila Proposition
    2.2.16). -/
def QBSMLFormula.isNEFree : QBSMLFormula Var Pred → Bool
  | .pred _ _ => true
  | .ne => false
  | .neg φ => φ.isNEFree
  | .conj φ ψ => φ.isNEFree && ψ.isNEFree
  | .disj φ ψ => φ.isNEFree && ψ.isNEFree
  | .poss φ => φ.isNEFree
  | .exi _ φ => φ.isNEFree
  | .univ _ φ => φ.isNEFree

end Semantics.QBSML

-- ============================================================================
-- §4 Models
-- ============================================================================

namespace Semantics.QBSML

/-- A QBSML model. Aloni & van Ormondt §4 Definition 4.2: `M = ⟨W, D, R, I⟩`.

    We use `Domain : Type*` as a parameter and `[Fintype Domain]` for the
    universal extension. The interpretation function is split: accessibility
    `R : W → Finset W` and predicate interpretation
    `pInterp : Pred → W → Finset Domain`. -/
structure QBSMLModel (W : Type*) (Domain : Type*) (Pred : Type*)
    [DecidableEq W] [Fintype W] where
  /-- Accessibility relation (per-world set of accessible worlds). -/
  access : W → Finset W
  /-- Predicate interpretation: at world `w`, predicate `p` picks out the
      Finset of domain elements satisfying it. -/
  pInterp : Pred → W → Finset Domain

end Semantics.QBSML

-- ============================================================================
-- §5 Bilateral evaluation
-- ============================================================================

namespace Semantics.QBSML

variable {W Var Domain Pred : Type*}
variable [DecidableEq W] [Fintype W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-- Bilateral evaluation of QBSML formulas. Aloni & van Ormondt §4 Definition 4.9.

    `eval M true φ s` is support (`M, s ⊨ φ`); `eval M false φ s` is
    anti-support (`M, s ⊧ φ`). Negation flips polarity, making DNE
    definitional.

    Key shape: `Bool → Form → Finset Index → Prop` — exactly the template
    `Core.Logic.Team.flat_iff_downwardClosed_unionClosed_emptyTeam` is
    parameterized over (with `Point := Index W Var Domain`). The substrate
    test is whether the property + flatness theorems compose identically
    to BSML's. -/
def eval (M : QBSMLModel W Domain Pred) :
    Bool → QBSMLFormula Var Pred → Finset (Index W Var Domain) → Prop
  | true,  .pred P x, s =>
      ∀ i ∈ s, ∃ d, i.assign x = some d ∧ d ∈ M.pInterp P i.world
  | false, .pred P x, s =>
      ∀ i ∈ s, ∃ d, i.assign x = some d ∧ d ∉ M.pInterp P i.world
  | true,  .ne, s => s.Nonempty
  | false, .ne, s => s = ∅
  | true,  .neg ψ, s => eval M false ψ s
  | false, .neg ψ, s => eval M true ψ s
  | true,  .conj φ ψ, s => eval M true φ s ∧ eval M true ψ s
  | false, .conj φ ψ, s => ∃ t₁ t₂ : Finset (Index W Var Domain),
      Core.Logic.Team.splitsAs s t₁ t₂ ∧ eval M false φ t₁ ∧ eval M false ψ t₂
  | true,  .disj φ ψ, s => ∃ t₁ t₂ : Finset (Index W Var Domain),
      Core.Logic.Team.splitsAs s t₁ t₂ ∧ eval M true φ t₁ ∧ eval M true ψ t₂
  | false, .disj φ ψ, s => eval M false φ s ∧ eval M false ψ s
  | true,  .poss ψ, s =>
      ∀ i ∈ s, ∃ X : Finset W, X ⊆ M.access i.world ∧ X.Nonempty ∧
        eval M true ψ (State.modalLift X i.assign)
  | false, .poss ψ, s =>
      ∀ i ∈ s, eval M false ψ (State.modalLift (M.access i.world) i.assign)
  | true,  .univ x ψ, s => eval M true ψ (State.extendUniversal s x)
  | false, .univ x ψ, s =>
      ∃ h : Index W Var Domain → Finset Domain, (∀ i ∈ s, (h i).Nonempty) ∧
        eval M false ψ (State.extendFunctional s x h)
  | true,  .exi x ψ, s =>
      ∃ h : Index W Var Domain → Finset Domain, (∀ i ∈ s, (h i).Nonempty) ∧
        eval M true ψ (State.extendFunctional s x h)
  | false, .exi x ψ, s => eval M false ψ (State.extendUniversal s x)

/-- Support: positive evaluation. -/
abbrev support (M : QBSMLModel W Domain Pred) (φ : QBSMLFormula Var Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M true φ s

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : QBSMLModel W Domain Pred) (φ : QBSMLFormula Var Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M false φ s

-- ============================================================================
-- §6 DNE and basic unfolding lemmas
-- ============================================================================

theorem dne_support (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain)) :
    support M (.neg (.neg φ)) s ↔ support M φ s := Iff.rfl

theorem dne_antiSupport (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain)) :
    antiSupport M (.neg (.neg φ)) s ↔ antiSupport M φ s := Iff.rfl

@[simp] lemma support_neg (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain)) :
    support M (.neg φ) s ↔ antiSupport M φ s := Iff.rfl

@[simp] lemma antiSupport_neg (M : QBSMLModel W Domain Pred)
    (φ : QBSMLFormula Var Pred) (s : Finset (Index W Var Domain)) :
    antiSupport M (.neg φ) s ↔ support M φ s := Iff.rfl

/-- QBSML's `support` and `antiSupport` form a paraconsistent bilateral
    logic (`Core.Logic.Bilateral.IsBilateral`) under `QBSMLFormula.neg`.
    Same shape as BSML's `isBilateral`, lifted to the `Index W Var Domain`
    carrier — point-polymorphism at work. -/
theorem isBilateral (M : QBSMLModel W Domain Pred) :
    Core.Logic.Bilateral.IsBilateral
      (Form := QBSMLFormula Var Pred)
      (Result := Finset (Index W Var Domain) → Prop)
      (support M) (antiSupport M) QBSMLFormula.neg where
  positive_negate φ := funext fun s => propext (support_neg M φ s)
  negative_negate φ := funext fun s => propext (antiSupport_neg M φ s)

-- ============================================================================
-- §7 Frame conditions via s↓ projection
-- ============================================================================

/-- QBSML's `isStateBased`: defined via the `s↓` projection composed with
    `Core.Logic.Team.isStateBased`. The same Core function as BSML uses,
    just applied to the world-set of the team rather than the team itself.

    Aloni & van Ormondt §4 Definition 4.10: `R is state-based on (M, s)` iff
    `R(w) = s↓` for all `w ∈ s↓`. Specialization-via-composition exemplifies
    the foundational mathlib pattern: same Core definition, different
    instantiation via projection. -/
def QBSMLModel.isStateBased (M : QBSMLModel W Domain Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  Core.Logic.Team.isStateBased M.access (State.worldProj s)

/-- QBSML's `isIndisputable`: same Core function, applied to `s↓`. -/
def QBSMLModel.isIndisputable (M : QBSMLModel W Domain Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  Core.Logic.Team.isIndisputable M.access (State.worldProj s)

end Semantics.QBSML
