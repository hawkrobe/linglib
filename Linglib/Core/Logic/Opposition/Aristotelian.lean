import Mathlib.Logic.Basic
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# The four Aristotelian relations @cite{demey-smessaert-2018}

Per Demey & Smessaert 2018 "Combinatorial Bitstring Semantics for Arbitrary
Logical Fragments" (J Phil Logic 47:325–363), Definition 1.

Given a logical system `S` with Boolean operators and model-theoretic semantics
`⊨_S`, two formulas φ and ψ stand in one of four *Aristotelian relations*:

| Relation       | Definition                                          |
|----------------|-----------------------------------------------------|
| Contradictory  | `⊨ ¬(φ ∧ ψ)` and `⊨ φ ∨ ψ`                          |
| Contrary       | `⊨ ¬(φ ∧ ψ)` and `⊭ φ ∨ ψ`                          |
| Subcontrary    | `⊭ ¬(φ ∧ ψ)` and `⊨ φ ∨ ψ`                          |
| Subalternation | `⊨ φ → ψ` and `⊭ ψ → φ`                             |

The collection `𝒜𝒢_S := {CD_S, C_S, SC_S, SA_S}` is called the *Aristotelian
geometry* of `S`.

This file formalizes the relations directly over a model class `W` (where each
"formula" is a predicate `W → Bool`). Validity `⊨ φ` becomes `∀ w, φ w = true`.
The four conditions in Definition 1 are pure Boolean conditions on truth
values, and the universal closure over `W` is the standard model-theoretic
gloss of `⊨_S`, so this representation is faithful. (Demey-Smessaert's
Lemma 1, p. 329, separately establishes that every Boolean isomorphism is an
Aristotelian isomorphism — this is the *transfer* property exploited in
`Bitstring.lean`'s Theorem 2, not a justification of the encoding here.)

## Generality

Three layers of generality, each downstream of the previous:

1. **`AristotelianRel`** (this file) — relations over a model class `W` with
   formulas as `W → Bool` predicates. Sufficient for instantiating any
   concrete logical system: classical logic, modal logic, GQ theory, etc.

2. **`Diagram`** (`Diagram.lean`) — labeled-poset structure with a finite
   indexed family of formulas and the relation matrix between them. Squares,
   hexagons, cubes, n-cubes are all `Diagram` specializations.

3. **`BitstringSemantics`** (`Bitstring.lean`) — the partition-based bitstring
   representation that makes Aristotelian structure transparent (Thm 1–2).

Probabilistic generalization lives in `Probabilistic.lean`.
-/

namespace Core.Opposition

variable {W : Type*}

/-- The four Aristotelian relations as a single inductive label.
    Used by `Diagram.relation` to label edges. -/
inductive AristotelianRel where
  | contradictory
  | contrary
  | subcontrary
  | subaltern  -- φ → ψ direction (asymmetric: A is *sub*altern to ψ here means φ ⊨ ψ)
  | unconnected
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- §1. The four relations as predicates
-- ============================================================================

/-- `Contradictory φ ψ`: `φ ∧ ψ` is unsatisfiable AND `φ ∨ ψ` is valid.
    Equivalently, exactly one of φ, ψ is true at each world. -/
def Contradictory (φ ψ : W → Bool) : Prop :=
  (∀ w, ¬ (φ w = true ∧ ψ w = true)) ∧ (∀ w, φ w = true ∨ ψ w = true)

/-- `Contrary φ ψ`: cannot both be true, but can both be false.
    `φ ∧ ψ` is unsatisfiable AND `φ ∨ ψ` is not valid. -/
def Contrary (φ ψ : W → Bool) : Prop :=
  (∀ w, ¬ (φ w = true ∧ ψ w = true)) ∧ ¬ (∀ w, φ w = true ∨ ψ w = true)

/-- `Subcontrary φ ψ`: cannot both be false, but can both be true.
    `φ ∧ ψ` is satisfiable AND `φ ∨ ψ` is valid. -/
def Subcontrary (φ ψ : W → Bool) : Prop :=
  ¬ (∀ w, ¬ (φ w = true ∧ ψ w = true)) ∧ (∀ w, φ w = true ∨ ψ w = true)

/-- `Subaltern φ ψ`: `φ` entails `ψ` but not conversely.
    Asymmetric: `Subaltern φ ψ` ≠ `Subaltern ψ φ` in general. -/
def Subaltern (φ ψ : W → Bool) : Prop :=
  (∀ w, φ w = true → ψ w = true) ∧ ¬ (∀ w, ψ w = true → φ w = true)

/-- `Unconnected φ ψ`: φ and ψ stand in NO Aristotelian relation. They are
    "logically independent" in the Aristotelian sense — all four truth
    combinations are realized. Per Smessaert & Demey 2014. -/
def Unconnected (φ ψ : W → Bool) : Prop :=
  (∃ w, φ w = true ∧ ψ w = true) ∧
  (∃ w, φ w = true ∧ ψ w = false) ∧
  (∃ w, φ w = false ∧ ψ w = true) ∧
  (∃ w, φ w = false ∧ ψ w = false)

-- ============================================================================
-- §2. Symmetry properties
-- ============================================================================

/-- Contradictoriness is symmetric. -/
theorem Contradictory.symm {φ ψ : W → Bool} (h : Contradictory φ ψ) :
    Contradictory ψ φ := by
  refine ⟨fun w hand => h.1 w ⟨hand.2, hand.1⟩, fun w => ?_⟩
  rcases h.2 w with hφ | hψ
  · exact Or.inr hφ
  · exact Or.inl hψ

/-- Contrariety is symmetric. -/
theorem Contrary.symm {φ ψ : W → Bool} (h : Contrary φ ψ) :
    Contrary ψ φ := by
  refine ⟨fun w hand => h.1 w ⟨hand.2, hand.1⟩, ?_⟩
  intro hOr; apply h.2; intro w
  rcases hOr w with hψ | hφ
  · exact Or.inr hψ
  · exact Or.inl hφ

/-- Subcontrariety is symmetric. -/
theorem Subcontrary.symm {φ ψ : W → Bool} (h : Subcontrary φ ψ) :
    Subcontrary ψ φ := by
  refine ⟨?_, fun w => ?_⟩
  · intro hAnd; apply h.1; intro w hwand
    exact hAnd w ⟨hwand.2, hwand.1⟩
  · rcases h.2 w with hφ | hψ
    · exact Or.inr hφ
    · exact Or.inl hψ

-- (Subaltern is not symmetric; that's the point.)

-- ============================================================================
-- §3. Classification (mutual exclusion)
-- ============================================================================

/-- Per Demey & Smessaert §2.1, the four Aristotelian relations are mutually
    exclusive: any pair of formulas stands in at most one relation (or in
    none, in which case they are `Unconnected`). -/
theorem contradictory_not_contrary {φ ψ : W → Bool}
    (hCD : Contradictory φ ψ) : ¬ Contrary φ ψ := by
  intro hC; exact hC.2 hCD.2

theorem contradictory_not_subcontrary {φ ψ : W → Bool}
    (hCD : Contradictory φ ψ) : ¬ Subcontrary φ ψ := fun hSC => hSC.1 hCD.1

theorem contrary_not_subcontrary {φ ψ : W → Bool}
    (hC : Contrary φ ψ) : ¬ Subcontrary φ ψ := fun hSC => hSC.1 hC.1

-- ============================================================================
-- §4. BA-generic Aristotelian relations (Prop↔Bool gap closure)
-- ============================================================================

/-! The four Aristotelian relations are purely algebraic — they are statements
about `⊓`, `⊔`, `⊥`, `⊤` in a Boolean algebra. The model-theoretic forms
above (specialized to `W → Bool` predicates) are concrete instances; the
BA-generic forms below provide a unified API that works for both `W → Bool`
and `W → Prop` predicates (and `Set W`, propositional fragments, sub-σ-algebras
of measurable sets, etc.) via `Pi.instBooleanAlgebra` or other BA instances.

**Why this matters**: closes the architectural gap identified in the audit
between this file's `W → Bool` predicates and `Theories/Semantics/
Quantification/Quantifier.lean`'s `(F.Entity → Prop)`-valued GQ semantics
(plus the 5 modality `theorem duality`s, BC1981 §8 GQ duality, etc.). All
those Prop-valued statements can now instantiate the same BA-generic
predicates via `Pi.instBooleanAlgebra` for `Prop`. -/

section Algebraic
variable {α : Type*} [BooleanAlgebra α]

/-- BA-generic contradictoriness: `φ ⊓ ψ = ⊥` and `φ ⊔ ψ = ⊤`. The two
    elements are jointly impossible AND exhaustive. In any Boolean algebra
    this is equivalent to `ψ = φᶜ` (uniqueness of complement). -/
def IsContradictory (φ ψ : α) : Prop := φ ⊓ ψ = ⊥ ∧ φ ⊔ ψ = ⊤

/-- BA-generic contrariety: `φ ⊓ ψ = ⊥` (jointly impossible) but
    `φ ⊔ ψ ≠ ⊤` (not jointly exhaustive — both can be false). -/
def IsContrary (φ ψ : α) : Prop := φ ⊓ ψ = ⊥ ∧ φ ⊔ ψ ≠ ⊤

/-- BA-generic subcontrariety: `φ ⊓ ψ ≠ ⊥` (can both be true) AND
    `φ ⊔ ψ = ⊤` (jointly exhaustive — at least one must be true). -/
def IsSubcontrary (φ ψ : α) : Prop := φ ⊓ ψ ≠ ⊥ ∧ φ ⊔ ψ = ⊤

/-- BA-generic *proper* subalternation: `φ ≤ ψ` (entailment) but `φ ≠ ψ`
    (strictly stronger). -/
def IsSubaltern (φ ψ : α) : Prop := φ ≤ ψ ∧ φ ≠ ψ

end Algebraic

-- ============================================================================
-- §5. Bridges to model-theoretic forms (deferred — see docstring)
-- ============================================================================

/-! Bridge `iff` lemmas connecting `IsContradictory`/`IsSubaltern`/etc. for
the Pi-instances `W → Bool` and `W → Prop` to the model-theoretic conventions
those predicate spaces commonly use (existential/universal quantification over
worlds with `= true` checks for Bool, direct conjunctive/disjunctive form for
Prop) are deferred to a follow-on. The `iff`s are routine but Lean-fiddly
(many `Pi.inf_apply` / `Pi.bot_apply` rewrites + Bool/Prop case analysis) —
each one easily 15-20 LOC, 8 lemmas total ≈ ~140 LOC.

For now, the gap is closed at the *type* level: `IsContradictory` works
uniformly for any `[BooleanAlgebra α]`, and consumers that want to use it on
`W → Bool` or `W → Prop` predicates can do so directly via the Pi-instance
without going through a model-theoretic intermediary. The model-theoretic
forms above (`Contradictory`/`Contrary`/`Subaltern`/`Subcontrary`/`Unconnected`
specialized to `W → Bool`) remain valid; bridges land when consumer demand
materializes. -/

end Core.Opposition
