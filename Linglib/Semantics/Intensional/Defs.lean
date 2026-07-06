import Mathlib.Data.Set.Basic
import Mathlib.Data.Rat.Defs

/-!
# Intensional Logic: Types and Denotations

[dowty-wall-peters-1981] [gallin-1975]

Foundations for intensional logic following DWP Ch. 6. `Ty` is the recursive
grammar of semantic types; `Denot E W` computes denotation domains from
explicit entity (`E`) and index (`W`) type parameters and a type.

## Key definitions

- `Ty` — semantic types: `e`, `t`, `⟨a,b⟩`, `⟨s,a⟩`
- `Denot E W` — denotation domains (DWP Def B.3), parameterized by entity and index types
- `up`, `down` — intension formation / extension extraction (DWP Rules B.14–B.15)
-/

namespace Intensional

-- ════════════════════════════════════════════════════════════════
-- § Semantic Types (DWP Ch. 6, Def B.1)
-- ════════════════════════════════════════════════════════════════

/-- Semantic types for Intensional Logic.

- `e` — entities
- `t` — truth values
- `fn a b` — functions ⟨a,b⟩
- `intens a` — intensions ⟨s,a⟩ (functions from indices to a-extensions)

The old `Ty.s` base type is replaced by the `intens` constructor:
intensionality is a type-forming operation, not a separate domain. -/
inductive Ty where
  | e : Ty
  | t : Ty
  /-- Degrees (type `d`): the scale sort of degree semantics
      ([heim-2001], [wellwood-2015]). Denoted by ℚ, the repo's exact
      degree carrier. -/
  | d : Ty
  | fn : Ty → Ty → Ty
  | intens : Ty → Ty
  deriving Repr, DecidableEq

infixr:25 " ⇒ " => Ty.fn

/-- Standard type abbreviations. -/
abbrev Ty.et : Ty := .e ⇒ .t
abbrev Ty.eet : Ty := .e ⇒ .e ⇒ .t
abbrev Ty.ett : Ty := (.e ⇒ .t) ⇒ .t
/-- ⟨s,t⟩ — propositions (sets of indices). -/
abbrev Ty.prop : Ty := .intens .t
/-- ⟨s,e⟩ — individual concepts (index-dependent individuals). -/
abbrev Ty.indConcept : Ty := .intens .e

/-- A type is conjoinable if it "ends in `t`" ([partee-rooth-1983] Definition 4).
    Intension types `⟨s,a⟩` are conjoinable iff the base type is —
    conjunction is pointwise over indices. -/
def Ty.isConjoinable : Ty → Bool
  | .t => true
  | .e => false
  | .d => false
  | .fn _ τ => τ.isConjoinable
  | .intens a => a.isConjoinable

-- ════════════════════════════════════════════════════════════════
-- § Denotation Domains (DWP Ch. 6, Def B.3)
-- ════════════════════════════════════════════════════════════════

/-- Denotation domains, computed from an entity type `E`, an index type `W`,
    and a semantic type.

    DWP's model is ⟨A, W, T, <, F⟩; here `E` = A (the domain of individuals) and
    `W` = W × T (world-time pairs), or just W, or `Unit` for extensional. Temporal
    ordering, accessibility relations, etc. are structure on `W`, not baked in.

    D_e = E
    D_t = Prop
    D_⟨a,b⟩ = D_a → D_b
    D_⟨s,a⟩ = W → D_a -/
def Denot (E W : Type) : Ty → Type
  | .e => E
  | .t => Prop
  | .d => ℚ
  | .fn a b => Denot E W a → Denot E W b
  | .intens a => W → Denot E W a

-- ════════════════════════════════════════════════════════════════
-- § Up and Down (DWP Rules B.14–B.15)
-- ════════════════════════════════════════════════════════════════

/-- ^α — form the rigid intension of an expression.
    Maps a denotation to the constant function over indices.
    Definitionally equal to `Intensional.Intension.rigid`. -/
def up {E W : Type} {a : Ty} (x : Denot E W a) : Denot E W (.intens a) :=
  λ _ => x

/-- ˇα — extract the extension at index i.
    Evaluates an intension at a given index.
    Definitionally equal to `Intensional.Intension.evalAt`. -/
def down {E W : Type} {a : Ty} (s : Denot E W (.intens a)) (i : W) : Denot E W a :=
  s i

/-- Down-up cancellation: ˇ(^α) = α at any index. DWP Theorem 1. -/
theorem down_up {E W : Type} {a : Ty} (x : Denot E W a) (i : W) :
    down (up x) i = x := rfl

-- ════════════════════════════════════════════════════════════════
-- § Sentential Operators
-- ════════════════════════════════════════════════════════════════

/-- Sentence negation. -/
def neg {E W : Type} (p : Denot E W .t) : Denot E W .t := ¬p

/-- Sentence conjunction. -/
def conj {E W : Type} (p q : Denot E W .t) : Denot E W .t := p ∧ q

/-- Sentence disjunction. -/
def disj {E W : Type} (p q : Denot E W .t) : Denot E W .t := p ∨ q

theorem double_negation {E W : Type} (p : Denot E W .t) : neg (neg p) = p := by
  simp only [neg, not_not]

-- ════════════════════════════════════════════════════════════════
-- § Characteristic Functions
-- ════════════════════════════════════════════════════════════════

/-- Convert a predicate `e → t` to a `Set` (the extension). -/
def predicateToSet {E W : Type} (p : Denot E W (.e ⇒ .t)) : Set E :=
  { x | p x }

/-- Convert a set to a predicate. -/
def setToPredicate {E W : Type} (s : Set E) : Denot E W (.e ⇒ .t) :=
  λ x => x ∈ s

/-- Membership in a predicate's extension. -/
def inExtension {E W : Type} (p : Denot E W (.e ⇒ .t)) (x : E) : Prop := p x

-- ════════════════════════════════════════════════════════════════
-- § Currying
-- ════════════════════════════════════════════════════════════════

/-- Uncurry a binary relation (obj-first) to a pair relation (subj-first). -/
def uncurry {E W : Type} (f : Denot E W (.e ⇒ .e ⇒ .t)) : E × E → Prop :=
  λ (x, y) => f y x

/-- Curry a pair relation to a binary relation. -/
def curry {E W : Type} (r : E × E → Prop) : Denot E W (.e ⇒ .e ⇒ .t) :=
  λ y x => r (x, y)

theorem curry_uncurry {E W : Type} (f : Denot E W (.e ⇒ .e ⇒ .t)) :
    curry (uncurry f) = f := rfl

theorem uncurry_curry {E : Type} (W : Type) (r : E × E → Prop) :
    uncurry (curry (W := W) r) = r := rfl

end Intensional
