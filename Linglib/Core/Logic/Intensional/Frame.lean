import Mathlib.Data.Set.Basic

/-!
# Intensional Logic: Frames and Types

@cite{dowty-wall-peters-1981} @cite{gallin-1975}

Foundations for intensional logic following DWP Ch. 6. A **Frame** provides
the entity domain and index set; **Ty** is the recursive grammar of semantic
types; **Frame.Denot** computes denotation domains from a frame and type.

## Key definitions

- `Ty` — semantic types: `e`, `t`, `⟨a,b⟩`, `⟨s,a⟩`
- `Frame` — entity domain + index set
- `Frame.Denot` — denotation domains (DWP Def B.3)
- `up`, `down` — intension formation / extension extraction (DWP Rules B.14–B.15)
-/

namespace Core.IntensionalLogic

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

/-- A type is conjoinable if it "ends in `t`" (@cite{partee-rooth-1983} Definition 4).
    Intension types `⟨s,a⟩` are conjoinable iff the base type is —
    conjunction is pointwise over indices. -/
def Ty.isConjoinable : Ty → Bool
  | .t => true
  | .e => false
  | .fn _ τ => τ.isConjoinable
  | .intens a => a.isConjoinable

-- ════════════════════════════════════════════════════════════════
-- § Frames (DWP Ch. 6)
-- ════════════════════════════════════════════════════════════════

/-- An IL frame: entity domain + index set.

DWP's model is ⟨A, W, T, <, F⟩. The frame provides the domains:

- `Entity` = A (the domain of individuals)
- `Index` = W × T (world-time pairs), or just W, or Unit for extensional

Temporal ordering, accessibility relations, etc. are added as structure
on the Index type, not baked into the frame. -/
structure Frame where
  Entity : Type
  Index : Type

-- ════════════════════════════════════════════════════════════════
-- § Denotation Domains (DWP Ch. 6, Def B.3)
-- ════════════════════════════════════════════════════════════════

/-- Denotation domains, computed from a frame and a type.

    D_e = F.Entity
    D_t = Prop
    D_⟨a,b⟩ = D_a → D_b
    D_⟨s,a⟩ = F.Index → D_a -/
def Frame.Denot (F : Frame) : Ty → Type
  | .e => F.Entity
  | .t => Prop
  | .fn a b => F.Denot a → F.Denot b
  | .intens a => F.Index → F.Denot a

-- ════════════════════════════════════════════════════════════════
-- § Up and Down (DWP Rules B.14–B.15)
-- ════════════════════════════════════════════════════════════════

/-- ^α — form the rigid intension of an expression.
    Maps a denotation to the constant function over indices.
    Definitionally equal to `Core.Intension.rigid`. -/
def up {F : Frame} {a : Ty} (x : F.Denot a) : F.Denot (.intens a) :=
  λ _ => x

/-- ˇα — extract the extension at index i.
    Evaluates an intension at a given index.
    Definitionally equal to `Core.Intension.evalAt`. -/
def down {F : Frame} {a : Ty} (s : F.Denot (.intens a)) (i : F.Index) : F.Denot a :=
  s i

/-- Down-up cancellation: ˇ(^α) = α at any index. DWP Theorem 1. -/
theorem down_up {F : Frame} {a : Ty} (x : F.Denot a) (i : F.Index) :
    down (up x) i = x := rfl

-- ════════════════════════════════════════════════════════════════
-- § Sentential Operators
-- ════════════════════════════════════════════════════════════════

/-- Sentence negation. -/
def neg {F : Frame} (p : F.Denot .t) : F.Denot .t := ¬p

/-- Sentence conjunction. -/
def conj {F : Frame} (p q : F.Denot .t) : F.Denot .t := p ∧ q

/-- Sentence disjunction. -/
def disj {F : Frame} (p q : F.Denot .t) : F.Denot .t := p ∨ q

theorem double_negation {F : Frame} (p : F.Denot .t) : neg (neg p) = p := by
  simp only [neg, not_not]

-- ════════════════════════════════════════════════════════════════
-- § Characteristic Functions
-- ════════════════════════════════════════════════════════════════

/-- Convert a predicate `e → t` to a `Set` (the extension). -/
def predicateToSet {F : Frame} (p : F.Denot (.e ⇒ .t)) : Set F.Entity :=
  { x | p x }

/-- Convert a set to a predicate. -/
def setToPredicate {F : Frame} (s : Set F.Entity) : F.Denot (.e ⇒ .t) :=
  λ x => x ∈ s

/-- Membership in a predicate's extension. -/
def inExtension {F : Frame} (p : F.Denot (.e ⇒ .t)) (x : F.Entity) : Prop := p x

-- ════════════════════════════════════════════════════════════════
-- § Currying
-- ════════════════════════════════════════════════════════════════

/-- Uncurry a binary relation (obj-first) to a pair relation (subj-first). -/
def uncurry {F : Frame} (f : F.Denot (.e ⇒ .e ⇒ .t)) : F.Entity × F.Entity → Prop :=
  λ (x, y) => f y x

/-- Curry a pair relation to a binary relation. -/
def curry {F : Frame} (r : F.Entity × F.Entity → Prop) : F.Denot (.e ⇒ .e ⇒ .t) :=
  λ y x => r (x, y)

theorem curry_uncurry {F : Frame} (f : F.Denot (.e ⇒ .e ⇒ .t)) :
    curry (uncurry f) = f := rfl

theorem uncurry_curry {F : Frame} (r : F.Entity × F.Entity → Prop) :
    uncurry (curry r) = r := rfl

end Core.IntensionalLogic
