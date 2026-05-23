import Mathlib.Data.List.Basic

/-!
# Writer Monad for Compositional Side-Effects
@cite{giorgolo-asudeh-2012} @cite{shan-2001}

The Writer monad `⟨M, η, ⋆⟩` models meaning dimensions that accumulate
side-effect information during compositional interpretation:

- **M** (the functor): maps a type `A` to paired values `A × List P`
- **η** (unit/pure): lifts a value with an empty log
- **⋆** (bind): sequences computations, combining their logs

This pattern unifies several linglib constructions:

| Phenomenon | Value | Log |
|------------|-------|-----|
| Conventional implicatures | at-issue content | CI propositions |
| Post-suppositions | DRS content | cardinality tests |
| Expressives | denotation | speaker attitude |

The Writer monad enforces @cite{potts-2005}'s flow restriction structurally:
`bind`'s function argument receives only the value, never the log. At-issue
content can flow into side-issue computations, but side-issue content cannot
leak back into at-issue computation.

See `PostSuppositional.lean` for the same pattern applied to dynamic GQs.
-/

namespace Semantics.Composition.WriterMonad

/-- The Writer monad: a value paired with an accumulated log.

    In @cite{giorgolo-asudeh-2012}'s notation, `Writer P A` is `M(A)`,
    where the second component is a collection of logged items of type `P`,
    represented as a `List` for computability. -/
structure Writer (P : Type*) (A : Type*) where
  /-- The at-issue value -/
  val : A
  /-- Accumulated side-effect log -/
  log : List P

namespace Writer

variable {P A B C : Type*}

-- ════════════════════════════════════════════════════
-- § Extensionality
-- ════════════════════════════════════════════════════

@[ext]
theorem ext {m₁ m₂ : Writer P A}
    (hv : m₁.val = m₂.val) (hl : m₁.log = m₂.log) : m₁ = m₂ := by
  cases m₁; cases m₂; simp_all

-- ════════════════════════════════════════════════════
-- § Core Operations: η, ⋆, tell
-- ════════════════════════════════════════════════════

/-- **η** (unit): lift a pure value with an empty log.

    Ordinary lexical items are η-lifted:
    `⟦john⟧ = η(j)`, `⟦likes⟧ = η(λyλx.like(x,y))` -/
def pure (a : A) : Writer P A := ⟨a, []⟩

/-- **⋆** (bind): sequence computations, combining logs.

    `⟨x, P⟩ ⋆ f = ⟨π₁(f x), P ++ π₂(f x)⟩`

    The function `f` receives only the value `x`, not the log `P`.
    This enforces @cite{potts-2005}'s restriction: side-issue content
    (in the log) is invisible to subsequent at-issue computation. -/
def bind (m : Writer P A) (f : A → Writer P B) : Writer P B :=
  ⟨(f m.val).val, m.log ++ (f m.val).log⟩

/-- **map**: apply a function to the value, preserving the log. -/
def map (f : A → B) (m : Writer P A) : Writer P B :=
  ⟨f m.val, m.log⟩

/-- **tell** (write): log a single item.

    Used by CI-contributing expressions to add propositions to the
    side-issue dimension. In @cite{giorgolo-asudeh-2012}:
    `write(t) = ⟨⊥, {t}⟩` -/
def tell (p : P) : Writer P Unit := ⟨(), [p]⟩

-- ════════════════════════════════════════════════════
-- § Monadic Application
-- ════════════════════════════════════════════════════

/-- Monadic application (⊸-elimination in Glue).

    `A(f)(x) = f ⋆ λg. x ⋆ λy. η(g y)`

    Both function and argument may carry side-effects;
    all side-effects are combined in the result. -/
def app (mf : Writer P (A → B)) (mx : Writer P A) : Writer P B :=
  mf.bind λ f => mx.bind λ x => Writer.pure (f x)

-- ════════════════════════════════════════════════════
-- § Simp Lemmas
-- ════════════════════════════════════════════════════

@[simp] theorem pure_val (a : A) :
    (Writer.pure (P := P) a).val = a := rfl
@[simp] theorem pure_log (a : A) :
    (Writer.pure (P := P) a).log = [] := rfl
@[simp] theorem bind_val (m : Writer P A) (f : A → Writer P B) :
    (m.bind f).val = (f m.val).val := rfl
@[simp] theorem bind_log (m : Writer P A) (f : A → Writer P B) :
    (m.bind f).log = m.log ++ (f m.val).log := rfl
@[simp] theorem tell_val (p : P) :
    (Writer.tell p).val = () := rfl
@[simp] theorem tell_log (p : P) :
    (Writer.tell p).log = [p] := rfl
@[simp] theorem map_val (f : A → B) (m : Writer P A) :
    (m.map f).val = f m.val := rfl
@[simp] theorem map_log (f : A → B) (m : Writer P A) :
    (m.map f).log = m.log := rfl

-- ════════════════════════════════════════════════════
-- § Monad Laws
-- ════════════════════════════════════════════════════

/-- Left identity: `η(a) ⋆ f = f a` -/
theorem bind_pure_left (a : A) (f : A → Writer P B) :
    (Writer.pure a).bind f = f a := by
  ext <;> simp

/-- Right identity: `m ⋆ η = m` -/
theorem bind_pure_right (m : Writer P A) :
    m.bind Writer.pure = m := by
  ext <;> simp

/-- Associativity: `(m ⋆ f) ⋆ g = m ⋆ (λa. f a ⋆ g)` -/
theorem bind_assoc (m : Writer P A) (f : A → Writer P B)
    (g : B → Writer P C) :
    (m.bind f).bind g = m.bind (λ a => (f a).bind g) := by
  ext <;> simp [List.append_assoc]

-- ════════════════════════════════════════════════════
-- § Log Monotonicity
-- ════════════════════════════════════════════════════

/-- The log only grows: bind's output log extends the input log. -/
theorem log_grows (m : Writer P A) (f : A → Writer P B) :
    ∃ suffix, (m.bind f).log = m.log ++ suffix :=
  ⟨(f m.val).log, rfl⟩

/-- Side-effects are permanent: once logged, a proposition stays in the log. -/
theorem tell_persists (m : Writer P A) (f : A → Writer P B)
    (p : P) (h : p ∈ m.log) : p ∈ (m.bind f).log := by
  simp only [bind_log, List.mem_append]
  exact Or.inl h

end Writer

end Semantics.Composition.WriterMonad
