import Mathlib.Control.Monad.Writer

/-!
# Writer Monad for Compositional Side-Effects
[giorgolo-asudeh-2012] [shan-2001]

The Writer monad `⟨M, η, ⋆⟩` models meaning dimensions that accumulate
side-effect information during compositional interpretation:

- **M** (the functor): maps a type `A` to paired values `A × List P`
- **η** (unit/pure): lifts a value with an empty log
- **⋆** (bind): sequences computations, combining their logs

The carrier is mathlib's `Writer (List P) A` (= `WriterT (List P) Id A`),
whose `Monad` instance comes from mathlib's `[EmptyCollection ω] [Append ω]`
instance for `WriterT`. This file adds the domain-named surface
(`Writer.mk`/`val`/`log`/`tell`), projection simp lemmas, and the
`LawfulMonad` instance for list logs.

This pattern unifies several linglib constructions:

| Phenomenon | Value | Log |
|------------|-------|-----|
| Conventional implicatures | at-issue content | CI propositions |
| Post-suppositions | DRS content | cardinality tests |
| Expressives | denotation | speaker attitude |

The Writer monad enforces [potts-2005]'s flow restriction structurally:
`bind`'s function argument receives only the value, never the log. At-issue
content can flow into side-issue computations, but side-issue content cannot
leak back into at-issue computation.

See `Studies/Charlow2021.lean` (`PostSupp`) for the same pattern applied to
dynamic GQs, with the log monoid `(Update S, Update.seq, test ⊤)` in place of
`List P`.
-/

universe u

namespace Writer

variable {ω : Type u} {P A B : Type u}

/-- Construct a Writer computation from a value and a log. -/
protected def mk (a : A) (w : ω) : Writer ω A := WriterT.mk (a, w)

/-- The at-issue value of a Writer computation. -/
def val (m : Writer ω A) : A := m.run.1

/-- The accumulated side-effect log of a Writer computation. -/
def log (m : Writer ω A) : ω := m.run.2

@[ext]
protected theorem ext {m₁ m₂ : Writer ω A}
    (hv : m₁.val = m₂.val) (hl : m₁.log = m₂.log) : m₁ = m₂ :=
  WriterT.ext _ _ (Prod.ext_iff.mpr ⟨hv, hl⟩)

@[simp] theorem val_mk (a : A) (w : ω) : (Writer.mk a w).val = a := rfl

@[simp] theorem log_mk (a : A) (w : ω) : (Writer.mk a w).log = w := rfl

/-- **tell** (write): log a single item. Used by CI-contributing expressions
to add propositions to the side-issue dimension; in [giorgolo-asudeh-2012]:
`write(t) = ⟨⊥, {t}⟩`. (`PUnit` rather than `Unit` keeps it
universe-polymorphic; at `Type 0` they coincide.) -/
def tell (p : P) : Writer (List P) PUnit := Writer.mk PUnit.unit [p]

/-! ### Projection lemmas for list logs -/

@[simp] theorem val_pure (a : A) : (pure a : Writer (List P) A).val = a := rfl

@[simp] theorem log_pure (a : A) : (pure a : Writer (List P) A).log = [] := rfl

@[simp] theorem val_bind (m : Writer (List P) A) (f : A → Writer (List P) B) :
    (m >>= f).val = (f m.val).val := rfl

@[simp] theorem log_bind (m : Writer (List P) A) (f : A → Writer (List P) B) :
    (m >>= f).log = m.log ++ (f m.val).log := rfl

@[simp] theorem val_map (f : A → B) (m : Writer (List P) A) :
    (f <$> m).val = f m.val := rfl

@[simp] theorem log_map (f : A → B) (m : Writer (List P) A) :
    (f <$> m).log = m.log := rfl

@[simp] theorem val_tell (p : P) : (tell p).val = PUnit.unit := rfl

@[simp] theorem log_tell (p : P) : (tell p).log = [p] := rfl

/-! ### Monad laws

The `Monad (Writer (List P))` instance is mathlib's
`[EmptyCollection ω] [Append ω]` instance for `WriterT`; the laws hold
because `(List P, ++, [])` is a monoid. -/

instance : LawfulMonad (Writer (List P)) := LawfulMonad.mk' (Writer (List P))
  (id_map := λ _ => rfl)
  (pure_bind := λ _ _ => rfl)
  (bind_assoc := λ _ _ _ => Writer.ext rfl (List.append_assoc ..))
  (bind_pure_comp := λ _ _ => Writer.ext rfl (List.append_nil _))

/-! ### Log monotonicity -/

/-- The log only grows: bind's output log extends the input log. -/
theorem log_grows (m : Writer (List P) A) (f : A → Writer (List P) B) :
    ∃ suffix, (m >>= f).log = m.log ++ suffix :=
  ⟨(f m.val).log, rfl⟩

/-- Side-effects are permanent: once logged, an item stays in the log. -/
theorem tell_persists (m : Writer (List P) A) (f : A → Writer (List P) B)
    (p : P) (h : p ∈ m.log) : p ∈ (m >>= f).log := by
  simp only [log_bind, List.mem_append]
  exact Or.inl h

end Writer
