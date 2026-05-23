/-!
# Polarity Operators
@cite{laka-1990} @cite{turk-hirsch-2026}

The two semantic operators that polarity heads spell out, as bare functions
on `(W → Prop)` propositions:

- **`affirm`** — identity (the affirmative Σ operator of @cite{laka-1990}).
- **`neg`** — pointwise propositional negation.

This module is deliberately syntax-free: no UPOS, no head structure, no
"PolarityHead" packaging. Those notions belong at the syntax-semantics
interface or in fragment-level entries that pair a semantic operator with
its syntactic realization. The semantics layer only owns the operator.

Equational simp lemmas (`affirm_eq_id`, `neg_apply`, `neg_neg`) make the
operators transparent to downstream reasoning.
-/

namespace Semantics.Polarity

universe u

/-- Affirmative polarity operator — identity on propositions
    (@cite{laka-1990}'s Σ). -/
def affirm (W : Type u) : (W → Prop) → (W → Prop) := id

/-- Negative polarity operator — pointwise propositional negation
    (@cite{laka-1990}'s NEG). -/
def neg (W : Type u) : (W → Prop) → (W → Prop) := λ p w => ¬ p w

@[simp] theorem affirm_eq_id (W : Type u) : affirm W = id := rfl

@[simp] theorem affirm_apply {W : Type u} (p : W → Prop) :
    affirm W p = p := rfl

@[simp] theorem neg_apply {W : Type u} (p : W → Prop) (w : W) :
    neg W p w ↔ ¬ p w := Iff.rfl

/-- `neg` is an involution (up to propositional extensionality). -/
theorem neg_neg {W : Type u} (p : W → Prop) (w : W) :
    neg W (neg W p) w ↔ p w := by
  unfold neg
  exact ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

end Semantics.Polarity
