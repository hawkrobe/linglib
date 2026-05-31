import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.Atoms

/-!
# Anchor formulas as atoms: Lemma 6 of @cite{demey-smessaert-2018}

For a finite generator set `s : Finset α` of a Boolean algebra, an *anchor
formula* `anchorBA s σ` is the meet of one literal `±x` per generator `x ∈ s`,
with polarities `σ : s → Bool`. Lemma 6 (`anchorBA_le_or_le_compl_mem_closure`)
states that every element of the Boolean closure of `s` is *anchor-decided*: each
anchor entails it or its complement. This drives the bitstring representation in
`Bitstring.lean`.

## Main declarations

* `anchorBA` — the anchor formula of a polarity assignment over a `Finset`.
* `anchorBA_le_or_le_compl_mem_closure` — Lemma 6 (anchor-decidedness).
* `anchorBA_le_or_le_compl_exclusive` — its exclusive form for consistent anchors.
-/

namespace Aristotelian

variable {α : Type*} [BooleanAlgebra α]

/-! ### Literals and anchor formulas -/

/-- A literal over a generator `φ`: `φ` itself (`b = true`) or `φᶜ` (`b = false`). -/
def lit (φ : α) (b : Bool) : α := if b then φ else φᶜ

@[simp] lemma lit_true (φ : α) : lit φ true = φ := rfl
@[simp] lemma lit_false (φ : α) : lit φ false = φᶜ := rfl

/-- The anchor formula for `σ : s → Bool`: the meet of `lit x (σ x)` over `x ∈ s`. -/
def anchorBA (s : Finset α) (σ : s → Bool) : α :=
  s.attach.inf (fun x => lit x.val (σ x))

/-- The anchor lies below each of its constituent literals. -/
lemma anchorBA_le_lit (s : Finset α) (σ : s → Bool) (x : s) :
    anchorBA s σ ≤ lit x.val (σ x) :=
  Finset.inf_le (s.mem_attach x)

/-- If `σ x = true` then `anchorBA s σ ≤ x`. -/
lemma anchorBA_le_of_pos {s : Finset α} {σ : s → Bool} {x : s} (h : σ x = true) :
    anchorBA s σ ≤ x.val := by
  have := anchorBA_le_lit s σ x
  rwa [lit, if_pos h] at this

/-- If `σ x = false` then `anchorBA s σ ≤ xᶜ`. -/
lemma anchorBA_le_compl_of_neg {s : Finset α} {σ : s → Bool} {x : s}
    (h : σ x = false) : anchorBA s σ ≤ x.valᶜ := by
  have hLit := anchorBA_le_lit s σ x
  rw [lit, h] at hLit
  exact hLit

/-! ### Lemma 6 — anchor-decidedness for closure elements -/

/-- Lemma 6 (@cite{demey-smessaert-2018}): every element of the Boolean closure of
a finite generator set is anchor-decided — every anchor entails it or its
complement. Holds unconditionally (if the anchor is `⊥`, both disjuncts hold);
`Bitstring.lean` applies it to nonzero anchors for the exclusive form. -/
theorem anchorBA_le_or_le_compl_mem_closure
    {s : Finset α} (σ : s → Bool) {ψ : α}
    (hψ : ψ ∈ BooleanSubalgebra.closure (s : Set α)) :
    anchorBA s σ ≤ ψ ∨ anchorBA s σ ≤ ψᶜ := by
  induction hψ using BooleanSubalgebra.closure_bot_sup_induction with
  | mem ψ' hψ' =>
    by_cases h : σ ⟨ψ', hψ'⟩ = true
    · left
      have := anchorBA_le_of_pos (s := s) (σ := σ) (x := ⟨ψ', hψ'⟩) h
      simpa using this
    · right
      have hf : σ ⟨ψ', hψ'⟩ = false := Bool.eq_false_iff.mpr h
      have := anchorBA_le_compl_of_neg (s := s) (σ := σ) (x := ⟨ψ', hψ'⟩) hf
      simpa using this
  | bot =>
    right
    simp
  | sup x _ y _ ihx ihy =>
    rcases ihx with hx | hx
    · left; exact hx.trans le_sup_left
    rcases ihy with hy | hy
    · left; exact hy.trans le_sup_right
    · right; rw [compl_sup]; exact le_inf hx hy
  | compl x _ ih =>
    rcases ih with h | h
    · right; rw [compl_compl]; exact h
    · left; exact h

/-- The exclusive form: a consistent anchor satisfies exactly one disjunct of
Lemma 6. -/
theorem anchorBA_le_or_le_compl_exclusive {s : Finset α} (σ : s → Bool) {ψ : α}
    (hψ : ψ ∈ BooleanSubalgebra.closure (s : Set α))
    (hCons : anchorBA s σ ≠ ⊥) :
    (anchorBA s σ ≤ ψ ∧ ¬ anchorBA s σ ≤ ψᶜ) ∨
    (¬ anchorBA s σ ≤ ψ ∧ anchorBA s σ ≤ ψᶜ) := by
  rcases anchorBA_le_or_le_compl_mem_closure σ hψ with hL | hR
  · left
    refine ⟨hL, fun hR => hCons ?_⟩
    have : anchorBA s σ ≤ ψ ⊓ ψᶜ := le_inf hL hR
    rwa [inf_compl_eq_bot, le_bot_iff] at this
  · right
    refine ⟨fun hL => hCons ?_, hR⟩
    have : anchorBA s σ ≤ ψ ⊓ ψᶜ := le_inf hL hR
    rwa [inf_compl_eq_bot, le_bot_iff] at this

end Aristotelian
