import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.Atoms

/-!
# Anchor formulas in a Boolean algebra: Lemma 6 of @cite{demey-smessaert-2018}

For a finite generator set `s : Finset α` of a Boolean algebra `α`, an
*anchor formula* is a meet of literals over `s` — one literal `lit φ b`
per generator, with polarity selected by an assignment `σ : s → Bool`:

  anchorBA s σ := ⨅ x ∈ s, (if σ x then x else xᶜ)

The central technical lemma (Demey-Smessaert §3, Lemma 6) is *anchor-
decidedness*: for every element `ψ` of the Boolean closure of `s`, every
anchor formula either entails `ψ` or entails `¬ψ`. Equivalently, the anchor
formulas partition the closure's "truth space" into mutually-deciding cells.

Lemma 6 is the engine driving the bitstring representation in `Bitstring.lean`:
the i-th bit of `bitstringOf φ ψ` is well-defined precisely because the i-th
anchor decides ψ. Closing Theorems 1 and 2 from `Bitstring.lean` reduces to
this lemma plus mathlib's existing infrastructure.

## What this file uses from mathlib

- `BooleanSubalgebra` (Yaël Dillies, 2024) for `closure`-based reasoning
- `closure_bot_sup_induction` for the inductive proof of Lemma 6
- Standard `BooleanAlgebra` API (`compl_sup`, `compl_compl`, `le_inf`, ...)

## Generality

The lemma is stated for an arbitrary `[BooleanAlgebra α]`. Specializations to
`α = W → Bool` (the syllogistic case) are immediate.
-/

namespace Core.Opposition

variable {α : Type*} [BooleanAlgebra α]

-- ============================================================================
-- §1. Literals and anchor formulas
-- ============================================================================

/-- A *literal* over a generator `φ : α`: either `φ` itself (positive polarity)
    or its complement `φᶜ` (negative polarity). -/
def lit (φ : α) (b : Bool) : α := if b then φ else φᶜ

@[simp] lemma lit_true (φ : α) : lit φ true = φ := rfl
@[simp] lemma lit_false (φ : α) : lit φ false = φᶜ := rfl

/-- The *anchor formula* for a polarity assignment `σ : s → Bool` over a
    finite generator set `s : Finset α`: the meet of `lit x (σ x)` over all
    `x ∈ s`. This is a generic Boolean-algebra version of the Demey-Smessaert
    anchor (Definition 5). -/
def anchorBA (s : Finset α) (σ : s → Bool) : α :=
  s.attach.inf (fun x => lit x.val (σ x))

/-- The anchor lies below each of its constituent literals. -/
lemma anchorBA_le_lit (s : Finset α) (σ : s → Bool) (x : s) :
    anchorBA s σ ≤ lit x.val (σ x) :=
  Finset.inf_le (s.mem_attach x)

/-- A specific positive-polarity case: if `σ x = true`, then `anchorBA s σ ≤ x`. -/
lemma anchorBA_le_of_pos {s : Finset α} {σ : s → Bool} {x : s} (h : σ x = true) :
    anchorBA s σ ≤ x.val := by
  have := anchorBA_le_lit s σ x
  rwa [lit, if_pos h] at this

/-- A specific negative-polarity case: if `σ x = false`, then `anchorBA s σ ≤ xᶜ`. -/
lemma anchorBA_le_compl_of_neg {s : Finset α} {σ : s → Bool} {x : s}
    (h : σ x = false) : anchorBA s σ ≤ x.valᶜ := by
  have hLit := anchorBA_le_lit s σ x
  rw [lit, h] at hLit
  exact hLit

-- ============================================================================
-- §2. Lemma 6 — anchor-decidedness for closure elements
-- ============================================================================

/-- **Lemma 6 (Demey & Smessaert 2018)**: every element of the Boolean closure
    of a finite generator set is *anchor-decided* — every anchor formula either
    entails it or entails its complement.

    This holds **unconditionally** (no consistency hypothesis on the anchor):
    if the anchor is `⊥`, both disjuncts hold trivially. The bitstring
    semantics in `Bitstring.lean` uses Lemma 6 with the anchor known to be
    nonzero (i.e., σ in the partition), giving the *exclusive* decidedness
    that makes each bit well-defined.

    Proof: induction on closure membership via `closure_bot_sup_induction`.
    - `mem`: anchor includes `lit x (σ x)` as a meet; sign of `σ x` decides.
    - `bot`: `anchor ≤ ⊥ᶜ = ⊤` trivially.
    - `sup`: case on which side of the disjunction the anchor sits below.
    - `compl`: flip the disjunction (`compl_compl`). -/
theorem anchorBA_le_or_le_compl_mem_closure
    {s : Finset α} (σ : s → Bool) {ψ : α}
    (hψ : ψ ∈ BooleanSubalgebra.closure (s : Set α)) :
    anchorBA s σ ≤ ψ ∨ anchorBA s σ ≤ ψᶜ := by
  induction hψ using BooleanSubalgebra.closure_bot_sup_induction with
  | mem ψ' hψ' =>
    -- ψ' ∈ s; the anchor includes lit ⟨ψ', hψ'⟩ (σ ⟨ψ', hψ'⟩) as a meet
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

/-- The *exclusive* form: for a consistent anchor, exactly one disjunct of
    Lemma 6 holds. (If both held, anchor would be below `ψ ⊓ ψᶜ = ⊥`.) -/
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

end Core.Opposition
