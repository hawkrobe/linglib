import Mathlib.Data.Set.Basic

/-!
# Alternative sources

A common abstraction over the many "alternative-generation" mechanisms
in formal pragmatics. Different theories generate different competitor
sets for the same expression:

- [katzir-2007] structural alternatives — substitution/deletion/
  contraction over a parse tree, using items in the lexicon ∪ subtrees
- [buccola-kriz-chemla-2018] conceptual alternatives — including
  competitors not realizable by linguistic material
- [sauerland-alexiadou-2020] Meaning First — alternatives drawn
  at the thought-structure level, prior to compression
- [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]
  indirect alternatives — pronounceable expressions equivalent in
  meaning to an unpronounceable Katzir alternative

All of these are functions `S → Set S`. We give that function type a
name so that pragmatic competition operators (`violatesMP`,
`violatesMaximize`, `violatesMCIs`, in `Alternatives.Competition`) can be
parameterized over the alternative source rather than hardcoding any
single one.

This follows mathlib's pattern of naming a function-shaped abstraction
under a structural alias (cf. `Set α := α → Prop`, `Rel α β := α → β →
Prop`) rather than as a typeclass — there is no canonical alternative
source per carrier type, since different theories supply different
sources for the same parse. The alias also inherits the pointwise
`CompleteLattice` on `S → Set S` for free, so source subsumption is just
`≤` (pointwise `⊆`) and source union is `⊔`.

## Main definitions

* `Source` — the alternative-source abbreviation `S → Set S`.
* `indirectFrom` — the indirect-alternative combinator: pronounceable
  expressions meaning-equivalent to an *unpronounceable* alternative of
  the original, at most as complex
  ([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]).

## Main results

* `mem_indirectFrom` — membership characterization of `indirectFrom`.
* `size_le_of_mem` — indirect alternatives are at most as complex as the
  original.
* `indirectFrom_eq_empty_of_forall_pron` — `indirectFrom` is empty when
  the base has no unpronounceable witness.
-/

namespace Alternatives

/-- An alternative source assigns to each expression a set of competitors.

Theory-specific base sources live elsewhere:
`Alternatives.Structural.katzirSource` (Katzir 2007),
`Alternatives.HornScale.toSource` (Horn scales), etc. The combinator
`indirectFrom` below transforms any base source. -/
abbrev Source (S : Type*) := S → Set S

variable {S M : Type*}

/-- The indirect-alternative combinator (eq. 43,
[jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]).

`indirectFrom base pron meaning size s` is the set of *pronounceable*
expressions `s'` such that `size s' ≤ size s` and there is some
*unpronounceable* `sₓ ∈ base s` with `meaning s' = meaning sₓ`.

Parameters:
- `base`: the underlying alternative source (typically Katzir).
- `pron`: the pronounceability predicate; an expression is silent
  when `¬ pron s` holds.
- `meaning`: the semantic interpretation function.
- `size`: complexity measure (e.g. `Tree.size`).

Both the surrogate `s'` (the indirect alternative `I`) and the witness
`sₓ` are constrained by `pron`: `I` must be pronounceable while `sₓ` —
the silent structural alternative it stands in for — must not be, per
the paper's definition. -/
def indirectFrom (base : Source S) (pron : S → Prop)
    (meaning : S → M) (size : S → Nat) :
    Source S :=
  fun s =>
    {s' | pron s' ∧ size s' ≤ size s ∧ ∃ sₓ ∈ base s, ¬ pron sₓ ∧ meaning s' = meaning sₓ}

variable {base : Source S} {pron : S → Prop}
  {meaning : S → M} {size : S → Nat} {s' s : S}

/-- Membership in the indirect-alternative source. -/
@[simp] theorem mem_indirectFrom :
    s' ∈ indirectFrom base pron meaning size s ↔
      pron s' ∧ size s' ≤ size s ∧ ∃ sₓ ∈ base s, ¬ pron sₓ ∧ meaning s' = meaning sₓ :=
  Iff.rfl

/-- Indirect alternatives are at most as complex as the original. -/
theorem size_le_of_mem (h : s' ∈ indirectFrom base pron meaning size s) :
    size s' ≤ size s := h.2.1

/-- The indirect-alternative set is empty when the base source contains
no unpronounceable witnesses — the genuine refinement: an indirect
alternative requires a *silent* witness in the base. -/
theorem indirectFrom_eq_empty_of_forall_pron (allPron : ∀ x ∈ base s, pron x) :
    indirectFrom base pron meaning size s = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨_, _, sₓ, hMem, hUnpron, _⟩
  exact hUnpron (allPron sₓ hMem)

end Alternatives
