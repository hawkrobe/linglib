import Linglib.Theories.Semantics.Dynamic.PLA.DeepTheorems

/-!
# Dekker (2012): Predicate Logic with Anaphora vs Bilateral Update Semantics
@cite{dekker-2012} @cite{krahmer-muskens-1995}

PLA (`Theories/Semantics/Dynamic/PLA/`) is the foundational system for
dynamic semantics with explicit pronoun indices. This study verifies
PLA's behavior on the canonical anaphora puzzles and contrasts it
with Bilateral Update Semantics (BUS, `Theories/Semantics/Dynamic/Bilateral/`),
which solves anaphora cases that PLA structurally cannot.

## The Core Difference

PLA has only positive updates (eliminative CCPs); BUS has both positive
and negative dimensions.

- In PLA: `¬φ` tests if `φ.update(s) ≠ ∅`, returns `s` or `∅`. Double
  negation preserves the *domain* of bound variables (syntactically the
  same) but not their *witnesses* (semantically lost).
- In BUS: `¬φ` swaps positive/negative, so `¬¬φ = φ` definitionally.
  Witnesses introduced by `∃` survive in the negative dimension and
  become available in cross-disjunct contexts.

This is the bilateral DNE strategy listed in
`Dynamic/Core/DynProp.lean`'s "three incompatible DNE solutions" table;
ICDRT (`Phenomena/Anaphora/Studies/Hofmann2025.lean §7`) is the third
strategy and dominates BUS on disagreement, modal subordination, and
three-way veridicality.

## What this file proves

§ 1 — PLA-side analysis of the bathroom sentence and double negation.
§ 2 — Architectural divergence summary; the BUS side is documented as
prose because BUS and PLA use different `Core` infrastructures that
cannot be co-imported.

-/

namespace Dekker2012

open Semantics.Dynamic.PLA

-- ════════════════════════════════════════════════════════════════
-- § 1. PLA-side facts: domain vs witness asymmetry
-- ════════════════════════════════════════════════════════════════

/-- PLA double negation: `¬¬φ` has the same *domain* as `φ`. The
syntactic presence of the existentially-bound variable is preserved
because `Formula.domain` is computed from the formula structure, not
the update behavior. -/
theorem pla_dne_syntactic (φ : Formula) :
    (∼(∼φ)).domain = φ.domain :=
  dne_domain_same φ

/-- PLA existential exports witnesses to the output info state.
Single existentials work fine; the failure mode is double negation. -/
theorem pla_existential_exports {E : Type*} [Nonempty E] (M : Model E)
    (x : VarIdx) (φ : Formula) (s : InfoState E) (p : Poss E)
    (hp : p ∈ (Formula.exists_ x φ).update M s) :
    ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 :=
  export_witness M x φ s p hp

/-- The PLA puzzle: `x` is in the *domain* of `¬¬∃x.φ` (syntactically
present, by `pla_dne_syntactic`) — but the update behavior of `¬¬`
discards the actual witnesses. The discourse referent looks bound
syntactically yet is unavailable for anaphora. -/
theorem pla_dne_has_domain {E : Type*} [Nonempty E] (x : VarIdx) (φ : Formula) :
    x ∈ (∼(∼(Formula.exists_ x φ))).domain := by
  simp only [Formula.domain]
  exact Finset.mem_insert_self x _

/-- Bathroom sentence in PLA: "Either there's no bathroom, or it's in
a funny place." The pronoun "it" (index 0) appears in the range
because the existential that would bind it sits under negation. -/
theorem bathroom_pla_has_unbound_pronoun :
    0 ∈ bathroomSentence.range :=
  bathroom_range_has_pronoun

/-- The bathroom sentence has nonempty *domain* (the existential is
syntactically present) — PLA can write the formula but cannot resolve
the pronoun against any introduced witness. -/
theorem bathroom_pla_has_domain :
    bathroomSentence.domain.Nonempty :=
  bathroom_domain_nonempty


-- ════════════════════════════════════════════════════════════════
-- § 2. PLA vs BUS: architectural divergence
-- ════════════════════════════════════════════════════════════════

/-! BUS lives in `Theories/Semantics/Dynamic/Bilateral/Basic.lean` with
the type

```
structure BilateralDen (W E : Type*) where
  positive : InfoState W E → InfoState W E
  negative : InfoState W E → InfoState W E
```

and negation as `def neg φ := { positive := φ.negative, negative := φ.positive }`.
The DNE law `neg (neg φ) = φ` then holds by `rfl`
(`BilateralDen.neg_neg` in `Bilateral/Basic.lean`).

PLA and BUS use different `InfoState` parametrizations, so a single
file cannot import both side-by-side. The BUS-side facts are stated
abstractly here and verified in their home file.

### Bathroom sentence in BUS

For `¬∃x.φ ∨ ψ`:

- `(¬∃x.φ).negative s = (∃x.φ).positive s` — the witness is in the
  negative dimension of the negated existential.
- BUS disjunction routes `ψ` through the negative dimension of the
  first disjunct: `disjPos2 φ ψ s := ψ.positive (φ.negative s)`.
- So `ψ` receives the existential's *positive* update, with `x` bound
  — the pronoun in "it's in a funny place" finds its referent.

This is why bathroom sentences work in BUS and fail in PLA: BUS routes
the witness through the swap, while PLA discards it via the eliminative
test.

### Summary

| Property              | PLA                  | BUS                            |
|-----------------------|----------------------|--------------------------------|
| Negation              | Test (`s` or `∅`)    | Swap (pos ↔ neg)              |
| `¬¬φ` semantics      | Returns `s`, not `s[φ]` | `= φ` definitionally        |
| `∃x` under negation  | Witness trapped      | Witness in negative dimension  |
| Bathroom sentence     | Pronoun unbound      | Pronoun bound via dimension swap |

The structural difference in negation is the key architectural choice:
PLA's eliminative test traps drefs under negation; BUS's structural
swap preserves them in the other dimension.

-/

end Dekker2012
