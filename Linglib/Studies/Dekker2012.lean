import Linglib.Semantics.Dynamic.PLA.Update

/-!
# Dekker (2012): Predicate Logic with Anaphora vs Bilateral Update Semantics
[dekker-2012] [dekker-1994] [krahmer-muskens-1995]

PLA (`Semantics/Dynamic/PLA/`, originating in [dekker-1994]) is the
foundational system for dynamic semantics with explicit pronoun indices.
This study verifies the formalized PLA's behavior on the canonical anaphora
puzzles and contrasts it with Bilateral Update Semantics (BUS,
`UpdateSemantics/Bilateral.lean` and `Studies/ElliottSudo2025.lean`), which solves
anaphora cases that PLA structurally cannot.

**Caveat on the formalization**: the PLA substrate as formalized is
*eliminative* — every update filters the input state
(`update_eliminative`), and existentials certify witness satisfiability in
their membership condition without storing the witness in the output
possibilities. Dekker's own PLA exports witnesses to output states;
anaphora resolution here goes through an explicit `Resolution` instead.
The theorems below are therefore facts about satisfiability and formula
structure (domain/range), not about witness export.

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
`Dynamic/Update.lean`'s "three incompatible DNE solutions" table;
ICDRT (`Studies/Hofmann2025.lean §7`) is the third
strategy and dominates BUS on disagreement, modal subordination, and
three-way veridicality.

## What this file proves

§ 1 — PLA-side analysis of the bathroom sentence and double negation.
§ 2 — Architectural divergence summary; the BUS side is documented as
prose because BUS and PLA use different `Core` infrastructures that
cannot be co-imported.

-/

namespace Dekker2012

open PLA
open DynamicSemantics.CCP

-- ════════════════════════════════════════════════════════════════
-- § 1. PLA-side facts: domain vs witness asymmetry
-- ════════════════════════════════════════════════════════════════

/-- PLA double negation: `¬¬φ` has the same *domain* as `φ`. The
syntactic presence of the existentially-bound variable is preserved
because `Formula.domain` is computed from the formula structure, not
the update behavior. -/
theorem pla_dne_syntactic (φ : Formula) :
    (∼(∼φ)).domain = φ.domain :=
  dne_syntactic φ

/-- Surviving an existential update certifies a witness: if `p` is in
`(∃x.φ).update M s`, some value for `x` satisfies `φ` at `p`.

Note what this does *not* say: `p` itself is unchanged (updates are
eliminative), so the witness is certified but not exported to the output
state — the formalized PLA's existential is a satisfiability test. -/
theorem pla_exists_certifies_witness {E : Type*} [Nonempty E] (M : Model E)
    (x : VarIdx) (φ : Formula) (s : InfoState E) (p : Poss E)
    (hp : p ∈ (Formula.exists_ x φ).update M s) :
    ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 := by
  simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat] at hp
  exact hp.2

/-- Surviving a sequenced update `∃x.φ` then `ψ` means surviving the
existential update *and* satisfying `ψ` — the possibility is filtered by
both conjuncts. Since the state is only filtered, this records
satisfiability of both conjuncts at `p`; it does not link `ψ`'s pronouns
to the existential's witness (that would require witness export, which
the eliminative formalization lacks). -/
theorem pla_seq_certifies_both {E : Type*} [Nonempty E] (M : Model E)
    (x : VarIdx) (φ ψ : Formula) (s : InfoState E) (p : Poss E)
    (hp : p ∈ (seq ((Formula.exists_ x φ).update M) (ψ.update M)) s) :
    p ∈ (Formula.exists_ x φ).update M s ∧ ψ.sat M p.1 p.2 := by
  simp only [DynamicSemantics.CCP.seq] at hp
  constructor
  · exact update_eliminative M ψ _ hp
  · simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq] at hp
    exact hp.2

/-- Combining the two: a possibility surviving `∃x.φ` then `ψ` certifies a
witness for `φ` and satisfies `ψ`. -/
theorem pla_seq_certifies_witness {E : Type*} [Nonempty E] (M : Model E)
    (x : VarIdx) (φ ψ : Formula) (s : InfoState E) (p : Poss E)
    (hp : p ∈ (seq ((Formula.exists_ x φ).update M) (ψ.update M)) s) :
    (∃ e : E, φ.sat M (p.1[x ↦ e]) p.2) ∧ ψ.sat M p.1 p.2 :=
  ⟨pla_exists_certifies_witness M x φ s p (pla_seq_certifies_both M x φ ψ s p hp).1,
   (pla_seq_certifies_both M x φ ψ s p hp).2⟩

/-- The PLA puzzle: `x` is in the *domain* of `¬¬∃x.φ` (syntactically
present, by `pla_dne_syntactic`) — but the update behavior of `¬¬`
discards the actual witnesses. The discourse referent looks bound
syntactically yet is unavailable for anaphora. -/
theorem pla_dne_has_domain {E : Type*} [Nonempty E] (x : VarIdx) (φ : Formula) :
    x ∈ (∼(∼(Formula.exists_ x φ))).domain := by
  simp only [Formula.domain]
  exact Finset.mem_insert_self x _

/-- Bathroom sentence (Partee): "Either there's no bathroom, or it's
upstairs" — `¬∃x.Bathroom(x) ∨ Upstairs(p₀)`. -/
def bathroomSentence : Formula :=
  Formula.disj
    (∼(Formula.exists_ 0 (Formula.atom "Bathroom" [.var 0])))
    (Formula.atom "Upstairs" [.pron 0])

/-- Bathroom sentence in PLA: the pronoun "it" (index 0) appears in the
range because the existential that would bind it sits under negation. -/
theorem bathroom_pla_has_unbound_pronoun :
    0 ∈ bathroomSentence.range := by
  simp only [bathroomSentence, Formula.disj, Formula.range,
             termsPronouns]
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.biUnion_insert,
             Finset.biUnion_empty, Finset.union_empty, Term.pronouns]
  simp only [Finset.mem_union, Finset.mem_singleton]
  right; trivial

/-- The bathroom sentence has nonempty *domain* (the existential is
syntactically present) — PLA can write the formula but cannot resolve
the pronoun against any introduced witness. -/
theorem bathroom_pla_has_domain :
    bathroomSentence.domain.Nonempty := by
  simp only [bathroomSentence, Formula.disj, Formula.domain]
  use 0
  simp only [Finset.mem_union]
  left
  exact Finset.mem_insert_self 0 _


-- ════════════════════════════════════════════════════════════════
-- § 2. PLA vs BUS: architectural divergence
-- ════════════════════════════════════════════════════════════════

/-! BUS's bilateral substrate lives in `Semantics/Dynamic/UpdateSemantics/Bilateral.lean`
with the type

```
structure BilateralDen (W V E : Type*) where
  positive negative :
    Set (Possibility W V (Part E)) → Set (Possibility W V (Part E))
```

and negation as `def neg φ := { positive := φ.negative, negative := φ.positive }`.
The DNE law `neg (neg φ) = φ` then holds by `rfl`
(`BilateralDen.neg_neg` in `UpdateSemantics/Bilateral.lean`).

PLA states (assignment-witness pairs) and BUS states (`Part`-partial
possibility sets) are different carriers, so a single file cannot state
both side-by-side. The BUS-side facts are stated
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
