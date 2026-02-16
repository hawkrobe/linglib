/-
# PLA ↔ BUS Comparison

Comparison between Predicate Logic with Anaphora (PLA) and
Bilateral Update Semantics (BUS), showing:

1. DNE gap: where PLA fails (DNE for anaphora), BUS succeeds
2. Bathroom bridge: the sentence that breaks PLA works in BUS
3. Structural difference: PLA negation = test, BUS negation = swap

## The Core Difference

PLA has only positive updates (eliminative CCPs).
BUS has both positive and negative dimensions.

In PLA: ¬φ tests if φ.update(s) ≠ ∅, returns s or ∅
In BUS: ¬φ swaps positive/negative, so ¬¬φ = φ definitionally
-/

-- Note: PLA and BUS use different Core infrastructure that conflicts.
-- We import PLA (the "problem" side) and state BUS facts abstractly.
import Linglib.Theories.Semantics.Dynamic.Systems.PLA.DeepTheorems

namespace DynamicSemantics.Comparisons

open DynamicSemantics.PLA


/--
In PLA, ¬¬φ has the same domain as φ syntactically,
but doesn't export witnesses semantically.
-/
theorem pla_dne_syntactic (φ : Formula) :
    (∼(∼φ)).domain = φ.domain :=
  dne_domain_same φ

/--
PLA existential introduces witnesses that survive in the output.
-/
theorem pla_existential_exports {E : Type*} [Nonempty E] (M : Model E)
    (x : VarIdx) (φ : Formula) (s : InfoState E) (p : Poss E)
    (hp : p ∈ (Formula.exists_ x φ).update M s) :
    ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 :=
  export_witness M x φ s p hp

/--
The problem: x is in the domain of ¬¬∃x.φ (syntactically present),
but the update doesn't recover witnesses.
-/
theorem pla_dne_has_domain {E : Type*} [Nonempty E] (x : VarIdx) (φ : Formula) :
    x ∈ (∼(∼(Formula.exists_ x φ))).domain := by
  simp only [Formula.domain]
  exact Finset.mem_insert_self x _


/-!
## BUS Structure (from Core.Bilateral)

In BUS, a denotation is a pair of update functions:
```
structure BilateralDen (W E : Type*) where
  positive : InfoState W E → InfoState W E
  negative : InfoState W E → InfoState W E
```

Negation swaps the dimensions:
```
def neg (φ : BilateralDen W E) : BilateralDen W E :=
  { positive := φ.negative, negative := φ.positive }
```

This gives DNE definitionally: `neg (neg φ) = φ` by `rfl`.

See `Linglib.Theories.Semantics.Dynamic.Core.Bilateral` for the full development.
-/

-- BUS DNE principle: in bilateral semantics, ¬¬φ = φ definitionally.
-- Negation swaps positive/negative dimensions, so swapping twice gives identity.
-- Proved as `BilateralDen.neg_neg` in Core.Bilateral (cannot import here due to
-- conflicting PLA/BUS infrastructure; stated abstractly as documentation).


/--
PLA problem: the bathroom sentence has an unbound pronoun.

"Either there's no bathroom, or it's in a funny place."
The pronoun "it" (index 0) appears in the range but the existential
that would bind it is under negation.
-/
theorem bathroom_pla_has_unbound_pronoun :
    0 ∈ bathroomSentence.range :=
  bathroom_range_has_pronoun

/--
PLA problem: the domain is nonempty (existential is syntactically present).
-/
theorem bathroom_pla_has_domain :
    bathroomSentence.domain.Nonempty :=
  bathroom_domain_nonempty

/-!
## BUS Solution (from BUS.FreeChoice)

In BUS disjunction with modal semantics, the second disjunct receives
the negative dimension of the first:

```
def disjPos2 (φ ψ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  ψ.positive (φ.negative s)
```

For ¬∃x.φ ∨ ψ:
- (¬∃x.φ).negative s = (∃x.φ).positive s
- So ψ receives the existential's positive update, with x bound!

This is why bathroom sentences work in BUS: the pronoun in
"it's in a funny place" gets bound because ∃x.bathroom is
available in the negative dimension of ¬∃x.bathroom.

See `Linglib.Theories.Semantics.Dynamic.BUS.FreeChoice` for the full derivation.
-/


/-!
## Summary: PLA vs BUS

| Property | PLA | BUS |
|----------|-----|-----|
| Negation | Test (s or ∅) | Swap (pos ↔ neg) |
| ¬¬φ | ≠ φ (returns s) | = φ (definitional) |
| ∃x under ¬ | Witness trapped | Witness in neg dim |
| Bathroom | Unbound pronoun | Bound via swap |

### PLA Negation (Test)
```
s[¬φ] = s   if s[φ] = ∅
      = ∅   otherwise
```
This is why ¬¬φ ≠ φ: double negation returns s, not s[φ].

### BUS Negation (Swap)
```
s[¬φ]⁺ = s[φ]⁻
s[¬φ]⁻ = s[φ]⁺
```
Swapping twice gives identity, so ¬¬φ = φ.

The structural difference in negation is the key:
- PLA traps drefs under negation (eliminative test)
- BUS preserves them in the other dimension (structural swap)
-/

end DynamicSemantics.Comparisons
