import Mathlib.Logic.Function.Basic

/-!
# Classical bilateral satisfaction — `SatDuality`

[cobreros-etal-2012] [ripley-2012]

The **classical** bilateral pattern: a satisfaction relation
`sat : Model → Mode → Formula → Prop` parameterised by `Mode`, with a
negation operation on formulas and a dual operation on modes such that
negation flips satisfaction across mode-duality.

```
M, m ⊨ ¬φ  ↔  ¬(M, dual m ⊨ φ)
```

The Mode parameter generalises:
- **Classical bivalent**: `Mode := Bool`, `dual := not`
- **TCS strict-tolerant** (`[cobreros-etal-2012]`): `Mode := {strict, tolerant}`,
  `dual` swaps them
- **LP / RM3**: `Mode := {true, false, both}`, `dual` swaps the first two

In all cases, negation IS propositional negation (modulo mode duality),
unlike the paraconsistent bilateral pattern (`Bilateral.Defs.IsBilateral`)
where negation merely swaps two interpretations without committing them
to be propositional negations of each other.

## Sibling abstraction

`Core.Logic.Bilateral.IsBilateral` (in `Bilateral.lean`) is the
**paraconsistent** sibling — same shape (negation relates two
interpretations) but no commitment to classical-style negation.

| Pattern | Negation behavior | Consumers |
|---|---|---|
| `IsBilateral` (paraconsistent) | swaps positive/negative | BSML, QBSML, BUS, ICDRT, Truthmaker |
| `SatDuality` (classical, mode-parametric) | `sat (neg φ) ↔ ¬sat (dual m) φ` | TCS, LP, RM3 |

## Provenance

Extracted from `Core/Logic/Consequence.lean` in 0.230.654 to surface
the bilateral-substrate joint. The `consequence_dual` theorem (Cobreros
Lemma 6) stays with the Consequence machinery in `Consequence.lean` and
imports this file.
-/

namespace Core.Logic.Bilateral

variable {Model Formula Mode : Type*}

/-- Satisfaction duality: a negation operation on formulas and a
    dual operation on modes such that:
    - `dual` is an involution (d(d(m)) = m)
    - `neg` is an involution (¬¬φ = φ)
    - Negation swaps modes: `M ⊨ᵐ ¬φ ↔ M ⊭^{d(m)} φ`

    In TCS, d(t) = s, d(s) = t, d(c) = c, and negation is formula
    negation. -/
structure SatDuality (sat : Model → Mode → Formula → Prop)
    (neg : Formula → Formula) (dual : Mode → Mode) : Prop where
  dual_invol : ∀ m : Mode, dual (dual m) = m
  neg_invol : ∀ φ : Formula, neg (neg φ) = φ
  neg_swap : ∀ (M : Model) (m : Mode) (φ : Formula),
    sat M m (neg φ) ↔ ¬sat M (dual m) φ

end Core.Logic.Bilateral
