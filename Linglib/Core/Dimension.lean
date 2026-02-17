import Linglib.Core.Mereology
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# Mereological Dimensions

Both `IsSumHom` (join-preserving maps: τ, θ) and `ExtMeasure` (additive measures:
μ, dur) provide `StrictMono`, which is the exact algebraic condition for QUA pullback.
This file makes that explicit: QUA and CUM are contravariant functors on the category
of mereological domains with strictly monotone (resp. join-preserving) maps.

## Categorical interpretation

- **QUA : Mereo^op → Prop.** An object of Mereo is a type `α` with `PartialOrder`.
  A morphism `d : α → β` is `StrictMono`. QUA acts contravariantly:
  if `QUA P` in the codomain, then `QUA (P ∘ d)` in the domain.

- **CUM : JoinMereo^op → Prop.** An object of JoinMereo is a type `α` with
  `SemilatticeSup`. A morphism `d : α → β` is `IsSumHom`. CUM acts contravariantly:
  if `CUM P` in the codomain, then `CUM (P ∘ d)` in the domain.

The key insight: `ExtMeasure` provides `StrictMono` (via positivity + additivity
in CEM), and `IsSumHom` provides `StrictMono` (via monotonicity). So both
`extMeasure_qua` and the functional version of `qua_propagation` are special
cases of `qua_pullback`.

## The GRAD square (lax commutativity)

The Krifka (1989/1998) linking theory involves two dimension chains:

```
Events →θ Entities →μ ℚ       (object dimension)
Events →τ Times    →dur ℚ     (temporal dimension)
```

These form a square that commutes *laxly*: the two paths Events → ℚ need not
agree pointwise, but they are related by a proportionality constant (the "rate"
of gradual change). This is captured by `MeasureProportional.rate` in
`Events/Krifka1998.lean`. The GRAD theorem then says that the object-measure
ordering and the event-measure ordering agree — a consequence of this lax
commutativity.

## References

- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics.
- Krifka, M. (1998). The origins of telicity. In S. Rothstein (ed.),
  *Events and Grammar*, 197–235. Kluwer.
- Champollion, L. (2017). *Parts of a Whole*. OUP.
-/

namespace Mereology

-- ════════════════════════════════════════════════════
-- § 1. QUA Pullback (the foundation)
-- ════════════════════════════════════════════════════

/-- QUA pullback along strictly monotone maps: the functoriality proof for
    QUA : Mereo^op → Prop.

    If `d : α → β` is strictly monotone and `P` is quantized over `β`,
    then `P ∘ d` is quantized over `α`. This is the general theorem
    subsuming both `extMeasure_qua` (where d = μ) and the functional
    version of `qua_propagation` (where d = θ as a function).

    The relational `qua_propagation` in Krifka1998.lean (using MSO + UP
    on a binary relation θ) is genuinely different — it operates on
    relations, not functions. Both coexist: the functional case is a
    special case of this theorem. -/
theorem qua_pullback {α β : Type*} [PartialOrder α] [PartialOrder β]
    {d : α → β} (hd : StrictMono d)
    {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ d) :=
  fun _x _y hx hlt hy => hP _ _ hx (hd hlt) hy

-- ════════════════════════════════════════════════════
-- § 2. CUM Pullback
-- ════════════════════════════════════════════════════

/-- CUM pullback along sum homomorphisms: the functoriality proof for
    CUM : JoinMereo^op → Prop.

    If `d : α → β` is a sum homomorphism and `P` is cumulative over `β`,
    then `P ∘ d` is cumulative over `α`. Wrapper for `IsSumHom.cum_preimage`,
    documented here as the CUM functor on JoinMereo^op. -/
theorem cum_pullback {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    {d : α → β} (hd : IsSumHom d)
    {P : β → Prop} (hP : CUM P) :
    CUM (P ∘ d) :=
  hd.cum_preimage hP

-- ════════════════════════════════════════════════════
-- § 3. ExtMeasure → StrictMono Bridge
-- ════════════════════════════════════════════════════

/-- Extract `StrictMono` from an extensive measure.
    `ExtMeasure.strict_mono` axiomatizes that proper parts have strictly
    smaller measure; this is exactly `StrictMono μ`. -/
theorem extMeasure_strictMono {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (hμ : ExtMeasure α μ) : StrictMono μ :=
  fun _a _b hab => hμ.strict_mono _ _ hab

-- ════════════════════════════════════════════════════
-- § 4. Subsumption: extMeasure_qua as corollary
-- ════════════════════════════════════════════════════

/-- Singleton predicates are quantized on any partial order.
    `{x | x = n}` is QUA because `y < n → y ≠ n` (by irreflexivity
    of `<` after substitution).

    This generalizes `atom_qua` from Core/Mereology.lean, which required
    `Atom x`. The Atom hypothesis is unnecessary for singletons. -/
theorem singleton_qua {α : Type*} [PartialOrder α]
    (n : α) : QUA (· = n) := by
  intro x y hx hlt hy
  subst hx; subst hy
  exact absurd hlt (lt_irrefl _)

/-- `extMeasure_qua` derived from `qua_pullback` + `singleton_qua`.
    This shows that the `extMeasure_qua` theorem in Core/Mereology.lean
    is a special case of QUA pullback, not an independent theorem:

      {x | μ(x) = n} = (· = n) ∘ μ

    and QUA pulls back along the StrictMono map μ.

    Note: unlike the original `extMeasure_qua`, this derivation does not
    require `0 < n`. The positivity hypothesis was an artifact of the
    direct proof; the pullback route is strictly more general.

    The original `extMeasure_qua` is preserved in Mereology.lean for
    backward compatibility. -/
theorem extMeasure_qua' {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] (n : ℚ) :
    QUA (fun x => μ x = n) :=
  qua_pullback (extMeasure_strictMono hμ) (singleton_qua n)

-- ════════════════════════════════════════════════════
-- § 5. Composition
-- ════════════════════════════════════════════════════

/-- QUA pullback composes: functoriality for QUA : Mereo^op → Prop.
    If `d₁ : α → β` and `d₂ : β → γ` are both StrictMono, then
    `QUA P → QUA (P ∘ d₂ ∘ d₁)`.

    Equivalently: `StrictMono.comp hd₂ hd₁` gives `StrictMono (d₂ ∘ d₁)`,
    and a single `qua_pullback` suffices. The nested formulation here
    makes the functorial structure explicit.

    This captures the Krifka dimension chain:
      Events →θ Entities →μ ℚ
    where θ extracts the incremental theme and μ measures it. The
    composition `μ ∘ θ` is StrictMono, so QUA predicates on ℚ
    (measure phrases like "two kilograms") pull back to QUA predicates
    on Events (telic VPs like "eat two kilograms of flour"). -/
theorem qua_pullback_comp {α β γ : Type*}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {d₁ : α → β} {d₂ : β → γ}
    (hd₁ : StrictMono d₁) (hd₂ : StrictMono d₂)
    {P : γ → Prop} (hP : QUA P) :
    QUA (P ∘ d₂ ∘ d₁) :=
  qua_pullback hd₁ (qua_pullback hd₂ hP)

-- ════════════════════════════════════════════════════
-- § 6. IsSumHom + Injective → StrictMono
-- ════════════════════════════════════════════════════

/-- A sum homomorphism that is injective is strictly monotone.

    `IsSumHom.monotone` gives `Monotone f` (x ≤ y → f(x) ≤ f(y)).
    Adding injectivity strengthens this: x < y means x ≤ y ∧ x ≠ y,
    so f(x) ≤ f(y) ∧ f(x) ≠ f(y), i.e., f(x) < f(y).

    This bridges `IsSumHom` (the CUM pullback morphism class) to
    `StrictMono` (the QUA pullback morphism class): an injective sum
    homomorphism supports both CUM and QUA pullback.

    Linguistically: a sum-homomorphic thematic role that is also
    injective (unique participant assignment, Krifka's UE/UO
    conditions) supports telicity transfer via `qua_pullback`. -/
theorem IsSumHom.strictMono_of_injective {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f) (hinj : Function.Injective f) :
    StrictMono f := by
  intro x y hlt
  exact lt_of_le_of_ne (hf.monotone hlt.le) (fun h => hlt.ne (hinj h))

-- ════════════════════════════════════════════════════
-- § 7. Functional QUA propagation as pullback instance
-- ════════════════════════════════════════════════════

/-- QUA propagation through an injective sum homomorphism.

    When the relational θ in Krifka's `qua_propagation` (Krifka1998.lean)
    is actually a function `f` with `IsSumHom` + injectivity, the
    relational proof (needing UP + MSO) reduces to functional
    `qua_pullback` via `StrictMono`.

    This is the functional special case of Krifka (1998) §3.3:
    SINC(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ), where θ is a function
    rather than a relation, and SINC reduces to IsSumHom + Injective.

    See also: `qua_propagation` in Krifka1998.lean for the relational
    version using UP + MSO + UO. -/
theorem qua_of_injective_sumHom {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f) (hinj : Function.Injective f)
    {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ f) :=
  qua_pullback (hf.strictMono_of_injective hinj) hP

-- ════════════════════════════════════════════════════
-- § 8. CUM + QUA dimension interaction
-- ════════════════════════════════════════════════════

/-- The pullback of P through an injective sum homomorphism inherits
    the CUM/QUA incompatibility from `cum_qua_disjoint`.

    If P ∘ f has two distinct witnesses x ≠ y, then P ∘ f cannot be
    both CUM and QUA. This is `cum_qua_disjoint` instantiated to the
    pullback predicate, stated explicitly to document that dimension
    maps preserve the mereological partition.

    Linguistically: if a verbal predicate V is formed by pulling back
    a nominal predicate P through an injective incremental-theme
    function θ, then V inherits the CUM/QUA incompatibility — V
    cannot be simultaneously cumulative and quantized (given two
    distinct events satisfying V). -/
theorem cum_qua_dimension_disjoint {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} {P : β → Prop}
    {x y : α} (hx : (P ∘ f) x) (hy : (P ∘ f) y) (hne : x ≠ y) :
    ¬ (CUM (P ∘ f) ∧ QUA (P ∘ f)) :=
  cum_qua_disjoint ⟨x, y, hx, hy, hne⟩

end Mereology
