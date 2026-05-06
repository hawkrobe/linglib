/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Tier
import Linglib.Core.Computability.Subregular.StrictlyPiecewise
import Linglib.Core.Computability.Subregular.PiecewiseTestable
import Linglib.Core.Computability.Subregular.Definite

/-!
# Multitier Extensions of Subregular Classes

Generic Boolean closure of tier-projected language families
@cite{lambert-2022} @cite{lambert-2026}. The construction proceeds in
two stages:

1. **Tier-projected family** `IsTierBased 𝒞 L`: `L` is the preimage
   under some Boolean tier predicate of a language in `𝒞`.
2. **Boolean closure** `BoolClosure 𝒞 L`: `L` is built from members of
   `𝒞` via finite intersection, union, and complement.

Composing the two: `IsBTC 𝒞 := BoolClosure (IsTierBased 𝒞)` is the
**multitier (Boolean tier-projected) closure** of `𝒞`. Specializing
yields the six classes Lambert (2026) tabulates:

* `IsBTSL` — multitier strictly local
* `IsBTSP` — multitier strictly piecewise
* `IsBTD`  — multitier definite (e.g. Uyghur backness harmony per
  @cite{lambert-2026} §4.3, refining @cite{mayer-major-2018})
* `IsBTK`  — multitier reverse definite
* `IsBTLI` — multitier generalized definite (e.g. Karanga Shona tone
  per @cite{lambert-2026} §5.6, refining @cite{jardine-2020})
* `IsBTN`  — multitier finite-or-cofinite (e.g. culminativity)

## Architecture

A single generic `BoolClosure : (Language α → Prop) → Language α → Prop`
operator pays for itself across the six specializations and across other
"closure-of-X" patterns elsewhere in linglib (`IsLocallyTestable` is
arguably another instance, though kept structurally distinct for now).
The mathlib analogue is `Probability.Kernel.Defs` general +
`Probability.Kernel.Deterministic` specialized — generic operator at the
top, one-line abbreviations downstream.

## Tier representation: Bool, not Prop+DecidablePred

`IsTierBased` quantifies over tier predicates `T : α → Bool`. The Bool
choice avoids the awkward `∃ T, ∃ _ : DecidablePred T, …` quantifier
shape and gives a decidable filter operation by construction. The
existing `tierProject` (taking `T : α → Prop` with `[DecidablePred T]`)
is recoverable via `tierProject T = (·.filter (decide ∘ T))`; the bridge
to `TSLGrammar` lives in `Tier.lean`.

## Decidability

`IsBTC 𝒞` is a `Prop`-valued classifier; deciding membership of a
specific language requires a finite witness (an automaton, a syntactic
monoid). The decidability story lives in a separate `DFA.isBTC` style
classifier, deferred to PR-3+.
-/

namespace Core.Computability.Subregular

variable {α : Type*}

/-! ## Boolean closure of a language class -/

/-- The **Boolean closure** of a class of languages `𝒞`: the smallest
predicate containing `𝒞` and closed under finite intersection, union,
and complement. Free of base-class assumptions; the closure is empty
iff `𝒞` is empty.

Constructors are the closure operations themselves; derived stability
lemmas (top, bot, sdiff, finite intersections, …) live below or follow
mechanically from the four primitives. -/
inductive BoolClosure (𝒞 : Language α → Prop) : Language α → Prop where
  /-- Languages in the base class are in the closure. -/
  | base   {L : Language α} : 𝒞 L → BoolClosure 𝒞 L
  /-- Pairwise intersection (lattice `⊓`, equiv. `Set.inter` via the
  `CompleteAtomicBooleanAlgebra` instance derived in mathlib's `Language`). -/
  | inter  {L₁ L₂ : Language α} :
      BoolClosure 𝒞 L₁ → BoolClosure 𝒞 L₂ → BoolClosure 𝒞 (L₁ ⊓ L₂)
  /-- Pairwise union (lattice `⊔`; mathlib's `Language` derives the Boolean
  algebra, so `⊔` is union and `+` is the same operation under the Kleene
  algebra alias). -/
  | union  {L₁ L₂ : Language α} :
      BoolClosure 𝒞 L₁ → BoolClosure 𝒞 L₂ → BoolClosure 𝒞 (L₁ ⊔ L₂)
  /-- Complement (Boolean algebra `ᶜ`). -/
  | compl  {L : Language α} : BoolClosure 𝒞 L → BoolClosure 𝒞 Lᶜ

namespace BoolClosure

variable {𝒞 : Language α → Prop}

/-- The Boolean closure is monotone in the base class: enlarging `𝒞`
enlarges the closure. -/
theorem mono {𝒟 : Language α → Prop} (h : ∀ L, 𝒞 L → 𝒟 L) :
    ∀ {L : Language α}, BoolClosure 𝒞 L → BoolClosure 𝒟 L := by
  intro L hL
  induction hL with
  | base h₁           => exact .base (h _ h₁)
  | inter _ _ ih₁ ih₂ => exact .inter ih₁ ih₂
  | union _ _ ih₁ ih₂ => exact .union ih₁ ih₂
  | compl _ ih        => exact .compl ih

end BoolClosure

/-! ## Tier-based language families -/

/-- A language `L` is **tier-based for class `𝒞`** iff there is some
Boolean tier predicate `T : α → Bool` and some `L' : Language α` with
`L'` in `𝒞` such that `L` is the preimage of `L'` under projection by
`T`: `w ∈ L ↔ w.filter T ∈ L'`.

The Bool tier shape is the existence-friendly form (no instance
quantifier issues). For the Prop+DecidablePred form used by
`tierProject` and `TSLGrammar`, convert via `T x ↔ tier x = true`
(see `Tier.lean`'s `TSLGrammar.ofByClass` adapter). -/
def IsTierBased (𝒞 : Language α → Prop) (L : Language α) : Prop :=
  ∃ T : α → Bool, ∃ L' : Language α,
    L = { w | w.filter T ∈ L' } ∧ 𝒞 L'

namespace IsTierBased

variable {𝒞 : Language α → Prop}

/-- **Class injection**: every `𝒞`-language is tier-based for `𝒞` via the
universal-true tier (no symbols erased). The witness is `T = fun _ => true`
and `L' = L`. -/
theorem of_class {L : Language α} (h : 𝒞 L) : IsTierBased 𝒞 L := by
  refine ⟨fun _ => true, L, ?_, h⟩
  ext w
  show w ∈ L ↔ List.filter (fun _ => true) w ∈ L
  rw [List.filter_true]

/-- Monotonicity in the base class. -/
theorem mono {𝒟 : Language α → Prop} (h : ∀ L, 𝒞 L → 𝒟 L)
    {L : Language α} (hL : IsTierBased 𝒞 L) : IsTierBased 𝒟 L := by
  obtain ⟨T, L', hL_eq, hL'⟩ := hL
  exact ⟨T, L', hL_eq, h _ hL'⟩

end IsTierBased

/-! ## Multitier (Boolean tier-projected) closure -/

/-- The **multitier closure** of a class `𝒞`: the Boolean closure of the
tier-projected family. Lambert's `B(TC)` notation. -/
def IsBTC (𝒞 : Language α → Prop) : Language α → Prop :=
  BoolClosure (IsTierBased 𝒞)

/-- **Class injection** into the multitier closure: every `𝒞`-language
is in `IsBTC 𝒞`. Composed of `IsTierBased.of_class` (universal tier)
and `BoolClosure.base`. -/
theorem IsBTC.of_class {𝒞 : Language α → Prop} {L : Language α}
    (h : 𝒞 L) : IsBTC 𝒞 L :=
  .base (IsTierBased.of_class h)

/-- **Tier-based injection** into the multitier closure: every
tier-based-for-`𝒞` language is in `IsBTC 𝒞`. -/
theorem IsBTC.of_tierBased {𝒞 : Language α → Prop} {L : Language α}
    (h : IsTierBased 𝒞 L) : IsBTC 𝒞 L :=
  .base h

/-- Monotonicity of multitier closure in the base class. -/
theorem IsBTC.mono {𝒞 𝒟 : Language α → Prop} (h : ∀ L, 𝒞 L → 𝒟 L)
    {L : Language α} : IsBTC 𝒞 L → IsBTC 𝒟 L :=
  BoolClosure.mono fun _ => IsTierBased.mono h

/-! ## Specializations: Lambert (2026) Table 6

One line each. Closure under intersection, union, and complement comes
from `BoolClosure`'s constructors; class injection from
`IsBTC.of_class`. -/

/-- **Multitier strictly local** (BTSL): Boolean closure of tier-projected
SL_k languages. -/
def IsBTSL (k : ℕ) : Language α → Prop := IsBTC (IsStrictlyLocal k)

/-- **Multitier strictly piecewise** (BTSP): Boolean closure of
tier-projected SP_k languages. -/
def IsBTSP (k : ℕ) : Language α → Prop := IsBTC (IsStrictlyPiecewise k)

/-- **Multitier definite** (BTD): Boolean closure of tier-projected D_k
languages. Lambert (2026) §4.3 places Uyghur backness harmony in this
class — strictly stronger than the multiple-tier-based strictly-local
class of @cite{de-santo-graf-2019}. -/
def IsBTD (k : ℕ) : Language α → Prop := IsBTC (IsDefinite k)

/-- **Multitier reverse definite** (BTK): Boolean closure of tier-projected
RD_k languages. -/
def IsBTK (k : ℕ) : Language α → Prop := IsBTC (IsReverseDefinite k)

/-- **Multitier generalized definite** (BTLI): Boolean closure of
tier-projected ℒℐ_k languages. Lambert (2026) §5.6 places Karanga Shona
tone in this class (verb-stem domain) — refining @cite{jardine-2020}. -/
def IsBTLI (k : ℕ) : Language α → Prop := IsBTC (IsGeneralizedDefinite k)

/-- **Multitier finite-or-cofinite** (BTN): Boolean closure of
tier-projected co/finite languages. Captures culminativity-style
constraints when projected to the stress tier. -/
def IsBTN : Language α → Prop := IsBTC IsFiniteOrCofinite

/-! ## Cross-class inclusions

Class containment lifts through the multitier construction: if `𝒞 ⊆ 𝒟`
pointwise, then `IsBTC 𝒞 ⊆ IsBTC 𝒟`. Specializing yields the standard
inclusions BTSL ⊆ BTSP, BTD ⊆ BTLI, BTK ⊆ BTLI, BTN ⊆ BTLI (per Lambert
(2026) Table 6 and the §2.4 small hierarchy diagram). -/

/-- **D_k ⊆ ℒℐ_k** lifts to **BTD_k ⊆ BTLI_k**. -/
theorem IsBTD.toIsBTLI {k : ℕ} {L : Language α} (h : IsBTD k L) :
    IsBTLI k L :=
  IsBTC.mono (fun _ => IsDefinite.toIsGeneralizedDefinite) h

/-- **RD_k ⊆ ℒℐ_k** lifts to **BTK_k ⊆ BTLI_k**. -/
theorem IsBTK.toIsBTLI {k : ℕ} {L : Language α} (h : IsBTK k L) :
    IsBTLI k L :=
  IsBTC.mono (fun _ => IsReverseDefinite.toIsGeneralizedDefinite) h

/-! ## Bridge: TSL ↔ tier-based SL -/

/-- **TSL_k = `IsTierBased (IsStrictlyLocal k)`**. The
`TSLGrammar`-witnessed predicate `IsTierStrictlyLocal` and the generic
preimage-of-SL predicate `IsTierBased ∘ IsStrictlyLocal` are co-extensive
on `Language α`. The bridge gives every existing `IsTierStrictlyLocal`
witness a free `IsBTSL` corollary via `BoolClosure.base`. -/
theorem isTierStrictlyLocal_iff_isTierBased_isStrictlyLocal {k : ℕ}
    {L : Language α} :
    IsTierStrictlyLocal k L ↔ IsTierBased (IsStrictlyLocal k) L := by
  refine ⟨?_, ?_⟩
  · rintro ⟨G, rfl⟩
    refine ⟨fun x => decide (G.tier x), (⟨G.permitted⟩ : SLGrammar k α).lang,
            ?_, ⟨_, rfl⟩⟩
    ext w
    show (∀ f ∈ kFactors k (boundary k (tierProject G.tier w)), f ∈ G.permitted) ↔
         ∀ f ∈ kFactors k (boundary k (List.filter _ w)), f ∈ G.permitted
    rw [tierProject_eq_filter]
  · rintro ⟨T, L', hL_eq, ⟨G', rfl⟩⟩
    let tier_pred : α → Prop := fun x => T x = true
    have dec : DecidablePred tier_pred := fun x => Bool.decEq (T x) true
    refine ⟨{ tier := tier_pred, decTier := dec, permitted := G'.permitted }, ?_⟩
    have hT : (fun x => decide (tier_pred x)) = T := by
      funext x
      show decide (T x = true) = T x
      exact Bool.decide_eq_true
    ext w
    show (∀ f ∈ kFactors k (boundary k (tierProject tier_pred w)),
            f ∈ G'.permitted) ↔ w ∈ L
    rw [hL_eq, tierProject_eq_filter, hT]
    rfl

/-- **TSL_k → BTSL_k**: every tier-based strictly local language is in
the multitier closure of strictly local languages. Combines the bridge
with `BoolClosure.base`. -/
theorem IsTierStrictlyLocal.toIsBTSL {k : ℕ} {L : Language α}
    (h : IsTierStrictlyLocal k L) : IsBTSL k L :=
  .base (isTierStrictlyLocal_iff_isTierBased_isStrictlyLocal.mp h)

end Core.Computability.Subregular
