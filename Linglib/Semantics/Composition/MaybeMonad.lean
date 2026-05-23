import Linglib.Core.Logic.Truth3
import Linglib.Core.Semantics.Presupposition

/-!
# The Maybe Monad: Presupposition as Scope
@cite{grove-2022}

@cite{grove-2022} argues that presupposition projection is a scope phenomenon.
The key insight: presupposition triggers denote values of type `α_#` (= `Option α`),
and they interact with their semantic context by **taking scope** via monadic bind
(`Option.bind`), exactly paralleling @cite{charlow-2020}'s treatment of indefinites
with the set monad.

The Maybe monad `(Option, some, bind)` is the presuppositional analog of
@cite{charlow-2020}'s set monad `(S, η, ⫝̸)` for alternatives. Where `S` gives
scope to alternative-denoting expressions, `Option` gives scope to
presupposition triggers. Both derive exceptional scope from ASSOCIATIVITY.

## Organization

- **§1** Connectives on `Option Bool`: material conditional (middle Kleene),
        conjunction/disjunction (weak Kleene)
- **§2** The intensional-presuppositional monad `Iₚ` (= `ReaderT i Option`)
- **§3** Monad laws for `Iₚ`
- **§4** Semantic operations: evaluation `(·)^ž`, presuppositional universal `∀ₚ`
- **§5** Attitude verb semantics: `believe` via doxastic accessibility
- **§6** Bridge: `Option Bool ↔ Truth3 ↔ PrProp`

## The Maybe Monad as Presupposition

`Option` is already a `LawfulMonad` in Lean. Grove's operators are:

| Grove notation | Lean | Type |
|---|---|---|
| `η_#` | `some` | `α → Option α` |
| `⋆_#` | `Option.bind` | `Option α → (α → Option β) → Option β` |
| `#` | `none` | `Option α` |

The monad laws (Left Identity, Right Identity, Associativity from Figure 7)
hold definitionally.

## Parallel with the Set Monad

| | Alternatives (@cite{charlow-2020}) | Presupposition (@cite{grove-2022}) |
|---|---|---|
| Monad | `S α = α → Prop` (sets) | `Option α` (maybe) |
| Unit | `η_S(x) = {x}` | `η_#(v) = some v` |
| Bind | `m ⫝̸_S f = ⋃_{x∈m} f(x)` | `v ⋆_# k = k(v); # ⋆_# k = #` |
| Effect | Indeterminacy | Partiality |
| Scope | Indefinites escape islands | Presuppositions project past filters |
-/

set_option autoImplicit false

namespace Semantics.Composition.MaybeMonad

open Core.Duality (Truth3 Prop3)
open Core.Presupposition (PrProp)

-- ════════════════════════════════════════════════════════════════
-- §1 Connectives on Option Bool
-- ════════════════════════════════════════════════════════════════

/-! ### §1 Connectives on `Option Bool`

Grove uses two distinct gap-propagation policies:

- **Middle Kleene** for the material conditional `⇒`: left-undefined absorbs,
  but right-undefined does NOT absorb when the left is false (`⊥ ⇒ # = ⊤`).
- **Weak Kleene** for `∀_#`: undefinedness absorbs from either side
  (`⊥ ∧ # = #`, unlike Strong Kleene where `⊥ ∧ # = ⊥`). -/

section Connectives

/-- Material conditional `⇒` with **middle Kleene** semantics (Grove eq. 16).

    `⊤ ⇒ ψ = ψ`, `⊥ ⇒ ψ = ⊤`, `# ⇒ ψ = #`.

    The conditional is true when its antecedent is false (regardless of
    the consequent's definedness), and propagates the consequent when the
    antecedent is true. Undefinedness in the antecedent absorbs. -/
def materialCond : Option Bool → Option Bool → Option Bool
  | none, _ => none
  | some false, _ => some true
  | some true, ψ => ψ

/-- **Weak Kleene** conjunction (used by `∀ₚ`).

    Undefinedness absorbs from either side, then falsity absorbs.
    In contrast, Strong Kleene has `⊥ ∧ # = ⊥`, while Weak Kleene
    has `⊥ ∧ # = #`. -/
def meetWK : Option Bool → Option Bool → Option Bool
  | none, _ | _, none => none
  | some false, _ | _, some false => some false
  | some true, some true => some true

/-- **Weak Kleene** disjunction. Dual of `meetWK`. -/
def joinWK : Option Bool → Option Bool → Option Bool
  | none, _ | _, none => none
  | some true, _ | _, some true => some true
  | some false, some false => some false

/-- Negation preserves definedness. -/
def negP : Option Bool → Option Bool
  | some b => some (!b)
  | none => none

theorem materialCond_false_absorbs (ψ : Option Bool) :
    materialCond (some false) ψ = some true := rfl

theorem materialCond_true_passes (ψ : Option Bool) :
    materialCond (some true) ψ = ψ := rfl

theorem materialCond_undef_absorbs (ψ : Option Bool) :
    materialCond none ψ = none := rfl

theorem meetWK_comm (a b : Option Bool) : meetWK a b = meetWK b a := by
  cases a with
  | none => cases b <;> rfl
  | some a => cases b with
    | none => rfl
    | some b => cases a <;> cases b <;> rfl

private theorem meetWK_none_right (a : Option Bool) : meetWK a none = none := by
  cases a with | none => rfl | some b => cases b <;> rfl

/-- Once the accumulator is `none`, folding with `meetWK` preserves it. -/
private theorem foldl_meetWK_none {α : Type} (ys : List α) (φ : α → Option Bool) :
    ys.foldl (λ acc x => meetWK acc (φ x)) none = none := by
  induction ys with
  | nil => rfl
  | cons _ ys ih => exact ih

end Connectives

-- ════════════════════════════════════════════════════════════════
-- §2 The Intensional-Presuppositional Monad Iₚ
-- ════════════════════════════════════════════════════════════════

/-! ### §2 The monad `Iₚ`

`Iₚ I α = I → Option α`: the Reader monad transformer applied to the
Maybe monad. An expression of type `Iₚ I α` reads an index (world,
world-assignment pair, etc.) and returns a possibly-undefined value.

This monad treats intensionality and presupposition uniformly
(Grove §4.1): `Iₚ` is obtained by replacing `t` with `t_#` in
standard intensional types (`i → t` becomes `i → t_#`). -/

section IMonad

variable {I : Type}

/-- `Iₚ I α`: the intensional-presuppositional monad.

    An expression of type `Iₚ I α` reads an index `i` and returns
    `some v` if defined at `i`, or `none` if presupposition failure
    occurs at `i`. -/
abbrev Iₚ (I : Type) (α : Type) := I → Option α

/-- `ηI`: unit for `Iₚ`. Makes a value trivially index-sensitive
    (ignores the index, always defined). Grove eq. 19, first line. -/
def ηI {α : Type} (v : α) : Iₚ I α := λ _ => some v

/-- `bindI`: bind for `Iₚ`. Evaluates `m` at index `i`; if defined,
    feeds the result to `k` at the same index. Grove eq. 19, second line. -/
def bindI {α β : Type} (m : Iₚ I α) (k : α → Iₚ I β) : Iₚ I β :=
  λ i => m i >>= (λ v => k v i)

end IMonad

-- ════════════════════════════════════════════════════════════════
-- §3 Monad Laws for Iₚ
-- ════════════════════════════════════════════════════════════════

/-! ### §3 Monad laws

The three laws from Figure 7 hold for `Iₚ`. Left Identity and
Associativity are the key properties for scope-taking: Left Identity
ensures that `η` + `⋆` = reconstruction (no scope), and Associativity
ensures that cyclic scope-taking (roll-up pied-piping) works. -/

section MonadLaws

variable {I α β γ : Type}

/-- **Left Identity**: lifting a value into the monad and immediately
    binding is the same as applying the continuation directly.

    This is why global scope for a presupposition trigger that has been
    locally `η`-shifted reconstructs to the local meaning (Grove fn. 13). -/
theorem left_identity (v : α) (k : α → Iₚ I β) :
    bindI (ηI v) k = k v := rfl

/-- **Right Identity**: binding with `ηI` is a no-op. -/
theorem right_identity (m : Iₚ I α) : bindI m ηI = m := by
  funext i; simp [bindI, ηI]

/-- **Associativity**: sequential scope-taking = direct wide scope.

    This is the presuppositional analog of @cite{charlow-2020}'s
    ASSOCIATIVITY theorem for the set monad. It guarantees that
    roll-up pied-piping (taking scope at an island edge, then further)
    yields the same result as direct scope-taking. -/
theorem assoc (m : Iₚ I α) (f : α → Iₚ I β) (g : β → Iₚ I γ) :
    bindI (bindI m f) g = bindI m (λ x => bindI (f x) g) := by
  funext i; simp [bindI]; cases m i <;> rfl

/-- **Backward compatibility**: non-presuppositional expressions (those
    wrapped in `some`) compose the same way they do without the monad.
    This means traditional satisfaction-theoretic analyses that use only
    defined values are preserved inside the monadic setting (Grove §5). -/
theorem backward_compat (f : α → β) (v : α) :
    bindI (ηI v) (λ x => ηI (f x)) = (ηI (f v) : Iₚ I β) := rfl

end MonadLaws

-- ════════════════════════════════════════════════════════════════
-- §4 Semantic Operations
-- ════════════════════════════════════════════════════════════════

/-! ### §4 Evaluation and presuppositional universal

The evaluation function `evalI` (Grove's `(·)^ž`) converts an intension
that may be undefined into an intensional truth value that may be undefined,
by feeding the index to itself. The presuppositional universal `forallP`
(Grove's `∀_#`) quantifies over a domain with weak-Kleene semantics. -/

section Operations

variable {I : Type}

/-- Evaluation function `(·)^ž` (Grove eq. 20).

    Given `φ : Iₚ I (I → Bool)` (a proposition that reads an index, possibly
    undefined, to return an intension), `evalI φ` feeds the index to itself:
    `evalI φ i = (φ i).map (· i)`. -/
def evalI (φ : Iₚ I (I → Bool)) : Iₚ I Bool :=
  λ i => (φ i).map (· i)

/-- Presuppositional universal `∀_#` (Grove eq. 27).

    Uses weak Kleene semantics: `none` absorbs (if the scope is undefined
    at any value, the whole universal is undefined). -/
def forallP {α : Type} (xs : List α) (φ : α → Option Bool) : Option Bool :=
  xs.foldl (λ acc x => meetWK acc (φ x)) (some true)

/-- Presuppositional existential (dual of `forallP`). -/
def existsP {α : Type} (xs : List α) (φ : α → Option Bool) : Option Bool :=
  xs.foldl (λ acc x => joinWK acc (φ x)) (some false)

/-- `forallP` on an all-true list is `some true`. -/
theorem forallP_all_true {α : Type} (xs : List α) (φ : α → Option Bool)
    (h : ∀ x, x ∈ xs → φ x = some true) :
    forallP xs φ = some true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [forallP, List.foldl]
    rw [show meetWK (some true) (φ x) = φ x from by
      cases hx : φ x <;> simp [meetWK]; cases ‹Bool› <;> rfl]
    rw [h x List.mem_cons_self]
    exact ih (λ y hy => h y (List.mem_cons_of_mem x hy))

/-- Helper: folding `meetWK` with an element that maps to `none` yields `none`,
    regardless of the accumulator or subsequent elements. -/
private theorem foldl_meetWK_hits_none {α : Type}
    (pre : List α) (x : α) (post : List α) (φ : α → Option Bool)
    (acc : Option Bool) (hu : φ x = none) :
    (pre ++ x :: post).foldl (λ a y => meetWK a (φ y)) acc = none := by
  rw [List.foldl_append]
  simp only [List.foldl]
  rw [show meetWK (pre.foldl (λ a y => meetWK a (φ y)) acc) (φ x) = none from by
    rw [hu]; exact meetWK_none_right _]
  exact foldl_meetWK_none post φ

/-- `forallP` with an undefined element is `none`.

    Since `meetWK` has `none` as a zero element, once any `φ(x) = none`
    is encountered, the accumulator becomes `none` and stays `none`. -/
theorem forallP_undef {α : Type} (xs : List α) (φ : α → Option Bool)
    (x : α) (hx : x ∈ xs) (hu : φ x = none) :
    forallP xs φ = none := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hx
  exact foldl_meetWK_hits_none pre x post φ (some true) hu

end Operations

-- ════════════════════════════════════════════════════════════════
-- §5 Attitude Verb Semantics
-- ════════════════════════════════════════════════════════════════

/-! ### §5 `believe` via doxastic accessibility

Grove §4.2 (eq. 28): `believe = λφ,x,i. ∀_# j : dox(x,i,j) ⇒ φ(j)`.
The verb quantifies over doxastically accessible worlds with `∀_#` and
uses the material conditional `⇒`. The `⇒` contributes the key
filtering behavior: when `dox(x,i,j) = false`, `⇒` returns `some true`
regardless of `φ(j)`'s definedness. -/

section AttitudeVerbs

variable {W E : Type}

/-- `believe` (Grove eq. 28).

    Given an accessibility relation `dox`, a list of worlds, a complement
    `φ : Iₚ W Bool`, an agent `x`, and an evaluation world `i`:
    `believe dox worlds φ x i = ∀_# j ∈ worlds : dox(x,i,j) ⇒ φ(j)` -/
def believe (dox : E → W → W → Bool) (worlds : List W)
    (φ : Iₚ W Bool) (x : E) : Iₚ W Bool :=
  λ i => forallP worlds (λ j => materialCond (some (dox x i j)) (φ j))

end AttitudeVerbs

-- ════════════════════════════════════════════════════════════════
-- §6 Bridges
-- ════════════════════════════════════════════════════════════════

/-! ### §6 Bridges to existing linglib types

`Option Bool`, `Truth3`, and `PrProp W` are three representations
of possibly-undefined truth values. These conversions connect Grove's
formalization to the rest of the presupposition infrastructure. -/

section Bridges

/-- Convert `Option Bool` to `Truth3`. -/
def toTruth3 : Option Bool → Truth3
  | some true => .true
  | some false => .false
  | none => .indet

/-- Convert `Truth3` to `Option Bool`. -/
def ofTruth3 : Truth3 → Option Bool
  | .true => some true
  | .false => some false
  | .indet => none

theorem roundtrip_truth3 (v : Truth3) : toTruth3 (ofTruth3 v) = v := by
  cases v <;> rfl

theorem roundtrip_option (v : Option Bool) : ofTruth3 (toTruth3 v) = v := by
  cases v with
  | none => rfl
  | some b => cases b <;> rfl

/-- Middle Kleene implication on `Truth3`. -/
def impMK : Truth3 → Truth3 → Truth3
  | .indet, _ => .indet
  | .false, _ => .true
  | .true, ψ => ψ

/-- `materialCond` corresponds to middle Kleene implication on `Truth3`. -/
theorem materialCond_eq_truth3 (p q : Option Bool) :
    toTruth3 (materialCond p q) = impMK (toTruth3 p) (toTruth3 q) := by
  cases p with
  | none => rfl
  | some b => cases b <;> cases q with
    | none => rfl
    | some c => cases c <;> rfl

/-- `meetWK` corresponds to `Truth3.meetWeak` from `Core.Duality`. -/
theorem meetWK_eq_truth3 (p q : Option Bool) :
    toTruth3 (meetWK p q) = Truth3.meetWeak (toTruth3 p) (toTruth3 q) := by
  cases p with
  | none => cases q with | none => rfl | some c => cases c <;> rfl
  | some b => cases b <;> cases q with
    | none => rfl
    | some c => cases c <;> rfl

/-- `joinWK` corresponds to `Truth3.joinWeak` from `Core.Duality`. -/
theorem joinWK_eq_truth3 (p q : Option Bool) :
    toTruth3 (joinWK p q) = Truth3.joinWeak (toTruth3 p) (toTruth3 q) := by
  cases p with
  | none => cases q with | none => rfl | some c => cases c <;> rfl
  | some b => cases b <;> cases q with
    | none => rfl
    | some c => cases c <;> rfl

/-- Convert `Iₚ W Bool` to `Prop3 W` (world-indexed three-valued proposition). -/
def toProp3 {W : Type} (φ : Iₚ W Bool) : Prop3 W :=
  λ w => toTruth3 (φ w)

/-- Convert `Iₚ W Bool` to `PrProp W`.

    The presupposition field is `isSome` (defined?), and the assertion
    is the Bool value (defaulting to `false` when undefined). -/
def toPrProp {W : Type} (φ : Iₚ W Bool) : PrProp W :=
  { presup := λ w => (φ w).isSome
  , assertion := λ w => (φ w).getD false }

theorem toPrProp_presup {W : Type} (φ : Iₚ W Bool) (w : W) :
    (toPrProp φ).presup w = (φ w).isSome := rfl

theorem toPrProp_assertion {W : Type} (φ : Iₚ W Bool) (w : W) (v : Bool)
    (h : φ w = some v) :
    (toPrProp φ).assertion w = v := by
  simp [toPrProp, h]

end Bridges

end Semantics.Composition.MaybeMonad
