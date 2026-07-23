import Linglib.Core.Logic.Trivalent.Prop3
import Linglib.Semantics.Presupposition.Basic
import Linglib.Studies.Heim1992Projection

/-!
# [grove-2022]: Presupposition Projection as a Scope Phenomenon

Julian Grove (2022). "Presupposition projection as a scope phenomenon."
*Semantics and Pragmatics* 15, Article 15: 1–39.
<https://doi.org/10.3765/sp.15.15>

## Thesis

The proviso problem — where [heim-1983]'s satisfaction theory predicts
weak conditional presuppositions for sentences that intuitively have
unconditional ones — dissolves when presupposition projection is treated
as **scope-taking**. Presupposition triggers have `α#`-typed denotations
(= `Option α`); they interact with the surrounding context via monadic
bind, exactly paralleling [charlow-2020]'s treatment of indefinites with
the set monad.

The paper develops the apparatus (Part I below) and applies it to the
classic "If Theo has a brother, he'll bring his wetsuit" minimal pair
plus attitude-verb examples (Part II).

## Part I — Apparatus (Grove §§3–4)

* `materialCond` — material conditional with middle Kleene semantics
  (eq. 16): `⊤ ⇒ ψ = ψ`, `⊥ ⇒ ψ = ⊤`, `# ⇒ ψ = #`
* `meetWK` / `joinWK` — weak Kleene conjunction / disjunction (used by
  the presuppositional universal, where undefinedness absorbs from
  either side)
* `Iₚ I := ReaderT I Option` — Grove's `I#` (footnote 18: "Reader monad
  transformer applied to the maybe monad"); `Iₚ` is a Lean-typographical
  rename since `#` isn't a Lean subscript
* Monad laws (Figure 7) inherited via mathlib's `LawfulMonad ReaderT`
* `evalI` — evaluation `(·)^ž` (eq. 20)
* `forallP` / `existsP` — presuppositional quantifiers (eq. 27)
* `believe` — doxastic attitude verb (eq. 28)
* Bridges to `Trivalent`, `Prop3`, `PartialProp`

## Part II — Empirical predictions (Grove §3, §4.2)

For "If Theo has a brother, he'll bring his wetsuit":

* **Local reading** (narrow scope): trigger stays in the consequent →
  presupposition is `hasBrother → hasWetsuit` (conditional)
* **Global reading** (wide scope): trigger scopes over the conditional
  via roll-up pied-piping → presupposition is `hasWetsuit` (unconditional)

The two readings are a genuine **scope ambiguity**, not a semantic +
pragmatic strengthening. The proviso problem does not arise because the
unconditional presupposition is semantically available.

For attitude verbs ("Theo believes he lost his wetsuit"), the same
mechanism derives:
* **Local** (de dicto): presupposition is that Theo *believes* he has
  a wetsuit
* **Global** (de re): presupposition is that Theo *has* a wetsuit

This connects to `Heim1992Projection.lean`'s know/believe asymmetry but
derives it from scope rather than from local-context filtering.

## Parallel with the set monad ([charlow-2020])

| | Alternatives ([charlow-2020]) | Presupposition ([grove-2022]) |
|---|---|---|
| Monad | `S α = α → Prop` (sets) | `Option α` (maybe) |
| Unit | `η_S(x) = {x}` | `η_#(v) = some v` |
| Bind | `m ⫝̸_S f = ⋃_{x∈m} f(x)` | `v ⋆_# k = k(v); # ⋆_# k = #` |
| Effect | Indeterminacy | Partiality |
| Scope | Indefinites escape islands | Presuppositions project past filters |
-/

set_option autoImplicit false

namespace Grove2022

open Trivalent (Prop3)
open Semantics.Presupposition (PartialProp)

/-! ## Part I — Apparatus -/

/-! ### §1 Connectives on `Option Bool`

Grove uses two distinct gap-propagation policies:

* **Middle Kleene** for the material conditional `⇒`: left-undefined
  absorbs, but right-undefined does NOT absorb when the left is false
  (`⊥ ⇒ # = ⊤`).
* **Weak Kleene** for `∀_#`: undefinedness absorbs from either side
  (`⊥ ∧ # = #`, unlike Strong Kleene where `⊥ ∧ # = ⊥`). -/

section Connectives

/-- Material conditional `⇒` with **middle Kleene** semantics (eq. 16):
`⊤ ⇒ ψ = ψ`, `⊥ ⇒ ψ = ⊤`, `# ⇒ ψ = #`. The conditional is true when
its antecedent is false (regardless of consequent definedness), and
propagates the consequent when the antecedent is true. Undefinedness
in the antecedent absorbs. -/
def materialCond : Option Bool → Option Bool → Option Bool
  | none, _ => none
  | some false, _ => some true
  | some true, ψ => ψ

/-- **Weak Kleene** conjunction (used by `forallP`). Undefinedness
absorbs from either side, then falsity absorbs. (Contrast Strong
Kleene: `⊥ ∧ # = ⊥` vs Weak Kleene `⊥ ∧ # = #`.) -/
def meetWK : Option Bool → Option Bool → Option Bool
  | none, _ | _, none => none
  | some false, _ | _, some false => some false
  | some true, some true => some true

/-- **Weak Kleene** disjunction. Dual of `meetWK`. -/
def joinWK : Option Bool → Option Bool → Option Bool
  | none, _ | _, none => none
  | some true, _ | _, some true => some true
  | some false, some false => some false

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

/-! ### §2 The intensional-presuppositional monad `Iₚ`

`Iₚ I α = I → Option α`: the Reader monad transformer applied to the
maybe monad. An expression of type `Iₚ I α` reads an index `i` (world,
world-assignment pair, etc.) and returns `some v` if defined at `i`,
or `none` on presupposition failure — Grove §4.1's uniform treatment
of intensionality and presupposition (replacing `t` with `t_#` in the
intensional type `i → t`).

Defining `Iₚ` as `ReaderT I Option` makes `pure`/`>>=` Grove's
`η_#`/`⋆_#` and inherits `Monad`/`LawfulMonad` from mathlib. (Grove
writes `I#`; `Iₚ` here is a Lean-friendly rename since `#` isn't a
subscript glyph.) -/

abbrev Iₚ (I : Type) := ReaderT I Option

/-! ### §3 Monad laws

`Iₚ = ReaderT I Option` is a `LawfulMonad`, so Grove's three laws
(Figure 7: Left Identity, Right Identity, Associativity) hold via
`pure_bind`, `bind_pure`, `bind_assoc` — no standalone `rfl` theorems
needed. Left Identity and Associativity are the load-bearing
scope-taking properties: Left Identity gives reconstruction (`η` + `⋆`
= no scope; fn. 13), and Associativity makes cyclic scope-taking
(roll-up pied-piping) sound (the presuppositional analog of
[charlow-2020]'s ASSOCIATIVITY for the set monad). -/

/-! ### §4 Semantic operations -/

section Operations

variable {I : Type}

/-- Evaluation function `(·)^ž` (eq. 20). Given `φ : Iₚ I (I → Bool)`
(a proposition that reads an index, possibly undefined, to return an
intension), `evalI φ` feeds the index to itself:
`evalI φ i = (φ i).map (· i)`. -/
def evalI (φ : Iₚ I (I → Bool)) : Iₚ I Bool :=
  λ i => (φ i).map (· i)

/-- Presuppositional universal `∀_#` (eq. 27). Weak Kleene: `none`
absorbs (if the scope is undefined at any value, the whole universal
is undefined). -/
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

/-- Helper: folding `meetWK` with an element that maps to `none` yields
`none`, regardless of the accumulator or subsequent elements. -/
private theorem foldl_meetWK_hits_none {α : Type}
    (pre : List α) (x : α) (post : List α) (φ : α → Option Bool)
    (acc : Option Bool) (hu : φ x = none) :
    (pre ++ x :: post).foldl (λ a y => meetWK a (φ y)) acc = none := by
  rw [List.foldl_append]
  simp only [List.foldl]
  rw [show meetWK (pre.foldl (λ a y => meetWK a (φ y)) acc) (φ x) = none from by
    rw [hu]; exact meetWK_none_right _]
  exact foldl_meetWK_none post φ

/-- `forallP` with an undefined element is `none` — `meetWK` has `none`
as a zero element, so once any `φ(x) = none` is encountered, the
accumulator becomes `none` and stays `none`. -/
theorem forallP_undef {α : Type} (xs : List α) (φ : α → Option Bool)
    (x : α) (hx : x ∈ xs) (hu : φ x = none) :
    forallP xs φ = none := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hx
  exact foldl_meetWK_hits_none pre x post φ (some true) hu

end Operations

/-! ### §5 Attitude verb semantics (Grove §4.2, eq. 28)

`believe = λφ,x,i. ∀_# j : dox(x,i,j) ⇒ φ(j)` — the verb quantifies
over doxastically accessible worlds with `∀_#` and uses the material
conditional `⇒`. The `⇒` contributes the key filtering behavior: when
`dox(x,i,j) = false`, `⇒` returns `some true` regardless of `φ(j)`'s
definedness. -/

section AttitudeVerbs

variable {W E : Type}

/-- `believe` (eq. 28). Given an accessibility relation `dox`, a list
of worlds, a complement `φ : Iₚ W Bool`, an agent `x`, and an
evaluation world `i`:
`believe dox worlds φ x i = ∀_# j ∈ worlds : dox(x,i,j) ⇒ φ(j)` -/
def believe (dox : E → W → W → Bool) (worlds : List W)
    (φ : Iₚ W Bool) (x : E) : Iₚ W Bool :=
  λ i => forallP worlds (λ j => materialCond (some (dox x i j)) (φ j))

end AttitudeVerbs

/-! ### §6 Bridges to existing linglib types

`Option Bool`, `Trivalent`, and `PartialProp W` are three representations of
possibly-undefined truth values. These conversions connect Grove's
formalisation to the rest of the presupposition infrastructure. -/

section Bridges

/-- Convert `Option Bool` to `Trivalent`. -/
def toTruth : Option Bool → Trivalent
  | some true => .true
  | some false => .false
  | none => .indet

/-- Convert `Trivalent` to `Option Bool`. -/
def ofTruth : Trivalent → Option Bool
  | .true => some true
  | .false => some false
  | .indet => none

theorem roundtrip_truth3 (v : Trivalent) : toTruth (ofTruth v) = v := by
  cases v <;> rfl

theorem roundtrip_option (v : Option Bool) : ofTruth (toTruth v) = v := by
  cases v with
  | none => rfl
  | some b => cases b <;> rfl

/-- Middle Kleene implication on `Trivalent`. -/
def impMK : Trivalent → Trivalent → Trivalent
  | .indet, _ => .indet
  | .false, _ => .true
  | .true, ψ => ψ

/-- `materialCond` corresponds to middle Kleene implication on `Trivalent`. -/
theorem materialCond_eq_truth3 (p q : Option Bool) :
    toTruth (materialCond p q) = impMK (toTruth p) (toTruth q) := by
  cases p with
  | none => rfl
  | some b => cases b <;> cases q with
    | none => rfl
    | some c => cases c <;> rfl

/-- `meetWK` corresponds to `Trivalent.meetWeak`. -/
theorem meetWK_eq_truth3 (p q : Option Bool) :
    toTruth (meetWK p q) = Trivalent.meetWeak (toTruth p) (toTruth q) := by
  cases p with
  | none => cases q with | none => rfl | some c => cases c <;> rfl
  | some b => cases b <;> cases q with
    | none => rfl
    | some c => cases c <;> rfl

/-- `joinWK` corresponds to `Trivalent.joinWeak`. -/
theorem joinWK_eq_truth3 (p q : Option Bool) :
    toTruth (joinWK p q) = Trivalent.joinWeak (toTruth p) (toTruth q) := by
  cases p with
  | none => cases q with | none => rfl | some c => cases c <;> rfl
  | some b => cases b <;> cases q with
    | none => rfl
    | some c => cases c <;> rfl

/-- Convert `Iₚ W Bool` to `Prop3 W` (world-indexed three-valued
proposition). -/
def toProp3 {W : Type} (φ : Iₚ W Bool) : Prop3 W :=
  λ w => toTruth (φ w)

/-- Convert `Iₚ W Bool` to `PartialProp W`. The presupposition field is
`isSome` (defined?), and the assertion is the Bool value (defaulting
to `false` when undefined). -/
def toPartialProp {W : Type} (φ : Iₚ W Bool) : PartialProp W :=
  { presup := λ w => (φ w).isSome
  , assertion := λ w => (φ w).getD false }

theorem toPartialProp_presup {W : Type} (φ : Iₚ W Bool) (w : W) :
    (toPartialProp φ).presup w = (φ w).isSome := rfl

theorem toPartialProp_assertion {W : Type} (φ : Iₚ W Bool) (w : W) (v : Bool)
    (h : φ w = some v) :
    (toPartialProp φ).assertion w = v := by
  simp [toPartialProp, h]

end Bridges

/-! ## Part II — Empirical predictions -/

/-! ### §7 World model for the conditional cases

Four worlds varying two properties: whether Theo has a brother, and
whether Theo has a (unique) wetsuit. -/

inductive CWorld where
  | broSuit   -- has brother, has wetsuit
  | broNoSuit -- has brother, no wetsuit
  | noBroSuit -- no brother, has wetsuit
  | noBro     -- no brother, no wetsuit
  deriving DecidableEq, Repr

open CWorld

def hasBrother : CWorld → Bool
  | .broSuit | .broNoSuit => true
  | .noBroSuit | .noBro => false

def hasWetsuit : CWorld → Bool
  | .broSuit | .noBroSuit => true
  | .broNoSuit | .noBro => false

/-- Whether Theo brings his wetsuit (only meaningful when he has one). -/
def bringsWetsuit : CWorld → Bool
  | .broSuit => true
  | _ => false

/-! ### §8 The presupposition trigger "his wetsuit"

"His wetsuit" denotes type `e_#` (= `Option Entity`): defined when
Theo has a unique wetsuit, undefined otherwise. In our simplified
model, the entity is irrelevant — what matters is the definedness
condition. So we model the trigger's contribution to the truth value
as `Option Bool`: defined (with value `bring(t)`) when `hasWetsuit`,
undefined otherwise. -/

/-- "his wetsuit" contributes definedness + the `bring` predicate.

* At worlds where Theo has a wetsuit: `some (bringsWetsuit w)`
* At worlds where he doesn't: `none` (presupposition failure) -/
def hisWetsuit : CWorld → Option Bool :=
  λ w => if hasWetsuit w then some (bringsWetsuit w) else none

/-! ### §9 Local reading: conditional presupposition

The trigger takes scope within the consequent clause. The conditional's
interpretation uses `materialCond`, which checks the consequent only
when the antecedent is true. Result: the presupposition is conditional
(`hasBrother → hasWetsuit`). -/

/-- Local reading of "If Theo has a brother, he'll bring his wetsuit."
The trigger stays inside the consequent. The conditional filters:
`materialCond (some (hasBrother w)) (hisWetsuit w)`. -/
def localReading : CWorld → Option Bool :=
  λ w => materialCond (some (hasBrother w)) (hisWetsuit w)

/-- At `broSuit`: brother ✓, wetsuit ✓, brings ✓ → `some true`. -/
theorem local_broSuit : localReading .broSuit = some true := rfl

/-- At `broNoSuit`: brother ✓, no wetsuit → `none` (presup failure). -/
theorem local_broNoSuit : localReading .broNoSuit = none := rfl

/-- At `noBroSuit`: no brother → `some true` (conditional vacuously true). -/
theorem local_noBroSuit : localReading .noBroSuit = some true := rfl

/-- At `noBro`: no brother → `some true` (vacuously true). -/
theorem local_noBro : localReading .noBro = some true := rfl

/-- The local reading is defined iff `hasBrother → hasWetsuit`. This is
the **conditional presupposition** that [geurts-1996] observed
satisfaction accounts predict — and which Grove argues is merely one of
two available readings. -/
theorem local_definedness (w : CWorld) :
    (localReading w).isSome = (!hasBrother w || hasWetsuit w) := by
  cases w <;> rfl

/-! ### §10 Global reading: unconditional presupposition

The trigger takes scope over the entire conditional via cyclic
scope-taking (roll-up pied-piping). The trigger's definedness is
checked first; only then does the conditional apply. Result: the
presupposition is unconditional (`hasWetsuit`). -/

/-- Global reading: the trigger scopes over the conditional.
`hisWetsuit w >>= (λ b => materialCond (some (hasBrother w)) (some b))`.
First check definedness of the trigger; then, if defined, evaluate the
conditional with a fully-defined consequent. -/
def globalReading : CWorld → Option Bool :=
  λ w => hisWetsuit w >>= (λ b => materialCond (some (hasBrother w)) (some b))

/-- At `broSuit`: wetsuit ✓ → defined. Brother ✓, brings ✓ → `some true`. -/
theorem global_broSuit : globalReading .broSuit = some true := rfl

/-- At `broNoSuit`: no wetsuit → `none` (presup failure). -/
theorem global_broNoSuit : globalReading .broNoSuit = none := rfl

/-- At `noBroSuit`: wetsuit ✓ → defined. No brother → `some true`. -/
theorem global_noBroSuit : globalReading .noBroSuit = some true := rfl

/-- At `noBro`: no wetsuit → `none` (presup failure). -/
theorem global_noBro : globalReading .noBro = none := rfl

/-- The global reading is defined iff `hasWetsuit`. This is the
**unconditional presupposition** that speakers actually accommodate for
"If Theo has a brother, he'll bring his wetsuit." The proviso problem
does not arise: this reading is semantically available without
pragmatic strengthening. -/
theorem global_definedness (w : CWorld) :
    (globalReading w).isSome = hasWetsuit w := by
  cases w <;> rfl

/-! ### §11 Scope ambiguity = no proviso problem

The two readings differ only in scope. At worlds where both readings
are defined, they agree on truth value — the readings differ only in
their **presuppositions** (definedness conditions). -/

/-- Where both readings are defined, they agree on truth value. -/
theorem readings_agree_when_defined (w : CWorld)
    (_hl : (localReading w).isSome = true)
    (_hg : (globalReading w).isSome = true) :
    localReading w = globalReading w := by
  cases w <;> simp_all [localReading, globalReading, hisWetsuit,
    materialCond, hasBrother, hasWetsuit, bringsWetsuit]

/-- The global presupposition is strictly stronger than the local one:
`hasWetsuit → (hasBrother → hasWetsuit)` but not vice versa. -/
theorem global_stronger_than_local :
    (∀ w, hasWetsuit w = true → (!hasBrother w || hasWetsuit w) = true)
    ∧ ¬(∀ w, (!hasBrother w || hasWetsuit w) = true → hasWetsuit w = true) := by
  constructor
  · intro w hw; simp [hw, Bool.or_true]
  · intro h; have := h .noBro (by rfl); simp [hasWetsuit] at this

/-- Left Identity ensures that `η`-shifting inside the trigger's scope
and then binding is the same as not shifting at all — this is why the
narrow-scope derivation is equivalent to the standard satisfaction-
theory prediction (Grove fn. 13). -/
theorem eta_bind_reconstructs (w : CWorld) :
    (some (hisWetsuit w) >>= id) = hisWetsuit w := by
  cases hisWetsuit w <;> rfl

/-! ### §12 Attitude verbs: "Theo believes he lost his wetsuit"

Reuse the world model from [heim-1992] (`AttWorld` with `actual` and
`believed`) and show that the scope theory derives the same empirical
predictions via different machinery. -/

open Heim1992 (AttWorld believesRBool)

/-- The complement "he lost his wetsuit" as an `Iₚ`-typed meaning.
Presupposes Theo has a wetsuit at the evaluation world. When defined,
asserts he lost it. At `believed`: has wetsuit ✓, lost it ✓. At
`actual`: no wetsuit → undefined. -/
def lostWetsuit : Iₚ AttWorld Bool
  | .believed => some true   -- has wetsuit, lost it
  | .actual => none          -- no wetsuit: presupposition failure

/-- Local reading of "Theo believes he lost his wetsuit." The
complement stays in situ; `believe` quantifies over doxastic
alternatives with the complement evaluated locally. -/
def believeLocal : Iₚ AttWorld Bool :=
  believe (λ _ => believesRBool) [AttWorld.actual, AttWorld.believed]
    lostWetsuit () -- () stands for Theo (single-agent model)

/-- Local reading at `actual`: Theo's only belief-world is `believed`,
where the complement is defined and true → `some true`. -/
theorem believe_local_actual : believeLocal .actual = some true := rfl

/-- Local reading at `believed`: same → `some true`. -/
theorem believe_local_believed : believeLocal .believed = some true := rfl

/-- The local reading is always defined. The presupposition is that
Theo **believes** he has a wetsuit (= the complement is defined at all
doxastic alternatives). Since `believed` is the only belief-accessible
world from either world, and the complement is defined there, this
always holds. No projection to the actual world. -/
theorem believe_local_always_defined (w : AttWorld) :
    (believeLocal w).isSome = true := by
  cases w <;> rfl

/-- Global reading: the complement scopes out. The complement's
definedness is evaluated at the actual world (not within the scope of
`believe`). -/
def believeGlobal : Iₚ AttWorld Bool :=
  λ i => lostWetsuit i >>= (λ b =>
    believe (λ _ => believesRBool) [AttWorld.actual, AttWorld.believed]
      (pure b) () i)

/-- Global reading at `actual`: complement is undefined → `none`. The
presupposition projects globally: Theo must *actually* have a wetsuit
at the evaluation world. -/
theorem believe_global_actual : believeGlobal .actual = none := rfl

/-- Global reading at `believed`: complement defined → `some true`. -/
theorem believe_global_believed : believeGlobal .believed = some true := rfl

/-- The global reading is defined iff the complement is defined at the
evaluation world — the presupposition projects past `believe`. -/
theorem believe_global_definedness (w : AttWorld) :
    (believeGlobal w).isSome = (lostWetsuit w).isSome := by
  cases w <;> rfl

/-! ### §13 Bridge to [heim-1992]

[heim-1992]'s know/believe asymmetry is derived in
`Heim1992Projection.lean` via local-context filtering and KD45 frame
conditions. The scope theory provides an alternative explanation: the
asymmetry arises because the trigger can take different scopes relative
to the attitude verb.

The **local** reading corresponds to Heim's standard satisfaction-
theory prediction. The **global** reading is what the satisfaction
theory cannot derive — and what the scope theory adds. -/

/-- The local reading's definedness matches Heim's belief-embedding
prediction: the presupposition is filtered (projected into the attitude
holder's beliefs, not to the actual world). -/
theorem local_matches_heim_belief :
    -- Local reading defined at actual (no projection to actual world)
    (believeLocal .actual).isSome = true
    -- Even though the complement's presupposition fails at actual
    ∧ (lostWetsuit .actual).isSome = false := by
  exact ⟨rfl, rfl⟩

/-- The global reading adds what Heim's account lacks: a reading where
the presupposition projects past the attitude verb entirely. -/
theorem global_projects_past_attitude :
    -- Global reading undefined at actual (projects to actual world)
    (believeGlobal .actual).isSome = false
    -- Because the complement's presupposition fails at actual
    ∧ (lostWetsuit .actual).isSome = false := by
  exact ⟨rfl, rfl⟩

end Grove2022
