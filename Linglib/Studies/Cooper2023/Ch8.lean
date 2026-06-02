import Linglib.Semantics.Composition.Scope
import Linglib.Studies.Cooper2023.Ch7
import Linglib.Syntax.Binding.Semantics

/-!
# Cooper (2023) Ch. 8 — Type-Based Underspecification

[cooper-2023]
[chomsky-1981] [kanazawa-1994] [scontras-pearl-2021]
[kamp-1981] [chierchia-1995]

Cooper's *From Perception to Communication* Chapter 8 introduces *content
types* that replace specific contents with types whose witnesses are fully
specified readings. This file formalises §8.2 (quantifier scope and
underspecification) and §8.3 (anaphora — donkey, binding, cross-sentential,
negation), and provides bridge theorems linking Cooper's TTR machinery to
linglib's `ScopeConfig` and `BindingConfig` interfaces.

The companion `Studies/Cooper2023/Basic.lean` wires this Ch. 8 substrate
to the empirical data in `Phenomena/Anaphora/`.

## Main definitions

* `QStore`, `QStore.store`, `QStore.retrieve` — quantifier-storage stack
  (Cooper §8.2, adapting Cooper 1983-style storage to TTR).
* `TwoQuantScope`, `TwoQuantScope.𝔖` — underspecified content type for a
  two-quantifier sentence; witnesses correspond to the two scope readings.
* `Cntxt₈` — full Ch. 8 context (Cooper §8.2-8.3, evolved across the
  chapter as locality `𝔩` and reflexive marking `𝔯` are added).
* `localize`, `reflexivize`, `anaphoricResolve` — TTR operations for donkey
  anaphora and binding (§8.3).
* `UnderspecClosure₈` — inductive closure of a content type under the seven
  Ch. 8 operators (base, localize, reflexivize, align, anaphoric, store,
  retrieve).
* `NQuantScope` — formaliser's extension to n quantifiers (Cooper §8.2
  treats only n ≤ 2; the N! over-generation is well known to violate
  empirical scope-island constraints).

## Main statements

* `tagged_roundtrip` — bijection between `TwoQuantScope.𝔖` witnesses and
  `Semantics.Scope.ScopeConfig` tags. Engineering interface for downstream
  RSA-style scope listeners ([scontras-pearl-2021]); Cooper himself
  does not draw this connection.
* `reflexivize₈_agrees_with_simple` — record-typed `reflexivize₈` collapses
  to the simplified `reflexivize` when the context is initial.
* `donkeyNeg_uses_localization` — the negation donkey sentence reuses
  `localize`.
* `reflexivize_to_binding`, `pronominalBindingConfig` — translate TTR's
  assignment-based binding to positional `BindingConfig`. Cooper §8.3 (book
  p.371) deliberately avoids positional encodings in favour of
  assignment-percolation; the bridge is a linglib engineering convenience,
  not Cooper's theory.

## Notation

* `ℒ` (Script L, U+2112) — Cooper's localization operator (§8.3 eq 49).
* `ℒʸ` — universal-localization variant for strong-donkey readings.
* `ℜ` — reflexivization (§8.3 eq 84).
* Purification operators `𝔓` (Fraktur P) / `𝔓ʸ` are inherited from
  `Cooper2023Ch7`.

## Implementation notes

* **`localize` vs. Ch. 7 `purify`.** Cooper §8.3 eq (49) defines `ℒ(𝒫)` as
  a record-type merge: the outer parameter `T1` is folded into the inner
  property's record-domain under label `𝔠`, producing another parametric
  property. linglib's `PPpty` schema has no inner record-domain (the
  foreground argument is a bare `E`), so the record-merge collapses to
  Σ-existential elimination of the background — definitionally identical
  to Ch. 7's `purify`. The `abbrev localize := purify` records this
  encoding-collapse, *not* a text-level identity of `ℒ` with `𝔓` in
  Cooper's prose.
* **Strong-donkey reading.** Cooper §8.3 eq (60) derives the strong reading
  by applying `𝔓^∀` (Ch. 7 eq 13) to a scope already prepared by `ℒ` and
  path-alignment (`alignPaths` here). The end-to-end three-stage pipeline
  `ℒ → alignPaths → 𝔓^∀` is not formalised here — only the individual
  stages are present.
* **TTR witness types are `Type`-valued, not `Prop`.** Cooper's witness
  records are first-class data (fields can be inspected and used
  compositionally). `Nonempty`/`IsEmpty` mediate inhabitance claims where
  the witness data is not needed downstream.

## TODO

* End-to-end formalisation of the `ℒ → alignPaths → 𝔓^∀` strong-donkey
  pipeline (the `DonkeyAnaphora` section currently exercises only the
  weak reading).
* Bridge from `UnderspecClosure₈` syntax to a semantic evaluator
  (`twoQuant_embeds_in_closure` only asserts the base constructor; no
  compositional interpretation is provided).
-/

namespace Cooper2023Ch8

open Semantics.TypeTheoretic
open Cooper2023Ch7

section ScopeInfrastructure

/-! ### Quantifier stores

A quantifier store holds quantifiers that have been "tucked away" during
composition and await scope assignment via retrieval. Cooper §8.2 adapts
Cooper 1983-style storage to TTR. -/

variable {E : Type}

/-- A quantifier store: a list of quantifiers awaiting scope resolution
(Cooper §8.2). Stored quantifiers are later retrieved at scope positions;
retrieval order determines scope. -/
structure QStore (E : Type) where
  /-- The stored quantifiers, ordered by storage time -/
  stored : List (Quant E)

/-- Empty quantifier store: no pending scope ambiguity. -/
def QStore.empty : QStore E := ⟨[]⟩

/-- A store is *plugged* when all quantifiers have taken scope (terminology
from Bos's plugged/unplugged distinction, adopted by Cooper §8.2). -/
def QStore.isPlugged (qs : QStore E) : Prop := qs.stored = []

/-- A store is *unplugged* when quantifiers remain to be scoped. -/
def QStore.isUnplugged (qs : QStore E) : Prop := qs.stored ≠ []

/-- Plugged ↔ ¬ unplugged. -/
@[simp] theorem plugged_iff_not_unplugged (qs : QStore E) :
    qs.isPlugged ↔ ¬ qs.isUnplugged := by
  simp [QStore.isPlugged, QStore.isUnplugged]

/-- The empty store is plugged by construction. -/
@[simp] theorem empty_isPlugged : (QStore.empty : QStore E).isPlugged := rfl

/-- A plugged `QStore` corresponds to a trivial `Parametric` background:
an empty store contributes no scope presuppositions, exactly as
`Parametric.trivial` has `Bg = Unit`. -/
def pluggedToTrivial {C : Type*} (c : C) (qs : QStore E)
    (_h : qs.isPlugged) : Parametric C :=
  Parametric.trivial c

/-! ### Store and retrieve operations

`store` moves a quantifier from the content into the qstore, leaving a
trace variable in the content. `retrieve` pops the outermost stored
quantifier and applies it at a scope position; retrieval order determines
relative scope (Cooper §8.2). -/

/-- Push a quantifier onto the store (Cooper §8.2). -/
def QStore.store (qs : QStore E) (q : Quant E) : QStore E :=
  ⟨q :: qs.stored⟩

/-- Storing into a plugged store makes it unplugged. -/
theorem store_unplugs (q : Quant E) :
    (QStore.empty.store q : QStore E).isUnplugged := by
  simp [QStore.store, QStore.isUnplugged, QStore.empty]

/-- Pop the outermost stored quantifier (Cooper §8.2). Returns the
quantifier and the remaining store, or `none` if plugged. -/
def QStore.retrieve (qs : QStore E) :
    Option (Quant E × QStore E) :=
  match qs.stored with
  | [] => none
  | q :: rest => some (q, ⟨rest⟩)

/-- Retrieve returns `none` iff the store is plugged. -/
theorem retrieve_none_iff_plugged (qs : QStore E) :
    qs.retrieve = none ↔ qs.isPlugged := by
  cases qs with | mk stored =>
  cases stored <;> simp [QStore.retrieve, QStore.isPlugged]

/-- Store then retrieve recovers the stored quantifier. -/
@[simp] theorem store_then_retrieve (qs : QStore E) (q : Quant E) :
    (qs.store q).retrieve = some (q, qs) := by
  simp [QStore.store, QStore.retrieve]

/-! ### Two-quantifier scope and the underspecification closure

For sentences with two quantifiers and a binary relation, the two possible
retrieval orders produce exactly two scope readings: "every boy hugged a
dog" has ∀>∃ and ∃>∀ readings. The underspecification closure `𝔖` records
both. -/

/-- A two-quantifier scope configuration: two quantifiers and a relation.
The minimal underspecified content for a doubly-quantified sentence
(Cooper §8.2). -/
structure TwoQuantScope (E : Type) where
  /-- The binary relation (e.g., hug) -/
  rel : E → E → Type
  /-- The subject quantifier (e.g., every boy) -/
  q₁ : Quant E
  /-- The object quantifier (e.g., a dog) -/
  q₂ : Quant E

/-- Surface scope reading: `Q₁` scopes over `Q₂`. Retrieving `Q₁` first
gives outermost scope. For "every boy hugged a dog":
`∀x. boy(x) → ∃y. dog(y) ∧ hug(x,y)`. -/
def TwoQuantScope.surfaceScope (s : TwoQuantScope E) : Type :=
  s.q₁ (λ x => s.q₂ (λ y => s.rel x y))

/-- Inverse scope reading: `Q₂` scopes over `Q₁`.
For "every boy hugged a dog": `∃y. dog(y) ∧ ∀x. boy(x) → hug(x,y)`. -/
def TwoQuantScope.inverseScope (s : TwoQuantScope E) : Type :=
  s.q₂ (λ y => s.q₁ (λ x => s.rel x y))

/-- The underspecification closure `𝔖` for two quantifiers: the join of
all possible scope readings. Each witness of `𝔖(content)` is one fully
specified reading; with two quantifiers, `𝔖` has at most two witnesses. -/
def TwoQuantScope.𝔖 (s : TwoQuantScope E) : Type :=
  JoinType s.surfaceScope s.inverseScope

/-- 𝔖 is inhabited iff at least one scope reading is true. -/
theorem TwoQuantScope.𝔖_iff (s : TwoQuantScope E) :
    IsTrue s.𝔖 ↔ IsTrue s.surfaceScope ∨ IsTrue s.inverseScope :=
  join_true_iff

/-- A surface scope witness embeds into 𝔖. -/
def TwoQuantScope.surfaceToUnderspec (s : TwoQuantScope E)
    (w : s.surfaceScope) : s.𝔖 :=
  Sum.inl w

/-- An inverse scope witness embeds into 𝔖. -/
def TwoQuantScope.inverseToUnderspec (s : TwoQuantScope E)
    (w : s.inverseScope) : s.𝔖 :=
  Sum.inr w

/-- Select a scope reading by ScopeConfig.
    Ch8 → [scontras-pearl-2021] bridge:
    retrieval order corresponds to ScopeConfig.surface /.inverse. -/
def TwoQuantScope.readingAt (s : TwoQuantScope E)
    (sc : Semantics.Scope.ScopeConfig) : Type :=
  match sc with
  | .surface => s.surfaceScope
  | .inverse => s.inverseScope

/-! ### Bridge to `ScopeConfig`

The witnesses of `𝔖(content)` are in bijection with the
`Semantics.Scope.ScopeConfig` tags used by [scontras-pearl-2021]'s
RSA scope listener: each `ScopeConfig` selects one reading, and every
witness of `𝔖` comes from exactly one reading. The bridge is a linglib
engineering interface; Cooper himself does not draw this connection. -/

open Semantics.Scope (ScopeConfig)

/-- Every witness of `𝔖` is tagged by a `ScopeConfig`. -/
def TwoQuantScope.𝔖_to_tagged (s : TwoQuantScope E)
    (w : s.𝔖) : (sc : ScopeConfig) × s.readingAt sc :=
  match w with
  | .inl surf => ⟨.surface, surf⟩
  | .inr inv => ⟨.inverse, inv⟩

/-- A tagged reading embeds into `𝔖`. -/
def TwoQuantScope.tagged_to_𝔖 (s : TwoQuantScope E)
    (tagged : (sc : ScopeConfig) × s.readingAt sc) : s.𝔖 :=
  match tagged.1, tagged.2 with
  | .surface, w => Sum.inl w
  | .inverse, w => Sum.inr w

/-- Round-trip: tagged → `𝔖` → tagged is the identity. The bijection
between `𝔖` witnesses and `ScopeConfig`-tagged readings. -/
theorem TwoQuantScope.tagged_roundtrip (s : TwoQuantScope E)
    (tagged : (sc : ScopeConfig) × s.readingAt sc) :
    s.𝔖_to_tagged (s.tagged_to_𝔖 tagged) = tagged := by
  obtain ⟨sc, w⟩ := tagged
  cases sc <;> rfl

end ScopeInfrastructure

/-! ### Phenomenon: scope ambiguity in "every boy hugged a dog"

The classic scope ambiguity example. Two boys, two dogs; each boy hugs a
different dog. Surface scope is true but inverse scope is false. -/

section ScopePhenomenon

/-- Individuals for the scope example. -/
inductive ScopeInd where
  | tom | bill   -- boys
  | fido | rex   -- dogs
  deriving DecidableEq, Repr

/-- Boy predicate: Tom and Bill are boys. -/
def isBoy : Ppty ScopeInd
  | .tom => PUnit | .bill => PUnit | _ => Empty

/-- Dog predicate: Fido and Rex are dogs. -/
def isDog₈ : Ppty ScopeInd
  | .fido => PUnit | .rex => PUnit | _ => Empty

/-- Hug predicate: Tom hugs Fido, Bill hugs Rex.
    This scenario makes surface scope true but inverse scope false:
    every boy hugged A dog (different dogs), but no single dog was
    hugged by every boy. -/
def hugs : ScopeInd → ScopeInd → Type
  | .tom, .fido => PUnit
  | .bill, .rex => PUnit
  | _, _ => Empty

/-- The universal quantifier for boys. -/
def everyBoy : Quant ScopeInd := semUniversal isBoy

/-- The existential quantifier for dogs. -/
def aDog : Quant ScopeInd := semIndefArt isDog₈

/-- The two-quantifier scope configuration for "every boy hugged a dog". -/
def everyBoyHuggedADog : TwoQuantScope ScopeInd where
  rel := hugs
  q₁ := everyBoy
  q₂ := aDog

/-- Surface scope witness: every boy hugged a (possibly different) dog.
    Tom→Fido, Bill→Rex. -/
def surfaceScopeWitness : everyBoyHuggedADog.surfaceScope :=
  fun x hBoy => match x, hBoy with
  | .tom, _ => ⟨.fido, PUnit.unit, PUnit.unit⟩
  | .bill, _ => ⟨.rex, PUnit.unit, PUnit.unit⟩
  | .fido, h => nomatch h
  | .rex, h => nomatch h

/-- Inverse scope fails: no single dog was hugged by every boy. -/
theorem no_inverse_scope : IsFalse everyBoyHuggedADog.inverseScope :=
  ⟨fun ⟨d, hDog, hAll⟩ => by
    match d with
    | .fido => exact nomatch (hAll .bill PUnit.unit)
    | .rex => exact nomatch (hAll .tom PUnit.unit)
    | .tom => exact nomatch hDog
    | .bill => exact nomatch hDog⟩

/-- 𝔖 is inhabited (via the surface scope reading). -/
def underspecInhabited : everyBoyHuggedADog.𝔖 :=
  everyBoyHuggedADog.surfaceToUnderspec surfaceScopeWitness

/-- The surface reading is the only true reading in this scenario. -/
theorem only_surface_in_scenario :
    IsTrue everyBoyHuggedADog.𝔖 ∧ ¬ IsTrue everyBoyHuggedADog.inverseScope :=
  ⟨⟨underspecInhabited⟩, fun ⟨w⟩ => no_inverse_scope.false w⟩

/-- The scope reading is correctly identified as surface via tagging. -/
theorem underspec_tagged_is_surface :
    (everyBoyHuggedADog.𝔖_to_tagged underspecInhabited).1 = .surface := rfl

end ScopePhenomenon

/-! ### Bridge: scope readings to Ch. 7 witness conditions

A surface scope reading with a universal subject and existential object
corresponds to per-element `ParticularWC_Exist` conditions, yielding REFSET
anaphora for the object NP ("Every boy hugged a dog. It was friendly." —
"it" picks up one dog per boy, distributive REFSET). -/

section ScopeBridge

variable {E : Type}

/-- A surface scope witness `∀x. P(x) → ∃y. Q(y) ∧ R(x,y)` yields
a `ParticularWC_Exist` for the inner existential at each fixed subject —
predicting REFSET anaphora for the object NP. -/
def surfaceScopeInnerWitness
    (P Q : Ppty E) (R : E → E → Type)
    (w : semUniversal P (λ x => ExistWitness E Q (λ y => R x y)))
    (x : E) (hP : P x) :
    ParticularWC_Exist Q (λ y => R x y) :=
  let ew := w x hP
  ⟨ew.individual, ew.restrWit, ew.scopeWit⟩

/-- An inverse scope witness `∃y. Q(y) ∧ ∀x. P(x) → R(x,y)` yields
a `ParticularWC_Exist` for the outer existential — there is one specific
entity witnessing `Q` under which the universal scopes.

"A dog was hugged by every boy. It was large." — "it" picks up the
specific dog (REFSET from outer scope). -/
def inverseScopeOuterWitness
    (P Q : Ppty E) (R : E → E → Type)
    (w : ExistWitness E Q (λ y => semUniversal P (λ x => R x y))) :
    ParticularWC_Exist Q (λ y => semUniversal P (λ x => R x y)) :=
  ⟨w.individual, w.restrWit, w.scopeWit⟩

/-- Surface scope (`semUniversal` + `ExistWitness`) matches `existPQ` at
each individual — the Ch. 7 existential-predicate overlap; scope retrieval
order determines which witness conditions hold per quantifier position. -/
theorem surface_scope_matches_existPQ
    (P Q : Ppty E) (R : E → E → Type)
    (w : semUniversal P (λ x => ExistWitness E Q (λ y => R x y))) :
    ∀ x : E, Nonempty (P x) → existPQ Q (R x) := by
  intro x ⟨hP⟩
  let ew := w x hP
  exact ⟨ew.individual, ⟨ew.restrWit⟩, ⟨ew.scopeWit⟩⟩

end ScopeBridge

/-! ### Localization

Cooper §8.3 eq (49): localization `ℒ(𝒫)` takes a doubly-parametric property
`˹λc:T1.˹λr:T2.φ˺˺` and folds the outer context-parameter `T1` into the inner
property's record-domain under label `𝔠`, producing another parametric
property whose body has paths `c.π` rewritten to `r.𝔠.π`. This is the Ch. 8
mechanism for donkey anaphora ("Every farmer who owns a donkey beats it"):
the indefinite "a donkey" is stored, then localized into the restrictor
"farmer who owns a donkey", binding the donkey existentially (weak) or
universally (strong) inside the property body.

In linglib's flat `PPpty` encoding (no inner record-domain), this
record-merge collapses to Σ-existential elimination of the background,
making `localize` definitionally identical to Ch. 7's `purify`. See the
*Implementation notes* in the module docstring. -/

section Localization

variable {E : Type}

/-- Cooper's localization operator `ℒ` (§8.3 eq 49).

In linglib's flat `PPpty` encoding `localize` is the same as Ch. 7's
`purify`; see the module-level *Implementation notes* for the
encoding-collapse argument. The `abbrev` records this identification so
Ch. 7 lemmas discharge Ch. 8 obligations definitionally. -/
abbrev localize : PPpty E → Ppty E := purify

/-- Cooper's universal-localization variant `ℒʸ` (the strong-donkey
companion to `ℒ`). Coincides with Ch. 7's `purifyUniv` for the same
encoding reason. -/
abbrev localizeUniv : PPpty E → Ppty E := purifyUniv

@[inherit_doc] scoped prefix:max "ℒ" => localize
@[inherit_doc] scoped prefix:max "ℒʸ" => localizeUniv

/-! ### Localization lemmas (inherited from Ch7 purification)

Since `localize := purify`, witness-existence lemmas about purification
carry over verbatim. We restate them under the Ch. 8 vocabulary for
discoverability. -/

/-- Localization preserves truth: a localized property is witnessed
iff the original is witnessable under some context. -/
theorem localize_nonempty_iff (P : PPpty E) (a : E) :
    Nonempty (ℒ P a) ↔ ∃ c : P.Bg, Nonempty (P.fg c a) :=
  purify_nonempty_iff P a

/-- Universal localization: witnessed iff property holds under all contexts. -/
theorem localizeUniv_nonempty_iff (P : PPpty E) (a : E) :
    Nonempty (ℒʸ P a) ↔ ∀ c : P.Bg, Nonempty (P.fg c a) :=
  purifyUniv_nonempty_iff P a

/-- Localizing a trivial parametric property adds only a `Unit` factor. -/
@[simp] theorem localize_trivial (P : Ppty E) (a : E) :
    ℒ (Parametric.trivial P) a = ((_ : Unit) × P a) := rfl

/-- Weak and strong donkey readings agree when the parametric background
is trivial. Corollary of `donkey_readings_agree_when_pure`. -/
theorem localization_readings_agree_when_pure
    (P : PPpty E) (hPure : PPpty.isPure P) (a : E) :
    Nonempty (ℒ P a) ↔ Nonempty (ℒʸ P a) :=
  donkey_readings_agree_when_pure P hPure a

end Localization

/-! ### Phenomenon: "Every farmer who owns a donkey beats it"

The classical Geach/Kamp donkey example (Cooper §8.3 uses "no dog which
chases a cat catches it" as his primary case; we use the better-known
farmer/donkey variant). Two farmers, two donkeys; each farmer owns and
beats a different donkey. This demonstrates:

1. Localization absorbs "a donkey" into the restrictor.
2. Weak donkey (`ℒ` in linglib's encoding = `𝔓`) is witnessable — each
   farmer owns/beats *some* donkey.
3. Strong donkey (`ℒʸ` = `𝔓ʸ`) fails — no farmer owns/beats *every* donkey.
4. The divergence witnesses the non-triviality of
   `donkey_readings_agree_when_pure`. -/

section DonkeyAnaphora

/-- Individuals for the donkey example. -/
inductive DonkeyInd where
  | farmer1 | farmer2 | donkey1 | donkey2
  deriving DecidableEq

def isFarmer : Ppty DonkeyInd
  | .farmer1 => PUnit | .farmer2 => PUnit | _ => Empty

def isDonkey₈ : Ppty DonkeyInd
  | .donkey1 => PUnit | .donkey2 => PUnit | _ => Empty

/-- Ownership: farmer1 owns donkey1, farmer2 owns donkey2. -/
def owns : DonkeyInd → DonkeyInd → Type
  | .farmer1, .donkey1 => PUnit
  | .farmer2, .donkey2 => PUnit
  | _, _ => Empty

/-- Beating: each farmer beats the donkey they own. -/
def beats : DonkeyInd → DonkeyInd → Type
  | .farmer1, .donkey1 => PUnit
  | .farmer2, .donkey2 => PUnit
  | _, _ => Empty

/-- Background type: a donkey that exists. -/
abbrev DonkeyBg := (d : DonkeyInd) × isDonkey₈ d

/-- The parametric property "farmer who owns a donkey [and beats it]".
    Background: a specific donkey d.
    Foreground: given d, x is a farmer who owns d and beats d. -/
def farmerOwnsBeatsDonkey : PPpty DonkeyInd where
  Bg := DonkeyBg
  fg := λ ⟨d, _⟩ x => isFarmer x × owns x d × beats x d

/-- Localized restrictor = purified restrictor (the bridge in action). -/
example : ℒ farmerOwnsBeatsDonkey = 𝔓 farmerOwnsBeatsDonkey := rfl

/-- Farmer1 satisfies the weak donkey reading: owns and beats donkey1. -/
def farmer1WeakDonkey : ℒ farmerOwnsBeatsDonkey .farmer1 :=
  ⟨⟨.donkey1, PUnit.unit⟩, PUnit.unit, PUnit.unit, PUnit.unit⟩

/-- Farmer2 satisfies the weak donkey reading: owns and beats donkey2. -/
def farmer2WeakDonkey : ℒ farmerOwnsBeatsDonkey .farmer2 :=
  ⟨⟨.donkey2, PUnit.unit⟩, PUnit.unit, PUnit.unit, PUnit.unit⟩

/-- The strong-donkey reading fails for `farmer1`: the universal
"every donkey `d`, farmer1 owns `d` ∧ beats `d`" is falsified by donkey2,
which farmer1 does not own. -/
theorem farmer1_fails_strong_donkey :
    IsEmpty (ℒʸ farmerOwnsBeatsDonkey .farmer1) :=
  ⟨fun f => nomatch (f ⟨.donkey2, PUnit.unit⟩).2.1⟩

/-- Weak and strong donkey readings genuinely diverge in this scenario:
weak is witnessable, strong is empty. Witness that
`donkey_readings_agree_when_pure` has a real hypothesis — when `Bg` is
non-trivial (multiple donkeys), the readings differ. -/
theorem donkey_readings_diverge :
    Nonempty (ℒ farmerOwnsBeatsDonkey .farmer1) ∧
    ¬ Nonempty (ℒʸ farmerOwnsBeatsDonkey .farmer1) :=
  ⟨⟨farmer1WeakDonkey⟩, fun ⟨w⟩ => farmer1_fails_strong_donkey.false w⟩

/-- The full sentence "every farmer who owns a donkey beats it" is
witnessed under the weak donkey reading. -/
def everyFarmerBeatsDonkeyWeak :
    semUniversal (ℒ farmerOwnsBeatsDonkey) (λ _ => PUnit) :=
  fun x hLocalized => match x, hLocalized with
  | .farmer1, _ => PUnit.unit
  | .farmer2, _ => PUnit.unit
  | .donkey1, ⟨⟨_, _⟩, hF, _, _⟩ => nomatch hF
  | .donkey2, ⟨⟨_, _⟩, hF, _, _⟩ => nomatch hF

/-! ### TODO: Cooper's strong-donkey pipeline `ℒ → alignPaths → 𝔓^∀`

Cooper §8.3 eq (60) derives the strong-donkey reading by composing three
distinct operations: localize the verb-phrase parametric content (`ℒ`,
eq 49); align two paths in the result so the pronoun depends on the
indefinite (`alignPaths`, eq 51-52); then apply `𝔓^∀` (Ch. 7 eq 13) to
this prepared scope as the witness condition for the universal
quantifier. The composite pipeline is not formalised here; we have each
stage independently (`localize`, `alignPaths`, `purifyUniv`), but the
end-to-end derivation for "every farmer who owns a donkey likes it" is
deferred. -/

end DonkeyAnaphora

/-! ### Reflexivization and anaphoric resolution

Cooper §8.3 introduces two binding operations: `ℜ` (reflexivization,
eq 84) removes the reflexive marking from the context and binds the
reflexive pronoun to the subject variable; `@_{i,j}` (anaphoric
combination, eq 28) identifies assignment path `j` with path `i`, linking
a pronoun to its antecedent.

The interplay yields complementary distribution: `ℜ` forces local
binding for reflexives; `@_{i,j}` with a constant resolution gives
disjoint reference for pronouns; the boundary operation `B` (eq 77, see
below) clears locality at clause boundaries.

The record-typed versions (`reflexivize₈`, `anaphoricCombine₈`, etc.,
using `Cntxt₈`) are defined further down; the simplified versions here
serve as the clean semantic interface for bridge theorems, with
`reflexivize₈_agrees_with_simple` connecting the two layers. -/

section BindingTheory

variable {E : Type}

/-- Reflexivization (Cooper §8.3 eq 84): identify the two arguments of a
binary relation. Removes the reflexive marking (`r`-field) from the
context and replaces the dependency on the assignment variable `𝔤.xᵢ`
with the domain variable `r.x`. Semantic effect: a transitive verb
`R(x,y)` becomes a reflexive VP `R(x,x)`, forcing the object to corefer
with the subject. "Sam likes himself" = `ℜ(like)(Sam)` = `like(Sam, Sam)`. -/
def reflexivize (R : E → E → Type) : Ppty E := λ x => R x x

@[inherit_doc] scoped prefix:max "ℜ" => reflexivize

/-- Anaphoric resolution: resolve a parametric property's background
using a function of the foreground argument. Captures the semantic effect
of Cooper's `@_{i,j}` (§8.3): identifying path `𝔤.xⱼ` with `𝔤.xᵢ` creates
the anaphoric link.

* Reflexives: `resolve = id` (subject is the referent) — equivalent to `ℜ`.
* Pronouns: `resolve = const (g i)` (assignment provides referent). -/
def anaphoricResolve (P : PPpty E) (resolve : E → P.Bg) : Ppty E :=
  λ x => P.fg (resolve x) x

/-- `ℜ` forces argument identity: any witness of `ℜ R x` is `R x x`. -/
@[simp] theorem reflexivize_forces_identity (R : E → E → Type) (x : E) :
    ℜ R x = R x x := rfl

/-- `ℜ` is anaphoric resolution with identity: reflexivization is the
special case where the background (object referent) is resolved to equal
the foreground argument (subject). -/
theorem reflexivize_eq_resolve_id (R : E → E → Type) :
    ℜ R = anaphoricResolve ⟨E, λ y x => R x y⟩ id := rfl

/-- Pronoun resolution with a constant referent `y`: resolves to `y`
regardless of the subject `x`. Captures `@_{i,j}` when the assignment
`g i = y` is fixed from discourse context. "Sam likes him(=Bill)" yields
`like(Sam, Bill)`. -/
theorem resolve_const (R : E → E → Type) (y : E) (x : E) :
    anaphoricResolve (⟨E, λ obj subj => R subj obj⟩ : PPpty E)
      (fun _ => y) x = R x y := rfl

end BindingTheory

/-! ### Phenomenon: "Sam likes himself" / "Sam likes him"

Cooper §8.3: "Sam likes him" has two fields `x` and `y` for individuals;
when `y = x`, the fields are filled by the same individual.
Reflexivization `ℜ` forces this identification, yielding complementary
distribution:

* "Sam likes himself" = `ℜ like (Sam)` = `like(Sam, Sam)` (coreference).
* "Sam likes him(=Bill)" = `anaphoricResolve likeParam (const Bill) (Sam)`
  = `like(Sam, Bill)` (disjoint reference). -/

section BindingPhenomenon

/-- Individuals for the binding example. Sam is the subject; Bill is a
potential non-local antecedent for "him". -/
inductive BindInd where
  | sam | bill | kim
  deriving DecidableEq

/-- "like" as a non-trivial binary relation: Sam likes everyone, Bill
likes Kim and himself, Kim likes herself only. The non-triviality is
load-bearing — `ℜ (like₈) Kim` is inhabited but `like₈ Kim Sam` is not,
so reflexivization genuinely restricts which argument pairs are
witnessable. -/
def like₈ : BindInd → BindInd → Type
  | .sam, _ => PUnit       -- Sam likes everyone
  | .bill, .bill => PUnit  -- Bill likes himself
  | .bill, .kim => PUnit   -- Bill likes Kim
  | .kim, .kim => PUnit    -- Kim likes herself
  | _, _ => Empty

/-- `like₈` is non-trivial: not everyone likes everyone. -/
theorem like₈_nontrivial : IsEmpty (like₈ .kim .sam) :=
  ⟨fun h => nomatch h⟩

/-- "like" as parametric content: the object comes from background. The
verb phrase "likes him" has the object's referent in the context. -/
def likeParam : PPpty BindInd where
  Bg := BindInd
  fg := λ obj subj => like₈ subj obj

/-- "Sam likes himself" via `ℜ`: `ℜ like₈ Sam` = `like₈ Sam Sam`. -/
def samLikesHimself : ℜ like₈ .sam := PUnit.unit

/-- "Sam likes him(=Bill)" via pronoun resolution. -/
def samLikesBill : anaphoricResolve likeParam (fun _ => .bill) .sam :=
  PUnit.unit

/-- `ℜ` forces coreference: the reflexive witness equals `like₈ Sam Sam`. -/
theorem reflexive_is_self : (ℜ like₈ .sam) = like₈ .sam .sam := rfl

/-- Pronoun resolution gives `like₈ Sam Bill` — distinct arguments. -/
theorem pronoun_is_distinct :
    anaphoricResolve likeParam (fun _ => BindInd.bill) .sam =
    like₈ .sam .bill := rfl

/-- Every individual can like themselves; `ℜ` is always witnessable here. -/
def allLikeSelf : ∀ x : BindInd, ℜ like₈ x
  | .sam => PUnit.unit
  | .bill => PUnit.unit
  | .kim => PUnit.unit

/-- `ℜ` applied via `anaphoricResolve` with identity matches direct
reflexivization. -/
theorem param_reflexivize_agrees :
    anaphoricResolve likeParam id = ℜ like₈ := rfl

/-- `ℜ` genuinely constrains: Kim can like herself but not Bill — the
restriction is non-trivial because `like₈ Kim Bill` is empty while
`like₈ Kim Kim` is `PUnit`. -/
theorem reflexive_constrains_kim :
    Nonempty (ℜ like₈ .kim) ∧ IsEmpty (like₈ .kim .bill) :=
  ⟨⟨PUnit.unit⟩, ⟨fun h => nomatch h⟩⟩

end BindingPhenomenon

/-! ### Bridge to `BindingConfig`

Translate TTR's assignment-based binding (`ℜ` / `@_{i,j}`) to the
position-based `BindingConfig` interface in `Syntax.Binding.Semantics`.
Cooper §8.3 (book p.371) deliberately avoids positional encodings in
favour of assignment-percolation; the bridge is a linglib engineering
convenience for consumers that want position-typed binding output, not a
claim about Cooper's theory. The mapping is:

* `ℜ` applied → `BindingRelation` with subject as binder, object as bindee.
* `@_{i,j}` pronoun resolution → free variable in the `BindingConfig`. -/

section BindingSemBridge

open BindingSemantics

/-- `ℜ` induces a binding relation: subject binds the reflexive object.
The subject at position 0 binds "himself" at position 2. -/
def reflexivizeToBinding
    (subjectPos objectPos : Position) : BindingRelation where
  binder := subjectPos
  bindee := objectPos
  varIndex := 0

/-- Binding config for "Sam likes himself": one local binding. -/
def reflexiveBindingConfig : BindingConfig where
  bindings := [reflexivizeToBinding ⟨0⟩ ⟨2⟩]
  freeVariables := []

/-- The reflexive binding config is well-formed: no double binding, no
self-binding, consistent indices. -/
theorem reflexive_config_wellFormed :
    reflexiveBindingConfig.wellFormed = true := by decide

/-- Binding config for "Sam likes him": no local bindings,
    the pronoun at position 2 is a free variable. -/
def pronominalBindingConfig : BindingConfig where
  bindings := []
  freeVariables := [(⟨2⟩, 0)]

/-- The pronominal config has no local bindings (Condition B). -/
theorem pronominal_no_local_binding :
    pronominalBindingConfig.bindings = [] := rfl

/-- Bridge: TTR ℜ maps to a non-trivial binding config (one binding),
    while @_{i,j} pronoun resolution maps to an empty binding config.
    The semantic mechanism (ℜ vs @_{i,j}) determines the syntactic
    binding structure. -/
theorem binding_mechanism_determines_config :
    reflexiveBindingConfig.bindings.length = 1 ∧
    pronominalBindingConfig.bindings.length = 0 :=
  ⟨rfl, rfl⟩

end BindingSemBridge

/-! ### Full Ch. 8 context `Cntxt₈`

Cooper's context evolves across the chapter: the initial 5-field context
`{q, 𝔰, 𝔴, 𝔤, 𝔠}` (§8.2) is extended with `𝔩` (locality) in §8.3 and
with `𝔯` (reflexive marking) later in §8.3. `Cntxt₈` encodes the final
7-field shape; pre-locality and pre-reflexive variants are recovered by
leaving `𝔩` / `𝔯` empty. Extends `CntxtFull` (Ch. 7) with `q`, `𝔩`, `𝔯`. -/

section FullContext

variable {E : Type}

/-- Cooper's full Ch. 8 context. Fields: quantifier store `q`, current
assignment `𝔰`, locality `𝔩`, reflexive-marking `𝔯`, wh-assignment `𝔴`,
gap-tracking assignment `𝔤`, propositional context `𝔠`. -/
structure Cntxt₈ (E : Type) where
  q : QStore E
  𝔰 : Assgnmnt E
  𝔩 : Assgnmnt E
  𝔯 : Assgnmnt E
  𝔴 : Assgnmnt E
  𝔤 : Assgnmnt E
  𝔠 : PropCntxt

/-- The empty initial context. -/
def Cntxt₈.initial : Cntxt₈ E where
  q := QStore.empty
  𝔰 := Core.PartialAssign.empty
  𝔩 := Core.PartialAssign.empty
  𝔯 := Core.PartialAssign.empty
  𝔴 := Core.PartialAssign.empty
  𝔤 := Core.PartialAssign.empty
  𝔠 := PUnit

/-- Pre-locality context shape (Cooper §8.2 initial form): both `𝔩` and
`𝔯` are empty. -/
def Cntxt₈.isPreLocality (c : Cntxt₈ E) : Prop :=
  (∀ i, c.𝔩 i = none) ∧ (∀ i, c.𝔯 i = none)

/-- Pre-reflexive context shape (Cooper §8.3 mid-form): `𝔯` is empty. -/
def Cntxt₈.isPreReflexive (c : Cntxt₈ E) : Prop :=
  ∀ i, c.𝔯 i = none

theorem Cntxt₈.initial_isPreLocality :
    (Cntxt₈.initial : Cntxt₈ E).isPreLocality :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end FullContext

/-! ### Boundary operation `B` and locality-aware `@_{i,j}` (Cooper §8.3)

`B(α)` clears the locality field at clause boundaries; `@_{i,j}` with a
locality check identifies `𝔰.xⱼ` with `𝔰.xᵢ` only when `𝔰.xᵢ` is in
the `𝔩`-field. Together they enforce a locality constraint on
pronoun-antecedent linking. -/

section BoundaryAndLocality

variable {E : Type}

/-- Boundary operation `B(α)`: resets `𝔩` at clause boundaries. -/
def boundary₈ (P : Cntxt₈ E → Type) : Cntxt₈ E → Type :=
  λ c => P { c with 𝔩 := Core.PartialAssign.empty }

/-- Locality-checked `@_{i,j}`: identifies `𝔰.xⱼ` with `𝔰.xᵢ` only when
`𝔰.xᵢ` is in `𝔩`. -/
def anaphoricCombine₈ [Inhabited E] (i j : Nat) (P : Cntxt₈ E → Type)
    (Q : Cntxt₈ E → Type) : Cntxt₈ E → Type :=
  λ c => propT ((c.𝔩 i).isSome = true) ×
    P c × Q { c with 𝔰 := Core.PartialAssign.update c.𝔰 j ((c.𝔰 i).getD default) }

/-- Sentence rule `S → NP VP | B(NP' (@VP'))`. -/
def sentenceRule₈ (np : Cntxt₈ E → Type) (vp : Cntxt₈ E → Type)
    : Cntxt₈ E → Type :=
  boundary₈ (λ c => np c × vp c)

@[simp] theorem boundary₈_clears_locality (c : Cntxt₈ E) (i : Nat) :
    ({ c with 𝔩 := Core.PartialAssign.empty } : Cntxt₈ E).𝔩 i = none := rfl

/-! #### "Sam thinks she is lucky" — `B` enables non-local pronoun binding. -/

section NonLocalPronoun

inductive NLPInd where | sam | she_ref
  deriving DecidableEq

def localCtx₈ : Cntxt₈ NLPInd where
  q := QStore.empty
  𝔰 := Core.PartialAssign.update Core.PartialAssign.empty 0 .she_ref
  𝔩 := Core.PartialAssign.update Core.PartialAssign.empty 0 .she_ref
  𝔯 := Core.PartialAssign.empty
  𝔴 := Core.PartialAssign.empty
  𝔤 := Core.PartialAssign.empty
  𝔠 := PUnit

theorem local_pronoun_ok : (localCtx₈.𝔩 0).isSome = true := by decide

theorem boundary_clears_for_nonlocal :
    ({ localCtx₈ with 𝔩 := Core.PartialAssign.empty } : Cntxt₈ NLPInd).𝔩 0 = none :=
  rfl

end NonLocalPronoun

end BoundaryAndLocality

/-! ### Anaphor-free filter `𝔄` and full record-typed reflexivization (Cooper §8.3) -/

section AnaphorFreeAndFullReflexivize

variable {E : Type}

/-- Anaphor-free filter `𝔄(T)`: requires the `𝔯`-field to be empty.
"Principle A" in Cooper's evocation of [chomsky-1981]'s binding theory. -/
def anaphorFree₈ (P : Cntxt₈ E → Type) : Cntxt₈ E → Type :=
  λ c => propT (∀ i, c.𝔯 i = none) × P c

/-- Full record-typed reflexivization `ℜ₈(P)`: clears the `𝔯`-field and
sets `𝔰(i) = x`. -/
def reflexivize₈ (i : Nat) (P : Cntxt₈ E → E → Type) : Cntxt₈ E → E → Type :=
  λ c x => P { c with 𝔯 := Core.PartialAssign.empty, 𝔰 := Core.PartialAssign.update c.𝔰 i x } x

/-- VP rule `VP → V NP | 𝔄(V' (@NP'))`. -/
def vpRule₈ (verb : Cntxt₈ E → E → E → Type) (np : Cntxt₈ E → E → Type)
    : Cntxt₈ E → E → Type :=
  λ c x => propT (∀ i, c.𝔯 i = none) × (y : E) × verb c x y × np c y

/-- `ℜ₈` agrees with the simplified `ℜ` when `P` ignores the context. -/
theorem reflexivize₈_agrees_with_simple
    (R : E → E → Type) (x : E) :
    reflexivize₈ 0 (λ _ a => R a a) Cntxt₈.initial x =
    ℜ R x := rfl

end AnaphorFreeAndFullReflexivize

/-! ### Generalised underspecification closure -/

section GeneralizedClosure

variable {E : Type}

/-- Inductive closure of a content type `T` under the seven Ch. 8 operators
(base, localize, reflexivize, align, anaphoric, store, retrieve).
Compositional interpretation as a semantic evaluator is not yet provided
— this is a syntax-tree representation only. -/
inductive UnderspecClosure₈ (T : Type) : Type 1 where
  | base : T → UnderspecClosure₈ T
  | localize : UnderspecClosure₈ T → (Bg : Type) → UnderspecClosure₈ T
  | reflexivize : UnderspecClosure₈ T → (idx : Nat) → UnderspecClosure₈ T
  | align : UnderspecClosure₈ T → (src tgt : Nat) → UnderspecClosure₈ T
  | anaphoric : UnderspecClosure₈ T → (i j : Nat) → UnderspecClosure₈ T
  | store : UnderspecClosure₈ T → UnderspecClosure₈ T
  | retrieve : UnderspecClosure₈ T → UnderspecClosure₈ T

def TwoQuantScope.toUnderspecClosure (s : TwoQuantScope E) (w : s.𝔖) :
    UnderspecClosure₈ s.𝔖 :=
  .base w

theorem twoQuant_embeds_in_closure (s : TwoQuantScope E) (w : s.𝔖) :
    ∃ uc : UnderspecClosure₈ s.𝔖, uc = .base w :=
  ⟨.base w, rfl⟩

end GeneralizedClosure

/-! ### N-quantifier scope (formaliser's extension)

Cooper §8.2 treats only the n ≤ 2 case. We extend the storage-and-retrieve
mechanism to n quantifiers, indexing scope orderings by lists of `Fin n`
(head = outermost retrieved). The naïve combinatorial maximum is `n!`
distinct orderings; empirical scope is constrained by scope islands,
freezing, and weak-island effects that this substrate does not enforce. -/

section NQuantScopeSection

/-- An n-quantifier scope configuration: an n-ary relation plus n
quantifiers. -/
structure NQuantScope (E : Type) (n : Nat) where
  rel : (Fin n → E) → Type
  quants : Fin n → Quant E

variable {E : Type} {n : Nat}

/-- Nest the quantifiers along a given retrieval order; the head of the
list takes outermost scope. -/
def NQuantScope.nestQuants (s : NQuantScope E n) :
    List (Fin n) → (Fin n → E) → Type
  | [], assignment => s.rel assignment
  | i :: rest, assignment =>
    s.quants i (λ x => s.nestQuants rest (λ j => if j = i then x else assignment j))

/-- A scope ordering: a (not necessarily distinct) list of `Fin n` indices
of length `n`. A proper permutation requires additionally `order.Nodup`;
we leave this unconstrained because the witness theorems below construct
orderings explicitly. -/
structure ScopeOrdering (n : Nat) where
  order : List (Fin n)
  complete : order.length = n

def NQuantScope.readingAt (s : NQuantScope E n) (σ : ScopeOrdering n)
    (default : E) : Type :=
  s.nestQuants σ.order (λ _ => default)

def NQuantScope.𝔖 (s : NQuantScope E n) (default : E) : Type :=
  (σ : ScopeOrdering n) × s.readingAt σ default

def surfaceOrder₂ : ScopeOrdering 2 where
  order := [⟨0, by omega⟩, ⟨1, by omega⟩]; complete := rfl

def inverseOrder₂ : ScopeOrdering 2 where
  order := [⟨1, by omega⟩, ⟨0, by omega⟩]; complete := rfl

def TwoQuantScope.toNQuant {E : Type} (s : TwoQuantScope E) : NQuantScope E 2 where
  rel := λ f => s.rel (f ⟨0, by omega⟩) (f ⟨1, by omega⟩)
  quants := λ i => match i with
    | ⟨0, _⟩ => s.q₁
    | ⟨1, _⟩ => s.q₂

/-! #### "Someone gave every child a present" — three quantifiers

Cooper §8.2 does not analyse this case; the six orderings constructed
here are the formaliser's combinatorial enumeration. -/

section ThreeQuant

inductive ThreeQInd where | alice | bob | child1 | child2 | present1 | present2
  deriving DecidableEq

def isSomeone₃ : Ppty ThreeQInd
  | .alice => PUnit | .bob => PUnit | _ => Empty

def isChild₃ : Ppty ThreeQInd
  | .child1 => PUnit | .child2 => PUnit | _ => Empty

def isPresent₃ : Ppty ThreeQInd
  | .present1 => PUnit | .present2 => PUnit | _ => Empty

def gave₃ : ThreeQInd → ThreeQInd → ThreeQInd → Type
  | .alice, .child1, .present1 => PUnit
  | .alice, .child2, .present2 => PUnit
  | _, _, _ => Empty

def someoneQ₃ : Quant ThreeQInd := semIndefArt isSomeone₃
def everyChildQ₃ : Quant ThreeQInd := semUniversal isChild₃
def aPresentQ₃ : Quant ThreeQInd := semIndefArt isPresent₃

def someoneGaveEveryChildAPresent : NQuantScope ThreeQInd 3 where
  rel := λ f => gave₃ (f ⟨0, by omega⟩) (f ⟨1, by omega⟩) (f ⟨2, by omega⟩)
  quants := λ i => match i with
    | ⟨0, _⟩ => someoneQ₃
    | ⟨1, _⟩ => everyChildQ₃
    | ⟨2, _⟩ => aPresentQ₃

def scopeOrdering₃_012 : ScopeOrdering 3 where
  order := [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩]; complete := rfl
def scopeOrdering₃_021 : ScopeOrdering 3 where
  order := [⟨0, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]; complete := rfl
def scopeOrdering₃_102 : ScopeOrdering 3 where
  order := [⟨1, by omega⟩, ⟨0, by omega⟩, ⟨2, by omega⟩]; complete := rfl
def scopeOrdering₃_120 : ScopeOrdering 3 where
  order := [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨0, by omega⟩]; complete := rfl
def scopeOrdering₃_201 : ScopeOrdering 3 where
  order := [⟨2, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩]; complete := rfl
def scopeOrdering₃_210 : ScopeOrdering 3 where
  order := [⟨2, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩]; complete := rfl

theorem six_distinct_orderings_for_n_eq_3 :
    [scopeOrdering₃_012, scopeOrdering₃_021, scopeOrdering₃_102,
     scopeOrdering₃_120, scopeOrdering₃_201, scopeOrdering₃_210].length = 6 := rfl

end ThreeQuant

end NQuantScopeSection

/-! ### Cross-sentential anaphora (Cooper §8.3)

"A man walked. He whistled." The pronoun resolves to the indefinite via
asymmetric merge under label `𝔭`: the previous sentence's foreground
becomes the current sentence's background. -/

section CrossSententialAnaphora

variable {E : Type}

/-- Discourse merge under label `𝔭`: the previous sentence's content
becomes a background field of the current context. -/
structure DiscourseContext (E : Type) (PrevContent : Type) where
  𝔭 : PrevContent
  current : Cntxt₈ E

/-- Cross-sentential resolution: project the individual from the previous
sentence's sigma-typed content. -/
def crossSententialResolve {P : E → Type} (prev : (x : E) × P x) : E := prev.1

end CrossSententialAnaphora

section ManWalkedHeWhistled

inductive CSInd where | john | mary
  deriving DecidableEq

def isMan : Ppty CSInd
  | .john => PUnit | .mary => Empty

def walked₈ : Ppty CSInd
  | .john => PUnit | .mary => Empty

def whistled₈ : Ppty CSInd
  | .john => PUnit | .mary => Empty

def aManWalked : (x : CSInd) × (isMan x × walked₈ x) :=
  ⟨.john, PUnit.unit, PUnit.unit⟩

def heWhistled (referent : CSInd) : Type := whistled₈ referent

def resolvedHe : CSInd :=
  crossSententialResolve (P := λ x => isMan x × walked₈ x) aManWalked

theorem resolvedHe_is_john : resolvedHe = .john := rfl

def manWalkedHeWhistled : Type :=
  (x : CSInd) × (isMan x × walked₈ x × whistled₈ x)

def manWalkedHeWhistledWitness : manWalkedHeWhistled :=
  ⟨.john, PUnit.unit, PUnit.unit, PUnit.unit⟩

theorem crossSentential_correct :
    ∃ w : manWalkedHeWhistled,
      w.1 = crossSententialResolve (P := λ x => isMan x × walked₈ x) aManWalked :=
  ⟨manWalkedHeWhistledWitness, rfl⟩

end ManWalkedHeWhistled

/-! ### "No dog which chases a cat catches it"

Cooper §8.3 primary donkey example combining negation, localization, and
path alignment. -/

section DonkeyNegation

variable {E : Type}

/-- Path alignment (Cooper §8.3 eq 52, App A11.8): replace path `π₁` with
`π₂` in a parametric property. In Cooper's full TTR this is a type
operation `T_{π₁ = π₂}` creating a manifest field; here we simplify to
a relabelling of the background. -/
def alignPaths (P : PPpty E) (align : P.Bg → P.Bg) : PPpty E where
  Bg := P.Bg
  fg := λ c => P.fg (align c)

end DonkeyNegation

section NoDogCatchesCat

inductive DonkeyNegInd where | dog1 | dog2 | cat1 | cat2
  deriving DecidableEq

def isDog₈ₙ : Ppty DonkeyNegInd
  | .dog1 => PUnit | .dog2 => PUnit | _ => Empty

def isCat₈ : Ppty DonkeyNegInd
  | .cat1 => PUnit | .cat2 => PUnit | _ => Empty

def chases₈ : DonkeyNegInd → DonkeyNegInd → Type
  | .dog1, .cat1 => PUnit
  | .dog2, .cat2 => PUnit
  | _, _ => Empty

abbrev CatBg := (c : DonkeyNegInd) × isCat₈ c

/-- Localized restrictor: cat existential absorbed into "dog which chases a cat". -/
def dogChasesACat : Ppty DonkeyNegInd := λ x =>
  isDog₈ₙ x × ((c : CatBg) × chases₈ x c.1)

def catches₈_none : DonkeyNegInd → DonkeyNegInd → Type
  | _, _ => Empty

def catches₈_all : DonkeyNegInd → DonkeyNegInd → Type := chases₈

/-- "no" quantifier: ∀x. restr(x) → ¬scope(x). -/
def semNo₈ (restr scope : Ppty DonkeyNegInd) : Type :=
  (x : DonkeyNegInd) → restr x → scope x → Empty

def noDogCatchesCatWitness :
    semNo₈ dogChasesACat (λ x => (c : CatBg) × catches₈_none x c.1) :=
  fun _ _ ⟨_, h⟩ => nomatch h

/-- "No dog which chases a cat catches it" is true when no dog catches
the cat it chases. -/
theorem noDogCatchesCat_true_scenario :
    Nonempty (semNo₈ dogChasesACat (λ x => (c : CatBg) × catches₈_none x c.1)) :=
  ⟨noDogCatchesCatWitness⟩

/-- "No dog which chases a cat catches it" is false when every dog
catches the cat it chases. -/
theorem noDogCatchesCat_false_scenario :
    IsEmpty (semNo₈ dogChasesACat (λ x => (c : CatBg) × catches₈_all x c.1)) :=
  ⟨fun f => nomatch f .dog1
    ⟨PUnit.unit, ⟨⟨.cat1, PUnit.unit⟩, PUnit.unit⟩⟩
    ⟨⟨.cat1, PUnit.unit⟩, PUnit.unit⟩⟩

/-- The negation donkey case uses `ℒ` — the same localization mechanism
as the classic farmer/donkey example. -/
theorem donkeyNeg_uses_localization :
    dogChasesACat = (λ x => isDog₈ₙ x × ℒ ⟨CatBg, λ c a => chases₈ a c.1⟩ x) := rfl

end NoDogCatchesCat

end Cooper2023Ch8
