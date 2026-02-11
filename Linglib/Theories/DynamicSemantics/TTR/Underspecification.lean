import Linglib.Theories.DynamicSemantics.TTR.Quantification
import Linglib.Theories.TruthConditional.Derivation.Scope
import Linglib.Phenomena.Anaphora.DonkeyAnaphora
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Core.Interfaces.BindingSemantics

/-!
# Type Theory with Records — Chapter 8: Type-Based Underspecification

Cooper (2023) Chapter 8 introduces *content types* that replace specific
contents with types whose witnesses are fully specified readings. This module
formalizes the chapter's mechanisms at two levels:

## Simplified semantic interface (used by bridge theorems)

1. **Scope ambiguity**: QStore, store/retrieve, 𝔖 (underspecification closure)
2. **Donkey anaphora**: localization 𝔏/𝔏ʸ/𝔏ᶜ (= purification 𝔓/𝔓ʸ from Ch7)
3. **Binding theory**: reflexivization ℜ, anaphoric resolution @_{i,j}
4. **Conditional localization**: 𝔏ᶜ for the correct strong donkey reading

## Full Ch8 context machinery (eqs 10→74→82→89)

5. **Cntxt₈**: full 7-field context (q, 𝔰, 𝔩, 𝔯, 𝔴, 𝔤, 𝔠)
6. **B** (eq 77): boundary operation removing locality at clause boundaries
7. **𝔄** (eq 85): anaphor-free filter via r-field checking
8. **ℜ₈** (eq 84): full reflexivization on Cntxt₈
9. **@_{i,j} with l-field** (eq 76): locality-aware anaphoric combination
10. **UnderspecClosure₈** (eq 89): generalized 𝔖 with 7 closure clauses
11. **NQuantScope**: N-quantifier scope generalization (N! readings)
12. **Cross-sentential anaphora** (eqs 37-44): discourse merge
13. **Donkey + negation** (eqs 46-55): path alignment, "no" quantifier

## Bridge theorems

1. `tagged_roundtrip` — 𝔖 witnesses ↔ ScopeConfig
2. `localization_is_purification` — 𝔏 = 𝔓 (Ch8 ↔ Ch7)
3. `reflexive_predicts_binding` — ℜ predicts Binding Conditions A/B
4. `reflexivize₈_agrees_with_simple` — full ℜ₈ ↔ simplified ℜ
5. `twoQuant_embeds_in_closure` — TwoQuantScope.𝔖 embeds in UnderspecClosure₈
6. `donkeyNeg_uses_localization` — negation donkey uses 𝔏

## Key connections

- `QStore.isPlugged` bridges to `Parametric.trivial` (no pending scope)
- Scope witnesses bridge to `ParticularWC_Exist` / `existPQ` (Ch7)
- `TwoQuantScope.𝔖` bridges to `ScopeConfig` (Scontras & Pearl 2021)
- `reflexivize` bridges to `CoreferencePattern` (Phenomena)
- `localizeConditional` derives the correct strong donkey reading
- `crossSententialResolve` bridges discourse merge to pronoun resolution

## References

- Cooper (2023). From Perception to Communication. OUP. Ch 8.
- Scontras & Pearl (2021). When pragmatics matters more for TVJ.
- Chomsky (1981). Lectures on Government and Binding.
- Kanazawa (1994). Weak vs. Strong Readings of Donkey Sentences.
-/

namespace Theories.DynamicSemantics.TTR

-- ============================================================================
-- Quantifier stores and plugged/unplugged content
-- ============================================================================

section ScopeInfrastructure

/-! ### Quantifier stores

A quantifier store holds quantifiers that have been "tucked away" during
composition and await scope assignment via retrieval. -/

variable {E : Type}

/-- A quantifier store: a list of quantifiers awaiting scope resolution.
    Cooper (2023) Ch8 §8.3: stored quantifiers are later retrieved at
    scope positions, and retrieval order determines scope. -/
structure QStore (E : Type) where
  /-- The stored quantifiers, ordered by storage time -/
  stored : List (Quant E)

/-- Empty quantifier store: no pending scope ambiguity. -/
def QStore.empty : QStore E := ⟨[]⟩

/-- A store is *plugged* when all quantifiers have taken scope.
    Cooper (2023) Ch8: plugged content is fully scope-resolved. -/
def QStore.isPlugged (qs : QStore E) : Prop := qs.stored = []

/-- A store is *unplugged* when quantifiers remain to be scoped. -/
def QStore.isUnplugged (qs : QStore E) : Prop := qs.stored ≠ []

/-- Plugged ↔ ¬ unplugged. -/
theorem plugged_iff_not_unplugged (qs : QStore E) :
    qs.isPlugged ↔ ¬ qs.isUnplugged := by
  simp [QStore.isPlugged, QStore.isUnplugged]

/-- The empty store is plugged by construction. -/
theorem empty_isPlugged : (QStore.empty : QStore E).isPlugged := rfl

/-- Bridge: a plugged QStore corresponds to a trivial Parametric background.
    When the store is empty, the content has no scope presuppositions —
    just like `Parametric.trivial` has `Bg = Unit`. -/
def pluggedToTrivial {C : Type*} (c : C) (qs : QStore E)
    (_h : qs.isPlugged) : Parametric C :=
  Parametric.trivial c

-- ============================================================================
-- Store and retrieve operations
-- ============================================================================

/-! ### Store

Store moves a quantifier from content into the qstore, leaving behind
a variable (trace) in the content. -/

/-- Store a quantifier: push it onto the front of the store.
    Cooper (2023) Ch8 §8.3: store(Q) moves Q into the qstore. -/
def QStore.store (qs : QStore E) (q : Quant E) : QStore E :=
  ⟨q :: qs.stored⟩

/-- Storing into a plugged store makes it unplugged. -/
theorem store_unplugs (q : Quant E) :
    (QStore.empty.store q : QStore E).isUnplugged := by
  simp [QStore.store, QStore.isUnplugged, QStore.empty]

/-! ### Retrieve

Retrieve pops a quantifier from the store and applies it at a scope
position. The order of retrieval determines relative scope. -/

/-- Retrieve the first quantifier from the store.
    Cooper (2023) Ch8 §8.3: retrieve pops the outermost stored quantifier.
    Returns the quantifier and the remaining store, or `none` if plugged. -/
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
theorem store_then_retrieve (qs : QStore E) (q : Quant E) :
    (qs.store q).retrieve = some (q, qs) := by
  simp [QStore.store, QStore.retrieve]

-- ============================================================================
-- Scope readings and 𝔖 (underspecification closure)
-- ============================================================================

/-! ### Two-quantifier scope

For sentences with two quantifiers and a binary relation, the two
possible retrieval orders produce exactly two scope readings.
Cooper (2023) Ch8: "every boy hugged a dog" has ∀>∃ and ∃>∀ readings. -/

/-- A two-quantifier scope configuration: two quantifiers and a relation.
    Cooper (2023) Ch8: the minimal underspecified content for a
    doubly-quantified sentence. -/
structure TwoQuantScope (E : Type) where
  /-- The binary relation (e.g., hug) -/
  rel : E → E → Type
  /-- The subject quantifier (e.g., every boy) -/
  q₁ : Quant E
  /-- The object quantifier (e.g., a dog) -/
  q₂ : Quant E

/-- Surface scope reading: Q₁ scopes over Q₂.
    Cooper (2023) Ch8: retrieving Q₁ first = outermost scope.
    For "every boy hugged a dog": ∀x.boy(x) → ∃y.dog(y) ∧ hug(x,y). -/
def TwoQuantScope.surfaceScope (s : TwoQuantScope E) : Type :=
  s.q₁ (λ x => s.q₂ (λ y => s.rel x y))

/-- Inverse scope reading: Q₂ scopes over Q₁.
    For "every boy hugged a dog": ∃y.dog(y) ∧ ∀x.boy(x) → hug(x,y). -/
def TwoQuantScope.inverseScope (s : TwoQuantScope E) : Type :=
  s.q₂ (λ y => s.q₁ (λ x => s.rel x y))

/-- The underspecification closure 𝔖 for two quantifiers:
    the join of all possible scope readings.
    Cooper (2023) Ch8 §8.4: each witness of 𝔖(content) is one
    fully specified reading. With two quantifiers, |𝔖| = 2. -/
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
    Cooper (2023) Ch8 → Scontras & Pearl (2021) bridge:
    retrieval order corresponds to ScopeConfig.surface / .inverse. -/
def TwoQuantScope.readingAt (s : TwoQuantScope E)
    (sc : TruthConditional.Derivation.Scope.ScopeConfig) : Type :=
  match sc with
  | .surface => s.surfaceScope
  | .inverse => s.inverseScope

-- ============================================================================
-- Bridge: 𝔖 witnesses ↔ ScopeConfig (bridge theorem 1)
-- ============================================================================

/-! ### Bridge: underspec witnesses match scope readings

The witnesses of 𝔖(content) are in bijection with the scope orderings
predicted by retrieve. Each ScopeConfig selects one reading, and every
witness of 𝔖 comes from exactly one reading.

This connects TTR's type-based underspecification to the `ScopeConfig`
infrastructure used by Scontras & Pearl (2021) in the RSA implementation. -/

open TruthConditional.Derivation.Scope (ScopeConfig)

/-- Forward direction: every witness of 𝔖 is tagged by a ScopeConfig. -/
def TwoQuantScope.𝔖_to_tagged (s : TwoQuantScope E)
    (w : s.𝔖) : (sc : ScopeConfig) × s.readingAt sc :=
  match w with
  | .inl surf => ⟨.surface, surf⟩
  | .inr inv => ⟨.inverse, inv⟩

/-- Backward direction: a tagged reading embeds into 𝔖. -/
def TwoQuantScope.tagged_to_𝔖 (s : TwoQuantScope E)
    (tagged : (sc : ScopeConfig) × s.readingAt sc) : s.𝔖 :=
  match tagged.1, tagged.2 with
  | .surface, w => Sum.inl w
  | .inverse, w => Sum.inr w

/-- Round-trip: tagged → 𝔖 → tagged is the identity.
    This is the bijection theorem connecting Ch8's 𝔖 to ScopeConfig. -/
theorem TwoQuantScope.tagged_roundtrip (s : TwoQuantScope E)
    (tagged : (sc : ScopeConfig) × s.readingAt sc) :
    s.𝔖_to_tagged (s.tagged_to_𝔖 tagged) = tagged := by
  obtain ⟨sc, w⟩ := tagged
  cases sc <;> rfl

end ScopeInfrastructure

-- ============================================================================
-- Phenomenon: "Every boy hugged a dog"
-- ============================================================================

/-! ### Scope ambiguity in "every boy hugged a dog"

Cooper (2023) Ch8: the classic scope ambiguity example.
Two boys, two dogs; each boy hugs a different dog.
Surface scope is true but inverse scope is false. -/

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

-- ============================================================================
-- Bridge: scope witnesses ↔ Ch7 witness conditions (bridge theorem 2)
-- ============================================================================

/-! ### Bridge: scope readings → witness conditions

The connection between Ch8's scope readings and Ch7's witness conditions:
a surface scope reading with a universal subject and existential object
corresponds to per-element `ParticularWC_Exist` conditions, yielding
REFSET anaphora for the object NP.

"Every boy hugged a dog. It was friendly."
→ "it" picks up one dog per boy (distributive anaphora, REFSET). -/

section ScopeBridge

variable {E : Type}

/-- Bridge: a surface scope witness (∀x.P(x) → ∃y.Q(y) ∧ R(x,y)) yields
    a `ParticularWC_Exist` for the inner existential at each fixed subject.

    Cooper Ch8→Ch7: the inner quantifier's witness condition is exactly
    `ParticularWC_Exist`, predicting REFSET anaphora for the object. -/
def surfaceScope_inner_witness
    (P Q : Ppty E) (R : E → E → Type)
    (w : semUniversal P (λ x => ExistWitness E Q (λ y => R x y)))
    (x : E) (hP : P x) :
    ParticularWC_Exist Q (λ y => R x y) :=
  let ew := w x hP
  ⟨ew.individual, ew.restrWit, ew.scopeWit⟩

/-- Bridge: an inverse scope witness (∃y.Q(y) ∧ ∀x.P(x) → R(x,y)) yields
    a `ParticularWC_Exist` for the outer existential — there is ONE specific
    entity witnessing Q that the universal scopes under.

    "A dog was hugged by every boy. It was large."
    → "it" picks up the specific dog (REFSET from outer scope). -/
def inverseScope_outer_witness
    (P Q : Ppty E) (R : E → E → Type)
    (w : ExistWitness E Q (λ y => semUniversal P (λ x => R x y))) :
    ParticularWC_Exist Q (λ y => semUniversal P (λ x => R x y)) :=
  ⟨w.individual, w.restrWit, w.scopeWit⟩

/-- Bridge: surface scope (semUniversal + ExistWitness) matches
    `existPQ` at each individual — the Ch7 existential predicate overlap.

    Cooper Ch8→Ch7: scope retrieval order determines which witness
    conditions hold per quantifier position. -/
theorem surface_scope_matches_existPQ
    (P Q : Ppty E) (R : E → E → Type)
    (w : semUniversal P (λ x => ExistWitness E Q (λ y => R x y))) :
    ∀ x : E, Nonempty (P x) → existPQ Q (R x) := by
  intro x ⟨hP⟩
  let ew := w x hP
  exact ⟨ew.individual, ⟨ew.restrWit⟩, ⟨ew.scopeWit⟩⟩

end ScopeBridge

-- ============================================================================
-- Localization (𝔏) — Donkey anaphora
-- ============================================================================

/-! ### Localization

Cooper (2023) Ch8 §8.5: localization moves a stored quantifier's
background into the domain of a property, absorbing the context
dependency. This is the Ch8 mechanism for donkey anaphora:

"Every farmer who owns a donkey beats it"
→ "a donkey" is stored, then localized into the restrictor "farmer who
   owns a donkey", binding the donkey existentially (weak) or
   universally (strong) inside the property body.

The central insight: this is *the same operation* as Ch7's purification. -/

section Localization

variable {E : Type}

/-- Localization: absorb a parametric property's background into its body.
    Cooper (2023) Ch8 §8.5: 𝔏(P) moves context material into the
    property's domain type, enabling donkey anaphora.

    Before 𝔏: restrictor is parametric (depends on which donkey).
    After 𝔏: restrictor is pure (donkey existentially bound inside). -/
def localize (P : PPpty E) : Ppty E := λ a => (c : P.Bg) × P.fg c a

/-- Universal localization: strong donkey reading variant.
    Cooper (2023) Ch8: 𝔏ʸ(P) uses universal instead of existential binding.
    "Every farmer who owns a donkey beats it" with strong reading:
    every donkey a farmer owns, the farmer beats. -/
def localizeUniv (P : PPpty E) : Ppty E := λ a => (c : P.Bg) → P.fg c a

/-- Conditional localization: universal quantification gated by a condition.
    `localizeConditional P gate a` requires `P.fg c a` only for backgrounds
    where `gate c a` is inhabited.

    The three localization variants form a hierarchy:
    - 𝔏 P a  = (c : P.Bg) × P.fg c a           (existential / weak donkey)
    - 𝔏ʸ P a = (c : P.Bg) → P.fg c a           (unconditional universal / too strong)
    - localizeConditional P gate a
            = (c : P.Bg) → gate c a → P.fg c a  (conditional universal / correct strong)

    Kanazawa (1994): the correct strong donkey reading is conditional —
    "beats every donkey *it owns*", not "beats every donkey *that exists*". -/
def localizeConditional (P : PPpty E) (gate : P.Bg → E → Type) : Ppty E :=
  λ a => (c : P.Bg) → gate c a → P.fg c a

scoped prefix:max "𝔏" => localize
scoped prefix:max "𝔏ʸ" => localizeUniv

/-- 𝔏ʸ is the degenerate case of conditional localization with a trivially
    true gate. This makes the hierarchy explicit:
    𝔏ʸ quantifies over ALL backgrounds; conditional localization restricts
    to those satisfying the gate. -/
theorem localizeUniv_iff_conditional_trivial (P : PPpty E) (a : E) :
    Nonempty (𝔏ʸ P a) ↔ Nonempty (localizeConditional P (λ _ _ => PUnit) a) :=
  ⟨fun ⟨f⟩ => ⟨fun c _ => f c⟩, fun ⟨f⟩ => ⟨fun c => f c PUnit.unit⟩⟩

/-! ### Bridge theorem 2: localization is purification

The central bridge: Ch8's localization operator 𝔏 is exactly the same
operation as Ch7's purification operator 𝔓. Two independently motivated
mechanisms turn out to be identical:

- **𝔓 (Ch7)**: purify a parametric property for witness conditions
- **𝔏 (Ch8)**: localize stored quantifiers for scope resolution

Both absorb a `Parametric` background into the property body via
existential quantification (or universal, for 𝔓ʸ / 𝔏ʸ). -/

/-- 𝔏 = 𝔓: localization is purification.
    Cooper Ch8→Ch7: the underspecification mechanism for donkey
    anaphora (Ch8) is the same operation as purification (Ch7). -/
theorem localization_is_purification (P : PPpty E) :
    𝔏 P = 𝔓 P := rfl

/-- 𝔏ʸ = 𝔓ʸ: universal localization is universal purification. -/
theorem localizationUniv_is_purificationUniv (P : PPpty E) :
    𝔏ʸ P = 𝔓ʸ P := rfl

/-- Localization preserves truth: a localized property is witnessed
    iff the original is witnessable under some context. -/
theorem localize_nonempty_iff (P : PPpty E) (a : E) :
    Nonempty (𝔏 P a) ↔ ∃ c : P.Bg, Nonempty (P.fg c a) :=
  purify_nonempty_iff P a

/-- Universal localization: witnessed iff property holds under all contexts. -/
theorem localizeUniv_nonempty_iff (P : PPpty E) (a : E) :
    Nonempty (𝔏ʸ P a) ↔ ∀ c : P.Bg, Nonempty (P.fg c a) :=
  purifyUniv_nonempty_iff P a

/-- Localizing a trivial parametric property adds only a Unit factor. -/
theorem localize_trivial (P : Ppty E) (a : E) :
    𝔏 (Parametric.trivial P) a = ((_ : Unit) × P a) := rfl

/-- Bridge: localization readings agree when pure.
    Corollary of `localization_is_purification` +
    `donkey_readings_agree_when_pure`.
    When Bg is trivial, weak and strong donkey readings coincide. -/
theorem localization_readings_agree_when_pure
    (P : PPpty E) (hPure : P.isPure) (a : E) :
    Nonempty (𝔏 P a) ↔ Nonempty (𝔏ʸ P a) :=
  donkey_readings_agree_when_pure P hPure a

end Localization

-- ============================================================================
-- Phenomenon: Donkey anaphora
-- ============================================================================

/-! ### "Every farmer who owns a donkey beats it"

The classic donkey anaphora example. Two farmers, two donkeys; each
farmer owns and beats a different donkey. This demonstrates:

1. Localization absorbs "a donkey" into the restrictor
2. Weak donkey (𝔏 = 𝔓) is true — each farmer owns/beats *some* donkey
3. Strong donkey (𝔏ʸ = 𝔓ʸ) fails — no farmer owns/beats *every* donkey
4. The divergence witnesses the non-triviality of `donkey_readings_agree_when_pure` -/

section DonkeyAnaphora

/-- Individuals for the donkey example. -/
inductive DonkeyInd where
  | farmer1 | farmer2 | donkey1 | donkey2
  deriving DecidableEq, Repr

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
example : 𝔏 farmerOwnsBeatsDonkey = 𝔓 farmerOwnsBeatsDonkey := rfl

/-- Farmer1 satisfies the weak donkey reading: owns and beats donkey1. -/
def farmer1_weak_donkey : 𝔏 farmerOwnsBeatsDonkey .farmer1 :=
  ⟨⟨.donkey1, PUnit.unit⟩, PUnit.unit, PUnit.unit, PUnit.unit⟩

/-- Farmer2 satisfies the weak donkey reading: owns and beats donkey2. -/
def farmer2_weak_donkey : 𝔏 farmerOwnsBeatsDonkey .farmer2 :=
  ⟨⟨.donkey2, PUnit.unit⟩, PUnit.unit, PUnit.unit, PUnit.unit⟩

/-- Strong donkey FAILS for farmer1: farmer1 doesn't own donkey2.
    This is the ∀-reading: every donkey d, farmer1 owns d ∧ beats d.
    Fails because farmer1 doesn't own donkey2. -/
theorem farmer1_fails_strong_donkey :
    IsEmpty (𝔏ʸ farmerOwnsBeatsDonkey .farmer1) :=
  ⟨fun f => nomatch (f ⟨.donkey2, PUnit.unit⟩).2.1⟩

/-- Weak and strong donkey readings DIVERGE: weak is true, strong is false.
    This demonstrates that `donkey_readings_agree_when_pure` has a real
    hypothesis: when Bg is non-trivial (multiple donkeys), the readings
    genuinely differ. -/
theorem donkey_readings_diverge :
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer1) ∧
    ¬ Nonempty (𝔏ʸ farmerOwnsBeatsDonkey .farmer1) :=
  ⟨⟨farmer1_weak_donkey⟩, fun ⟨w⟩ => farmer1_fails_strong_donkey.false w⟩

/-- The full sentence "every farmer who owns a donkey beats it" is
    true under the weak donkey reading (via localization = purification). -/
def everyFarmerBeatsDonkey_weak :
    semUniversal (𝔏 farmerOwnsBeatsDonkey) (λ _ => PUnit) :=
  fun x hLocalized => match x, hLocalized with
  | .farmer1, _ => PUnit.unit
  | .farmer2, _ => PUnit.unit
  | .donkey1, ⟨⟨_, _⟩, hF, _, _⟩ => nomatch hF
  | .donkey2, ⟨⟨_, _⟩, hF, _, _⟩ => nomatch hF

/-- The parametric VP "beats it": the object donkey comes from background.
    This is the nuclear scope of "every farmer who owns a donkey beats it",
    decomposed so that ownership can serve as the conditional gate. -/
def beatsParam : PPpty DonkeyInd where
  Bg := DonkeyBg
  fg := λ ⟨d, _⟩ x => beats x d

/-- Ownership gate: filters which donkeys are relevant for the strong reading.
    Only donkeys that x actually owns are subject to the universal. -/
def ownsGate : DonkeyBg → DonkeyInd → Type :=
  λ ⟨d, _⟩ x => owns x d

/-- The conditional strong donkey reading via `localizeConditional`:
    x is a farmer ∧ for every donkey c that x owns, x beats c.

    This is the linguistically correct strong reading — unlike 𝔏ʸ
    which quantifies unconditionally over ALL donkeys (requiring every
    farmer to own every donkey), the conditional version only requires
    beating donkeys that are actually owned.

    Kanazawa (1994): the strong reading of "every farmer who owns
    a donkey beats it" means ∀d[donkey(d) ∧ owns(x,d) → beats(x,d)],
    not ∀d[donkey(d) → owns(x,d) ∧ beats(x,d)]. -/
def strongDonkeyConditional : Ppty DonkeyInd := λ x =>
  isFarmer x × localizeConditional beatsParam ownsGate x

/-- Farmer1 satisfies the conditional strong reading:
    farmer1 beats every donkey farmer1 owns (just donkey1). -/
def farmer1_strong_conditional : strongDonkeyConditional .farmer1 :=
  ⟨PUnit.unit, fun ⟨d, hDk⟩ hOwn => match d, hDk, hOwn with
  | .donkey1, _, _ => PUnit.unit
  | .donkey2, _, h => nomatch h
  | .farmer1, h, _ => nomatch h
  | .farmer2, h, _ => nomatch h⟩

/-- Farmer2 satisfies the conditional strong reading. -/
def farmer2_strong_conditional : strongDonkeyConditional .farmer2 :=
  ⟨PUnit.unit, fun ⟨d, hDk⟩ hOwn => match d, hDk, hOwn with
  | .donkey2, _, _ => PUnit.unit
  | .donkey1, _, h => nomatch h
  | .farmer1, h, _ => nomatch h
  | .farmer2, h, _ => nomatch h⟩

/-- The full sentence "every farmer who owns a donkey beats it" is
    true under the conditional strong donkey reading. -/
def everyFarmerBeatsDonkey_strong :
    semUniversal strongDonkeyConditional (λ _ => PUnit) :=
  fun x hStr => match x, hStr with
  | .farmer1, _ => PUnit.unit
  | .farmer2, _ => PUnit.unit
  | .donkey1, ⟨hF, _⟩ => nomatch hF
  | .donkey2, ⟨hF, _⟩ => nomatch hF

/-- 𝔏ʸ is NOT the correct strong donkey reading.
    𝔏ʸ requires every farmer to own EVERY donkey (unconditional universal),
    while the correct strong reading (conditional universal) only requires
    beating donkeys actually owned. The distinction matters whenever a
    farmer doesn't own all donkeys — which is the typical case. -/
theorem strong_donkey_distinction :
    ¬ Nonempty (𝔏ʸ farmerOwnsBeatsDonkey .farmer1) ∧
    Nonempty (strongDonkeyConditional .farmer1) :=
  ⟨fun ⟨w⟩ => farmer1_fails_strong_donkey.false w,
   ⟨farmer1_strong_conditional⟩⟩

/-- 𝔏ʸ (unconditional universal) implies conditional localization for any gate:
    if the foreground holds for ALL backgrounds, it holds for gated ones.
    This makes precise why 𝔏ʸ is strictly stronger than the conditional reading. -/
def localizeUniv_implies_conditional {E : Type} (P : PPpty E)
    (gate : P.Bg → E → Type) (a : E)
    (h : 𝔏ʸ P a) : localizeConditional P gate a :=
  fun c _ => h c

end DonkeyAnaphora

-- ============================================================================
-- Bridge: TTR donkey predictions → Phenomena/Anaphora/DonkeyAnaphora
-- ============================================================================

/-! ### Per-datum verification: TTR predictions match empirical data

Connect the TTR localization analysis to the theory-neutral donkey
anaphora data in `Phenomena.Anaphora.DonkeyAnaphora`. Each theorem
verifies one data point: the empirical datum records a reading as
available, and TTR produces a witness for that reading.

Changing a Ppty (e.g., making `beats` asymmetric) will break exactly
the theorems whose empirical predictions depend on it. -/

section PhenomenaBridge

open Phenomena.Anaphora.DonkeyAnaphora

/-- Geach donkey: weak reading available — TTR predicts ✓.
    `geachDonkey.weakReading = true` and TTR produces a weak (𝔏) witness
    for both farmers in the scenario. -/
theorem geach_weak_available :
    geachDonkey.weakReading = true ∧
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer1) ∧
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer2) :=
  ⟨rfl, ⟨farmer1_weak_donkey⟩, ⟨farmer2_weak_donkey⟩⟩

/-- Geach donkey: strong reading available — TTR predicts ✓.
    `geachDonkey.strongReading = true` and TTR produces a conditional
    strong witness for both farmers. -/
theorem geach_strong_available :
    geachDonkey.strongReading = true ∧
    Nonempty (strongDonkeyConditional .farmer1) ∧
    Nonempty (strongDonkeyConditional .farmer2) :=
  ⟨rfl, ⟨farmer1_strong_conditional⟩, ⟨farmer2_strong_conditional⟩⟩

/-- Geach donkey: bound reading — TTR confirms the pronoun depends on
    the indefinite via parametric background (the donkey is the Bg). -/
theorem geach_bound_reading :
    geachDonkey.boundReading = true ∧
    farmerOwnsBeatsDonkey.Bg = DonkeyBg :=
  ⟨rfl, rfl⟩

/-- Strong dominant: both readings TTR-available (consistent with
    `strongDominant` recording both as available with strong preferred). -/
theorem strongDominant_readings_available :
    strongDominant.strongAvailable = true ∧
    strongDominant.weakAvailable = true ∧
    Nonempty (strongDonkeyConditional .farmer1) ∧
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer1) :=
  ⟨rfl, rfl, ⟨farmer1_strong_conditional⟩, ⟨farmer1_weak_donkey⟩⟩

end PhenomenaBridge

-- ============================================================================
-- Binding Theory: ℜ and anaphoric resolution
-- ============================================================================

/-! ### Reflexivization and anaphoric operations

Cooper (2023) Ch8 introduces two operations for binding:

1. **ℜ(P)** (eq 84): *Reflexivization* — removes the reflexive marking (r-field)
   from the context and binds the reflexive pronoun to the subject variable
   in the domain of the property. Semantic effect: R(x,y) → R(x,x).

2. **@_{i,j}** (eq 28): *Anaphoric combination* — identifies assignment path j
   with path i, creating the anaphoric link between a pronoun and its
   antecedent. General mechanism for pronoun resolution.

The interplay creates complementary distribution:
- ℜ provides the mechanism for reflexives → they MUST be locally bound
- @_{i,j} with a constant resolve function gives disjoint reference for pronouns
- B (eq 77, not yet formalized) removes locality at clause boundaries

## Key connections

- `reflexivize` (ℜ) bridges to `CoreferencePattern.reflexivePattern` (Phenomena)
- `anaphoricResolve` captures @_{i,j} resolution → `pronounPattern`
- `reflexive_predicts_binding`: the main bridge theorem (bridge theorem 3) -/

section BindingTheory

variable {E : Type}

/-- Reflexivization: identify the two arguments of a binary relation.
    Cooper (2023) Ch8, eq (84): ℜ(P) removes the reflexive marking
    (r-field) from the context and replaces the dependency on the
    assignment variable 𝔤.xᵢ with the domain variable r.x.

    Semantic effect: a transitive verb R(x,y) becomes a reflexive
    VP R(x,x), forcing the object to corefer with the subject.
    "Sam likes himself" = ℜ(like)(Sam) = like(Sam, Sam). -/
def reflexivize (R : E → E → Type) : Ppty E := λ x => R x x

scoped prefix:max "ℜ" => reflexivize

/-- Anaphoric resolution: resolve a parametric property's background
    using a function of the foreground argument.
    Captures the semantic effect of Cooper's @_{i,j} (eq 28):
    @_{i,j} identifies path 𝔤.xⱼ with 𝔤.xᵢ, creating the anaphoric link.

    - Reflexives: resolve = id (subject IS the referent) → same as ℜ
    - Pronouns: resolve = const(g(i)) (assignment provides referent) -/
def anaphoricResolve (P : PPpty E) (resolve : E → P.Bg) : Ppty E :=
  λ x => P.fg (resolve x) x

/-- ℜ forces argument identity: any witness of ℜ(R)(x) IS R(x,x).
    Cooper Ch8: the reflexive marking ensures the object slot
    is filled by the same individual as the subject. -/
theorem reflexivize_forces_identity (R : E → E → Type) (x : E) :
    ℜ R x = R x x := rfl

/-- ℜ is anaphoric resolution with identity:
    reflexivization is the special case where the background (object
    referent) is resolved to equal the foreground argument (subject).
    ℜ(R) = anaphoricResolve(⟨E, λy x. R(x,y)⟩, id). -/
theorem reflexivize_eq_resolve_id (R : E → E → Type) :
    ℜ R = anaphoricResolve ⟨E, λ y x => R x y⟩ id := rfl

/-- Pronoun resolution with constant: resolves to a fixed referent y
    regardless of the subject x. Captures @_{i,j} when the assignment
    g(i) = y is fixed from discourse context.
    "Sam likes him(=Bill)" = anaphoricResolve(like_param, const Bill)(Sam)
                           = like(Sam, Bill). -/
theorem resolve_const (R : E → E → Type) (y : E) (x : E) :
    anaphoricResolve (⟨E, λ obj subj => R subj obj⟩ : PPpty E)
      (fun _ => y) x = R x y := rfl

-- NOTE: The full record-type versions of these operations (𝔄, B, ℜ₈, @_{i,j}
-- with locality) are defined below in the "Full Ch8 Context" sections using
-- `Cntxt₈`. The simplified definitions here (`reflexivize`, `anaphoricResolve`)
-- serve as the clean semantic interface for bridge theorems to Phenomena and
-- Core.Interfaces; `reflexivize₈_agrees_with_simple` connects the two layers.

end BindingTheory

-- ============================================================================
-- Phenomenon: "Sam likes himself" vs "Sam likes him"
-- ============================================================================

/-! ### Binding in "Sam likes himself" / "Sam likes him"

Cooper (2023) Ch8, eqs (67)–(73): "Sam likes him" has two fields x and y
for individuals (68a). When y=x, the fields are filled by the same individual
(68b,c). Reflexivization ℜ forces this identification.

The complementary distribution:
- "Sam likes himself" = ℜ(like)(Sam) = like(Sam, Sam) — coreference forced
- "Sam likes him(=Bill)" = anaphoricResolve(like_param, const Bill)(Sam)
                        = like(Sam, Bill) — disjoint reference -/

section BindingPhenomenon

/-- Individuals for the binding example.
    Cooper (2023) Ch8: Sam is the subject; Bill is a potential
    non-local antecedent for "him". -/
inductive BindInd where
  | sam | bill | kim
  deriving DecidableEq, Repr

/-- "like" as a non-trivial binary relation.
    Sam likes everyone, Bill likes Kim and himself, Kim likes herself only.
    This makes binding witnesses non-trivially constrained: ℜ(like₈)(Kim)
    is inhabited but like₈ .kim .sam is not, so reflexivization genuinely
    restricts which argument pairs are witnessable. -/
def like₈ : BindInd → BindInd → Type
  | .sam, _ => PUnit       -- Sam likes everyone
  | .bill, .bill => PUnit  -- Bill likes himself
  | .bill, .kim => PUnit   -- Bill likes Kim
  | .kim, .kim => PUnit    -- Kim likes herself
  | _, _ => Empty

/-- like₈ is non-trivial: not everyone likes everyone. -/
theorem like₈_nontrivial : IsEmpty (like₈ .kim .sam) :=
  ⟨fun h => nomatch h⟩

/-- "like" as parametric content: the object comes from background.
    Cooper Ch8, eq (69): the verb phrase "likes him" has the object's
    referent in the context (𝔤.x₀). -/
def likeParam : PPpty BindInd where
  Bg := BindInd
  fg := λ obj subj => like₈ subj obj

/-- "Sam likes himself" via ℜ: Cooper Ch8, eq (84).
    ℜ(like)(Sam) = like(Sam, Sam). -/
def samLikesHimself : ℜ like₈ .sam := PUnit.unit

/-- "Sam likes him(=Bill)" via pronoun resolution: Cooper Ch8, eq (72).
    @_{0,1}(Sam, likes him) resolves "him" to Bill from context. -/
def samLikesBill : anaphoricResolve likeParam (fun _ => .bill) .sam :=
  PUnit.unit

/-- ℜ forces coreference: the reflexive witness IS like(Sam, Sam). -/
theorem reflexive_is_self : (ℜ like₈ .sam) = like₈ .sam .sam := rfl

/-- Pronoun resolution gives like(Sam, Bill) — distinct arguments. -/
theorem pronoun_is_distinct :
    anaphoricResolve likeParam (fun _ => BindInd.bill) .sam =
    like₈ .sam .bill := rfl

/-- Every individual can like themselves (ℜ always witnessable).
    Non-trivial: each case uses a different constructor witness. -/
def allLikeSelf : ∀ x : BindInd, ℜ like₈ x
  | .sam => PUnit.unit
  | .bill => PUnit.unit
  | .kim => PUnit.unit

/-- ℜ applied to likeParam is the same as reflexivize applied to like₈.
    This shows the parametric and direct formulations agree. -/
theorem param_reflexivize_agrees :
    anaphoricResolve likeParam id = ℜ like₈ := rfl

/-- ℜ genuinely constrains: Kim can like herself (ℜ) but NOT Bill
    (pronoun resolution). This is non-trivial because like₈ .kim .bill
    is Empty while like₈ .kim .kim is PUnit. -/
theorem reflexive_constrains_kim :
    Nonempty (ℜ like₈ .kim) ∧ IsEmpty (like₈ .kim .bill) :=
  ⟨⟨PUnit.unit⟩, ⟨fun h => nomatch h⟩⟩

end BindingPhenomenon

-- ============================================================================
-- Bridge: TTR binding → Phenomena/Anaphora/Coreference (bridge theorem 3)
-- ============================================================================

/-! ### Per-datum verification: binding predictions match coreference data

Connect TTR's ℜ and anaphoric resolution to the theory-neutral binding
data in `Phenomena.Anaphora.Coreference`.

Cooper (2023) Ch8 §8.3 gives a type-theoretic account of Chomsky's (1981)
binding conditions:
- **Condition A** (reflexives must be locally bound): ℜ forces argument identity
- **Condition B** (pronouns must be locally free): @_{i,j} with disjoint reference
- **Complementary distribution**: ℜ vs @_{i,j} for the same position

Each theorem verifies one empirical pattern from `Coreference.lean`.
Changing `reflexivize` or `anaphoricResolve` will break these bridges. -/

section CoreferenceBridge

/-- TTR's ℜ predicts Binding Condition A:
    reflexives require a local antecedent because ℜ forces argument
    identity within the local clause.
    Cooper Ch8, eq (84) + (88): ℜ at VP level binds reflexive to subject.
    Matches `reflexivePattern` from Phenomena. -/
theorem reflexive_predicts_condA :
    reflexivePattern.requiresAntecedent = true ∧
    reflexivePattern.antecedentDomain = some .local_ ∧
    (∀ (R : BindInd → BindInd → Type) (x : BindInd), ℜ R x = R x x) :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- TTR predicts Binding Condition B:
    pronouns allow disjoint reference via @_{i,j} resolution with a
    constant function (the assignment provides the referent from
    non-local context). Cooper Ch8, eq (28).
    Matches `pronounPattern` from Phenomena. -/
theorem pronoun_predicts_condB :
    pronounPattern.requiresAntecedent = false ∧
    pronounPattern.antecedentDomain = some .nonlocal ∧
    (∀ (y x : BindInd),
      anaphoricResolve likeParam (fun _ => y) x = like₈ x y) :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Complementary distribution: reflexive and pronoun are predicted
    by different TTR mechanisms (ℜ vs @_{i,j}).
    Cooper Ch8, eqs (67)–(73): "Sam likes him" is NOT appropriate for
    "Sam likes himself" — ℜ must be used instead.
    Matches `complementaryDistributionData` from Phenomena. -/
theorem complementary_distribution_predicted :
    reflexivePattern.anaphorType = .reflexive ∧
    pronounPattern.anaphorType = .pronoun ∧
    Nonempty (ℜ like₈ .sam) ∧
    Nonempty (anaphoricResolve likeParam (fun _ => BindInd.bill) .sam) :=
  ⟨rfl, rfl, ⟨samLikesHimself⟩, ⟨samLikesBill⟩⟩

/-- The main bridge theorem (bridge theorem 3):
    TTR's reflexivization predicts the binding data.

    1. ℜ forces local coreference (Condition A): Cooper eq (84)
    2. @_{i,j} resolution allows disjoint reference (Condition B): Cooper eq (28)
    3. The empirical coreference patterns match: Chomsky (1981)
    4. ℜ = anaphoricResolve with id: reflexivization is a special case -/
theorem reflexive_predicts_binding :
    -- ℜ forces identity (Condition A)
    (∀ (R : BindInd → BindInd → Type) (x : BindInd), ℜ R x = R x x) ∧
    -- Pronoun resolution allows distinct arguments (Condition B)
    (∀ (y x : BindInd),
      anaphoricResolve likeParam (fun _ => y) x = like₈ x y) ∧
    -- ℜ is a special case of anaphoric resolution
    (anaphoricResolve likeParam id = ℜ like₈) ∧
    -- Matches empirical coreference patterns
    reflexivePattern.requiresAntecedent = true ∧
    pronounPattern.requiresAntecedent = false ∧
    reflexivePattern.antecedentDomain = some .local_ ∧
    pronounPattern.antecedentDomain = some .nonlocal :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

end CoreferenceBridge

-- ============================================================================
-- Bridge: TTR binding → Core/Interfaces/BindingSemantics
-- ============================================================================

/-! ### Bridge to positional binding interface

Connect TTR's semantic binding (ℜ / @_{i,j}) to the syntactic binding
interface in `Core.Interfaces.BindingSemantics`.

TTR's binding theory is *semantic* (argument identification via types),
while `BindingSemantics` is *syntactic* (position-based binder–bindee
relations). The bridge maps:
- ℜ applied → `BindingRelation` with subject as binder, object as bindee
- @_{i,j} resolution (pronoun) → free variable in the `BindingConfig` -/

section BindingSemBridge

open Interfaces.BindingSemantics

/-- ℜ induces a binding relation: subject binds the reflexive object.
    Cooper Ch8, (81): S → NP VP | B(NP'(@VP')).
    The subject at position 0 binds "himself" at position 2. -/
def reflexivize_to_binding
    (subjectPos objectPos : Position) : BindingRelation where
  binder := subjectPos
  bindee := objectPos
  varIndex := 0

/-- Binding config for "Sam likes himself": one local binding. -/
def reflexiveBindingConfig : BindingConfig where
  bindings := [reflexivize_to_binding ⟨0⟩ ⟨2⟩]
  freeVariables := []

/-- The reflexive binding config is well-formed:
    no double binding, no self-binding, consistent indices. -/
theorem reflexive_config_wellFormed :
    reflexiveBindingConfig.wellFormed = true := by native_decide

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

-- ============================================================================
-- Full Ch8 Context: Cntxt₈ (eqs 10, 74, 82)
-- ============================================================================

/-! ### Full Ch8 context

Context evolves: eq 10 `{q,𝔰,𝔴,𝔤,𝔠}` → eq 74 adds 𝔩 → eq 82 adds 𝔯.
`Cntxt₈` encodes eq 82 (final). Earlier versions recoverable via
`𝔩 := empty` / `𝔯 := empty`. Extends CntxtFull (Ch7, eq 122) with q/𝔩/𝔯. -/

section FullContext

variable {E : Type}

/-- Ch8 context, eq (82). -/
structure Cntxt₈ (E : Type) where
  q : QStore E
  𝔰 : Assgnmnt E
  𝔩 : Assgnmnt E       -- locality (eq 74)
  𝔯 : Assgnmnt E       -- reflexive marking (eq 82)
  𝔴 : Assgnmnt E
  𝔤 : Assgnmnt E
  𝔠 : PropCntxt

def Cntxt₈.initial : Cntxt₈ E where
  q := QStore.empty
  𝔰 := Assgnmnt.empty
  𝔩 := Assgnmnt.empty
  𝔯 := Assgnmnt.empty
  𝔴 := Assgnmnt.empty
  𝔤 := Assgnmnt.empty
  𝔠 := PUnit

/-- Eq 10 context: 𝔩 and 𝔯 both empty. -/
def Cntxt₈.isEq10 (c : Cntxt₈ E) : Prop :=
  (∀ i, c.𝔩 i = none) ∧ (∀ i, c.𝔯 i = none)

/-- Eq 74 context: 𝔯 empty. -/
def Cntxt₈.isEq74 (c : Cntxt₈ E) : Prop :=
  ∀ i, c.𝔯 i = none

theorem Cntxt₈.initial_isEq10 : (Cntxt₈.initial : Cntxt₈ E).isEq10 :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end FullContext

-- ============================================================================
-- B Operation and @_{i,j} with l-field (eqs 76–81)
-- ============================================================================

section BoundaryAndLocality

variable {E : Type}

/-- B(α): boundary operation, eq (77). Resets l-field at clause boundaries. -/
def boundary₈ (P : Cntxt₈ E → Type) : Cntxt₈ E → Type :=
  λ c => P { c with 𝔩 := Assgnmnt.empty }

/-- @_{i,j} with locality check, eq (76). Identifies 𝔰.xⱼ with 𝔰.xᵢ
    only when 𝔰.xᵢ is in the l-field. -/
def anaphoricCombine₈ [Inhabited E] (i j : Nat) (P : Cntxt₈ E → Type)
    (Q : Cntxt₈ E → Type) : Cntxt₈ E → Type :=
  λ c => propT ((c.𝔩 i).isSome = true) ×
    P c × Q { c with 𝔰 := Assgnmnt.update c.𝔰 j ((c.𝔰 i).getD default) }

/-- S → NP VP | B(NP'(@VP')), eq (81). -/
def sentenceRule₈ (np : Cntxt₈ E → Type) (vp : Cntxt₈ E → Type)
    : Cntxt₈ E → Type :=
  boundary₈ (λ c => np c × vp c)

theorem boundary₈_clears_locality (c : Cntxt₈ E) (i : Nat) :
    ({ c with 𝔩 := Assgnmnt.empty } : Cntxt₈ E).𝔩 i = none := rfl

/-! #### "Sam thinks she is lucky" — B enables non-local pronoun binding. -/

section NonLocalPronoun

inductive NLPInd where | sam | she_ref
  deriving DecidableEq

def localCtx₈ : Cntxt₈ NLPInd where
  q := QStore.empty
  𝔰 := Assgnmnt.update Assgnmnt.empty 0 .she_ref
  𝔩 := Assgnmnt.update Assgnmnt.empty 0 .she_ref
  𝔯 := Assgnmnt.empty
  𝔴 := Assgnmnt.empty
  𝔤 := Assgnmnt.empty
  𝔠 := PUnit

theorem local_pronoun_ok : (localCtx₈.𝔩 0).isSome = true := by decide

theorem boundary_clears_for_nonlocal :
    ({ localCtx₈ with 𝔩 := Assgnmnt.empty } : Cntxt₈ NLPInd).𝔩 0 = none := rfl

end NonLocalPronoun

end BoundaryAndLocality

-- ============================================================================
-- 𝔄 Filter and Full ℜ (eqs 84–88)
-- ============================================================================

section AnaphorFreeAndFullReflexivize

variable {E : Type}

/-- 𝔄(T): anaphor-free filter, eq (85). Requires r-field empty. -/
def anaphorFree₈ (P : Cntxt₈ E → Type) : Cntxt₈ E → Type :=
  λ c => propT (∀ i, c.𝔯 i = none) × P c

/-- ℜ₈(P): full reflexivization, eq (84). Clears r-field and sets 𝔰(i) = x. -/
def reflexivize₈ (i : Nat) (P : Cntxt₈ E → E → Type) : Cntxt₈ E → E → Type :=
  λ c x => P { c with 𝔯 := Assgnmnt.empty, 𝔰 := Assgnmnt.update c.𝔰 i x } x

/-- VP → V NP | 𝔄(V'(@NP')), eq (88). -/
def vpRule₈ (verb : Cntxt₈ E → E → E → Type) (np : Cntxt₈ E → E → Type)
    : Cntxt₈ E → E → Type :=
  λ c x => propT (∀ i, c.𝔯 i = none) × (y : E) × verb c x y × np c y

/-- ℜ₈ agrees with simplified ℜ when P ignores the context. -/
theorem reflexivize₈_agrees_with_simple
    (R : E → E → Type) (x : E) :
    reflexivize₈ 0 (λ _ a => R a a) Cntxt₈.initial x =
    ℜ R x := rfl

end AnaphorFreeAndFullReflexivize

-- ============================================================================
-- Generalized 𝔖 (eq 89)
-- ============================================================================

section GeneralizedClosure

variable {E : Type}

/-- Cooper (2023) eq (20). -/
abbrev ContType₈ (_E : Type) := Type

/-- 𝔖(T): underspecification closure, eq (89). 7 clauses:
    base, localize, reflexivize, align, anaphoric, store, retrieve. -/
inductive UnderspecClosure₈ (T : Type) : Type 1 where
  | base : T → UnderspecClosure₈ T
  | localize : UnderspecClosure₈ T → (Bg : Type) → UnderspecClosure₈ T
  | reflexivize : UnderspecClosure₈ T → (idx : Nat) → UnderspecClosure₈ T
  | align : UnderspecClosure₈ T → (src tgt : Nat) → UnderspecClosure₈ T
  | anaphoric : UnderspecClosure₈ T → (i j : Nat) → UnderspecClosure₈ T
  | store_ : UnderspecClosure₈ T → UnderspecClosure₈ T
  | retrieve_ : UnderspecClosure₈ T → UnderspecClosure₈ T

def TwoQuantScope.toUnderspecClosure (s : TwoQuantScope E) (w : s.𝔖) :
    UnderspecClosure₈ s.𝔖 :=
  .base w

theorem twoQuant_embeds_in_closure (s : TwoQuantScope E) (w : s.𝔖) :
    ∃ uc : UnderspecClosure₈ s.𝔖, uc = .base w :=
  ⟨.base w, rfl⟩

end GeneralizedClosure

-- ============================================================================
-- N-Quantifier Scope Generalization
-- ============================================================================

/-! ### N-quantifier scope

N quantifiers yield N! scope readings. Scope orderings are lists of
`Fin n`; list order = retrieval order (head = outermost). -/

section NQuantScopeSection

/-- N-quantifier scope: n-ary relation + n quantifiers. -/
structure NQuantScope (E : Type) (n : Nat) where
  rel : (Fin n → E) → Type
  quants : Fin n → Quant E

variable {E : Type} {n : Nat}

/-- Nest quantifiers: head = outermost, tail = innermost. -/
def NQuantScope.nestQuants (s : NQuantScope E n) :
    List (Fin n) → (Fin n → E) → Type
  | [], assignment => s.rel assignment
  | i :: rest, assignment =>
    s.quants i (λ x => s.nestQuants rest (λ j => if j = i then x else assignment j))

/-- A scope ordering: a permutation of `Fin n` as a list. -/
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

/-! #### "Someone gave every child a present" — 3 quantifiers, 6 readings. -/

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

theorem three_quant_has_six_orderings :
    [scopeOrdering₃_012, scopeOrdering₃_021, scopeOrdering₃_102,
     scopeOrdering₃_120, scopeOrdering₃_201, scopeOrdering₃_210].length = 6 := rfl

end ThreeQuant

end NQuantScopeSection

-- ============================================================================
-- Cross-Sentential Anaphora (eqs 37–44)
-- ============================================================================

/-! ### Cross-sentential anaphora

"A man walked. He whistled." — eqs (37)-(44). The pronoun resolves to
the indefinite via discourse merge: previous sentence's foreground becomes
current sentence's background under label 𝔭. -/

section CrossSententialAnaphora

variable {E : Type}

/-- Discourse merge, eqs (40)-(41). -/
structure DiscourseContext (E : Type) (PrevContent : Type) where
  𝔭 : PrevContent
  current : Cntxt₈ E

/-- Cross-sentential resolution, eqs (42)-(44): 𝔰.x₀ = ⇑𝔭.e.x -/
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

def resolved_he : CSInd :=
  crossSententialResolve (P := λ x => isMan x × walked₈ x) aManWalked

theorem resolved_he_is_john : resolved_he = .john := rfl

def manWalkedHeWhistled : Type :=
  (x : CSInd) × (isMan x × walked₈ x × whistled₈ x)

def manWalkedHeWhistled_witness : manWalkedHeWhistled :=
  ⟨.john, PUnit.unit, PUnit.unit, PUnit.unit⟩

theorem crossSentential_correct :
    ∃ w : manWalkedHeWhistled,
      w.1 = crossSententialResolve (P := λ x => isMan x × walked₈ x) aManWalked :=
  ⟨manWalkedHeWhistled_witness, rfl⟩

end ManWalkedHeWhistled

-- ============================================================================
-- Negation in Donkey Sentences (eqs 46–55)
-- ============================================================================

/-! ### "No dog which chases a cat catches it"

Eqs (46)-(55): negation + localization + path alignment. -/

section DonkeyNegation

variable {E : Type}

/-- Path alignment, eq (52): φ_{π₁=π₂} replaces path π₁ with π₂. -/
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

def noDogCatchesCat_true :
    semNo₈ dogChasesACat (λ x => (c : CatBg) × catches₈_none x c.1) :=
  fun _ _ ⟨_, h⟩ => nomatch h

/-- TRUE when no dog catches the cat it chases. -/
theorem noDogCatchesCat_true_scenario :
    Nonempty (semNo₈ dogChasesACat (λ x => (c : CatBg) × catches₈_none x c.1)) :=
  ⟨noDogCatchesCat_true⟩

/-- FALSE when every dog catches the cat it chases. -/
theorem noDogCatchesCat_false_scenario :
    IsEmpty (semNo₈ dogChasesACat (λ x => (c : CatBg) × catches₈_all x c.1)) :=
  ⟨fun f => nomatch f .dog1
    ⟨PUnit.unit, ⟨⟨.cat1, PUnit.unit⟩, PUnit.unit⟩⟩
    ⟨⟨.cat1, PUnit.unit⟩, PUnit.unit⟩⟩

/-- Negation donkey uses 𝔏 (same mechanism as classic donkey). -/
theorem donkeyNeg_uses_localization :
    dogChasesACat = (λ x => isDog₈ₙ x × 𝔏 ⟨CatBg, λ c a => chases₈ a c.1⟩ x) := rfl

end NoDogCatchesCat

end Theories.DynamicSemantics.TTR
