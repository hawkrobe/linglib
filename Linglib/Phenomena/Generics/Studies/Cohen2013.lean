import Linglib.Theories.Semantics.Composition.PredicateTransfer
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Theories.Semantics.Lexical.Verb.Habituals
import Linglib.Theories.Semantics.Composition.Scope
import Linglib.Theories.Semantics.Lexical.CovertQuantifier

/-!
# @cite{cohen-2013}: No Quantification without Reinterpretation

Ariel Cohen, "No Quantification without Reinterpretation." Chapter 13 in
*Genericity* (ed. Mari, Beyssade, Del Prete), OUP, pp. 334–351.

## Thesis

The generic quantifier GEN is not a phonologically null version of an overt
quantifier — it is introduced by the hearer through reinterpretation of
quantifier-free input. The two reinterpretation mechanisms (Predicate Transfer
for generics, type-shifting for habituals) explain the different scopal
properties of generics vs habituals.

## Empirical Generalizations (§13.2)

| Construction                  | Scope behavior                          |
|-------------------------------|-----------------------------------------|
| Overt quantifier (every, ∀)   | Full scope ambiguity                    |
| Generic (bare plural subject) | Ambiguous, except in opaque contexts    |
| Habitual (no restrictor)      | Narrow scope only                       |
| Habitual (with restrictor)    | Ambiguous (restrictor provides Q site)  |
| Bare plural in habitual       | Scope below habitual (DRT constraint)   |

## Core Proposal (§§13.3–13.4)

- **Generics** arise from **Predicate Transfer** (T_g, @cite{nunberg-1995}):
  T_g can apply locally (narrow scope) or globally (wide scope), yielding
  scope ambiguity. But T_g requires the intension of the transferred
  property, so it cannot scope out of opaque contexts like *believe*.

- **Habituals** arise from **type-shifting** (γ):
  Eventive verbs require interval arguments; present tense provides a
  moment → type mismatch → γ fires at the verb level (locally). Since the
  shift is local, the resulting GEN takes narrow scope only. With an overt
  restrictor or contextual restriction, there is no mismatch, so normal
  scope obtains.

## Argumentation Chain (§13.3.1 → §13.4.2)

The paper's key argument flows through the Partee-Rooth SHIFT operator:

1. SHIFT does not commute with negation (`shift_neg_noncommutative`)
2. Any type-shift shares this non-commutativity property
3. γ is a type-shift, so γ does not commute with ∃ (`gamma_noncommutative`)
4. Therefore γ must apply at the type-mismatch site (locally)
5. Therefore the existential from the indefinite scopes over γ
6. Therefore habituals take narrow scope (`habitual_narrow_scope`)

## Formalization Strategy

We verify Cohen's scope predictions using finite models, with definitions
built directly on `transferGen` and `gamma` from `PredicateTransfer.lean`:

1. **Storks / nesting areas**: T_g applied locally vs globally gives
   different truth conditions → generics are scopally ambiguous
2. **Mary / cigarettes**: γ applied locally gives the implausible narrow-
   scope reading; the plausible wide-scope reading would require global γ,
   which is unavailable because the type mismatch is at the verb level
3. **Scope hierarchy**: overt > predicateTransfer > typeShift

These connect to `PredicateTransfer.lean` (T_g, γ, SHIFT, `QuantifierSource`),
`Generics.lean` (traditionalGEN), `Habituals.lean` (traditionalHAB),
`CovertQuantifier.lean` (shared `covertQ`), and `Scope.lean` (ScopeConfig).
-/

namespace Cohen2013

open Semantics.Composition.PredicateTransfer
open Semantics.Lexical.CovertQuantifier
open Semantics.Scope (ScopeConfig)

-- ============================================================================
-- §13.2: Scopal Data
-- ============================================================================

/-- A datum recording the scope behavior of a construction type
    with respect to another operator (negation, existential, attitude). -/
structure ScopeDatum where
  sentence : String
  constructionType : String
  scopePartner : String
  wideAvailable : Bool   -- can the covert Q take wide scope?
  narrowAvailable : Bool -- can the covert Q take narrow scope?
  source : String

/-- §13.2.1: Generics interact scopally with negation.
    "Cows do not eat nettles" — ambiguous between gen > ¬ and ¬ > gen. -/
def genericNegation : ScopeDatum :=
  { sentence := "Cows do not eat nettles"
  , constructionType := "generic"
  , scopePartner := "negation"
  , wideAvailable := true   -- gen > ¬: "In general, cows don't eat nettles"
  , narrowAvailable := true -- ¬ > gen: "It's false that cows generally eat nettles"
  , source := "Krifka et al. 1995" }

/-- §13.2.1: Generics cannot scope out of opaque contexts.
    "The King believes enemy spies are loyal" — only bel > gen. -/
def genericOpaque : ScopeDatum :=
  { sentence := "The King believes enemy spies are loyal to him"
  , constructionType := "generic"
  , scopePartner := "believe"
  , wideAvailable := false  -- *gen > bel: not available
  , narrowAvailable := true -- bel > gen: "The King believes that gen..."
  , source := "Carlson 1977a" }

/-- §13.2.1: Generics exhibit scope ambiguity in transparent contexts.
    "Storks have a favorite nesting area" — gen > ∃ and ∃ > gen. -/
def genericTransparent : ScopeDatum :=
  { sentence := "Storks have a favorite nesting area"
  , constructionType := "generic"
  , scopePartner := "existential"
  , wideAvailable := true   -- gen > ∃: each stork has some area
  , narrowAvailable := true -- ∃ > gen: one area for all storks
  , source := "Schubert & Pelletier 1989" }

/-- §13.2.2: Habituals without restrictor take narrow scope only.
    "#John smokes a cigarette" — only ∃ > hab (implausible). -/
def habitualNoRestrictor : ScopeDatum :=
  { sentence := "#John smokes a cigarette"
  , constructionType := "habitual (no restrictor)"
  , scopePartner := "existential"
  , wideAvailable := false  -- *hab > ∃: unavailable
  , narrowAvailable := true -- ∃ > hab: one cigarette he always smokes
  , source := "Krifka et al. 1995" }

/-- §13.2.2: Habituals WITH restrictor are ambiguous.
    "John smokes a cigarette when he is nervous" — hab > ∃ and ∃ > hab. -/
def habitualWithRestrictor : ScopeDatum :=
  { sentence := "John smokes a cigarette when he is nervous"
  , constructionType := "habitual (with restrictor)"
  , scopePartner := "existential"
  , wideAvailable := true   -- ∃ > hab: there's a cigarette s.t. hab smokes it
  , narrowAvailable := true -- hab > ∃: each time, some cigarette
  , source := "Krifka et al. 1995" }

/-- §13.2.2: Bare plurals in habituals take scope below the habitual.
    "John smokes cigarettes" — only hab > gen (not gen > hab). -/
def barePluralInHabitual : ScopeDatum :=
  { sentence := "John smokes cigarettes"
  , constructionType := "bare plural in habitual"
  , scopePartner := "habitual"
  , wideAvailable := false  -- gen > hab: unavailable (DRT constraint)
  , narrowAvailable := true -- hab > gen: habitual scopes over bare plural
  , source := "Carlson 1977a, Cohen & Erteschik-Shir 2002" }

-- ============================================================================
-- §13.4.1: Generics via Predicate Transfer — Scope Ambiguity
-- ============================================================================

/-! ### Storks / Nesting Areas

"Storks have a favorite nesting area"

Initial LF: ∃x(nesting-area(x) ∧ have(∩storks, x))

This is anomalous: kinds don't have nesting areas — individuals do.
So Predicate Transfer applies (T_g from `PredicateTransfer.lean`),
with two options depending on the level of application:

- **Local T_g** (on the verb `have`):
  ∃x(area(x) ∧ T_g(λy.have(y,x))(∩storks))
  = ∃x(area(x) ∧ gen_y[stork(y)][have(y,x)]) — GEN takes **narrow** scope

- **Global T_g** (on the VP `have a favorite nesting area`):
  T_g(λy.∃x(area(x) ∧ have(y,x)))(∩storks)
  = gen_y[stork(y)][∃x(area(x) ∧ have(y,x))] — GEN takes **wide** scope

The kind ∩storks is modeled as `Unit` (a single kind-level entity); instances
are individual storks. This follows @cite{chierchia-1998}'s ∩ (down) operator,
where `∩storks` denotes the kind, and ∪(∩storks) gives the extension (the
set of individual storks). Here `instanceOfStork` plays the role of ∪.
-/

section GenericScope

inductive Stork where | s1 | s2 deriving DecidableEq, Repr
inductive NestArea where | a1 | a2 deriving DecidableEq, Repr

def storks : List Stork := [.s1, .s2]
def areas : List NestArea := [.a1, .a2]

/-- Each stork nests in a different area: s1→a1, s2→a2 -/
def nestsIn : Stork → NestArea → Bool
  | .s1, .a1 => true
  | .s2, .a2 => true
  | _, _ => false

/-- GEN as universal over storks (simplified: all storks are "normal"). -/
def genStork (restrictor scope : Stork → Bool) : Bool :=
  covertQ storks restrictor scope

/-- Chierchia's ∪ applied to ∩storks: every Stork is an instance of the kind. -/
def instanceOfStork (_ : Stork) (_ : Unit) : Bool := true

/-- The kind ∩storks (a single kind-level entity). -/
def storkKind : Unit := ()

/-- **Local T_g**: ∃area(T_g(λy.nestsIn(y, area))(∩storks))
    = ∃area(gen_y[stork(y)][nestsIn(y, area)])
    "There is one area that, in general, storks nest in." -/
def localTransfer : Bool :=
  areas.any fun a =>
    transferGen genStork instanceOfStork (fun y => nestsIn y a) storkKind

/-- **Global T_g**: T_g(λy.∃area(nestsIn(y, area)))(∩storks)
    = gen_y[stork(y)][∃area(nestsIn(y, area))]
    "In general, storks nest in some area (possibly different)." -/
def globalTransfer : Bool :=
  transferGen genStork instanceOfStork
    (fun y => areas.any fun a => nestsIn y a) storkKind

-- Local T_g is false: no single area works for all storks.
#guard !localTransfer

-- Global T_g is true: each stork has some area.
#guard globalTransfer

/-- **Generic scope ambiguity**: local and global T_g yield different
    truth conditions. This is why generics in transparent contexts
    are scopally ambiguous — Predicate Transfer can apply at either level.

    The two readings correspond to `ScopeConfig.surface` (∃ > gen)
    and `ScopeConfig.inverse` (gen > ∃). -/
theorem generic_scope_ambiguity :
    localTransfer = false ∧ globalTransfer = true := ⟨rfl, rfl⟩

/-- The scope ambiguity matches the empirical datum: both readings available. -/
theorem generic_both_scopes :
    genericTransparent.wideAvailable = true ∧
    genericTransparent.narrowAvailable = true := ⟨rfl, rfl⟩

end GenericScope

-- ============================================================================
-- §13.3.1 → §13.4.2: Type-Shift Locality
-- ============================================================================

/-! ### From SHIFT Non-Commutativity to γ Locality

Cohen's argument for habitual narrow scope flows through the Partee-Rooth
SHIFT operator (@cite{partee-rooth-1983}):

1. `shift_neg_noncommutative` (in `PredicateTransfer.lean`) proves that
   SHIFT does not commute with negation: ¬SHIFT(V) ≠ SHIFT(¬V).

2. γ is a type-shift (it resolves a type mismatch between eventive predicates
   and moments). Like any type-shift, γ does not commute with other operators.

3. `gamma_noncommutative` below proves the concrete instance: γ does not
   commute with the existential quantifier over our finite model.

4. Therefore γ must apply at the type-mismatch site — the verb level —
   before the existential from the indefinite object is composed in.

5. This forces the existential to scope over the habitual GEN.
-/

-- ============================================================================
-- §13.4.2: Habituals via Type-Shifting — Narrow Scope Only
-- ============================================================================

/-! ### Mary / Cigarettes

"Mary smokes a cigarette"

The verb *smoke* is eventive: λy.λx.λe.smoke(x, y, e). In present
tense, it applies to the speech time t₀ (a moment). Since an eventive
verb requires an interval but receives a moment, there is a type
mismatch. γ fires at the verb level:

γ(λe.smoke(m, c, e))(t₀) — this is what happens. THEN the object
composes, yielding: ∃c(cigarette(c) ∧ γ(λe.smoke(m, c, e))(t₀))

The existential (from the indefinite) takes wide scope over γ, giving
the implausible reading "there is one cigarette that Mary habitually smokes."

The plausible reading (different cigarettes each time) would require
GEN to scope over ∃. But that would need γ to apply globally — after
the existential is composed in — which is unavailable because the type
mismatch is at the verb level (step 4 of the argumentation chain above).
-/

section HabitualScope

inductive Occasion where | e1 | e2 | e3 deriving DecidableEq, Repr
inductive Cigarette where | c1 | c2 | c3 deriving DecidableEq, Repr

def occasions : List Occasion := [.e1, .e2, .e3]
def cigarettes : List Cigarette := [.c1, .c2, .c3]

/-- Mary smokes a different cigarette each time. -/
def smokes : Cigarette → Occasion → Bool
  | .c1, .e1 => true
  | .c2, .e2 => true
  | .c3, .e3 => true
  | _, _ => false

/-- GEN over occasions (simplified: all occasions are relevant). -/
def genHab (restrictor scope : Occasion → Bool) : Bool :=
  covertQ occasions restrictor scope

/-- All occasions are contained in the relevant interval of speech time t₀. -/
def containedInSpeech : Occasion → Unit → Bool := fun _ _ => true

/-- The speech time (a moment). -/
def speechTime : Unit := ()

/-- **Local γ** (γ at verb, then object composes):
    ∃c(cigarette(c) ∧ γ(λe.smoke(m,c,e))(t₀))
    "There is one cigarette that Mary habitually smokes." -/
def localGamma : Bool :=
  cigarettes.any fun c =>
    gamma genHab containedInSpeech (fun e => smokes c e) speechTime

/-- **Global γ** (hypothetical — if γ could apply to the whole VP):
    γ(λe.∃c(cigarette(c) ∧ smoke(m,c,e)))(t₀)
    "Mary is habitually in a situation where she smokes some cigarette." -/
def globalGamma : Bool :=
  gamma genHab containedInSpeech
    (fun e => cigarettes.any fun c => smokes c e) speechTime

-- Local γ is false: no single cigarette is smoked at all occasions.
#guard !localGamma

-- Global γ is true: at each occasion, some cigarette is smoked.
#guard globalGamma

/-- **Habitual narrow scope**: local and global γ differ, but only
    local is available. The plausible wide-scope reading is blocked
    because γ must apply at the type-mismatch site (the verb level).

    This explains why "#John smokes a cigarette" is odd: the only
    available reading (∃ > hab) is implausible. -/
theorem habitual_narrow_scope :
    localGamma = false ∧ globalGamma = true := ⟨rfl, rfl⟩

/-- The narrow-scope-only prediction matches the empirical datum. -/
theorem habitual_matches_datum :
    habitualNoRestrictor.wideAvailable = false := rfl

/-- **γ does not commute with ∃** on our model.

    This is the concrete instance of the general non-commutativity argument
    from §13.3.1 (proved abstractly for SHIFT in `shift_neg_noncommutative`).
    The non-commutativity is what forces γ to apply locally. -/
theorem gamma_noncommutative :
    localGamma ≠ globalGamma := by native_decide

end HabitualScope

-- ============================================================================
-- §13.4: Scope Hierarchy — Source Determines Behavior
-- ============================================================================

/-- Cohen's core thesis: the mechanism that introduces GEN determines
    its scope behavior. The three sources form a strict hierarchy:

    overt > predicateTransfer > typeShift

    in scope freedom. `QuantifierSource` in `PredicateTransfer.lean`
    encodes this hierarchy. -/
theorem scope_hierarchy :
    QuantifierSource.overt.canTakeWideScope = true ∧
    QuantifierSource.overt.canScopeOutOfOpaque = true ∧
    QuantifierSource.predicateTransfer.canTakeWideScope = true ∧
    QuantifierSource.predicateTransfer.canScopeOutOfOpaque = false ∧
    QuantifierSource.typeShift.canTakeWideScope = false ∧
    QuantifierSource.typeShift.canScopeOutOfOpaque = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The scope behavior of each construction type matches
    its QuantifierSource prediction. -/
theorem predictions_match_data :
    -- Generics (PT): wide scope available
    genericTransparent.wideAvailable =
      QuantifierSource.predicateTransfer.canTakeWideScope ∧
    -- Generics in opaque contexts: wide scope blocked
    genericOpaque.wideAvailable =
      QuantifierSource.predicateTransfer.canScopeOutOfOpaque ∧
    -- Habituals (type-shift): wide scope unavailable
    habitualNoRestrictor.wideAvailable =
      QuantifierSource.typeShift.canTakeWideScope :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Connection to Existing Infrastructure
-- ============================================================================

/-- Both T_g and γ produce instances of `covertQ`, confirming that
    `CovertQuantifier.lean`'s shared infrastructure correctly captures
    the common logical form. The difference is upstream (how the quantifier
    is introduced), not downstream (what it evaluates to).

    T_g with our stork model reduces to `covertQ storks` because
    `instanceOfStork y () = true` for all y, making the restrictor
    equivalent to `fun y => true` — i.e., all storks are in the domain.

    γ with our model reduces to `covertQ occasions` because
    `containedInSpeech e () = true` for all e, making the restrictor
    equivalent to `fun e => true` — i.e., all occasions are relevant. -/
theorem both_reduce_to_covertQ :
    -- T_g(nestsIn(·, a1))(∩storks) = covertQ storks (λ_ => true) (nestsIn · .a1)
    transferGen genStork instanceOfStork (fun y => nestsIn y .a1) storkKind =
    covertQ storks (fun _ => true) (fun y => nestsIn y .a1) ∧
    -- γ(smoke(c1, ·))(t₀) = covertQ occasions (λ_ => true) (smokes .c1 ·)
    gamma genHab containedInSpeech (fun e => smokes .c1 e) speechTime =
    covertQ occasions (fun _ => true) (fun e => smokes .c1 e) :=
  ⟨rfl, rfl⟩

/-- The available scope configurations for generics: both surface
    and inverse scope (matching `Scope.allScopeConfigs`). -/
theorem generic_scope_configs :
    [ScopeConfig.surface, ScopeConfig.inverse] =
    Semantics.Scope.allScopeConfigs := rfl

/-- The available scope configuration for unrestricted habituals:
    surface scope only (the covert Q takes narrow scope). -/
def habitualScopeConfigs : List ScopeConfig := [.surface]

theorem habitual_scope_restricted :
    habitualScopeConfigs.length < Semantics.Scope.allScopeConfigs.length := by
  native_decide

end Cohen2013
