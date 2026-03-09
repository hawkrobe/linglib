import Mathlib.Data.Rat.Defs
import Linglib.Theories.Semantics.Lexical.CovertQuantifier

/-!
# Traditional Generic Semantics (GEN Operator)

@cite{tessler-goodman-2019} @cite{chierchia-1995} @cite{krifka-etal-1995}

This module formalizes the traditional covert GEN operator posited for
generic sentences like "Dogs bark", "Birds fly", etc.

GEN is an instance of the shared covert quantifier infrastructure in
`CovertQuantifier.lean`: `traditionalGEN = covertQ` with `D = Situation`,
`restriction = normal ∧ restrictor`, `scope = scope`.

## The Traditional Account

In the standard analysis, generics involve:
1. A covert quantifier GEN over situations/cases
2. A restrictor (the kind)
3. A nuclear scope (the property)
4. A hidden normalcy parameter

Structure: GEN_s [Restrictor(s)] [NuclearScope(s)]

Example: "Dogs bark"
  → GEN_s [dog(x,s)] [bark(x,s)]
  → "In normal situations s where there's a dog x, x barks in s"

## The Problem with GEN

The `normal` parameter does all the explanatory work but is (1) not observable
(covert), (2) context-dependent (varies by property), and (3) essentially
circular (stipulated to give right results). See `CovertQuantifier.lean` for
the shared structure and the threshold-based alternative that eliminates it.

## Descriptive vs Definitional (@cite{krifka-2013})

@cite{krifka-2013} distinguishes **descriptive** generics ("Dogs bark") from
**definitional** generics ("A madrigal is polyphonic"). Only descriptive
generics are eliminable via threshold semantics; definitional generics
restrict the interpretation index, not the world index. See
`Phenomena/Generics/Studies/Krifka2013.lean` for the two-index formalization.

## Comparison with RSA Treatment

@cite{tessler-goodman-2019} and @cite{chierchia-1995} eliminate GEN via threshold semantics:
- Generic is true iff prevalence exceeds threshold
- Threshold is uncertain, inferred pragmatically
- Prior over prevalence varies by property

See `Phenomena/Generics/Studies/TesslerGoodman2019.lean` for the RSA account
and `Comparisons/GenericSemantics.lean` for the formal comparison.

-/

namespace Semantics.Lexical.Noun.Kind.Generics

open Semantics.Lexical.CovertQuantifier

-- Core Types

/-- A situation/case — the entities GEN quantifies over.

    In situation semantics, situations are parts of worlds that can be
    evaluated for truth of basic propositions. For generics, situations
    represent "cases" or "occasions" where the kind appears.

    For "Dogs bark", each situation s is a case where there is a dog
    that either barks or doesn't bark.
-/
structure Situation where
  /-- Identifier for the situation -/
  id : Nat
  deriving DecidableEq, Repr

instance : Inhabited Situation := ⟨{ id := 0 }⟩

/-- A restrictor is a property of situations (e.g., "there is a dog in s") -/
abbrev Restrictor := Situation → Bool

/-- A scope is a property of situations (e.g., "the dog barks in s") -/
abbrev Scope := Situation → Bool

/-- A normalcy predicate picks out "normal" or "characteristic" situations -/
abbrev NormalcyPredicate := Situation → Bool

-- The Traditional GEN Operator

/--
Traditional GEN as a quantifier over situations.

    GEN[restrictor][scope] is true iff
    in all NORMAL situations where restrictor holds, scope holds.

    This is essentially a restricted universal quantifier:
      ∀s. (normal(s) ∧ restrictor(s)) → scope(s)

    Equivalently, `covertQ situations (λ s => normal s && restrictor s) scope`,
    where the restriction is the conjunction of normalcy and restrictor.

    The key parameters:
    - `situations`: the domain of quantification (possible cases)
    - `normal`: which situations count as "normal" (the hidden parameter!)
    - `restrictor`: the kind property (e.g., "is a dog in s")
    - `scope`: the predicated property (e.g., "barks in s")

    The `normal` parameter is where all the
    context-sensitivity and exception-tolerance is hidden.
-/
def traditionalGEN
    (situations : List Situation)
    (normal : NormalcyPredicate)      -- THE HIDDEN PARAMETER
    (restrictor : Restrictor)
    (scope : Scope)
    : Bool :=
  situations.all λ s =>
    -- For all normal situations where restrictor holds, scope holds
    !(normal s && restrictor s) || scope s

/-- GEN is an instance of the shared covert quantifier, with restriction =
    normal ∧ restrictor. -/
theorem gen_is_covertQ
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : traditionalGEN situations normal restrictor scope =
      covertQ situations (λ s => normal s && restrictor s) scope := rfl

/--
Alternative formulation: existential test for counterexamples.

GEN is true iff there's no normal restrictor-situation that fails the scope.
-/
def traditionalGEN_existential
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : Bool :=
  !situations.any λ s => normal s && restrictor s && !scope s

/-- The two formulations are equivalent (derived from shared De Morgan proof). -/
theorem gen_formulations_equiv
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : traditionalGEN situations normal restrictor scope =
      traditionalGEN_existential situations normal restrictor scope := by
  rw [gen_is_covertQ]
  exact covertQ_equiv situations (λ s => normal s && restrictor s) scope

-- Prevalence-Based Alternative

/--
Prevalence of a property within restrictor situations.

This is `measure` from `CovertQuantifier` specialized to situations:
the proportion of restrictor-situations where the scope holds.
-/
def prevalence
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : ℚ :=
  measure situations restrictor scope

/--
Threshold-based generic (a la @cite{tessler-goodman-2019}).

The generic is true iff prevalence exceeds threshold.
This replaces the hidden "normalcy" with observable prevalence.
-/
def thresholdGeneric
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    (threshold : ℚ)
    : Bool :=
  prevalence situations restrictor scope > threshold

/-!
GEN is eliminable via threshold semantics — but only for **descriptive** generics
(@cite{krifka-2013}). Definitional generics ("A madrigal is polyphonic") restrict
the interpretation index, not the world index, and cannot be reduced to a
prevalence threshold.

The theorem `gen_eliminable` proving eliminability for the descriptive case is in
`Comparisons/GenericSemantics.lean`, which connects traditional GEN to
@cite{tessler-goodman-2019} RSA approach.
-/

-- Example: Dogs Bark

/-- Example situations for "Dogs bark" -/
def dogSituations : List Situation := [
  { id := 0 },  -- Fido barking
  { id := 1 },  -- Fido barking
  { id := 2 },  -- Rex not barking (sleeping)
  { id := 3 },  -- Spot barking
  { id := 4 },  -- Max barking
]

/-- All situations involve dogs (restrictor = true) -/
def isDogSituation : Restrictor := λ _ => true

/-- Most dogs bark in these situations -/
def dogBarks : Scope := λ s =>
  match s.id with
  | 2 => false  -- Rex is sleeping
  | _ => true

/-- "Normal" = typical/expected situations (NOT sleeping) -/
def normalDogSituation : NormalcyPredicate := λ s =>
  s.id != 2  -- Sleeping is not "normal" for purposes of barking

#guard traditionalGEN dogSituations normalDogSituation isDogSituation dogBarks
#guard prevalence dogSituations isDogSituation dogBarks == 4/5
#guard thresholdGeneric dogSituations isDogSituation dogBarks (1/2)

/-!
## Related Theory

- `Theories/Semantics/Lexical/Noun/Kind/Chierchia1998.lean` - Kind reference, bare plurals, DKP
- `Phenomena/Generics/Studies/TesslerGoodman2019.lean` - RSA treatment of generics

## Empirical Data

- `Phenomena/Generics/Data.lean` - prevalence asymmetries, rare property generics
- `Phenomena/Generics/KindReference.lean` - kind-level predicates, cross-linguistic patterns
-/

end Semantics.Lexical.Noun.Kind.Generics
