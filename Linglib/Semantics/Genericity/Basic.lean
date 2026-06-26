import Mathlib.Data.Rat.Defs
import Linglib.Semantics.Quantification.Counting

/-!
# Traditional Generic Semantics (GEN Operator)

[tessler-goodman-2019] [chierchia-1995] [krifka-etal-1995]

This module formalizes the traditional covert GEN operator posited for
generic sentences like "Dogs bark", "Birds fly", etc.

GEN is grounded on the canonical generalized-quantifier substrate in
`Quantification/Counting.lean`: `traditionalGEN` is `Quantification.everyOn`
over the situation domain with restriction `normal ∧ restrictor` and nuclear
scope `scope` (true by construction — see the definition). The prevalence-based alternative is the
ℚ view `Quantification.prevalenceOn` (`prevalence`), with the threshold
reading `Quantification.thresholdGtOn` (`thresholdGeneric`).

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
circular (stipulated to give right results). The threshold-based alternative
below (`thresholdGeneric`, grounded on `Quantification.thresholdGtOn`)
eliminates it.

## Descriptive vs Definitional ([krifka-2013])

[krifka-2013] distinguishes **descriptive** generics ("Dogs bark") from
**definitional** generics ("A madrigal is polyphonic"). Only descriptive
generics are eliminable via threshold semantics; definitional generics
restrict the interpretation index, not the world index. See
`Studies/Krifka2013.lean` for the two-index formalization.

## Comparison with RSA Treatment

[tessler-goodman-2019] and [chierchia-1995] eliminate GEN via threshold semantics:
- Generic is true iff prevalence exceeds threshold
- Threshold is uncertain, inferred pragmatically
- Prior over prevalence varies by property

See `Studies/TesslerGoodman2019.lean` for the RSA account.

-/

namespace Semantics.Genericity

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

    Equivalently, `Quantification.everyOn situations.toFinset
    (λ s => normal s && restrictor s) scope`, where the restriction is the
    conjunction of normalcy and restrictor — the canonical relativized
    restricted universal.

    The key parameters:
    - `situations`: the domain of quantification (possible cases)
    - `normal`: which situations count as "normal" (the hidden parameter!)
    - `restrictor`: the kind property (e.g., "is a dog in s")
    - `scope`: the predicated property (e.g., "barks in s")

    The `normal` parameter is where all the
    context-sensitivity and exception-tolerance is hidden.
-/
@[reducible] def traditionalGEN
    (situations : List Situation)
    (normal : NormalcyPredicate)      -- THE HIDDEN PARAMETER
    (restrictor : Restrictor)
    (scope : Scope)
    : Prop :=
  Quantification.everyOn situations.toFinset
    (fun s => (normal s && restrictor s) = true) (fun s => scope s = true)

/--
Alternative formulation: existential test for counterexamples.

GEN is true iff there's no normal restrictor-situation that fails the scope.
-/
def traditionalGEN_existential
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : Prop :=
  ¬ Quantification.someOn situations.toFinset
      (fun s => (normal s && restrictor s) = true) (fun s => scope s ≠ true)

/-- The two formulations are equivalent: the relativized restricted universal
    is exactly the absence of a (normal restrictor) counterexample to scope. -/
theorem gen_formulations_equiv
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : traditionalGEN situations normal restrictor scope ↔
      traditionalGEN_existential situations normal restrictor scope := by
  unfold traditionalGEN traditionalGEN_existential Quantification.everyOn Quantification.someOn
  push_neg
  rfl

-- Prevalence-Based Alternative

/--
Prevalence: the proportion of restrictor-satisfying cases where scope holds.

Polymorphic over the domain type — works for situation-based models
([cohen-1999a], [tessler-goodman-2019]) and entity-based models
([nickel-2009]) alike. The genericity-named view of the canonical
`Quantification.prevalenceOn` (the ℚ analogue of `Rel.edgeDensity`).
-/
def prevalence {D : Type} [DecidableEq D]
    (domain : List D)
    (restrictor : D → Bool)
    (scope : D → Bool)
    : ℚ :=
  Quantification.prevalenceOn domain.toFinset
    (fun d => restrictor d = true) (fun d => scope d = true)

/--
Threshold-based generic (a la [tessler-goodman-2019]).

The generic is true iff prevalence exceeds the threshold `num/denom`.
This replaces the hidden "normalcy" with observable prevalence. The canonical
cross-multiplied `Quantification.thresholdGtOn` (division-free `Nat`
comparison) so the truth value is kernel-`decide`-able.
-/
@[reducible] def thresholdGeneric {D : Type} [DecidableEq D]
    (domain : List D)
    (restrictor : D → Bool)
    (scope : D → Bool)
    (num denom : Nat)
    : Prop :=
  Quantification.thresholdGtOn domain.toFinset
    (fun d => restrictor d = true) (fun d => scope d = true) num denom

/-!
GEN is eliminable via threshold semantics — but only for **descriptive** generics
([krifka-2013]). Definitional generics ("A madrigal is polyphonic") restrict
the interpretation index, not the world index, and cannot be reduced to a
prevalence threshold. See `Studies/TesslerGoodman2019.lean` for the RSA
account that makes the threshold uncertain and pragmatically inferred, and
`Studies/Krifka2013.lean` for the descriptive/definitional split.
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

/-- "Dogs bark" is true on the traditional (normalcy-restricted universal)
    reading: every normal dog-situation has the dog barking. -/
example : traditionalGEN dogSituations normalDogSituation isDogSituation dogBarks := by decide

/-- Prevalence of barking among the (all-dog) situations is 4/5: four of the
    five dogs bark. Routed through the count form (ℚ division is not
    kernel-`decide`-able). -/
theorem dogBarks_prevalence :
    prevalence dogSituations isDogSituation dogBarks = 4/5 := by
  have hR : Quantification.countOn dogSituations.toFinset
      (fun d => isDogSituation d = true) = 5 := by decide
  have hRS : Quantification.countOn dogSituations.toFinset
      (fun d => (isDogSituation d = true) ∧ (dogBarks d = true)) = 4 := by decide
  unfold prevalence Quantification.prevalenceOn
  rw [hR, hRS]; norm_num

/-- On the threshold reading the generic holds at θ = 1/2: prevalence 4/5
    exceeds one half. Kernel-`decide`-able via the cross-multiplied count form. -/
example : thresholdGeneric dogSituations isDogSituation dogBarks 1 2 := by decide

/-!
## Related Theory

- `Semantics/Lexical/Noun/Kind/NMP.lean` - Kind reference, bare plurals, DKP
- `Studies/TesslerGoodman2019.lean` - RSA treatment of generics

-/

-- Homogeneity Presupposition

/-- GEN's homogeneity presupposition ([magri-2009]).

    The covert generic operator GEN carries a presupposition that the
    nuclear scope either holds of ALL restrictor-satisfying elements or
    of NONE — the **YES ∪ NO** partition:

    - YES = {w | ∀s. restrictor(s) → scope(s)}   (all satisfy scope)
    - NO  = {w | ∀s. restrictor(s) → ¬scope(s)}  (none satisfy scope)

    This presupposition is detectable by negation: "It's false that John
    smokes" conveys "he never smokes," not "he doesn't always smoke."
    The stronger reading follows from the plain meaning + homogeneity
    presupposition ([von-fintel-1997]).

    Overt *always* does NOT carry this presupposition. This asymmetry
    is the key to [magri-2009] §4.6: "#John is always tall" is odd
    because the blind strengthened presupposition (asserting that
    homogeneity fails) contradicts common knowledge. -/
def genHomogeneityPresup
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : Prop :=
  Quantification.everyOn situations.toFinset
      (fun s => restrictor s = true) (fun s => scope s = true) ∨
  Quantification.noOn situations.toFinset
      (fun s => restrictor s = true) (fun s => scope s = true)

/-- Homogeneity holds when ALL restrictor-situations satisfy scope
    (the YES branch). -/
theorem homogeneity_yes
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    (h : Quantification.everyOn situations.toFinset
      (fun s => restrictor s = true) (fun s => scope s = true)) :
    genHomogeneityPresup situations restrictor scope :=
  Or.inl h

/-- Homogeneity holds when NO restrictor-situation satisfies scope
    (the NO branch). -/
theorem homogeneity_no
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    (h : Quantification.noOn situations.toFinset
      (fun s => restrictor s = true) (fun s => scope s = true)) :
    genHomogeneityPresup situations restrictor scope :=
  Or.inr h

end Semantics.Genericity
