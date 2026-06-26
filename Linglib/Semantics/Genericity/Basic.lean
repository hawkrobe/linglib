import Mathlib.Data.Rat.Defs
import Linglib.Semantics.Quantification.Counting

/-!
# Traditional generic semantics: the GEN operator

The traditional covert GEN operator posited for generic sentences such as
"Dogs bark", grounded on the generalized-quantifier substrate in
`Quantification/Counting.lean`.

## Main definitions

* `traditionalGEN`: GEN as a normalcy-restricted universal — `Quantification.everyOn`
  with restriction `normal ∧ restrictor`.
* `traditionalGEN_existential`: the equivalent no-counterexample formulation.
* `prevalence`: the proportion of restrictor-satisfying cases that satisfy scope (ℚ).
* `thresholdGeneric`: the prevalence-exceeds-threshold reading, on
  `Quantification.thresholdGtOn`.

## Main statements

* `gen_formulations_equiv`: the universal and no-counterexample formulations agree.

## Notes

The `normal` parameter carries the account's empirical content: it is unobservable,
context-dependent, and the locus of exception-tolerance — hence also its critics'
main target ([nickel-2009]). `thresholdGeneric` replaces it with observable
prevalence (the *absolute* reading of [cohen-1999a]), but per [krifka-2013] this
eliminates GEN only for **descriptive** generics ("Dogs bark"), not **definitional**
ones ("A madrigal is polyphonic"), which restrict the interpretation index rather
than the world index. [chierchia-1995] instead *posits* a generic operator
(individual-level predicates as inherent generics). [tessler-goodman-2019] keeps a
threshold but makes it uncertain and pragmatically inferred; see
`Studies/TesslerGoodman2019.lean` and `Studies/Krifka2013.lean`.

## References

* [krifka-etal-1995], [chierchia-1995], [cohen-1999a], [nickel-2009], [krifka-2013],
  [tessler-goodman-2019]

## Tags

genericity, generic, GEN, characterizing sentence, normalcy, prevalence, threshold
-/

namespace Semantics.Genericity

/-! ### Core types -/

/-- A situation (case) — what GEN quantifies over. In situation semantics a
situation is a part of a world evaluable for basic propositions; for generics it is
a "case" where the kind appears (for "Dogs bark", a case with a dog that barks or
doesn't). Modelled here as an opaque index. -/
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

/-! ### The traditional GEN operator -/

/-- Traditional GEN as a normalcy-restricted universal over situations:
`GEN[restrictor][scope]` holds iff `scope` holds in every *normal* situation
satisfying `restrictor`, i.e. `∀ s, normal s ∧ restrictor s → scope s`. The hidden
`normal` parameter is where context-sensitivity and exception-tolerance live. -/
@[reducible] def traditionalGEN
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : Prop :=
  Quantification.everyOn situations.toFinset
    (fun s => (normal s && restrictor s) = true) (fun s => scope s = true)

/-- Existential formulation of `traditionalGEN`: there is no normal
restrictor-situation that fails `scope`. -/
def traditionalGEN_existential
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : Prop :=
  ¬ Quantification.someOn situations.toFinset
      (fun s => (normal s && restrictor s) = true) (fun s => scope s ≠ true)

/-- The two formulations agree: the normalcy-restricted universal is exactly the
absence of a normal restrictor-counterexample to `scope`. -/
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

/-! ### Prevalence-based alternative -/

/-- The proportion of restrictor-satisfying cases of `domain` that satisfy `scope`
(ℚ). The genericity-named view of `Quantification.prevalenceOn` (the ℚ analogue of
`Rel.edgeDensity`); polymorphic over the domain, so it serves situation-based
([cohen-1999a], [tessler-goodman-2019]) and entity-based ([nickel-2009]) models. -/
def prevalence {D : Type} [DecidableEq D]
    (domain : List D)
    (restrictor : D → Bool)
    (scope : D → Bool)
    : ℚ :=
  Quantification.prevalenceOn domain.toFinset
    (fun d => restrictor d = true) (fun d => scope d = true)

/-- Threshold generic: holds iff prevalence exceeds the fixed threshold `num/denom`
— the *absolute* reading of [cohen-1999a], replacing the hidden `normal` with
observable prevalence. Uses the cross-multiplied `Quantification.thresholdGtOn`
(division-free `Nat` comparison), so the truth value is kernel-`decide`-able.
[tessler-goodman-2019] instead makes the threshold uncertain and pragmatically
inferred (see `Studies/TesslerGoodman2019.lean`). -/
@[reducible] def thresholdGeneric {D : Type} [DecidableEq D]
    (domain : List D)
    (restrictor : D → Bool)
    (scope : D → Bool)
    (num denom : Nat)
    : Prop :=
  Quantification.thresholdGtOn domain.toFinset
    (fun d => restrictor d = true) (fun d => scope d = true) num denom

/-! ### Example: dogs bark -/

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

/-- "Dogs bark" holds on the traditional (normalcy-restricted) reading: every normal
dog-situation has the dog barking. -/
example : traditionalGEN dogSituations normalDogSituation isDogSituation dogBarks := by decide

/-- Prevalence of barking among the (all-dog) situations is `4/5`. Routed through the
count form (ℚ division is not kernel-`decide`-able). -/
theorem dogBarks_prevalence :
    prevalence dogSituations isDogSituation dogBarks = 4/5 := by
  have hR : Quantification.countOn dogSituations.toFinset
      (fun d => isDogSituation d = true) = 5 := by decide
  have hRS : Quantification.countOn dogSituations.toFinset
      (fun d => (isDogSituation d = true) ∧ (dogBarks d = true)) = 4 := by decide
  unfold prevalence Quantification.prevalenceOn
  rw [hR, hRS]; norm_num

/-- On the threshold reading the generic holds at θ = 1/2: prevalence `4/5` exceeds
one half, kernel-`decide`-able via the cross-multiplied count form. -/
example : thresholdGeneric dogSituations isDogSituation dogBarks 1 2 := by decide

end Semantics.Genericity
