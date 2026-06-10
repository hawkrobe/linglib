import Linglib.Morphology.Containment.Superset
import Linglib.Morphology.DegreeContainment
import Linglib.Fragments.English.Modifiers.Adjectives
import Mathlib.Tactic.TFAE

/-!
# Graf (2019): Monotonicity as an effective theory of morphosyntactic variation
[graf-2019]

[graf-2019] explains typological gaps — *ABA in adjectival gradation,
person-pronoun syncretism, case syncretism, noun stem allomorphy —
with two components: a fixed base hierarchy of prominence relations,
and the requirement that the form assignment from it be **feasibly
monotonic** (his def. (6)): monotone with respect to *some* linear
order on the output forms. Forms are "just abstract variables or
bins", so only the kernel of the assignment matters; over a linear
hierarchy, feasible monotonicity is the existence of a monotone score
with the assignment's kernel.

This study connects Graf's account to the realizational engines. The
keystone is `isContiguous_tfae`: contiguity, feasible monotonicity,
Elsewhere-generability, and Superset-spellability coincide over linear
hierarchies — Graf's reconstruction and the two insertion mechanisms
are provably one constraint. Graf establishes the
monotonicity–contiguity direction by exhausting the 3-cell case ("no
feasibly monotonic function over 1 > 2 > 3 can produce a pattern of
the form ABA") and verifies larger hierarchies instance-by-instance;
the general equivalence is
`Morphology.Containment.isContiguous_iff_exists_monotone`, which this
file instantiates on his Table 1 (adjectival gradation, via the
English fragment) and Table 2 (person-pronoun syncretism,
[harbour-2015]'s survey).

The AAB asymmetry is Graf's own division of labor: "monotonicity
cannot give a unified explanation of the absence of both ABA and AAB
patterns. However, this is actually a welcome state of affairs because
AAB patterns do show up in other empirical domains" — attested in
person systems (Winnebago 12|3) but not gradation, where its absence
"has to be stipulated", e.g. via syntactic containment.
`aab_division_of_labor` states this precisely: AAB is feasibly
monotonic, and excluding it requires realization-engine conditions
([bobaljik-2012]'s (202) via `Morphology.Containment.csg2`) that the
person data show are not category-general.

**Scope.** Only Graf's *linear* hierarchies are formalized: gradation
and person (3-cell), and in principle the strict Blake/Caha case
chains. His preferred case-layer hierarchy, the PCC person-pair poset,
and the GCC gender poset are genuinely *partial* orders — and the
PCC/GCC maps go into the fixed two-element truth-value algebra (upper
sets, not kernels) — so they need a partial-order generalization of
`Pattern` and an upper-set substrate, deferred.

## Main declarations

* `FeasiblyMonotone` — Graf's def. (6), in monotone-score form
* `isContiguous_tfae` — contiguous ↔ feasibly monotonic ↔
  Elsewhere-generable ↔ Superset-spellable
* `english_suppletion_feasiblyMonotone`, `person_*` — Tables 1–2
  instantiated ([harbour-2015] for the person survey)
* `aab_division_of_labor` — monotonicity permits AAB; engine
  conditions exclude it, non-category-generally
-/

namespace Graf2019

open Morphology.Containment
open Morphology.DegreeContainment
open English.Modifiers.Adjectives

/-! ### Feasible monotonicity -/

/-- **Feasible monotonicity** ([graf-2019] def. (6)): the assignment is
monotone with respect to some linear order on the output forms. Since
forms are bins ("any two forms that are put in the same bin must have
the same exponent"), this is equivalent, over a finite linear
hierarchy, to the existence of a monotone score sharing the
assignment's kernel — the form used here. -/
def FeasiblyMonotone {n : ℕ} {F : Type*} (p : Pattern n F) : Prop :=
  ∃ g : Fin n → ℕ, Monotone g ∧ ∀ i j, p i = p j ↔ g i = g j

/-- Feasible monotonicity is contiguity —
[graf-2019]'s reconstruction of *ABA, as the general theorem his
3-cell exhaustion instantiates. -/
theorem feasiblyMonotone_iff_isContiguous {n : ℕ} {F : Type*}
    [DecidableEq F] (p : Pattern n F) :
    FeasiblyMonotone p ↔ IsContiguous p :=
  (isContiguous_iff_exists_monotone p).symm

/-! ### The keystone: four characterizations coincide -/

/-- Over a linear containment hierarchy the following are equivalent:
the pattern is contiguous; it is feasibly monotonic ([graf-2019]); it
is generable by Elsewhere insertion over a terminal antihomophonous
vocabulary (DM, [bobaljik-2012] ch. 2); it is spellable by Superset
competition over a context-free antihomophonous lexicon (nanosyntax,
[caha-2009]). Graf's "effective theory" and the two insertion
mechanisms are one constraint. -/
theorem isContiguous_tfae {n : ℕ} {F : Type*} [DecidableEq F]
    (p : Pattern n F) :
    [IsContiguous p,
     FeasiblyMonotone p,
     ∃ v : List (ExponenceRule n F), Terminal v ∧ Antihomophonous v ∧
       ∀ g, realize v g = some (p g),
     ∃ v : List (ExponenceRule n F), ContextFree v ∧ Antihomophonous v ∧
       ∀ g, spellout v g = some (p g)].TFAE := by
  tfae_have 1 ↔ 2 := (feasiblyMonotone_iff_isContiguous p).symm
  tfae_have 1 ↔ 3 := isContiguous_iff_generable p
  tfae_have 1 ↔ 4 := isContiguous_iff_spelloutGenerable p
  tfae_finish

/-! ### Table 1: adjectival gradation -/

/-- Every English fragment suppletion pattern is feasibly monotonic —
[graf-2019] Table 1's attested rows (AAA *smart*, ABB *good*), run
over the whole fragment. -/
theorem english_suppletion_feasiblyMonotone :
    ∀ e ∈ allEntries, FeasiblyMonotone e.suppletion.toPattern := by
  intro e he
  rw [feasiblyMonotone_iff_isContiguous]
  revert e he
  decide

/-- The unattested *ABA row: no codomain order makes `good – better –
goodest` monotone ("Irrespective of how this set is ordered, there can
be no monotonic function f with f(1) = f(3) ≠ f(2)"). -/
theorem aba_not_feasiblyMonotone :
    ¬ FeasiblyMonotone (Morphology.DegreeContainment.aba.toPattern) := by
  rw [feasiblyMonotone_iff_isContiguous]
  decide

/-! ### Table 2: person-pronoun syncretism

[graf-2019] §3.1 runs the same hierarchy shape over person,
`1 > 2 > 3` (the Zwicky hierarchy, [zwicky-1977]), against
[harbour-2015]'s pronoun-inventory survey (Graf's Table 2): attested
partitions include
1|2|3 (Jarawa, Kiowa), 1|23 (Damin), and crucially 12|3 (Winnebago) —
an AAB shape — while 13|2 is missing. Monotonicity carves person
exactly: "the account provides a perfect fit for the typology
[of pronouns], whereas it only carves out a superset of the attested
patterns for adjectival gradation". -/

/-- Jarawa/Kiowa: all three persons distinct (1|2|3). -/
def personDistinct : Pattern 3 ℕ := ![0, 1, 2]

/-- Damin: second and third person share a form (1|23). -/
def personDamin : Pattern 3 ℕ := ![0, 1, 1]

/-- Winnebago: first and second person share a form (12|3) — an AAB
shape, attested in person though not in gradation. -/
def personWinnebago : Pattern 3 ℕ := ![0, 0, 1]

/-- The attested person partitions are all feasibly monotonic over
`1 > 2 > 3`. -/
theorem person_attested_feasiblyMonotone :
    FeasiblyMonotone personDistinct ∧ FeasiblyMonotone personDamin ∧
      FeasiblyMonotone personWinnebago := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [feasiblyMonotone_iff_isContiguous] <;> decide

/-- The missing partition 13|2 — first and third syncretic to the
exclusion of second — is exactly the non-monotonic one. -/
theorem person_one_three_not_feasiblyMonotone :
    ¬ FeasiblyMonotone (![0, 1, 0] : Pattern 3 ℕ) := by
  rw [feasiblyMonotone_iff_isContiguous]
  decide

/-! ### The AAB division of labor -/

/-- [graf-2019]'s division of labor, stated precisely. AAB is feasibly
monotonic — monotonicity cannot exclude it, "a welcome state of
affairs" given Winnebago — so its absence in adjectival gradation
needs realization-level conditions: under antihomophony plus
[bobaljik-2012]'s markedness condition (202), no vocabulary realizes
an AAB pattern (`Morphology.Containment.csg2`). The person attestation
(`personWinnebago`) shows those conditions are not category-general —
the same point the pronominal case/number data make in
`Studies/SmithMoskalEtAl2019.lean`. -/
theorem aab_division_of_labor :
    FeasiblyMonotone (Morphology.DegreeContainment.aab.toPattern) ∧
    ∀ (v : List (ExponenceRule 3 ℕ)) (a b : ℕ), a ≠ b →
      Antihomophonous v → Grounded v →
      realize v ≠ ![some a, some a, some b] := by
  constructor
  · rw [feasiblyMonotone_iff_isContiguous]; decide
  · intro v a b hab hAH hG h
    have h01 : realize v 0 = realize v 1 := by rw [h]; rfl
    have h2 : (realize v 2).isSome := by rw [h]; rfl
    have := csg2 hAH hG h01 h2
    rw [h] at this
    exact hab (by simpa using this)

end Graf2019
