import Linglib.Fragments.English.Modifiers.Adjectives
import Linglib.Morphology.Nanosyntax.Superset
import Linglib.Morphology.DegreeContainment
import Mathlib.Tactic.TFAE

/-!
# Graf (2019): Monotonicity as an effective theory of morphosyntactic variation
[graf-2019]

[graf-2019] explains typological gaps — *ABA in adjectival gradation,
person-pronoun syncretism, case syncretism, noun stem allomorphy —
with two components: a fixed base hierarchy of prominence relations,
and the requirement that the form assignment from it be feasibly
monotonic (`Morphology.FeasiblyMonotone`, his def. (6)).
The keystone here is `isContiguous_tfae`: contiguity, feasible
monotonicity, Elsewhere-generability, and Superset-spellability
coincide over linear hierarchies — Graf's "effective theory" and the
two insertion mechanisms are provably one constraint. Graf establishes
the 3-cell case by exhaustion and verifies larger hierarchies
instance-by-instance; the general equivalence is
`Morphology.isContiguous_iff_feasiblyMonotone`, which this
file instantiates on his Table 1 (adjectival gradation, via the
English fragment) and Table 2 (person-pronoun syncretism,
[harbour-2015]'s survey).

## Main declarations

* `isContiguous_tfae` — contiguous ↔ feasibly monotonic ↔
  Elsewhere-generable ↔ Superset-spellable
* `english_suppletion_feasiblyMonotone`, `person*` — Tables 1–2
  instantiated
* `aab_feasiblyMonotone`, `aab_not_groundedly_realizable` — the AAB
  division of labor

## TODO

Graf's preferred case-layer hierarchy, the PCC person-pair poset, and
the GCC gender poset are genuinely *partial* orders — and the PCC/GCC
maps go into the fixed two-element truth-value algebra (upper sets,
not kernels) — so they need a partial-order generalization of
`Paradigm` and an upper-set substrate. Concrete deferred targets: his
ban (14) on multiple cross-level case syncretisms; McFadden's
nominative stem-allomorphy generalization (16) via the conflated
hierarchy's cycle-forces-identity argument; the exactly-nine monotone
PCC maps as a finite check.
-/

namespace Graf2019

open Morphology Morphology.Containment
open Morphology.DegreeContainment
open English.Modifiers.Adjectives

/-! ### The keystone: four characterizations coincide -/

/-- Over a linear containment hierarchy the following are equivalent:
the pattern is contiguous; it is feasibly monotonic ([graf-2019]
def. (6)); it is generable by Elsewhere insertion over a terminal
antihomophonous vocabulary (DM, [bobaljik-2012] ch. 2); it is
spellable by Superset competition over a context-free antihomophonous
lexicon (nanosyntax, [caha-2009]). Graf's "effective theory" and the
two insertion mechanisms are one constraint. -/
theorem isContiguous_tfae {n : ℕ} {F : Type*} (p : Paradigm n F) :
    [IsContiguous p,
     FeasiblyMonotone p,
     ElsewhereGenerable p,
     SupersetSpellable p].TFAE := by
  tfae_have 1 ↔ 2 := isContiguous_iff_feasiblyMonotone p
  tfae_have 1 ↔ 3 := isContiguous_iff_generable p
  tfae_have 1 ↔ 4 := isContiguous_iff_spelloutGenerable p
  tfae_finish

/-! ### Table 1: adjectival gradation -/

/-- Every English fragment suppletion pattern is feasibly monotonic —
[graf-2019] Table 1's attested rows (AAA *smart*, ABB *good*), run
over the whole fragment. -/
theorem english_suppletion_feasiblyMonotone :
    ∀ e ∈ allEntries, FeasiblyMonotone e.suppletion.toParadigm := by
  simp only [← isContiguous_iff_feasiblyMonotone]
  decide

/-- The unattested *ABA row: no codomain order makes `good – better –
goodest` monotone ("Irrespective of how this set is ordered, there can
be no monotonic function f with f(1) = f(3) ≠ f(2)"). -/
theorem aba_not_feasiblyMonotone : ¬ FeasiblyMonotone aba.toParadigm := by
  rw [← isContiguous_iff_feasiblyMonotone]
  decide

/-! ### Table 2: person-pronoun syncretism

[graf-2019] §3.1 runs the same hierarchy shape over person,
`1 > 2 > 3` (the Zwicky hierarchy, [zwicky-1977]; the repo's
feature-level anchor for it is `Person.hierarchyRank`), against
[harbour-2015]'s pronoun-inventory survey (Graf's Table 2): attested
partitions include 1|2|3 (Jarawa, Kiowa), 1|23 (Damin), and crucially
12|3 (Winnebago) — an AAB shape — while 13|2 is missing from the
survey, as monotonicity predicts: "the account provides a perfect fit
for the typology [of pronouns], whereas it only carves out a superset
of the attested patterns for adjectival gradation and case
syncretism." The encoding runs the hierarchy with index ascending
1 → 3, the dual of Graf's prominence order — equivalent for (feasible)
monotonicity, his fn. 1. -/

/-- Jarawa, Kiowa: all three persons distinct (1|2|3). -/
def personJarawa : Paradigm 3 ℕ := ![0, 1, 2]

/-- Damin: second and third person share a form (1|23). -/
def personDamin : Paradigm 3 ℕ := ![0, 1, 1]

/-- Winnebago: first and second person share a form (12|3) — an AAB
shape, attested in person though not in gradation. -/
def personWinnebago : Paradigm 3 ℕ := ![0, 0, 1]

/-- The unattested partition 13|2: first and third persons syncretic
to the exclusion of second. -/
def personGap : Paradigm 3 ℕ := ![0, 1, 0]

/-- The attested person partitions are all feasibly monotonic over
`1 > 2 > 3`. -/
theorem person_attested_feasiblyMonotone :
    FeasiblyMonotone personJarawa ∧ FeasiblyMonotone personDamin ∧
      FeasiblyMonotone personWinnebago := by
  simp only [← isContiguous_iff_feasiblyMonotone]
  decide

/-- The missing partition is exactly the non-monotonic one. -/
theorem personGap_not_feasiblyMonotone : ¬ FeasiblyMonotone personGap := by
  rw [← isContiguous_iff_feasiblyMonotone]
  decide

/-! ### The AAB division of labor

[graf-2019]: "monotonicity cannot give a unified explanation of the
absence of both ABA and AAB patterns. However, this is actually a
welcome state of affairs because AAB patterns do show up in other
empirical domains" — attested in person (Winnebago), unattested in
adjectival gradation, where the absence "has to be stipulated", e.g.
in terms of syntactic containment (his suggestion). The pair below
states the division precisely: AAB is feasibly monotonic, and its
gradation-side exclusion is carried by realization-level conditions
([bobaljik-2012]'s markedness condition (202), via
`Morphology.Containment.realize_const_of_grounded`) — which the person
attestation shows
are not category-general, the same point the pronominal case/number
data make in `Studies/SmithMoskalEtAl2019.lean`. -/

/-- AAB is feasibly monotonic: Graf's account cannot — and, given
Winnebago, should not — exclude it. -/
theorem aab_feasiblyMonotone : FeasiblyMonotone aab.toParadigm := by
  rw [← isContiguous_iff_feasiblyMonotone]
  decide

/-- Under antihomophony plus the markedness condition (202), no
vocabulary realizes an AAB pattern — the gradation-side exclusion,
carried by the realization engine rather than by monotonicity. -/
theorem aab_not_groundedly_realizable {v : List (SpanRule 3 ℕ)}
    {a b : ℕ} (hAH : Antihomophonous v) (hG : Grounded v) (hab : a ≠ b) :
    realize v ≠ ![some a, some a, some b] := by
  intro h
  have h01 : realize v 0 = realize v 1 := by simp [h]
  have h2 : (realize v 2).isSome := by simp [h]
  have h12 := realize_const_of_grounded hAH hG h01 h2
  rw [h] at h12
  exact hab (by simpa using h12)

end Graf2019
