module

public import Linglib.Fragments.English.Adjectives
public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Linglib.Syntax.Person.Basic
public import Linglib.Syntax.Agreement.PersonCaseConstraint
public import Mathlib.Tactic.TFAE

/-!
# Graf (2019): Monotonicity as an Effective Theory of Morphosyntactic Variation

Graf explains typological gaps in adjectival gradation (*ABA), person-pronoun syncretism and the
Person Case Constraint by two components: a fixed base hierarchy of prominence relations, and the
requirement that the map from it to surface forms be feasibly monotonic, his definition (6). Over
a linear hierarchy feasible monotonicity coincides with contiguity, Elsewhere-generability and
Superset-spellability, so the effective theory and the two insertion mechanisms are one
constraint. A Person Case Constraint is a monotone map from the reduced dual person hierarchy
(27) to the truth values.

## Main results

* `isContiguous_tfae`: the four characterizations coincide over a linear hierarchy.
* `english_suppletion_feasiblyMonotone`, `aba_not_feasiblyMonotone`: Table 1's adjectival
  patterns over the English fragment.
* `person_attested_feasiblyMonotone`, `personGap_not_feasiblyMonotone`: Table 2's person
  systems over Zwicky's hierarchy.
* `aab_feasiblyMonotone`, `aab_not_groundedly_realizable`: monotonicity leaves the
  gradation-side *AAB to the realization engine.
* `monotone_iff`: exactly nine of the 64 conceivable constraints are monotone, the four of Table 4
  (`table4`) among them.
* `unattested_singleton_class`: the two monotone constraints without an attested pattern single
  out one combination.
* `uPCC_not_monotone_naive`: over the naive product hierarchy (23) the ultrastrong constraint is
  not monotone.

## Implementation notes

The person hierarchy is `Person.prominence`, Zwicky's order 1 > 2 > 3, which on the three persons
is the inclusion order of Nevins's privative bundles, as the paper observes
(`Person.prominence_le_iff_subset`). Table 2's paradigms index the persons ascending from the
first, the dual order, equivalent for feasible monotonicity by the paper's footnote 1. A constraint
is six truth values, one per off-diagonal combination of indirect and direct object, the diagonal
excluded as the paper does; Table 4's constraints are those of Pancheva and Zubizarreta's
grammars.

## TODO

The case-layer hierarchy (13) and the Gender Case Constraint are partial orders whose maps
need a partial-order generalization of `Paradigm`: the ban (14) on multiple cross-level case
syncretisms and the nominative stem-allomorphy generalization (16) remain.

## References

* [graf-2019]
* [bobaljik-2012]
* [bobaljik-sauerland-2018]
* [harbour-2015]
* [zwicky-1977b]
* [caha-2009]
* [nevins-2007]
* [pancheva-zubizarreta-2018]
-/

@[expose] public section

namespace Graf2019

open Morphology Morphology.Containment
open English.Adjectives

/-! ### Four characterizations coincide over a linear hierarchy -/

/-- Over a linear containment hierarchy, contiguity, feasible monotonicity (definition (6)),
generability by Elsewhere insertion over a terminal antihomophonous vocabulary ([bobaljik-2012])
and spellability by Superset competition over a context-free antihomophonous lexicon
([caha-2009]) are equivalent. -/
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

/-- Every suppletion pattern of the English fragment is feasibly monotonic, Table 1's attested
rows AAA *smart* and ABB *good*. -/
theorem english_suppletion_feasiblyMonotone :
    ∀ e ∈ allEntries, FeasiblyMonotone e.comparison.suppletion := by
  intro e he
  rw [← isContiguous_iff_feasiblyMonotone]
  revert e he
  decide +kernel

/-- No order on the forms makes *good, better, goodest* monotone, whatever the order of the
codomain, so the *ABA row is unattested. -/
theorem aba_not_feasiblyMonotone : ¬ FeasiblyMonotone Paradigm.aba := by
  rw [← isContiguous_iff_feasiblyMonotone]
  decide

/-! ### Table 2: person-pronoun syncretism

Section 3.1 runs the same hierarchy over person, `1 > 2 > 3`, against [harbour-2015]'s survey:
attested are 1|2|3 (Jarawa, Kiowa), 1|23 (Damin), and 12|3 (Winnebago), an AAB shape, while
13|2 is missing, as monotonicity predicts. -/

/-- Jarawa and Kiowa distinguish all three persons (1|2|3). -/
def personJarawa : Paradigm 3 ℕ := ![0, 1, 2]

/-- In Damin the second and third persons share a form (1|23). -/
def personDamin : Paradigm 3 ℕ := ![0, 1, 1]

/-- In Winnebago the first and second persons share a form (12|3), an AAB shape. -/
def personWinnebago : Paradigm 3 ℕ := ![0, 0, 1]

/-- The unattested partition 13|2 makes the first and third persons syncretic to the exclusion
of the second. -/
def personGap : Paradigm 3 ℕ := ![0, 1, 0]

/-- The attested person partitions are feasibly monotonic over `1 > 2 > 3`. -/
theorem person_attested_feasiblyMonotone :
    FeasiblyMonotone personJarawa ∧ FeasiblyMonotone personDamin ∧
      FeasiblyMonotone personWinnebago := by
  simp only [← isContiguous_iff_feasiblyMonotone]
  decide

/-- The missing partition is the non-monotonic one. -/
theorem personGap_not_feasiblyMonotone : ¬ FeasiblyMonotone personGap := by
  rw [← isContiguous_iff_feasiblyMonotone]
  decide

/-! ### The AAB division of labor

Monotonicity cannot exclude both ABA and AAB, and the paper welcomes this: AAB is attested in
person (Winnebago) though not in adjectival gradation, where its absence has to be stipulated,
for instance in terms of syntactic containment. -/

/-- AAB is feasibly monotonic. -/
theorem aab_feasiblyMonotone : FeasiblyMonotone Paradigm.aab := by
  rw [← isContiguous_iff_feasiblyMonotone]
  decide

/-- Under antihomophony and [bobaljik-2012]'s markedness condition no vocabulary realizes an
AAB pattern, so the gradation-side exclusion is carried by the realization engine, not by
monotonicity. -/
theorem aab_not_groundedly_realizable {v : List (SpanRule 3 ℕ)}
    {a b : ℕ} (hAH : Antihomophonous v) (hG : Grounded v) (hab : a ≠ b) :
    realize v ≠ ![some a, some a, some b] := by
  intro h
  have h01 : realize v 0 = realize v 1 := by simp [h]
  have h2 : (realize v 2).isSome := by simp [h]
  have h12 := realize_const_of_grounded hAH hG h01 h2
  rw [h] at h12
  exact hab (by simpa using h12)

/-! ### Section 4: the Person Case Constraint as a monotone map -/

/-- A clitic combination pairs the persons of the indirect and the direct object, the diagonal
excluded. -/
inductive Combination where
  | io1do2
  | io1do3
  | io2do1
  | io2do3
  | io3do1
  | io3do2
  deriving DecidableEq, Fintype

/-- The indirect object's person. -/
def Combination.io : Combination → Person
  | .io1do2 | .io1do3 => .first
  | .io2do1 | .io2do3 => .second
  | .io3do1 | .io3do2 => .third

/-- The direct object's person. -/
def Combination.do : Combination → Person
  | .io2do1 | .io3do1 => .first
  | .io1do2 | .io3do2 => .second
  | .io1do3 | .io2do3 => .third

/-- In the reduced dual person hierarchy (27) a combination is below another when its indirect
object is at most as prominent and its direct object at least as prominent, the product of the
person hierarchy with its dual, so that `1, 3` is the top and `3, 1` the bottom. -/
def Combination.Below (p q : Combination) : Prop :=
  p.io.prominence ≤ q.io.prominence ∧ q.do.prominence ≤ p.do.prominence

/-- The naive reduced hierarchy (23), which the paper rejects, is the product of the person
hierarchy with itself. -/
def Combination.BelowNaive (p q : Combination) : Prop :=
  p.io.prominence ≤ q.io.prominence ∧ p.do.prominence ≤ q.do.prominence

instance (p q : Combination) : Decidable (p.Below q) := inferInstanceAs (Decidable (_ ∧ _))
instance (p q : Combination) : Decidable (p.BelowNaive q) := inferInstanceAs (Decidable (_ ∧ _))

/-- A Person Case Constraint says which of the six combinations are well-formed, Table 4's
cells. -/
structure PCC where
  io1do2 : Bool
  io1do3 : Bool
  io2do1 : Bool
  io2do3 : Bool
  io3do1 : Bool
  io3do2 : Bool
  deriving DecidableEq, Repr

/-- A constraint is six truth values. -/
def PCC.equivProd : PCC ≃ Bool × Bool × Bool × Bool × Bool × Bool where
  toFun c := (c.io1do2, c.io1do3, c.io2do1, c.io2do3, c.io3do1, c.io3do2)
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype PCC := Fintype.ofEquiv _ PCC.equivProd.symm

/-- `c.allows p` is the constraint's verdict on a combination. -/
def PCC.allows (c : PCC) : Combination → Bool
  | .io1do2 => c.io1do2
  | .io1do3 => c.io1do3
  | .io2do1 => c.io2do1
  | .io2do3 => c.io2do3
  | .io3do1 => c.io3do1
  | .io3do2 => c.io3do2

/-- `PCC.ofPred f` is the constraint the verdict function `f` defines. -/
def PCC.ofPred (f : Combination → Bool) : PCC :=
  ⟨f .io1do2, f .io1do3, f .io2do1, f .io2do3, f .io3do1, f .io3do2⟩

/-- There are sixty-four conceivable constraints. -/
theorem card_pcc : Fintype.card PCC = 64 := by decide

/-- A constraint is monotone over a hierarchy when well-formedness never decreases upward, its
map to the algebra of truth values being monotonic. -/
def PCC.MonotoneOver (r : Combination → Combination → Prop) (c : PCC) : Prop :=
  ∀ p q, r p q → c.allows p = true → c.allows q = true

instance (r : Combination → Combination → Prop) [∀ p q, Decidable (r p q)] (c : PCC) :
    Decidable (c.MonotoneOver r) :=
  inferInstanceAs (Decidable (∀ _ _, _ → _ → _))

/-- `c.reverse` reverses the verdicts, the other order of the truth values. -/
def PCC.reverse (c : PCC) : PCC := .ofPred fun p ↦ !c.allows p

/-- `PCC.ofGrammar g` is the constraint a grammar of the P-Constraint family predicts. -/
def PCC.ofGrammar (g : PCC.Grammar) : PCC := .ofPred fun p ↦ decide (PCC.IsLicit g p.io p.do)

/-- `sPCC` is the Strong constraint (19a). -/
def sPCC : PCC := .ofGrammar PCC.strongGrammar

/-- `uPCC` is the Ultrastrong constraint (19b). -/
def uPCC : PCC := .ofGrammar PCC.ultraStrongGrammar

/-- `wPCC` is the Weak constraint (19c). -/
def wPCC : PCC := .ofGrammar PCC.weakGrammar

/-- `mPCC` is the Me-first constraint (19d). -/
def mPCC : PCC := .ofGrammar PCC.meFirstGrammar

/-- Table 4 states, in the paper's words (19), that the direct object must be third person, that
it is less prominent than the indirect object, that a third-person indirect object combines only
with a third-person direct object, and that a second- or third-person indirect object excludes a
first-person direct object. -/
theorem table4 :
    (∀ p, sPCC.allows p = true ↔ p.do = .third) ∧
      (∀ p, uPCC.allows p = true ↔ p.do.prominence < p.io.prominence) ∧
      (∀ p, wPCC.allows p = true ↔ (p.io = .third → p.do = .third)) ∧
      ∀ p, mPCC.allows p = true ↔ (p.io ≠ .first → p.do ≠ .first) := by
  decide

/-- `fPCC` allows free combination, as in German. -/
def fPCC : PCC := .ofPred fun _ ↦ true

/-- `iPCC` is indiscriminate, no clitics combining, as in Cairene Arabic. -/
def iPCC : PCC := .ofPred fun _ ↦ false

/-- In Choctaw as reanalyzed in (31) only a first-person indirect object combines. -/
def cPCC : PCC := .ofPred fun p ↦ p.io = .first

/-- In the first constraint of (32) only `1, 3` is licit. -/
def only13 : PCC := .ofPred fun p ↦ p = .io1do3

/-- In the second constraint of (32) only `3, 1` is illicit. -/
def allBut31 : PCC := .ofPred fun p ↦ p ≠ .io3do1

/-- The constraints with an attested pattern are Table 4's, the free and indiscriminate ones of
(28), and Choctaw's. -/
def attested : List PCC := [sPCC, uPCC, wPCC, mPCC, fPCC, iPCC, cPCC]

/-- Exactly nine constraints are monotone over the hierarchy (27), the seven attested ones and
the two of (32) (section 4.3). -/
theorem monotone_iff :
    ∀ c : PCC, c.MonotoneOver Combination.Below ↔ c ∈ attested ++ [only13, allBut31] := by
  decide

/-- The two monotone constraints without an attested pattern are exactly those whose class of
well-formed or of ill-formed combinations is a singleton. -/
theorem unattested_singleton_class :
    ∀ c : PCC, c.MonotoneOver Combination.Below →
      (c ∉ attested ↔ (Finset.univ.filter fun p ↦ c.allows p = true).card = 1 ∨
        (Finset.univ.filter fun p ↦ c.allows p = false).card = 1) := by
  decide

/-- Over the naive hierarchy (23) the ultrastrong constraint is not monotone, nor is its reversal,
so no order of the truth values rescues it, while the weak constraint is (25). -/
theorem uPCC_not_monotone_naive :
    ¬ uPCC.MonotoneOver Combination.BelowNaive ∧
      ¬ uPCC.reverse.MonotoneOver Combination.BelowNaive ∧
      wPCC.MonotoneOver Combination.BelowNaive := by
  decide

end Graf2019
