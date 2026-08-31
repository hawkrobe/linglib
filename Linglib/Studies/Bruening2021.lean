import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Studies.Larson1988
import Linglib.Studies.Pylkkanen2008

/-!
# Bruening 2021: implicit arguments in English double object constructions

This file formalizes the second of the four asymmetries [bruening-2021] draws between the arguments
of an English ditransitive. Table (56) classifies the verbs on three coordinates: how an implicit
second object is interpreted, whether the goal argument is a first object or a PP, and how that
goal is interpreted when implicit. Two of the three are Fragment fields, so what this file supplies
is the goal's position, and the grid's shape is then read off the Fragment: one combination —
an indefinite implicit first object — is systematically missing, and every other is attested.

That gap is the argument against treating both objects as selected arguments of V, since on
[pesetsky-1995]'s and [larson-1988]'s accounts the two objects should be interpreted alike. In
Bruening's analysis the second object is selected by V while the first is projected by Appl above
VP ([marantz-1993], [bruening-2010a]); an implicit argument of V is licensed by an ∃ or ι head
adjoined to V, while an implicit argument of a functional head needs a higher Pass or ApplPass, and
only the ι route is available to the first object. He rejects the small-clause analyses, among them
[pylkkanen-2008]'s low applicative, and Landau's null-NP view of implicit arguments.

The sluicing asymmetry (G1) is formalized in `Studies/Bruening2021Sluicing.lean`. Frame-conditioned
licensing (G4) is not: the Fragment records `implicitObj` globally rather than per frame, so the
contrast between *show*, licensed only in the double object frame, and *pass*, licensed only in the
PP frame, needs a field indexed by complement type.

Of the roughly 43 verbs of (56), the 32 whose Fragment encoding is unambiguous are classified here;
*ask*, *promise*, *wish*, *leave*, *afford*, *lose*, *guarantee*, *rent*, *save*, *email/text* and
*bill* are absent or carry attitude senses in the Fragment.

## Main definitions

* `GoalPosition`, `classification` — where each verb's goal argument sits in (56)
* `cell` — a verb's grid coordinates, the interpretations read off the Fragment

## Main results

* `no_indefinite_implicit_first_object` — the empty cell of the grid
* `other_combinations_attested` — every other cell is populated, so the gap is not a sampling gap
* `g2_asymmetry` — the two halves together, over the Fragment's fields
* `g3_base_transitive_constraint` — a base transitive with an implicit object has no double object
  frame to license it in
* `bruening_vs_larson_implicit_first_obj`, `bruening_vs_pylkkanen_low_recipient` — the disagreements
  with the accounts formalized alongside

## References

* [bruening-2021]
* [marantz-1993]
* [larson-1988]
* [pylkkanen-2008]
* [pesetsky-1995]
-/

namespace Bruening2021

open English.Predicates.Verbal
open ArgumentStructure

/-! ### Table (56) as a grid

Bruening's table is a grid: a verb's cell is fixed by how its implicit second object is
interpreted, whether its goal argument is a first object or a PP, and how that goal is interpreted
when implicit. Two of those three coordinates are already Fragment fields, so all this file adds is
the goal's position — the classification below is the table's content that the Fragment does not
carry, and every claim about interpretation is read off the Fragment itself. -/

/-- Where a verb's goal argument sits. Bruening files alternating verbs whose arguments cannot be
implicit under "PP" as well, so this classifies the goal, not the verb's frame inventory. -/
inductive GoalPosition where
  | firstObject
  | pp
  deriving DecidableEq, Repr, BEq

/-- The position of each verb's goal in (56), for the verbs whose Fragment encoding is
unambiguous. -/
def classification : List (VerbEntry × GoalPosition) := [
  (forgive, .firstObject), (spare, .firstObject), (show_, .firstObject),
  (tell, .pp), (pass, .pp), (throw, .pp), (sell, .pp),
  (charge, .firstObject), (cost, .firstObject), (envy, .firstObject), (fine, .firstObject),
  (pay, .firstObject), (strike_, .firstObject), (tip, .firstObject),
  (feed, .firstObject), (write, .firstObject),
  (give, .pp), (serve, .pp), (teach, .pp),
  (assign, .firstObject), (deny, .firstObject), (permit, .firstObject),
  (begrudge, .firstObject), (bet, .firstObject),
  (award, .pp), (forward_, .pp), (grant, .pp), (offer, .pp), (reserve, .pp), (send, .pp),
  (hand, .pp), (lend, .pp)
]

/-- The cell a verb occupies: its second object's interpretation, its goal's position, and the
goal's interpretation — the first and third read off the Fragment. -/
def cell (vp : VerbEntry × GoalPosition) :
    Option ImplicitInterp × GoalPosition × Option ImplicitInterp :=
  (vp.1.implicitObj, vp.2, vp.1.implicitGoal)

/-! ### Derived verb subsets -/

/-- The ditransitive verbs of (56). -/
def ditransitiveVerbs : List VerbEntry := classification.map (·.1)

/-- Verbs whose goal argument is a first object. -/
def docOnlyVerbs : List VerbEntry :=
  (classification.filter (fun vp => vp.2 == .firstObject)).map (·.1)

/-! ### G2: the empty cell

Bruening's second asymmetry (§2.2.4) is a gap in the grid: an implicit first object is always
definite, while implicit second objects and implicit PPs are either. So the claim has two halves —
one combination is systematically unattested, an indefinite implicit first object, and the rest of
the grid is populated, which is what makes the gap a fact about the paradigm rather than an
artefact of the sample. Bruening draws exactly that conclusion below the table: "all possible
combinations are attested, other than the missing indefinite implicit first object interpretation".

His ι-head, the licensor of a definite implicit argument, and the ApplPass head that licenses an
implicit first object have no substrate counterpart; `Voice.Voice.ExternalArgSemantics` carries
`thematicExistential`, the analogue of his ∃-head, so a `thematicIota` and a Pass-of-Appl head are
the gaps on that side. -/

/-- The empty cell: no verb leaves a first object implicit and indefinite. -/
theorem no_indefinite_implicit_first_object :
    classification.all (fun vp =>
      vp.2 != .firstObject || vp.1.implicitGoal != some .indef) = true := by decide

/-- Every other combination is attested, so the gap is not a sampling accident. -/
theorem other_combinations_attested :
    ([(some .def, .firstObject, some .def), (some .def, .firstObject, none),
      (some .def, .pp, some .indef), (some .indef, .firstObject, some .def),
      (some .indef, .firstObject, none), (some .indef, .pp, some .def),
      (some .indef, .pp, some .indef), (none, .firstObject, some .def),
      (none, .firstObject, none), (none, .pp, some .def), (none, .pp, none)] :
        List (Option ImplicitInterp × GoalPosition × Option ImplicitInterp)).all
      (fun c => classification.any (fun vp => cell vp == c)) = true := by decide

/-- The asymmetry stated over the two positions: a first-object goal is never implicit and
indefinite, while both interpretations occur for second objects and for PP goals. -/
theorem g2_asymmetry :
    docOnlyVerbs.all (fun v => v.implicitGoal != some .indef) = true ∧
      ditransitiveVerbs.any (fun v => v.implicitObj == some .def) = true ∧
      ditransitiveVerbs.any (fun v => v.implicitObj == some .indef) = true ∧
      ditransitiveVerbs.any (fun v => v.implicitGoal == some .indef) = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ### G3: base-transitivity constraint

Bruening's G3 (§2.3.1, summary point 3): a simple transitive that allows
an implicit object does NOT allow it when used in the DOC.

The encoded consequent: *melt* and *build* (Bruening p. 1025 ex. (7)–(8))
have `complementType = .np` (transitive) with `implicitObj.isSome`, AND
have no `.np_np` alt — so the Fragment itself blocks the spurious
"implicit-second-obj-in-DOC" reading for these verbs.

(Bruening's prototypical example *bake* is not in the English fragment.) -/

def baseTransitivesWithImplicit : List VerbEntry := [melt, build]

theorem g3_base_transitive_constraint :
    baseTransitivesWithImplicit.all (fun v =>
      decide (v.complementType = .np)
      && v.implicitObj.isSome
      && decide (v.altComplementType ≠ some .np_np)) = true := by decide

/-! ### G1 and G4

G1, the sluicing asymmetry of §2.1, is formalized in `Studies/Bruening2021Sluicing.lean` over the
maximal-projection identity condition of `Syntax/Minimalist/Ellipsis/FormalMatching.lean`.

G4, frame-conditioned licensing (§2.3.2), is not formalized: the Fragment carries `implicitObj`
globally rather than per frame, so the contrast between *show*, licensed only in the double object
frame, and *pass*, licensed only in the PP frame, cannot be stated without a schema field indexed
by complement type. -/

/-! ### Cross-framework contrasts

Bruening positions his analysis explicitly against several rivals
(§3.1 + fn. 10 p. 1042 + §4.1). Two of those rivals — Pylkkänen 2008 and
Larson 1988 — are formalized in this directory. Below we make Bruening's
disagreements with them Lean-checkable. -/

/-- Bruening vs Pylkkänen 2008.

Both analyses agree that the first object of English DOC is in an
Appl-projection above V (not selected by V). Pylkkänen's `english_appl`
commits English DOC to `.lowRecipient` (`Pylkkanen2008.lean:227`); this
classification correctly predicts the structural facts about c-command,
binding, and quantifier scope.

They diverge on what licenses *implicit* first objects. Bruening's
ApplPass derivation predicts implicit first objects are *uniformly
definite* (G2 above). Pylkkänen's `.lowRecipient` classification alone
does not entail this — it requires Bruening's additional Pass/ApplPass
machinery, which has no substrate analogue (see G2 ANALOGUE note).

Bruening explicitly *rejects* Pylkkänen 2008's analysis as a "variety of
small clause analysis" (fn. 10 p. 1042). -/
theorem bruening_vs_pylkkanen_low_recipient :
    Pylkkanen2008.english_appl.classification = Minimalist.ApplType.lowRecipient
    ∧ docOnlyVerbs.all (fun v => v.implicitGoal != some .indef) = true := by
  refine ⟨rfl, ?_⟩; decide

/-- Bruening vs Larson 1988.

Larson's VP-shell analysis (`Larson1988.docDativeShift`) treats both
objects of DOC as selected arguments of V (lower V'-shell + Dative Shift
movement). This predicts implicit first objects should pattern with
implicit second objects — both arguments-of-V should behave alike.

Bruening's data refute the prediction: *pay* has indef-implicit second
object (`some .indef`) but def-implicit first object (`some .def`). The
asymmetry is the load-bearing argument against Larson (§3.1 p. 1041),
and against [pesetsky-1995]'s "both selected by V" view. -/
theorem bruening_vs_larson_implicit_first_obj :
    pay.implicitObj = some .indef
    ∧ pay.implicitGoal = some .def
    ∧ pay.implicitObj ≠ pay.implicitGoal := by
  refine ⟨rfl, rfl, ?_⟩
  decide

end Bruening2021
