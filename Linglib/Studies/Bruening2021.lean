import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Studies.Larson1988
import Linglib.Studies.Pylkkanen2008

/-! # Bruening 2021 — Implicit Arguments in English Double Object Constructions
[bruening-2021]

Implicit arguments in English double object constructions.
*Natural Language and Linguistic Theory* 39:1023–1085.

## Core empirical findings

Bruening identifies four asymmetries in English ditransitives (§2.4
summary, p. 1040):

1. **Sluicing asymmetry** (G1): implicit second objects and PPs license
   sluicing, but implicit first objects never do.
2. **Interpretation asymmetry** (G2): implicit second objects and PPs
   can be definite or indefinite (depending on the verb), but implicit
   first objects are uniformly definite.
3. **Base-transitivity constraint** (G3): a simple transitive that allows
   an implicit object does NOT allow it when used in the DOC
   (*\*We're baking them* with intended-recipient reading).
4. **Frame-dependent licensing** (G4): an implicit direct object is
   licensed only in the DOC for some verbs (*show, ask, pay, serve,
   teach, feed*), only in the PP frame for others (*pass, throw, give*),
   and only *write* in both (§2.3.2 ex. (63)–(65)).

## Theoretical analysis

Bruening adopts the ApplP analysis of [marantz-1993], developed for
English in [bruening-2010a]: in DOC, the second object is selected
by V while the first object is projected by Appl(icative) above VP.
Implicit arguments of V are licensed by functional heads ∃ (indefinite)
or ι (definite) that adjoin to V; implicit arguments of functional heads
(Voice, Appl) require a higher functional head (Pass, ApplPass) to be
implicit.

Bruening explicitly *rejects* the rival accounts that this file's
contrastive theorems engage with: [pesetsky-1995]'s "both objects
selected by V" view (§3.1 p. 1041), [larson-1988]'s VP-shell
(§3.1), small-clause analyses including [pylkkanen-2008]'s low
applicative (§3.1 + fn. 10 p. 1042), and Landau 2010's null-NP
implicit-argument view (§4.1).

## Formalization scope

This file verifies Bruening's classification (Table 56, p. 1037) against
the English verb fragment via a single `decide`-checked drift sentry over
a `BruRow` table. Two cross-framework contrastive theorems make
Bruening's positions Lean-checkable against linglib's existing Pylkkänen
2008 (`english_appl.classification = .lowRecipient`) and Larson 1988
(`docDativeShift`) formalizations.

**What is formalized**: G2 directly; G3 with the implicational consequent
(*melt/build*-class transitives don't license `.np_np` as their alt frame).

**What is deferred**:
- G4 (frame-conditioned licensing) requires extending `Verb` with
  per-frame implicit fields; schema change is out of scope for this study.

**G1** (sluicing asymmetry) is formalized as a sibling in
`Studies/Bruening2021Sluicing.lean`, deriving
implicit-second-obj-licenses-sluicing-but-implicit-first-obj-doesn't from
the maximal-projection identity condition (Bruening §5.5).

## Coverage

Table (56) lists ~43 verbs across 15 cells (11 populated, 4 empty by
Bruening's footnote on p. 1037). This file covers 31 verbs whose Fragment
encoding is unambiguous; the remainder (*ask, promise, wish, leave,
afford, lose, guarantee, rent, save*) are listed in the Fragment with
attitude/question-embedding senses or absent.

The `BruRow.alternates` field encodes Bruening's classification of
DOC-vs-PP alternation. It is NOT checked by `BruRow.matches` because the
Fragment's two-slot frame schema cannot always represent
`{.np_np, .np_pp}` alternation — e.g. *tell* has `complementType =
.finiteClause, altComplementType = some .np_np`, with no PP slot
available. Treating alternation as Bruening's classification (not as a
Fragment-derivable fact) keeps the drift sentry focused on the schema
fields it can actually check.

See `Studies/HaddicanEtAl2026.lean`
(`doc_bruening` and `bruening_give_field_consistent`) for a
`SyntacticObject` witness of Bruening's V+P amalgam structure that
consumes this file's `give` Fragment entry — a complementary tree-shape
angle on the same paper.
-/

namespace Bruening2021

open English.Predicates.Verbal
open Semantics.Lexical

/-! ### Bruening's Table (56) — encoded as a row table -/

/-- A row in Bruening (56). Carries the verb, the expected
    `implicitObj`/`implicitGoal` Fragment fields per Bruening's
    classification, and Bruening's claim about whether this verb
    alternates between the DOC and PP frames.

    `alternates` is documentation of Bruening's classification, not a
    Fragment-checked claim — see the module docstring on the schema
    limitation. -/
structure BruRow where
  verb : VerbEntry
  expectedObj : Option ImplicitInterp
  expectedGoal : Option ImplicitInterp
  alternates : Bool

/-- A `BruRow` matches when the verb's Fragment fields agree with the
    expected projection. Returns `false` (rather than failing `decide`)
    so the diagnostic example below names the offending row directly. -/
def BruRow.matches (r : BruRow) : Bool :=
  r.verb.implicitObj == r.expectedObj && r.verb.implicitGoal == r.expectedGoal

/-- Bruening (56), p. 1037, encoded against the English verb fragment.
    Row groupings reflect Bruening's cell taxonomy; comments name each
    cell. -/
def bruening2021Table : List BruRow := [
  -- DOC-only, indef-implicit second obj, def-implicit first obj (Cell 6).
  ⟨charge,   some .indef, some .def,  false⟩,
  ⟨cost,     some .indef, some .def,  false⟩,
  ⟨fine,     some .indef, some .def,  false⟩,
  ⟨tip,      some .indef, some .def,  false⟩,
  ⟨pay,      some .indef, some .def,  false⟩,
  ⟨strike_,  some .indef, some .def,  false⟩,
  ⟨envy,     some .indef, some .def,  false⟩,
  -- DOC-only, def-implicit second obj, def-implicit first obj (Cell 1).
  ⟨forgive,  some .def,   some .def,  false⟩,
  -- DOC-only, def-implicit second obj, no implicit first obj (Cell 2).
  ⟨spare,    some .def,   none,       false⟩,
  -- DOC-only, no implicit second obj, no implicit first obj (Cell 12).
  ⟨begrudge, none,        none,       false⟩,
  ⟨bet,      none,        none,       false⟩,
  -- DOC-only, no implicit second obj, def-implicit first obj (Cell 11).
  ⟨deny,     none,        some .def,  false⟩,
  ⟨permit,   none,        some .def,  false⟩,
  -- Alternating, indef-implicit second obj, def-implicit goal (Cell 8).
  ⟨give,     some .indef, some .def,  true⟩,
  ⟨serve,    some .indef, some .def,  true⟩,
  -- Alternating, indef-implicit second obj, indef-implicit goal (Cell 9).
  ⟨teach,    some .indef, some .indef, true⟩,
  -- Alternating, indef-implicit second obj, no implicit goal (Cell 7).
  ⟨feed,     some .indef, none,       true⟩,
  ⟨write,    some .indef, none,       true⟩,
  -- Alternating, def-implicit second obj, no implicit goal (Cell 2-alt).
  ⟨show_,    some .def,   none,       true⟩,
  -- Alternating, def-implicit second obj, indef-implicit goal (Cell 4).
  ⟨tell,     some .def,   some .indef, true⟩,
  ⟨sell,     some .def,   some .indef, true⟩,
  ⟨pass,     some .def,   some .indef, true⟩,
  ⟨throw,    some .def,   some .indef, true⟩,
  -- Alternating, no implicit second obj, def-implicit goal (Cells 11+13).
  ⟨assign,   none,        some .def,  true⟩,
  ⟨award,    none,        some .def,  true⟩,
  ⟨forward_, none,        some .def,  true⟩,
  ⟨grant,    none,        some .def,  true⟩,
  ⟨offer,    none,        some .def,  true⟩,
  ⟨reserve,  none,        some .def,  true⟩,
  ⟨send,     none,        some .def,  true⟩,
  -- Alternating, no implicit second obj, no implicit goal (Cell 15).
  ⟨hand,     none,        none,       true⟩,
  ⟨lend,     none,        none,       true⟩
]

/-! ### Drift sentry

A single `decide`-checked theorem replaces 31 per-verb `⟨rfl, rfl⟩`
readouts. If a Fragment field changes or any verb's classification drifts,
this theorem fails — and the diagnostic example below names the offender
via `Repr`-printable output. -/

theorem verbs_match_bruening_table :
    bruening2021Table.all BruRow.matches = true := by decide

/-- Diagnostic. When `verbs_match_bruening_table` fails, this fails too,
    and the goal-state shows the residual non-empty list — naming the
    drifted verb directly via the row's verb-form field. -/
example : bruening2021Table.filter (fun r => !r.matches) = [] := by decide

/-! ### Derived verb subsets -/

/-- All ditransitive verbs in Bruening (56). Derived from the table. -/
def ditransitiveVerbs : List VerbEntry := bruening2021Table.map (·.verb)

/-- DOC-only verbs (those NOT alternating with a PP frame, per Bruening's
    classification — see module docstring on alternation). Derived. -/
def docOnlyVerbs : List VerbEntry :=
  (bruening2021Table.filter (fun r => !r.alternates)).map (·.verb)

/-! ### G2: definiteness asymmetry

Bruening's G2 (§2.4 summary point 2): implicit first objects in DOC are
uniformly definite, never indefinite. This is the empirical core of his
argument against accounts (Larson, Pesetsky) that treat both objects
symmetrically as V's selected arguments.

ANALOGUE: Bruening's ι-head (def-implicit licensor) and ApplPass
(licensor for implicit first object) have no current substrate primitives
in `Syntax/Minimalist/`. `Voice.Voice.ExternalArgSemantics` includes
`thematicExistential` (the analogue of Bruening's ∃-head); a parallel
`thematicIota` and a `Pass`-of-`Appl` head are substrate gaps. -/

theorem g2_doc_only_implicit_first_obj_definite :
    docOnlyVerbs.all (fun v => v.implicitGoal ≠ some .indef) = true := by decide

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

/-! ### G1 and G4: deferred substrate gaps

```
-- G1 (sluicing asymmetry, §2.1): formalized as a sibling in
-- `Studies/Bruening2021Sluicing.lean` via
-- `g1_sluicing_asymmetry`. Substrate: `bruening2021Identity` in
-- `Syntax/Minimalist/Ellipsis/FormalMatching.lean` § 7.
--
-- TODO(G4): Frame-conditioned implicit-arg licensing (§2.3.2 ex. 63-65).
-- The Fragment carries `implicitObj : Option ImplicitInterp` globally,
-- not per-frame. Bruening shows this distinction is real (e.g. *show*
-- is DOC-only, *pass* is PP-only, *write* is both). Schema extension
-- (`implicitObjByFrame : ComplementType → Option ImplicitInterp`) would
-- enable the theorem; deferred — out of scope for this refactor.
```
-/

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
    ∧ docOnlyVerbs.all (fun v => v.implicitGoal ≠ some .indef) = true := by
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
