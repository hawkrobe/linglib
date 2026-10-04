module

public import Linglib.Semantics.Presupposition.Trivalent
public import Linglib.Logic.Aristotelian.Square
public import Linglib.Semantics.Quantification.NP
public import Linglib.Data.Examples.Belnap1970

/-!
# Belnap (1970): Conditional Assertion and Restricted Quantification

Belnap reads "if p then q" as a *conditional assertion*, the assertion of q on the condition p,
which is assertive only where p is true and is as if never made elsewhere. Each sentence gets four
semantic coordinates per world (p. 3), true, false, assertive and what it asserts, which are the
two fields of `PartialProp`. Combining conditional assertion (3) with universal quantification
(10) derives restricted quantification (11): "All crows are black" becomes "Consider the crows:
each one is black", assertive only if there are crows.

## Main statements

* `belnap_forall_content_eq_every`, `belnap_exists_content_eq_some`: the restricted forms
  (11)–(12) assert `every` and `GQ.some`, and their shared assertiveness condition is Strawson's
  existential presupposition, here derived rather than stipulated.
* `contentSquare_eq_square`, `content_square_relations`: the asserted contents of the four forms
  are the quantifier square at the restrictor, so they stand in all six relations of the square
  whenever the restrictor is non-empty, which is exactly where they are assertive.
* `i_conversion_equitrue`, `i_conversion_not_equiassertive`, `barbara`: conversion preserves
  truth but not assertiveness, and Barbara's major does all the implying (pp. 8–9).

## References

* [belnap-1970]
* [quine-1950]
* [strawson-1952]
-/

@[expose] public section

namespace Belnap1970

open Presupposition
open Aristotelian (Square SquareRelations)
open Quantifier Quantifier.GQ Quantifier.NP

/-! ### Belnap's functors in the `PartialProp` substrate ((3), (6)–(10))

The four concepts of p. 3 are `PartialProp`'s fields: `presup` is
assertiveness, `assertion` the asserted content. (3) is
`PartialProp.condAssert` — assertive where the antecedent is true,
asserting the consequent there; (6)'s categorical atoms are
`PartialProp.ofProp`, assertive everywhere; (7) is `PartialProp.neg`,
which preserves assertiveness (`PartialProp.neg_presup`); the
skip-undefined conjunction (8) and disjunction (9) are
`PartialProp.andBelnap` and `PartialProp.orBelnap`, assertive iff at
least one operand is. The quantifiers (10) — assertive iff some instance
is, asserting the conjunction/disjunction of the assertive instances —
specialize to the restricted forms below when the instances are
conditional assertions over categorical predicates. -/

variable {E : Type}

/-- Restricted universal quantification ∀x(Cx/Bx) (11) is assertive iff ∃xCx and asserts the
conjunction of Bt for the t with Ct true, the A-form as "consider the crows: each one is
black". -/
def restrictedForall (C B : E → Prop) : PartialProp Unit where
  presup := fun _ => ∃ x : E, C x
  assertion := fun _ => ∀ x : E, C x → B x

/-- Restricted existential quantification ∃x(Cx/Bx) (12) is assertive iff ∃xCx and asserts the
disjunction of Bt for the t with Ct true. -/
def restrictedExists (C B : E → Prop) : PartialProp Unit where
  presup := fun _ => ∃ x : E, C x
  assertion := fun _ => ∃ x : E, C x ∧ B x

/-! ### The content is generalized quantification -/

/-- What (11) asserts, when assertive, is exactly `every`. -/
theorem belnap_forall_content_eq_every (C B : E → Prop) :
    (restrictedForall C B).assertion () ↔ every C B := Iff.rfl

/-- What (12) asserts, when assertive, is exactly `GQ.some`. -/
theorem belnap_exists_content_eq_some (C B : E → Prop) :
    (restrictedExists C B).assertion () ↔ GQ.some C B := Iff.rfl

/-- Assertiveness of (11) is the existential presupposition of universals, which Strawson
stipulated and Belnap derives, since ∀x(Cx/Bx) is nonassertive when nothing satisfies C. -/
theorem assertive_iff_restrictor_nonempty (C B : E → Prop) :
    (restrictedForall C B).presup () ↔ ∃ x : E, C x := Iff.rfl

/-! ### The square of opposition -/

/-- The four Aristotelian forms as restricted quantifications make up a square, since "semantic
relations between these forms turn out ... to constitute what is pretty much a good old
fashioned square of opposition" (p. 8). -/
def belnapSquare (C B : E → Prop) : Square (PartialProp Unit) where
  A := restrictedForall C B
  E := restrictedForall C (fun x => ¬B x)
  I := restrictedExists C B
  O := restrictedExists C (fun x => ¬B x)

/-- All four forms share one assertiveness condition, ∃xCx, so the square's relations are as
strong as possible, with equi-assertiveness on top of the content relations (p. 8). -/
theorem square_equiassertive (C B : E → Prop) :
    (belnapSquare C B).A.presup = (belnapSquare C B).E.presup ∧
    (belnapSquare C B).A.presup = (belnapSquare C B).I.presup ∧
    (belnapSquare C B).A.presup = (belnapSquare C B).O.presup :=
  ⟨rfl, rfl, rfl⟩

/-- Abstracting over the scope, the asserted contents of the four forms make up a square in the
Boolean algebra `(E → Prop) → Prop`. -/
def contentSquare (C : E → Prop) : Square ((E → Prop) → Prop) where
  A B := (belnapSquare C B).A.assertion ()
  E B := (belnapSquare C B).E.assertion ()
  I B := (belnapSquare C B).I.assertion ()
  O B := (belnapSquare C B).O.assertion ()

/-- The content square is the square of `every`, `no`, `some` and `not every` at the
restrictor `C`. -/
theorem contentSquare_eq_square (C : E → Prop) : contentSquare C = GQ.square C := by
  simp only [contentSquare, GQ.square, Square.mk.injEq]
  refine ⟨rfl, rfl, rfl, funext fun B ↦ propext ?_⟩
  simp [belnapSquare, restrictedExists, every]

/-- The content square satisfies `SquareRelations` when the restrictor is non-empty, which is
Belnap's assertiveness condition, so the relations hold exactly where the forms are
assertive. -/
theorem content_square_relations (C : E → Prop) (hR : ∃ x : E, C x) :
    SquareRelations (contentSquare C) :=
  contentSquare_eq_square C ▸ GQ.square_relations hR

/-! ### Obversion, I-conversion, Barbara -/

/-- Obversion is a strong equivalence (p. 8), since ∀x(Cx/¬¬Bx) and ∀x(Cx/Bx) are equi-assertive
with identical content. -/
theorem obversion (C B : E → Prop) :
    (restrictedForall C fun x => ¬¬B x).presup =
        (restrictedForall C B).presup ∧
      ((restrictedForall C fun x => ¬¬B x).assertion () ↔
        (restrictedForall C B).assertion ()) :=
  ⟨rfl, by simp [restrictedForall, not_not]⟩

/-- I-conversion preserves content, since ∃x(Cx/Bx) and ∃x(Bx/Cx) assert the same proposition
when assertive. -/
theorem i_conversion_content (C B : E → Prop) :
    (restrictedExists C B).assertion () ↔
      (restrictedExists B C).assertion () :=
  ⟨fun ⟨x, hC, hB⟩ => ⟨x, hB, hC⟩, fun ⟨x, hB, hC⟩ => ⟨x, hC, hB⟩⟩

/-- I-conversion is equitrue, in that "truth is preserved in passing from one to the other"
(p. 8). A true ∃x(Cx/Bx) makes its converse assertive and true, because its witness also
witnesses ∃xBx. -/
theorem i_conversion_equitrue (C B : E → Prop)
    (hTrue : (restrictedExists C B).assertion ()) :
    (restrictedExists B C).presup () ∧
      (restrictedExists B C).assertion () :=
  have ⟨x, _, hBx⟩ := hTrue
  ⟨⟨x, hBx⟩, (i_conversion_content C B).mp hTrue⟩

/-- I-conversion is not equi-assertive, since "'Some unicorns are animals' is nonassertive while
'Some animals are unicorns' is just plain false" (p. 8). In any nonempty domain, a restrictor true
of everything and one true of nothing separate the two conditions. -/
theorem i_conversion_not_equiassertive [Nonempty E] :
    ∃ C B : E → Prop, (restrictedExists C B).presup () ∧ ¬(restrictedExists B C).presup () :=
  ⟨fun _ ↦ True, fun _ ↦ False, ⟨Classical.arbitrary E, trivial⟩, fun ⟨_, h⟩ ↦ h⟩

/-- Barbara's minor propagates assertiveness, in that "for every w in which Barbara's minor is
true_w, both her major and her conclusion are assertive_w" (p. 9). -/
theorem barbara_assertive (A C B : E → Prop)
    (hMinorAssertive : (restrictedForall A C).presup ())
    (hMinorTrue : (restrictedForall A C).assertion ()) :
    (restrictedForall C B).presup () ∧ (restrictedForall A B).presup () :=
  have ⟨x, hAx⟩ := hMinorAssertive
  ⟨⟨x, hMinorTrue x hAx⟩, hMinorAssertive⟩

/-- The major alone implies Barbara's conclusion, "a feature of the situation which doubtless
explains the tradition according to which Barbara's major is major and her minor only minor"
(p. 9). -/
theorem barbara (A C B : E → Prop)
    (hMajor : (restrictedForall C B).assertion ())
    (hMinor : (restrictedForall A C).assertion ()) :
    (restrictedForall A B).assertion () :=
  fun x hAx => hMajor x (hMinor x hAx)

/-! ### Contraposition and confirmation (§6) -/

/-- The contrapositive ∀x(¬Bx/¬Cx) is assertive when there are nonblack things, and ∀x(Cx/Bx)
when there are crows. Reports that something is not a crow support the contrapositive but are
"evidentially irrelevant" to the original (p. 10), so the confirmation paradox dissolves because
the two are not the same conditional assertion. -/
theorem contrapositive_different_assertiveness (C B : E → Prop) :
    ((restrictedForall C B).presup () ↔ ∃ x : E, C x) ∧
      ((restrictedForall (fun x => ¬B x) fun x => ¬C x).presup () ↔
        ∃ x : E, ¬B x) :=
  ⟨Iff.rfl, Iff.rfl⟩

end Belnap1970
