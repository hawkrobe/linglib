import Linglib.Semantics.Presupposition.Trivalent
import Linglib.Logic.Aristotelian.Square
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Fragments.English.Toy
import Linglib.Data.Examples.Belnap1970
import Mathlib.Data.Fintype.Basic

/-!
# Belnap (1970): Conditional Assertion and Restricted Quantification

"If p then q" read as *conditional assertion*: the assertion of q on the
condition p, assertive only where p is true and as if never made
otherwise. Belnap gives each sentence four semantic coordinates per world
(p. 3) — true, false, assertive, and what it asserts — which are exactly
`PartialProp`'s two fields, and then combines conditional assertion (3)
with ordinary universal quantification (10) to *derive* restricted
quantification (11): "All crows are black" comes out as "Consider the
crows: each one is black", assertive only if there are crows. The four
Aristotelian forms then stand in "pretty much a good old fashioned square
of opposition" with equi-assertiveness on top of the content relations,
obversion is a strong equivalence, I-conversion preserves truth but not
assertiveness, and Barbara's major alone implies her conclusion.

## Main statements

* `belnap_forall_content_eq_every`, `belnap_exists_content_eq_some`: the
  content of the restricted forms (11)–(12) is `every_sem`/`some_sem`;
  their shared assertiveness condition is [strawson-1952]'s stipulated
  existential presupposition, here derived.
* `content_square_relations`: the four forms satisfy all six
  `SquareRelations` whenever the restrictor is non-empty — exactly the
  worlds where they are assertive.
* `i_conversion_equitrue`, `i_conversion_not_equiassertive`, `barbara`:
  the paper's asymmetries — conversion preserves truth only, and Barbara's
  major does all the implying (p. 8–9).

## References

* [belnap-1970]: Conditional Assertion and Restricted Quantification.
  *Noûs* 4.
* [quine-1950]: Methods of Logic (the Quine–Rhinelander reading).
* [strawson-1952]: Introduction to Logical Theory.
-/

namespace Belnap1970

open Presupposition
open Aristotelian (Square SquareRelations)
open Quantification

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

/-- (11): restricted universal quantification. ∀x(Cx/Bx) is assertive iff
∃xCx, and asserts the conjunction of Bt for the t with Ct true — the
A-form as "consider the crows: each one is black". -/
def restrictedForall (C B : E → Prop) : PartialProp Unit where
  presup := fun _ => ∃ x : E, C x
  assertion := fun _ => ∀ x : E, C x → B x

/-- (12): restricted existential quantification. ∃x(Cx/Bx) is assertive
iff ∃xCx, and asserts the disjunction of Bt for the t with Ct true. -/
def restrictedExists (C B : E → Prop) : PartialProp Unit where
  presup := fun _ => ∃ x : E, C x
  assertion := fun _ => ∃ x : E, C x ∧ B x

/-! ### The content is generalized quantification -/

/-- What (11) asserts, when assertive, is exactly `every_sem`. -/
theorem belnap_forall_content_eq_every (C B : E → Prop) :
    (restrictedForall C B).assertion () ↔ every_sem C B := Iff.rfl

/-- What (12) asserts, when assertive, is exactly `some_sem`. -/
theorem belnap_exists_content_eq_some (C B : E → Prop) :
    (restrictedExists C B).assertion () ↔ some_sem C B := Iff.rfl

/-- Assertiveness of (11) is the existential presupposition of universals:
what [strawson-1952] stipulated, Belnap derives — ∀x(Cx/Bx) is
nonassertive when nothing satisfies C. -/
theorem assertive_iff_restrictor_nonempty (C B : E → Prop) :
    (restrictedForall C B).presup () ↔ ∃ x : E, C x := Iff.rfl

/-! ### The square of opposition -/

/-- The four Aristotelian forms as restricted quantification: "semantic
relations between these forms turn out ... to constitute what is pretty
much a good old fashioned square of opposition" (p. 8). -/
def belnapSquare (C B : E → Prop) : Square (PartialProp Unit) where
  A := restrictedForall C B
  E := restrictedForall C (fun x => ¬B x)
  I := restrictedExists C B
  O := restrictedExists C (fun x => ¬B x)

/-- All four forms share one assertiveness condition, ∃xCx: the square's
relations are as strong as possible, equi-assertiveness on top of the
content relations (p. 8). -/
theorem square_equiassertive (C B : E → Prop) :
    (belnapSquare C B).A.presup = (belnapSquare C B).E.presup ∧
    (belnapSquare C B).A.presup = (belnapSquare C B).I.presup ∧
    (belnapSquare C B).A.presup = (belnapSquare C B).O.presup :=
  ⟨rfl, rfl, rfl⟩

section ContentSquare

variable [Fintype E]

/-- The assertion-level contents as a Boolean square, for
`SquareRelations`. -/
def contentSquare (C B : E → Prop) [DecidablePred C] [DecidablePred B] :
    Square (Unit → Bool) where
  A := fun _ => decide (∀ x : E, C x → B x)
  E := fun _ => decide (∀ x : E, C x → ¬B x)
  I := fun _ => decide (∃ x : E, C x ∧ B x)
  O := fun _ => decide (∃ x : E, C x ∧ ¬B x)

variable (C B : E → Prop) [DecidablePred C] [DecidablePred B]

/-- A and O have contradictory content. -/
theorem a_o_contradictory (w : Unit) :
    (contentSquare C B).A w = !((contentSquare C B).O w) := by
  simp only [contentSquare]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    not_exists, not_and, not_not]

/-- E and I have contradictory content. -/
theorem e_i_contradictory (w : Unit) :
    (contentSquare C B).E w = !((contentSquare C B).I w) := by
  simp only [contentSquare]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    not_exists, not_and]

/-- The content square satisfies all six `SquareRelations` when the
restrictor is non-empty — exactly Belnap's assertiveness condition, so the
relations hold precisely where the forms are assertive. -/
theorem content_square_relations (hR : ∃ x : E, C x) :
    SquareRelations (contentSquare C B) where
  subalternAI := Aristotelian.le_iff_forall.mpr fun w hA => by
    simp only [contentSquare, decide_eq_true_eq] at hA ⊢
    obtain ⟨x, hCx⟩ := hR
    exact ⟨x, hCx, hA x hCx⟩
  subalternEO := Aristotelian.le_iff_forall.mpr fun w hE => by
    simp only [contentSquare, decide_eq_true_eq] at hE ⊢
    obtain ⟨x, hCx⟩ := hR
    exact ⟨x, hCx, hE x hCx⟩
  contradAO := Aristotelian.isContradictory_iff_forall.mpr
    ⟨fun w hand => by
        have h := a_o_contradictory C B w
        rw [hand.1, hand.2] at h; simp at h,
     fun w => by
        by_cases hO : (contentSquare C B).O w = true
        · exact Or.inr hO
        · left
          have h := a_o_contradictory C B w
          rw [show (contentSquare C B).O w = false by simpa using hO] at h
          simpa using h⟩
  contradEI := Aristotelian.isContradictory_iff_forall.mpr
    ⟨fun w hand => by
        have h := e_i_contradictory C B w
        rw [hand.1, hand.2] at h; simp at h,
     fun w => by
        by_cases hI : (contentSquare C B).I w = true
        · exact Or.inr hI
        · left
          have h := e_i_contradictory C B w
          rw [show (contentSquare C B).I w = false by simpa using hI] at h
          simpa using h⟩
  contraryAE := Aristotelian.disjoint_iff_forall.mpr fun w hand => by
    obtain ⟨hA, hE⟩ := hand
    have hI : (contentSquare C B).I w = true := by
      simp only [contentSquare, decide_eq_true_eq] at hA ⊢
      obtain ⟨x, hCx⟩ := hR
      exact ⟨x, hCx, hA x hCx⟩
    have hEI := e_i_contradictory C B w
    rw [hI, hE] at hEI; simp at hEI
  subcontrIO := Aristotelian.codisjoint_iff_forall.mpr fun w => by
    by_cases hI : (contentSquare C B).I w = true
    · exact Or.inl hI
    · right
      have hIf : ¬∃ x : E, C x ∧ B x := by
        simpa [contentSquare] using hI
      push Not at hIf
      obtain ⟨x, hCx⟩ := hR
      simp only [contentSquare, decide_eq_true_eq]
      exact ⟨x, hCx, hIf x hCx⟩

end ContentSquare

/-! ### Obversion, I-conversion, Barbara -/

/-- Obversion is a strong equivalence (p. 8): ∀x(Cx/¬¬Bx) and ∀x(Cx/Bx)
are equi-assertive with identical content. -/
theorem obversion (C B : E → Prop) :
    (restrictedForall C fun x => ¬¬B x).presup =
        (restrictedForall C B).presup ∧
      ((restrictedForall C fun x => ¬¬B x).assertion () ↔
        (restrictedForall C B).assertion ()) :=
  ⟨rfl, by simp [restrictedForall, not_not]⟩

/-- I-conversion preserves content: ∃x(Cx/Bx) and ∃x(Bx/Cx) assert the
same proposition when assertive. -/
theorem i_conversion_content (C B : E → Prop) :
    (restrictedExists C B).assertion () ↔
      (restrictedExists B C).assertion () :=
  ⟨fun ⟨x, hC, hB⟩ => ⟨x, hB, hC⟩, fun ⟨x, hB, hC⟩ => ⟨x, hC, hB⟩⟩

/-- I-conversion is equitrue (p. 8): "truth is preserved in passing from
one to the other" — a true ∃x(Cx/Bx) makes its converse assertive and
true. Assertion alone suffices: the witness also witnesses ∃xBx. -/
theorem i_conversion_equitrue (C B : E → Prop)
    (hTrue : (restrictedExists C B).assertion ()) :
    (restrictedExists B C).presup () ∧
      (restrictedExists B C).assertion () :=
  have ⟨x, _, hBx⟩ := hTrue
  ⟨⟨x, hBx⟩, (i_conversion_content C B).mp hTrue⟩

/-- But not equi-assertive: "'Some unicorns are animals' is nonassertive
while 'Some animals are unicorns' is just plain false" (p. 8). -/
theorem i_conversion_not_equiassertive :
    ∃ (E : Type) (_ : Fintype E) (C B : E → Prop),
      (restrictedExists C B).presup () ∧
        ¬(restrictedExists B C).presup () :=
  ⟨Semantics.Montague.ToyEntity, inferInstance, (· = .john), fun _ => False,
    ⟨.john, rfl⟩, fun ⟨_, h⟩ => h⟩

/-- Barbara's assertiveness propagation (p. 9): "for every w in which
Barbara's minor is true_w, both her major and her conclusion are
assertive_w". -/
theorem barbara_assertive (A C B : E → Prop)
    (hMinorAssertive : (restrictedForall A C).presup ())
    (hMinorTrue : (restrictedForall A C).assertion ()) :
    (restrictedForall C B).presup () ∧ (restrictedForall A B).presup () :=
  have ⟨x, hAx⟩ := hMinorAssertive
  ⟨⟨x, hMinorTrue x hAx⟩, hMinorAssertive⟩

/-- Barbara's content implication: the major alone implies the conclusion
— "a feature of the situation which doubtless explains the tradition
according to which Barbara's major is major and her minor only minor"
(p. 9). -/
theorem barbara (A C B : E → Prop)
    (hMajor : (restrictedForall C B).assertion ())
    (hMinor : (restrictedForall A C).assertion ()) :
    (restrictedForall A B).assertion () :=
  fun x hAx => hMajor x (hMinor x hAx)

/-! ### Contraposition and confirmation (§6) -/

/-- The contrapositive ∀x(¬Bx/¬Cx) has a different assertiveness condition
from ∀x(Cx/Bx): there-are-nonblack-things vs there-are-crows. Reports that
something is not a crow support the contrapositive but are "evidentially
irrelevant" to the original (p. 10) — the confirmation paradox dissolves
because the two are not the same conditional assertion. -/
theorem contrapositive_different_assertiveness (C B : E → Prop) :
    ((restrictedForall C B).presup () ↔ ∃ x : E, C x) ∧
      ((restrictedForall (fun x => ¬B x) fun x => ¬C x).presup () ↔
        ∃ x : E, ¬B x) :=
  ⟨Iff.rfl, Iff.rfl⟩

end Belnap1970
