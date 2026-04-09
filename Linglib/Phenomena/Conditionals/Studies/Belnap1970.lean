import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Logic.SquareOfOpposition
import Linglib.Theories.Semantics.Quantification.Quantifier

/-!
# Belnap 1970: Conditional Assertion and Restricted Quantification
@cite{belnap-1970}

Nuel D. Belnap Jr. Conditional Assertion and Restricted Quantification.
*Noûs* 4(1): 1–12, 1970.

## Core idea

"If p then q" is not a truth-functional connective but a **conditional
assertion** — the assertion of q on the condition p. When p is false,
(p/q) is *nonassertive*: it asserts nothing. Belnap introduces four
semantic concepts per sentence A at world w (p. 3):

1. A is **true_w** — standard sentential truth
2. A is **false_w** — standard sentential falsity
3. A is **assertive_w** — whether A asserts anything at w
4. **A_w** — what A asserts at w (a proposition = set of worlds)

We formalize this via `PrProp` (presup = assertive, assertion = content),
showing that Belnap's system is isomorphic to linglib's existing partial
proposition infrastructure.

## Main result

Combining conditional assertion with universal quantification **derives
restricted quantification**: ∀x(Cx/Bx) is assertive_w iff ∃xCx is
true_w, and what it asserts = ⋀{Bt_w : Ct true_w}. "All crows are
black" = "Consider the crows: each one is black."

## Integration

- `belnap_forall_content_eq_every`: content of Belnap's restricted ∀
  equals `every_sem` from generalized quantifier infrastructure
- `belnap_exists_content_eq_some`: same for restricted ∃
- `subalternation_a_i` (in `Quantifier.lean`): the non-empty-restrictor
  condition that Belnap derives is exactly what @cite{strawson-1952}
  stipulated as a presupposition of universals
- `content_square_relations`: concrete `SquareRelations` instance from
  `Core.SquareOfOpposition`, connecting to the abstract algebraic framework
- `contrapositive_different_assertiveness`: ∀x(Cx/Bx) and ∀x(¬Bx/¬Cx)
  have different assertiveness conditions — relevant to the confirmation
  paradox

## Three Routes to Restricted Quantification

Belnap's derivation is one of three independent routes to restricted
quantification in linglib:

1. **Conditional assertion** (this file): ∀x(Cx/Bx) = conditional assertion
   + universal quantification. @cite{belnap-1970}
2. **Kratzer restrictor**: if-clauses restrict modal bases, deriving
   restricted quantification from modality. @cite{kratzer-1986}
   See `Theories/Semantics/Conditionals/Restrictor.lean`.
3. **Domain restriction**: contextual predicates intersect the restrictor,
   deriving restricted quantification from pragmatics.
   @cite{von-fintel-1994} @cite{stanley-szab-2000}
   See `Theories/Semantics/Lexical/Determiner/DomainRestriction.lean`.

The convergence of three independent mechanisms on the same result
suggests restricted quantification is a deep linguistic universal.
-/

set_option autoImplicit false

namespace Phenomena.Conditionals.Studies.Belnap1970

open Core.Presupposition (PrProp)
open Core.Duality (Truth3)
open Core.Proposition
open Core.SquareOfOpposition (Square SquareRelations)
open Semantics.Quantification.Quantifier
open Semantics.Montague (Model toyModel ToyEntity)

-- ════════════════════════════════════════════════════════════════
-- §2–3. Conditional Assertion as PrProp
-- ════════════════════════════════════════════════════════════════

/-- Belnap's (3): conditional assertion (A/B).

    "(A/B) is assertive_w just in case A is true_w.
     Provided (A/B) is assertive_w: (A/B)_w = B_w." -/
abbrev condAssert {W : Type*} := @PrProp.condAssert W

/-- Belnap's (6): atomic sentences are categorical — always assertive
    and always asserting the same proposition. -/
abbrev atomic {W : Type*} := @PrProp.ofBProp W

/-- Atomic sentences are assertive at every world (Belnap's (6)). -/
theorem atomic_always_assertive {W : Type*} (p : BProp W) (w : W) :
    (atomic p).presup w := trivial

-- ════════════════════════════════════════════════════════════════
-- §4. Connectives under Conditional Assertion
-- ════════════════════════════════════════════════════════════════

/-- Belnap's (7): negation preserves assertiveness and negates content.

    "~A is assertive_w just in case A is assertive_w. (~A)_w = ~(A_w)."
    This is exactly `PrProp.neg`. -/
theorem neg_preserves_assertiveness {W : Type*} (p : PrProp W) :
    (PrProp.neg p).presup = p.presup := PrProp.neg_presup p

/-- Belnap's (8): conjunction under conditional assertion is
    `PrProp.andBelnap`, not classical `PrProp.and`.

    Classical conjunction requires BOTH operands to be defined.
    Belnap's requires only ONE — undefined conjuncts are skipped. -/
abbrev belnapAnd {W : Type*} := @PrProp.andBelnap W

/-- Belnap's (9): disjunction under conditional assertion. -/
abbrev belnapOr {W : Type*} := @PrProp.orBelnap W

-- ════════════════════════════════════════════════════════════════
-- §5. Restricted Quantification
-- ════════════════════════════════════════════════════════════════

/-- Belnap's (11): restricted universal quantification.

    ∀x(Cx/Bx) is assertive_w iff ∃xCx is true_w.
    What it asserts = conjunction of Bt for all t such that Ct is true_w.

    This derives restricted quantification from two independent mechanisms:
    conditional assertion (§2) and standard universal quantification (§4). -/
def restrictedForall {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) : PrProp Unit where
  presup := λ _ => ∃ x : m.Entity, C x = true
  assertion := λ _ => ∀ x : m.Entity, C x = true → B x = true

/-- Belnap's (12): restricted existential quantification.

    ∃x(Cx/Bx) is assertive iff ∃xCx is true.
    What it asserts = disjunction of Bt for all t such that Ct is true. -/
def restrictedExists {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) : PrProp Unit where
  presup := λ _ => ∃ x : m.Entity, C x = true
  assertion := λ _ => ∃ x : m.Entity, C x = true ∧ B x = true

-- ════════════════════════════════════════════════════════════════
-- §5. Bridge: Belnap ↔ Standard GQ Infrastructure
-- ════════════════════════════════════════════════════════════════

/-- **Content bridge (∀)**: what Belnap's ∀x(Cx/Bx) asserts (when
    assertive) is exactly what `every_sem` computes.

    Proof uses `every_sem_extension`: every_sem m C B =
    (elements.filter C).all B. -/
theorem belnap_forall_content_eq_every {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) :
    (restrictedForall C B).assertion () ↔
      every_sem m (fun x => C x = true) (fun x => B x = true) := by
  simp only [restrictedForall, every_sem]

/-- **Content bridge (∃)**: what Belnap's ∃x(Cx/Bx) asserts (when
    assertive) is exactly what `some_sem` computes. -/
theorem belnap_exists_content_eq_some {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) :
    (restrictedExists C B).assertion () ↔
      some_sem m (fun x => C x = true) (fun x => B x = true) := by
  simp only [restrictedExists, some_sem]

/-- **Assertiveness = existential presupposition**: Belnap's
    assertiveness condition for ∀x(Cx/Bx) is exactly the existential
    presupposition of universal quantifiers.

    @cite{strawson-1952} argued "All S are P" *presupposes* there are Ss.
    Belnap *derives* this: ∀x(Cx/Bx) is nonassertive when nothing
    satisfies C. See also `subalternation_a_i` in `Quantifier.lean`,
    which proves the consequence: every(R,S) entails some(R,S)
    when the restrictor is non-empty. -/
theorem assertive_iff_restrictor_nonempty {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) :
    (restrictedForall C B).presup () ↔ ∃ x : m.Entity, C x = true := Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- §5. Square of Opposition
-- ════════════════════════════════════════════════════════════════

/-- The **Belnap square**: the four Aristotelian forms as Belnap
    restricted quantification, packaged as a `Core.SquareOfOpposition.Square`
    of partial propositions (`PrProp Unit`).

    A: ∀x(Cx/Bx)   "All C are B"
    E: ∀x(Cx/¬Bx)  "No C are B"
    I: ∃x(Cx/Bx)   "Some C are B"
    O: ∃x(Cx/¬Bx)  "Some C are not B"

    Belnap: "semantic relations between these forms turn out to be
    pretty much a good old fashioned square of opposition!" -/
def belnapSquare {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) : Square (PrProp Unit) where
  A := restrictedForall C B
  E := restrictedForall C (λ x => !B x)
  I := restrictedExists C B
  O := restrictedExists C (λ x => !B x)

/-- All four forms share the same assertiveness condition: ∃xCx. -/
theorem square_equiassertive {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) :
    (belnapSquare C B).A.presup = (belnapSquare C B).E.presup ∧
    (belnapSquare C B).A.presup = (belnapSquare C B).I.presup ∧
    (belnapSquare C B).A.presup = (belnapSquare C B).O.presup :=
  ⟨rfl, rfl, rfl⟩

/-- The **content square**: extract the assertion-level content into a
    `Square (Unit → Bool)`, suitable for constructing `SquareRelations`.

    Since `PrProp` assertions are now `Prop`-valued, we use `decide` to
    convert back to `Bool` for compatibility with `SquareRelations`. -/
def contentSquare {m : Model} [Fintype m.Entity] [DecidableEq m.Entity]
    (C B : m.Entity → Bool) : Square (Unit → Bool) where
  A := λ _ => decide (∀ x : m.Entity, C x = true → B x = true)
  E := λ _ => decide (∀ x : m.Entity, C x = true → (!B x) = true)
  I := λ _ => decide (∃ x : m.Entity, C x = true ∧ B x = true)
  O := λ _ => decide (∃ x : m.Entity, C x = true ∧ (!B x) = true)

/-- A and O have contradictory content (when both assertive). -/
theorem a_o_contradictory {m : Model} [Fintype m.Entity] [DecidableEq m.Entity]
    (C B : m.Entity → Bool) (w : Unit) :
    (contentSquare C B).A w = !((contentSquare C B).O w) := by
  simp only [contentSquare]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro h ⟨x, hCx, hBx⟩
    have := h x hCx; cases B x <;> simp_all
  · intro h x hCx
    by_contra hBx
    exact h ⟨x, hCx, by cases B x <;> simp_all⟩

/-- E and I have contradictory content (when both assertive). -/
theorem e_i_contradictory {m : Model} [Fintype m.Entity] [DecidableEq m.Entity]
    (C B : m.Entity → Bool) (w : Unit) :
    (contentSquare C B).E w = !((contentSquare C B).I w) := by
  simp only [contentSquare]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro h ⟨x, hCx, hBx⟩
    have := h x hCx; cases B x <;> simp_all
  · intro h x hCx
    by_contra hBx
    exact h ⟨x, hCx, by cases B x <;> simp_all⟩

/-- The content square satisfies all six `SquareRelations` when the
    restrictor is non-empty. The non-empty condition is exactly Belnap's
    assertiveness condition — the square's relations hold precisely in
    the worlds where the forms are assertive. -/
theorem content_square_relations {m : Model} [Fintype m.Entity] [DecidableEq m.Entity]
    (C B : m.Entity → Bool)
    (hR : ∃ x : m.Entity, C x = true) :
    SquareRelations (contentSquare C B) where
  contradAO := a_o_contradictory C B
  contradEI := e_i_contradictory C B
  contraryAE := λ w hA => by
    have hEI := e_i_contradictory C B w
    rw [hEI]; simp only [Bool.not_eq_false']
    simp only [contentSquare] at *
    rw [decide_eq_true_eq] at hA ⊢
    obtain ⟨x, hCx⟩ := hR
    exact ⟨x, hCx, hA x hCx⟩
  subalternAI := λ w hA => by
    simp only [contentSquare] at *
    rw [decide_eq_true_eq] at hA ⊢
    obtain ⟨x, hCx⟩ := hR
    exact ⟨x, hCx, hA x hCx⟩
  subalternEO := λ w hE => by
    simp only [contentSquare] at *
    rw [decide_eq_true_eq] at hE ⊢
    obtain ⟨x, hCx⟩ := hR
    exact ⟨x, hCx, hE x hCx⟩
  subcontrIO := λ w hI => by
    simp only [contentSquare] at *
    rw [decide_eq_false_iff_not] at hI; push Not at hI
    obtain ⟨x, hCx⟩ := hR
    have hBf := hI x hCx
    exact decide_eq_true_eq.mpr ⟨x, hCx, by simp [hBf]⟩

-- ════════════════════════════════════════════════════════════════
-- §5. Obversion
-- ════════════════════════════════════════════════════════════════

/-- **Obversion is a strong equivalence** (p. 8): "All S are P" ↔
    "No S are non-P". In Belnap's framework: ∀x(Cx/Bx) and
    ∀x(Cx/~~Bx) are equi-assertive and content-identical, since
    ~~B = B. This is trivially true but worth stating as Belnap
    explicitly mentions it. -/
theorem obversion {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) :
    restrictedForall C B = restrictedForall C (λ x => !!B x) := by
  simp only [restrictedForall, Bool.not_not]

-- ════════════════════════════════════════════════════════════════
-- §5. I-Conversion
-- ════════════════════════════════════════════════════════════════

/-- **I-conversion preserves assertion content**: ∃x(Cx/Bx) and
    ∃x(Bx/Cx) assert the same proposition (when assertive).

    Both reduce to ∃x. C(x) ∧ B(x), which is symmetric in C and B.
    However, they are NOT equi-assertive: the first requires ∃xCx,
    the second requires ∃xBx. -/
theorem i_conversion_content {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) :
    (restrictedExists C B).assertion () ↔
    (restrictedExists B C).assertion () := by
  simp only [restrictedExists]
  exact ⟨fun ⟨x, hC, hB⟩ => ⟨x, hB, hC⟩,
         fun ⟨x, hB, hC⟩ => ⟨x, hC, hB⟩⟩

/-- **I-conversion is equitrue** (p. 8): "truth is preserved in
    passing from one to the other." If ∃x(Cx/Bx)'s assertion holds,
    then ∃x(Bx/Cx) is assertive and its assertion holds too.

    Note: we prove the stronger result that assertion alone suffices —
    assertiveness is not needed as a hypothesis (it follows from
    assertion since any witness for the filter also witnesses ∃xBx).

    Belnap: "But 'Some unicorns are animals' is nonassertive while
    'Some animals are unicorns' is just plain false." -/
theorem i_conversion_equitrue {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool)
    (hTrue : (restrictedExists C B).assertion ()) :
    (restrictedExists B C).presup () ∧
    (restrictedExists B C).assertion () := by
  constructor
  · simp only [restrictedExists] at *
    obtain ⟨x, hCx, hBx⟩ := hTrue
    exact ⟨x, hBx⟩
  · exact (i_conversion_content C B).mp hTrue

/-- I-conversion is NOT equi-assertive in general:
    ∃xCx can hold while ∃xBx fails (or vice versa). -/
theorem i_conversion_not_equiassertive :
    ∃ (m : Model) (_ : Fintype m.Entity) (C B : m.Entity → Bool),
    ((restrictedExists C B).presup () ∧ ¬(restrictedExists B C).presup ()) := by
  refine ⟨toyModel, inferInstance,
    (λ x => match x with | .john => true | _ => false),
    (λ _ => false), ?_⟩
  simp only [restrictedExists]
  exact ⟨⟨.john, rfl⟩, fun ⟨_, h⟩ => nomatch h⟩

-- ════════════════════════════════════════════════════════════════
-- §5. Barbara Syllogism
-- ════════════════════════════════════════════════════════════════

/-- **Barbara: assertiveness propagation.** When Barbara's minor
    premise is true (assertive and assertion holds), both her major
    and her conclusion are assertive.

    Belnap (p. 9): "for every w in which Barbara's minor is true_w,
    both her major and her conclusion are assertive_w."

    Proof: the minor's truth means every A-element is a C-element.
    Combined with its assertiveness (∃xAx), this gives ∃xCx (major
    is assertive) and ∃xAx (conclusion is assertive, same as minor). -/
theorem barbara_assertive {m : Model} [Fintype m.Entity]
    (A C B : m.Entity → Bool)
    (hMinorAssertive : (restrictedForall A C).presup ())
    (hMinorTrue : (restrictedForall A C).assertion ()) :
    (restrictedForall C B).presup () ∧
    (restrictedForall A B).presup () := by
  simp only [restrictedForall] at *
  constructor
  · obtain ⟨x, hAx⟩ := hMinorAssertive
    exact ⟨x, hMinorTrue x hAx⟩
  · exact hMinorAssertive

/-- **Barbara: content implication.** What Barbara's major asserts
    propositionally implies what her conclusion asserts.

    Major: ∀x(Cx/Bx)  "All crows are black"
    Minor: ∀x(Ax/Cx)  "All of Alan's birds are crows"
    Concl: ∀x(Ax/Bx)  "All of Alan's birds are black"

    Belnap (p. 9): "it is her major alone which does any implying
    of her conclusion, a feature of the situation which doubtless
    explains the tradition according to which Barbara's major is
    major and her minor only minor." -/
theorem barbara {m : Model} [Fintype m.Entity]
    (A C B : m.Entity → Bool)
    (hMajor : (restrictedForall C B).assertion ())
    (hMinor : (restrictedForall A C).assertion ()) :
    (restrictedForall A B).assertion () := by
  simp only [restrictedForall] at *
  intro x hAx
  exact hMajor x (hMinor x hAx)

-- ════════════════════════════════════════════════════════════════
-- §6. Contrapositive and Confirmation
-- ════════════════════════════════════════════════════════════════

/-- The contrapositive ∀x(¬Bx/¬Cx) has a DIFFERENT assertiveness
    condition from the original ∀x(Cx/Bx).

    Original: assertive iff ∃xCx (there are crows)
    Contrapositive: assertive iff ∃x¬Bx (there are nonblack things)

    This is relevant to the confirmation paradox (p. 10): "reports
    that such and such is not a crow, although offering support for
    the contrapositive 'No nonblack things are noncrows' — ∀x(~Bx/~Cx) —
    when such and such is not black, is evidentially irrelevant to
    ∀x(Cx/Bx)." -/
theorem contrapositive_different_assertiveness {m : Model} [Fintype m.Entity]
    (C B : m.Entity → Bool) :
    ((restrictedForall C B).presup () ↔ ∃ x : m.Entity, C x = true) ∧
    ((restrictedForall (λ x => !B x) (λ x => !C x)).presup () ↔
      ∃ x : m.Entity, (!B x) = true) :=
  ⟨Iff.rfl, Iff.rfl⟩

end Phenomena.Conditionals.Studies.Belnap1970
