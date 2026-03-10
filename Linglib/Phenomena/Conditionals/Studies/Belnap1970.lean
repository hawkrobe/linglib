import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Logic.SquareOfOpposition
import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier

/-!
# Belnap 1970: Conditional Assertion and Restricted Quantification
@cite{belnap-1970}

Nuel D. Belnap Jr. Conditional Assertion and Restricted Quantification.
*Noûs* 4(1): 1–12, 1970.

## Core idea

"If p then q" is not a truth-functional connective but a **conditional
assertion** — the assertion of q on the condition p. When p is false,
(p/q) is *nonassertive*: it asserts nothing. Belnap introduces four
semantic concepts per sentence A at world w:

1. A is **true_w** / A is **false_w** — standard truth
2. A is **assertive_w** — whether A asserts anything at w
3. **A_w** — what A asserts at w (a proposition = set of worlds)

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
- `contrapositive_different_assertiveness`: ∀x(Cx/Bx) and ∀x(¬Bx/¬Cx)
  have different assertiveness conditions — relevant to the confirmation
  paradox
-/

set_option autoImplicit false

namespace Phenomena.Conditionals.Studies.Belnap1970

open Core.Presupposition (PrProp)
open Core.Duality (Truth3)
open Core.Proposition
open Core.SquareOfOpposition (Square SquareRelations)
open Semantics.Lexical.Determiner.Quantifier
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
    (atomic p).presup w = true := rfl

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
def restrictedForall {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) : PrProp Unit where
  presup := λ _ => FiniteModel.elements.any C
  assertion := λ _ => (FiniteModel.elements.filter C).all B

/-- Belnap's (12): restricted existential quantification.

    ∃x(Cx/Bx) is assertive iff ∃xCx is true.
    What it asserts = disjunction of Bt for all t such that Ct is true. -/
def restrictedExists {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) : PrProp Unit where
  presup := λ _ => FiniteModel.elements.any C
  assertion := λ _ => (FiniteModel.elements.filter C).any B

-- ════════════════════════════════════════════════════════════════
-- §5. Bridge: Belnap ↔ Standard GQ Infrastructure
-- ════════════════════════════════════════════════════════════════

/-- **Content bridge (∀)**: what Belnap's ∀x(Cx/Bx) asserts (when
    assertive) is exactly what `every_sem` computes.

    Proof uses `every_sem_extension`: every_sem m C B =
    (elements.filter C).all B. -/
theorem belnap_forall_content_eq_every {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) :
    (restrictedForall C B).assertion () = every_sem m C B :=
  (every_sem_extension C B).symm

/-- **Content bridge (∃)**: what Belnap's ∃x(Cx/Bx) asserts (when
    assertive) is exactly what `some_sem` computes. -/
theorem belnap_exists_content_eq_some {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) :
    (restrictedExists C B).assertion () = some_sem m C B :=
  (some_sem_extension C B).symm

/-- **Assertiveness = existential presupposition**: Belnap's
    assertiveness condition for ∀x(Cx/Bx) is exactly the existential
    presupposition of universal quantifiers.

    @cite{strawson-1952} argued "All S are P" *presupposes* there are Ss.
    Belnap *derives* this: ∀x(Cx/Bx) is nonassertive when nothing
    satisfies C. See also `subalternation_a_i` in `Quantifier.lean`,
    which proves the consequence: every(R,S) entails some(R,S)
    when the restrictor is non-empty. -/
theorem assertive_iff_restrictor_nonempty {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) :
    (restrictedForall C B).presup () = FiniteModel.elements.any C := rfl

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
def belnapSquare {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) : Square (PrProp Unit) where
  A := restrictedForall C B
  E := restrictedForall C (λ x => !B x)
  I := restrictedExists C B
  O := restrictedExists C (λ x => !B x)

/-- All four forms share the same assertiveness condition: ∃xCx. -/
theorem square_equiassertive {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) :
    (belnapSquare C B).A.presup = (belnapSquare C B).E.presup ∧
    (belnapSquare C B).A.presup = (belnapSquare C B).I.presup ∧
    (belnapSquare C B).A.presup = (belnapSquare C B).O.presup :=
  ⟨rfl, rfl, rfl⟩

/-- The **content square**: extract the assertion-level content into a
    `Square (Unit → Bool)`, suitable for constructing `SquareRelations`. -/
def contentSquare {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) : Square (Unit → Bool) where
  A := (belnapSquare C B).A.assertion
  E := (belnapSquare C B).E.assertion
  I := (belnapSquare C B).I.assertion
  O := (belnapSquare C B).O.assertion

/-- A and O have contradictory content (when both assertive). -/
theorem a_o_contradictory {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) (w : Unit) :
    (contentSquare C B).A w = !((contentSquare C B).O w) := by
  simp only [contentSquare, belnapSquare, restrictedForall, restrictedExists]
  rw [List.all_eq_not_any_not]

/-- E and I have contradictory content (when both assertive). -/
theorem e_i_contradictory {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) (w : Unit) :
    (contentSquare C B).E w = !((contentSquare C B).I w) := by
  simp only [contentSquare, belnapSquare, restrictedForall, restrictedExists]
  rw [List.all_eq_not_any_not]
  simp [Bool.not_not]

/-- The content square satisfies all six `SquareRelations` when the
    restrictor is non-empty. The non-empty condition is exactly Belnap's
    assertiveness condition — the square's relations hold precisely in
    the worlds where the forms are assertive. -/
theorem content_square_relations {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool)
    (hR : FiniteModel.elements.any C = true) :
    SquareRelations (contentSquare C B) where
  contradAO := a_o_contradictory C B
  contradEI := e_i_contradictory C B
  contraryAE := λ w hA => by
    -- A = true means all C-elements are B. E = false means not all C-elements are ¬B.
    -- Since the restrictor is non-empty, there's a C-element that is B, so E fails.
    have hAO := a_o_contradictory C B w
    -- E = ¬I (by contradiction). So E = false ↔ I = true.
    -- I = true ↔ some C-element is B. Subalternation gives this from A = true + non-empty.
    have hEI := e_i_contradictory C B w
    -- I = ¬E, so if I = true then E = false
    -- E = ¬I, so E = false ↔ ¬I = false ↔ I = true
    rw [hEI]
    simp only [Bool.not_eq_false']
    -- Goal: (contentSquare C B).I w = true, i.e. some C-element is B
    simp only [contentSquare, belnapSquare, restrictedExists]
    simp only [contentSquare, belnapSquare, restrictedForall] at hA
    rw [List.any_eq_true] at hR
    obtain ⟨x, hx, hCx⟩ := hR
    rw [List.any_eq_true]
    rw [List.all_eq_true] at hA
    exact ⟨x, List.mem_filter.mpr ⟨hx, hCx⟩,
           hA x (List.mem_filter.mpr ⟨hx, hCx⟩)⟩
  subalternAI := λ w hA => by
    simp only [contentSquare, belnapSquare, restrictedForall, restrictedExists] at *
    rw [List.all_eq_true] at hA
    rw [List.any_eq_true] at hR ⊢
    obtain ⟨x, hx, hCx⟩ := hR
    exact ⟨x, List.mem_filter.mpr ⟨hx, hCx⟩, hA x (List.mem_filter.mpr ⟨hx, hCx⟩)⟩
  subalternEO := λ w hE => by
    simp only [contentSquare, belnapSquare, restrictedForall, restrictedExists] at *
    rw [List.all_eq_true] at hE
    rw [List.any_eq_true] at hR ⊢
    obtain ⟨x, hx, hCx⟩ := hR
    exact ⟨x, List.mem_filter.mpr ⟨hx, hCx⟩, hE x (List.mem_filter.mpr ⟨hx, hCx⟩)⟩
  subcontrIO := λ w hI => by
    -- I = false means no C-element is B. O = true means some C-element is ¬B.
    -- Non-empty restrictor gives a C-element; since it's not B (by hI), it witnesses O.
    simp only [contentSquare, belnapSquare, restrictedExists] at *
    rw [List.any_eq_true] at hR
    obtain ⟨x, hx, hCx⟩ := hR
    have hxInFilter : x ∈ FiniteModel.elements.filter C :=
      List.mem_filter.mpr ⟨hx, hCx⟩
    -- hI says (filter C).any B = false, so B x = false for our witness
    have hNotB : B x = false := by
      by_contra h
      have hBx : B x = true := by cases B x <;> simp_all
      have : (FiniteModel.elements.filter C).any B = true :=
        List.any_eq_true.mpr ⟨x, hxInFilter, hBx⟩
      simp [this] at hI
    rw [List.any_eq_true]
    exact ⟨x, hxInFilter, by simp [hNotB]⟩

-- ════════════════════════════════════════════════════════════════
-- §6. Contrapositive and Confirmation
-- ════════════════════════════════════════════════════════════════

/-- The contrapositive ∀x(¬Bx/¬Cx) has a DIFFERENT assertiveness
    condition from the original ∀x(Cx/Bx).

    Original: assertive iff ∃xCx (there are crows)
    Contrapositive: assertive iff ∃x¬Bx (there are nonblack things)

    This is relevant to the confirmation paradox: a nonblack noncrow
    (~Bt ∧ ~Ct true) supports the contrapositive (when assertive)
    but is irrelevant to the original unless there are crows. -/
theorem contrapositive_different_assertiveness {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) :
    (restrictedForall C B).presup () = FiniteModel.elements.any C ∧
    (restrictedForall (λ x => !B x) (λ x => !C x)).presup () =
      FiniteModel.elements.any (λ x => !B x) :=
  ⟨rfl, rfl⟩

/-- **I-conversion preserves truth** (Belnap's observation about the
    I-form): ∃x(Cx/Bx) and ∃x(Bx/Cx) are equitrue — "truth is
    preserved in passing from one to the other."

    Both reduce to ∃x. C(x) ∧ B(x), which is symmetric in C and B.
    However, they are NOT equi-assertive: the first requires ∃xCx,
    the second requires ∃xBx. -/
theorem i_conversion_equitrue {m : Model} [FiniteModel m]
    (C B : m.Entity → Bool) :
    (restrictedExists C B).assertion () =
    (restrictedExists B C).assertion () := by
  simp only [restrictedExists]
  -- Both sides reduce to ∃x ∈ elements. C(x) ∧ B(x), which is symmetric
  show (FiniteModel.elements.filter C).any B =
       (FiniteModel.elements.filter B).any C
  rw [← some_sem_extension C B, ← some_sem_extension B C]
  exact some_symmetric C B

/-- I-conversion is NOT equi-assertive in general. -/
theorem i_conversion_not_equiassertive :
    ∃ (m : Model) (_ : FiniteModel m) (C B : m.Entity → Bool),
    (restrictedExists C B).presup () ≠
    (restrictedExists B C).presup () := by
  refine ⟨toyModel, inferInstance,
    (λ x => match x with | .john => true | _ => false),
    (λ _ => false), ?_⟩
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §5. Barbara Syllogism
-- ════════════════════════════════════════════════════════════════

/-- **Barbara holds asymmetrically**: when the minor premise's
    restrictor is non-empty, the major implies the conclusion.

    Major: ∀x(Cx/Bx)  "All crows are black"
    Minor: ∀x(Ax/Cx)  "All of Alan's birds are crows"
    Concl: ∀x(Ax/Bx)  "All of Alan's birds are black"

    Belnap: "for every w in which Barbara's minor is true_w, both
    her major and her conclusion are assertive_w, and what her major
    asserts in w propositionally implies what her conclusion asserts
    in w." -/
theorem barbara {m : Model} [FiniteModel m]
    (A C B : m.Entity → Bool)
    (hMajor : (restrictedForall C B).assertion () = true)
    (hMinor : (restrictedForall A C).assertion () = true) :
    (restrictedForall A B).assertion () = true := by
  simp only [restrictedForall] at *
  rw [List.all_eq_true] at *
  intro x hx
  have hC := hMinor x hx
  exact hMajor x (List.mem_filter.mpr ⟨List.mem_of_mem_filter hx, hC⟩)

end Phenomena.Conditionals.Studies.Belnap1970
