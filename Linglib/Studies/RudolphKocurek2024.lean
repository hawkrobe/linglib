import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Discourse.CommonGround

/-!
# [rudolph-kocurek-2024]: Metalinguistic Gradability

Semantic expressivist framework for metalinguistic comparatives ("Ann is more a
linguist than a philosopher"), equatives, degree modifiers, and conditionals
[rudolph-kocurek-2024], together with the revised semantics and degree-theoretic
formulation of its technical supplement [kocurek-2024-supplement].

Speakers express not only factual commitments (about the world) but also
**interpretive commitments** (about how to interpret language): the common ground
is generalized from sets of worlds to sets of ordering-world pairs ⟨≤, w⟩, where
≤ is a total preorder over interpretations (a **semantic ordering**). Truth is
evaluated at a triple ⟨≤, i, w⟩; the metalinguistic comparative `A ≻ B` holds iff
some (A∧¬B)-interpretation ranked ≤ i dominates every (B∧¬A)-interpretation.

## Contents

1. **Framework** — `SemanticOrdering`, `MFormula`, the basic (`eval`) and revised
   (`evalRevised`) semantics, assertoric content with its two entailment notions
   (truth- vs acceptance-preservation), distance functions and degree modifiers
   (*very much*, *sorta*, *mostly*), metalinguistic conditionals, No Reversal,
   and the common-ground wiring (`MetalinguisticCG`).
2. **Degree theory** ([kocurek-2024-supplement] §C) — the matching relation ∼ on
   interpretation sets and the ordering ⊐: Facts 8 and 11–13 (∼ is an equivalence,
   ⊐ transitive and total off ∼, extremal degrees), packaged as a mathlib `Setoid`
   with `MetaDegree` as its `Quotient`; Facts 9–10 (`me_iff_same_degree`,
   `mc_iff_degree_gt`) connect the degree structure back to `evalRevised`.
3. **Finite models** — four small models verifying the paper's predictions:
   the §4.4 entailment patterns (supplement Fact 3), borderline equatives and
   nonclassical acceptance-preservation (paralleling informational entailment
   for epistemic modals, [yalcin-2007]), degree modifiers (§6.1), metalinguistic
   conditionals (§6.3), the No Reversal bridge to [klein-1980] delineation
   (§7; see `Semantics/Degree/Gradability/Delineation.lean`), and the
   supplement's ME-transitivity counterexample with its revised-semantics
   repair (§B).
-/

namespace RudolphKocurek2024

/-! ### Helpers -/

/-- Boolean universal quantification over a finite type. -/
private def bAll (I : Type*) [Fintype I] (p : I → Bool) : Bool :=
  decide (∀ i : I, p i = true)

/-- Boolean existential quantification over a finite type. -/
private def bAny (I : Type*) [Fintype I] (p : I → Bool) : Bool :=
  decide (∃ i : I, p i = true)

/-! ### Interpretations and Semantic Orderings -/

/-- An interpretation maps predicate symbols to world-indexed extensions.

For the finite decidable models we work with, an interpretation is simply
a function from predicates and entities to Bool at each world. -/
structure Interpretation (W : Type*) (Pred : Type*) (Entity : Type*) where
  /-- Extension of predicate P at world w: the set of entities P applies to. -/
  ext : Pred → W → Entity → Bool

/-- A semantic ordering is a total preorder on a set of interpretations.

Represents a speaker's relative interpretive commitments: `le i j` means
the speaker is at least as committed to j as to i.

`le` is Prop-valued with `DecidableRel` for decidable computation.
Use `ofBool` for the common case of defining orderings via pattern matching. -/
structure SemanticOrdering (I : Type*) where
  /-- The preorder relation: `le i j` means i is ranked no higher than j. -/
  le : I → I → Prop
  /-- Reflexivity -/
  le_refl : ∀ (i : I), le i i
  /-- Transitivity -/
  le_trans : ∀ (i j k : I), le i j → le j k → le i k
  /-- Totality: any two interpretations are comparable -/
  le_total : ∀ (i j : I), le i j ∨ le j i
  /-- Decidability of the ordering relation -/
  decRel : DecidableRel le

attribute [instance] SemanticOrdering.decRel

namespace SemanticOrdering

variable {I : Type*} (ord : SemanticOrdering I)

/-- Bool-valued le for computation (eval, decide). -/
def leB (i j : I) : Bool := decide (ord.le i j)

/-- Strict ordering (Prop): i is ranked strictly below j. -/
def lt (i j : I) : Prop := ord.le i j ∧ ¬ ord.le j i

/-- Decidability of the strict ordering. -/
instance decRelLt : DecidableRel ord.lt :=
  fun i j => show Decidable (ord.le i j ∧ ¬ ord.le j i) from inferInstance

/-- Bool-valued strict ordering for computation. -/
def ltB (i j : I) : Bool := ord.leB i j && !ord.leB j i

/-- Bool-valued equivalence for computation. -/
def equivB (i j : I) : Bool := ord.leB i j && ord.leB j i

/-- ¬(a < b) → b ≤ a (by totality). -/
theorem le_of_not_lt {a b : I} : ¬ ord.lt a b → ord.le b a := by
  intro h
  rcases ord.le_total a b with hab | hba
  · exact Classical.byContradiction fun hba => h ⟨hab, hba⟩
  · exact hba

end SemanticOrdering

/-- Construct a `SemanticOrdering` from a Bool-valued function.
Convenient for defining concrete orderings via pattern matching. -/
def SemanticOrdering.ofBool {I : Type*} (f : I → I → Bool)
    (h_refl : ∀ i, f i i = true)
    (h_trans : ∀ i j k, f i j = true → f j k = true → f i k = true)
    (h_total : ∀ i j, f i j = true ∨ f j i = true) :
    SemanticOrdering I where
  le i j := f i j = true
  le_refl := h_refl
  le_trans := h_trans
  le_total := h_total
  decRel _ _ := inferInstance

/-! ### Evaluation Index and Formulas -/

/-- A metalinguistic formula over predicates and entities.

The language includes atomic predication, boolean connectives,
and the metalinguistic comparative ≻ (`.mc`). -/
inductive MFormula (Pred Entity : Type*) where
  | atom : Pred → Entity → MFormula Pred Entity
  | neg : MFormula Pred Entity → MFormula Pred Entity
  | conj : MFormula Pred Entity → MFormula Pred Entity → MFormula Pred Entity
  | disj : MFormula Pred Entity → MFormula Pred Entity → MFormula Pred Entity
  | mc : MFormula Pred Entity → MFormula Pred Entity → MFormula Pred Entity
  deriving DecidableEq

namespace MFormula

variable {Pred Entity : Type*}

/-- Metalinguistic equative: A ≈ B := ¬(A ≻ B) ∧ ¬(B ≻ A). -/
def me (A B : MFormula Pred Entity) : MFormula Pred Entity :=
  .conj (.neg (.mc A B)) (.neg (.mc B A))

end MFormula

/-! ### Semantics (§4.2 of the paper) -/

/-- Evaluate a formula at an index ⟨≤, i, w⟩.

- Atomic: true iff the entity is in the predicate's extension at w under i.
- MC (A ≻ B): true iff ∃ i' ≤ i with (A∧¬B) true at i', and
  ∀ i'' ≤ i, (B∧¬A) true at i'' implies i'' < i'. -/
def eval {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) : Bool :=
  match φ with
  | .atom P e => (interpFn i).ext P w e
  | .neg A => !eval interpFn A ord i w
  | .conj A B => eval interpFn A ord i w && eval interpFn B ord i w
  | .disj A B => eval interpFn A ord i w || eval interpFn B ord i w
  | .mc A B =>
    -- ∃ i' ≤ i : ⟦A ∧ ¬B⟧^{i'} = 1 ∧ ∀ i'' ≤ i : ⟦B ∧ ¬A⟧^{i''} = 1 → i'' < i'
    bAny I λ i' =>
      ord.leB i' i &&
      eval interpFn A ord i' w &&
      !(eval interpFn B ord i' w) &&
      bAll I λ i'' =>
        !(ord.leB i'' i &&
          eval interpFn B ord i'' w &&
          !(eval interpFn A ord i'' w)) ||
        (ord.ltB i'' i')

/-! ### General entailment facts

Of the supplement's Fact 3 entailment patterns, those that follow directly from
the shape of the semantics are proved here for arbitrary models; the remainder
are established mathematically in [kocurek-2024-supplement] and witnessed on
the finite models below. -/

/-- Fact 3(f): ≻ is irreflexive — ⊨ ¬(A ≻ A). A witness interpretation would
have to make A both true and false. -/
theorem eval_mc_self_eq_false {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity) (ord : SemanticOrdering I) (i : I) (w : W) :
    eval interpFn (.mc φ φ) ord i w = false := by
  simp only [eval, bAny, decide_eq_false_iff_not]
  rintro ⟨i', h⟩
  rcases h' : eval interpFn φ ord i' w <;> simp [h'] at h

/-- Fact 3(k): ≈ is reflexive — ⊨ A ≈ A. -/
theorem eval_me_self_eq_true {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity) (ord : SemanticOrdering I) (i : I) (w : W) :
    eval interpFn (φ.me φ) ord i w = true := by
  show (!eval interpFn (.mc φ φ) ord i w && !eval interpFn (.mc φ φ) ord i w) = true
  simp [eval_mc_self_eq_false]

/-- ≈ is symmetric in its arguments (Fact 3(l) is the entailment form). -/
theorem eval_me_comm {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ ψ : MFormula Pred Entity) (ord : SemanticOrdering I) (i : I) (w : W) :
    eval interpFn (φ.me ψ) ord i w = eval interpFn (ψ.me φ) ord i w := by
  show (!eval interpFn (.mc φ ψ) ord i w && !eval interpFn (.mc ψ φ) ord i w) = _
  exact Bool.and_comm _ _

/-! ### Assertoric Content and Entailment -/

/-- Is interpretation i maximal in the ordering? -/
def isMaximal {I : Type*} [Fintype I] (ord : SemanticOrdering I) (i : I) : Bool :=
  bAll I λ i' => !ord.ltB i i'

/-- Assertoric content: A is true at all ≤-maximal interpretations.

|A|^{≤,w} = 1 iff ∀ i, i is maximal → ⟦A⟧^{≤,i,w} = 1.
A speaker accepts A iff on every ordering-world pair they leave open,
A is true at every top-ranked interpretation. -/
def assertoricContent {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity) (ord : SemanticOrdering I) (w : W) : Bool :=
  bAll I λ i => !(isMaximal ord i) || eval interpFn φ ord i w

/-- Truth-preservation (⊨): for all ⟨≤, i, w⟩, if premises are true then
conclusion is true. Classical; validates Observations 1, 2, 4, 5. -/
def truthPreserves {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (premises : List (MFormula Pred Entity))
    (conclusion : MFormula Pred Entity) : Prop :=
  ∀ (ord : SemanticOrdering I) (i : I) (w : W),
    (premises.all (λ φ => eval interpFn φ ord i w)) = true →
    eval interpFn conclusion ord i w = true

/-- Acceptance-preservation (⊩): for all ⟨≤, w⟩, if assertoric content of
all premises holds, then assertoric content of conclusion holds.
Nonclassical; validates Observation 3 (A ∧ ¬B ⊩ A ≻ B). -/
def acceptancePreserves {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (premises : List (MFormula Pred Entity))
    (conclusion : MFormula Pred Entity) : Prop :=
  ∀ (ord : SemanticOrdering I) (w : W),
    (premises.all (λ φ => assertoricContent interpFn φ ord w)) = true →
    assertoricContent interpFn conclusion ord w = true

/-! ### Distance Functions and Degree Modifiers (§6.1) -/

/-- A distance function for a semantic ordering.

Maps each interpretation to the set of interpretations "reasonably close"
to it. Used to define `very much`, `sorta`, `mostly`. -/
structure DistanceFunction (I : Type*) (ord : SemanticOrdering I) where
  /-- d(i) = the set of interpretations reasonably close to i.
  `close i i'` means i' is reasonably close to i. -/
  close : I → I → Bool
  /-- Centered: i ∈ d(i) -/
  centered : ∀ (i : I), close i i = true
  /-- Top-bounded: if i' ∈ d(i), then i' ≤ i -/
  topBounded : ∀ (i i' : I), close i i' = true → ord.le i' i
  /-- Convex: if i' ∈ d(i) and i' ≤ i'' ≤ i, then i'' ∈ d(i) -/
  convex : ∀ (i i' i'' : I),
    close i i' = true → ord.le i' i'' → ord.le i'' i →
    close i i'' = true
  /-- Noncontractive: if i' ∈ d(i) and i' ≤ j ≤ i, then i' ∈ d(j) -/
  noncontractive : ∀ (i i' j : I),
    close i i' = true → ord.le i' j → ord.le j i →
    close j i' = true

/-- "Far below": i ≪ j iff i ≤ j and i ∉ d(j).
i is ranked below j and not even reasonably close. -/
def farBelow {I : Type*} (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i j : I) : Bool :=
  ord.leB i j && !d.close j i

/-- Much more (A ≫ B): like A ≻ B but with ≪ instead of <.

⟦A ≫ B⟧ = 1 iff ∃ i' ≤ i with (A∧¬B) true at i', and
∀ i'' ≤ i with (B∧¬A) true at i'', i'' ≪ i'. -/
def evalMuchMore {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ ψ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i : I) (w : W) : Bool :=
  bAny I λ i' =>
    ord.leB i' i &&
    eval interpFn φ ord i' w &&
    !(eval interpFn ψ ord i' w) &&
    bAll I λ i'' =>
      !(ord.leB i'' i &&
        eval interpFn ψ ord i'' w &&
        !(eval interpFn φ ord i'' w)) ||
      farBelow ord d i'' i'

/-- very A := A ≫ ¬A.
True iff every reasonably close interpretation makes A true.

Reduces to: ∀ i' ∈ d(i), ⟦A⟧^{i',w} = 1. -/
def evalVery {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i : I) (w : W) : Bool :=
  evalMuchMore interpFn φ (.neg φ) ord d i w

/-- sorta A := ¬ very ¬A.
True iff some reasonably close interpretation makes A true.

Reduces to: ∃ i' ∈ d(i), ⟦A⟧^{i',w} = 1. -/
def evalSorta {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i : I) (w : W) : Bool :=
  !evalVery interpFn (.neg φ) ord d i w

/-- mostly A (eq. 97 of [rudolph-kocurek-2024]).
True iff there is a reasonably high level (strictly below the top,
within the distance threshold) where A is uniformly true, and all
A-false levels below the current interpretation are ranked below it.

`mostly A` is compatible with A and with ¬A (unlike `very`). It entails
`sorta A`. And `mostly A ∧ mostly ¬A` is contradictory. -/
def evalMostly {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i : I) (w : W) : Bool :=
  bAny I λ i' =>
    ord.ltB i' i &&
    d.close i i' &&
    -- (ii) all j at the same rank as i' satisfy A
    bAll I (λ j => !(ord.equivB j i') || eval interpFn φ ord j w) &&
    -- (iii) all A-false levels below i are below i'
    bAll I (λ i'' =>
      !(ord.ltB i'' i &&
        bAll I (λ j => !(ord.equivB j i'') || !(eval interpFn φ ord j w))) ||
      ord.ltB i'' i')

/-- No Reversal constraint (van Benthem 1990; §7 of [rudolph-kocurek-2024]).

If entity e₁ is in the extension of P and e₂ is not at interpretation i,
then for all i' ≤ i where e₂ enters the extension, e₁ must also be in
the extension.

When NR holds for gradable adjectives, the MC `Fa ≻ Gb` simplifies to
the **delineation comparative**: ∃ i' ≤ i with Fa∧¬Gb — the second clause
of the MC semantics (about dominating all (B∧¬A)-witnesses) becomes
redundant. This connects metalinguistic comparatives to
[klein-1980] and [kamp-1975]. See
`Semantics/Degree/Gradability/Delineation.lean` for the delineation
framework. -/
def noReversal {I W Pred Entity : Type*}
    (interpFn : I → Interpretation W Pred Entity)
    (ord : SemanticOrdering I)
    (P : Pred) (w : W) (e1 e2 : Entity) : Prop :=
  ∀ (i i' : I),
    ord.le i' i →
    (interpFn i).ext P w e1 = true →
    (interpFn i).ext P w e2 = false →
    (interpFn i').ext P w e2 = true →
    (interpFn i').ext P w e1 = true

/-! ### Revised Semantics ([kocurek-2024-supplement] §B) -/

/-- Evaluate a formula under the revised MC semantics ([kocurek-2024-supplement] §B).

The basic semantics (`eval`) fails ME transitivity: `A ≈ B, B ≈ C ⊭ A ≈ C`.
The revised semantics strengthens the MC: the (A∧¬B)-witness must dominate
either **all B-interpretations** or **all ¬A-interpretations**, not merely
all (B∧¬A)-interpretations. This prevents cases where the basic MC holds
vacuously due to the absence of (B∧¬A)-witnesses while (A∧B) or (¬A∧¬B)
interpretations remain undominated.

Formally (simplified form): `A ≻ B` iff ∃ i' ≤ i with A∧¬B at i', and
either (a) ∀ i'' ≤ i: ⟦B⟧^{i''} → i'' < i', or
(b) ∀ i'' ≤ i: ⟦¬A⟧^{i''} → i'' < i'.

Properties ([kocurek-2024-supplement] §B):
- All basic entailment patterns (Fact 3 a-n) are preserved (Fact 5)
- ME transitivity is validated: `A ≈ B, B ≈ C ⊨ A ≈ C` (Fact 6)
- Interdefinable with basic semantics (Fact 7):
  `A >_basic B = (A∧¬B) >_revised (B∧¬A)` -/
def evalRevised {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) : Bool :=
  match φ with
  | .atom P e => (interpFn i).ext P w e
  | .neg A => !evalRevised interpFn A ord i w
  | .conj A B => evalRevised interpFn A ord i w && evalRevised interpFn B ord i w
  | .disj A B => evalRevised interpFn A ord i w || evalRevised interpFn B ord i w
  | .mc A B =>
    bAny I λ i' =>
      ord.leB i' i &&
      evalRevised interpFn A ord i' w &&
      !(evalRevised interpFn B ord i' w) &&
      (-- (a): witness dominates all B-interpretations
       bAll I (λ i'' =>
         !(ord.leB i'' i && evalRevised interpFn B ord i'' w) ||
         ord.ltB i'' i')
       ||
       -- (b): witness dominates all ¬A-interpretations
       bAll I (λ i'' =>
         !(ord.leB i'' i && !(evalRevised interpFn A ord i'' w)) ||
         ord.ltB i'' i'))

/-! ### Metalinguistic Conditional (§6.3) -/

/-- Evaluate a formula with a raw ordering relation.

Like `eval`, but takes `le : I → I → Bool` directly rather than
a `SemanticOrdering`. Needed for metalinguistic conditionals, where
the consequent is evaluated relative to a restricted ordering ≤_A
that may not satisfy totality (since non-A interpretations are
dropped). Agrees with `eval` when given `ord.le`. -/
def evalGen {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (le : I → I → Bool) (i : I) (w : W) : Bool :=
  match φ with
  | .atom P e => (interpFn i).ext P w e
  | .neg A => !evalGen interpFn A le i w
  | .conj A B => evalGen interpFn A le i w && evalGen interpFn B le i w
  | .disj A B => evalGen interpFn A le i w || evalGen interpFn B le i w
  | .mc A B =>
    bAny I λ i' =>
      le i' i &&
      evalGen interpFn A le i' w &&
      !(evalGen interpFn B le i' w) &&
      bAll I λ i'' =>
        !(le i'' i &&
          evalGen interpFn B le i'' w &&
          !(evalGen interpFn A le i'' w)) ||
        (le i'' i' && !(le i' i''))

/-- Restrict an ordering relation to A-interpretations (§6.3).

≤_A = {⟨i, j⟩ | i ≤ j ∧ ⟦A⟧^{≤,i,w} = 1 ∧ ⟦A⟧^{≤,j,w} = 1}

Drops non-A interpretations from the ordering. The resulting relation
satisfies reflexivity (at A-interps) and transitivity, but not totality
— hence the consequent is evaluated via `evalGen` rather than `eval`. -/
def restrictLE {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (A : MFormula Pred Entity)
    (le : I → I → Bool) (w : W) : I → I → Bool :=
  λ i j => le i j && evalGen interpFn A le i w && evalGen interpFn A le j w

/-- Metalinguistic conditional (eq. 120 of [rudolph-kocurek-2024]).

⟦A → B⟧^{≤,i,w} = 1 iff ∀ i' ≤ i : ⟦A⟧^{≤,i',w} = 1 → ⟦B⟧^{≤_A,i',w} = 1

The antecedent A is evaluated with the full ordering ≤. The consequent
B is evaluated with the A-restricted ordering ≤_A. When A and B are
non-metagradable (contain no ≻), ⟦B⟧^{≤_A} = ⟦B⟧^{≤}, so the
conditional reduces to interpretation-strict implication: every ranked
A-interpretation is a B-interpretation.

Key properties:
- C1: (A → B) ⊨ (B ≥ A) — conditionals entail weak comparatives
- M1: ⊨ A → (A ≻ ¬A) — classically valid
- M2: A → B, ¬B ⊮ ¬A — modus tollens fails for acceptance -/
def evalMCond {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (A B : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) : Bool :=
  let le := ord.leB
  let leA := restrictLE interpFn A le w
  bAll I λ i' =>
    !(le i' i && evalGen interpFn A le i' w) ||
    evalGen interpFn B leA i' w

/-! ### Connection to Common Ground -/

open CommonGround (ContextSet HasContextSet)

/-- An ordering-world pair: the enriched index for metalinguistic CommonGround.

The common ground is a set of ordering-world pairs ⟨≤, w⟩ compatible
with speakers' factual AND interpretive commitments. -/
structure OrderingWorldPair (I W : Type*) where
  ord : SemanticOrdering I
  world : W

/-- The metalinguistic common ground: a set of ordering-world pairs.

Generalizes Stalnaker's context set (= set of worlds) to include
interpretive commitments. Projects to a classical context set via
existential quantification over orderings. -/
abbrev MetalinguisticCG (I W : Type*) := OrderingWorldPair I W → Prop

namespace MetalinguisticCG

variable {I W : Type*}

/-- Project to a classical context set by existentially quantifying
over semantic orderings. A world w is in the context set iff some
ordering paired with w is in the metalinguistic CommonGround. -/
def toContextSet (cg : MetalinguisticCG I W) : ContextSet W :=
  λ w => ∃ ord, cg ⟨ord, w⟩

/-- Update with assertoric content: keep pairs where |A| holds. -/
def updateAssertoric {Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (cg : MetalinguisticCG I W) (φ : MFormula Pred Entity) :
    MetalinguisticCG I W :=
  λ pair => cg pair ∧ assertoricContent interpFn φ pair.ord pair.world = true

end MetalinguisticCG

/-- MetalinguisticCG projects to a ContextSet via HasContextSet. -/
instance {I W : Type*} : HasContextSet (MetalinguisticCG I W) W where
  toContextSet := MetalinguisticCG.toContextSet

/-! ### Prop-Level Characterization of the Revised MC -/

-- Bridge between leB/ltB and Prop-valued le/lt
private theorem leB_iff {I : Type*} (ord : SemanticOrdering I) (i j : I) :
    ord.leB i j = true ↔ ord.le i j := by
  simp [SemanticOrdering.leB, decide_eq_true_eq]

private theorem ltB_iff {I : Type*} (ord : SemanticOrdering I) (i j : I) :
    ord.ltB i j = true ↔ ord.lt i j := by
  simp [SemanticOrdering.ltB, SemanticOrdering.leB, SemanticOrdering.lt,
    Bool.and_eq_true, decide_eq_true_eq, decide_eq_false_iff_not]

-- Converts Bool disjunction to implication form
private theorem bGuard (a b c : Bool) :
    (!(a && b)) = true ∨ c = true ↔ (a = true → b = true → c = true) := by
  cases a <;> cases b <;> cases c <;> simp

private theorem bGuardNeg (a d c : Bool) :
    (!(a && !d)) = true ∨ c = true ↔ (a = true → d = false → c = true) := by
  cases a <;> cases d <;> cases c <;> simp

/-- Prop-level characterization of revised MC (`evalRevised` on `.mc A B`).
Converts Boolean `bAny`/`bAll` wrappers to standard Prop quantifiers. -/
theorem evalRevised_mc_iff {I W Pred Entity : Type*} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (A B : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    evalRevised interpFn (.mc A B) ord i w = true ↔
    ∃ i' : I,
      ord.le i' i ∧
      evalRevised interpFn A ord i' w = true ∧
      evalRevised interpFn B ord i' w = false ∧
      ((∀ i'' : I, ord.le i'' i → evalRevised interpFn B ord i'' w = true →
         ord.lt i'' i') ∨
       (∀ i'' : I, ord.le i'' i → evalRevised interpFn A ord i'' w = false →
         ord.lt i'' i')) := by
  -- evalRevised (.mc A B) reduces to bAny/bAll over leB/ltB
  show (bAny I fun i' => ord.leB i' i && evalRevised interpFn A ord i' w &&
       !(evalRevised interpFn B ord i' w) &&
       (bAll I (fun i'' => !(ord.leB i'' i && evalRevised interpFn B ord i'' w) ||
          ord.ltB i'' i') ||
        bAll I (fun i'' => !(ord.leB i'' i && !(evalRevised interpFn A ord i'' w)) ||
          ord.ltB i'' i')))
    = true ↔ _
  simp only [bAny, bAll, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨i', ⟨⟨h_le, h_A⟩, h_nB⟩, h_dom⟩
    have h_B : evalRevised interpFn B ord i' w = false := by
      revert h_nB; cases evalRevised interpFn B ord i' w <;> simp
    refine ⟨i', (leB_iff ord i' i).mp h_le, h_A, h_B, ?_⟩
    rcases h_dom with h1 | h2
    · exact Or.inl fun i'' h_le'' h_B'' => by
        have := h1 i''; rw [bGuard] at this
        exact (ltB_iff ord i'' i').mp (this ((leB_iff ord i'' i).mpr h_le'') h_B'')
    · exact Or.inr fun i'' h_le'' h_A'' => by
        have := h2 i''; rw [bGuardNeg] at this
        exact (ltB_iff ord i'' i').mp (this ((leB_iff ord i'' i).mpr h_le'') h_A'')
  · rintro ⟨i', h_le, h_A, h_B, h_dom⟩
    refine ⟨i', ⟨⟨(leB_iff ord i' i).mpr h_le, h_A⟩, by simp [h_B]⟩, ?_⟩
    rcases h_dom with h1 | h2
    · exact Or.inl fun i'' => by
        rw [bGuard]; intro h_le'' h_B''
        exact (ltB_iff ord i'' i').mpr (h1 i'' ((leB_iff ord i'' i).mp h_le'') h_B'')
    · exact Or.inr fun i'' => by
        rw [bGuardNeg]; intro h_le'' h_A''
        exact (ltB_iff ord i'' i').mpr (h2 i'' ((leB_iff ord i'' i).mp h_le'') h_A'')

/-! ### Field and Denotation Sets -/

/-- The field I_i: the set of interpretations ranked at or below i. -/
def field {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) : Finset I :=
  Finset.univ.filter (λ j => ord.le j i)

/-- The denotation of a formula: the set of interpretations in I_i
where the formula is true (under the revised semantics). -/
def denotation {I W Pred Entity : Type*} [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) : Finset I :=
  (field ord i).filter (λ j => evalRevised interpFn φ ord j w)

/-! ### The ∼ Equivalence Relation ([kocurek-2024-supplement] §C, p. 9) -/

/-- Condition (i) of the ∼ equivalence: every element of X\Y is
matched by an element of Y\X at least as high, and vice versa.

This is the same as the basic ME matching condition applied to
interpretation sets rather than formulas. -/
def equivCond1 {I : Type*} [DecidableEq I]
    (ord : SemanticOrdering I) (X Y : Finset I) : Prop :=
  (∀ i' ∈ X \ Y, ∃ i'' ∈ Y \ X, ord.le i' i'') ∧
  (∀ i' ∈ Y \ X, ∃ i'' ∈ X \ Y, ord.le i' i'')

/-- Condition (ii) of the ∼ equivalence: every element of the
symmetric difference (X ∪ Y) \ (X ∩ Y) is dominated by both
an element of X ∩ Y and an element of X̄ ∩ Ȳ (relative to I_i).

This handles the "Figure 1" situation where A ↔ ¬B always holds
at top-ranked interpretations: if every A-or-B-but-not-both
interpretation is matched by both an A∧B and a ¬A∧¬B interpretation. -/
def equivCond2 {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  ∀ i' ∈ (X ∪ Y) \ (X ∩ Y),
    (∃ i'' ∈ X ∩ Y, ord.le i' i'') ∧
    (∃ i'' ∈ field ord i \ (X ∪ Y), ord.le i' i'')

/-- Metalinguistic degree equivalence: X ∼_i Y.

Two interpretation sets have the same metalinguistic degree iff
either (i) their symmetric difference elements are pairwise matched
in rank, or (ii) every unmatched element is dominated by both an
element in the overlap and an element outside both sets.

This mirrors the revised ME truth conditions ([kocurek-2024-supplement] §B) applied
to sets rather than formulas. -/
def degreeEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  equivCond1 ord X Y ∨ equivCond2 ord i X Y

/-! ### Fact 8: ∼ is an Equivalence Relation -/

/-- Fact 8a: ∼ is reflexive.
X \ X = ∅, so all conditions are vacuously satisfied. -/
theorem degreeEquiv_refl {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) :
    degreeEquiv ord i X X := by
  left
  constructor <;> intro i' h <;> simp at h

/-- Fact 8b: ∼ is symmetric.
Both conditions are symmetric in X and Y: condition (i) swaps the
two conjuncts, and condition (ii) is invariant under X ↔ Y since
X ∩ Y = Y ∩ X and X ∪ Y = Y ∪ X. -/
theorem degreeEquiv_symm {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y : Finset I) :
    degreeEquiv ord i X Y → degreeEquiv ord i Y X := by
  intro h
  rcases h with h1 | h2
  · left; exact ⟨h1.2, h1.1⟩
  · right
    intro i' hi'
    have hi'swap : i' ∈ (X ∪ Y) \ (X ∩ Y) := by
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hi' ⊢
      exact ⟨Or.symm hi'.1, λ ⟨h1, h2⟩ => hi'.2 ⟨h2, h1⟩⟩
    obtain ⟨h2a, h2b⟩ := h2 i' hi'swap
    constructor
    · obtain ⟨i'', hi''mem, hi''le⟩ := h2a
      exact ⟨i'', by rwa [Finset.inter_comm] at hi''mem, hi''le⟩
    · obtain ⟨i'', hi''mem, hi''le⟩ := h2b
      exact ⟨i'', by rwa [Finset.union_comm] at hi''mem, hi''le⟩

/-! ### The ⊐ Ordering on Sets ([kocurek-2024-supplement] §C, p. 10) -/

/-- X ⊐ Y: interpretation set X is strictly better than Y.

Mirrors the revised MC truth conditions ([kocurek-2024-supplement] §B):
∃ i' ∈ I_i such that i' ∈ X \ Y and either
(a) all elements of X ∩ Y are strictly below i', or
(b) all elements of I_i \ (X ∪ Y) are strictly below i',
and in both cases all elements of Y \ X are strictly below i'. -/
def strictlyBetter {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  ∃ i' ∈ X \ Y,
    i' ∈ field ord i ∧
    (∀ i'' ∈ Y \ X, ord.lt i'' i') ∧
    ((∀ i'' ∈ X ∩ Y, ord.lt i'' i') ∨
     (∀ i'' ∈ field ord i \ (X ∪ Y), ord.lt i'' i'))

/-! ### Order-Theoretic Helpers -/

/-- Every nonempty Finset has a maximal element under a total preorder. -/
private lemma exists_le_max {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (S : Finset I) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ s ∈ S, ord.le s m := by
  induction S using Finset.cons_induction with
  | empty => exact absurd hS (by simp)
  | cons x S' hx ih =>
    by_cases hS' : S'.Nonempty
    · obtain ⟨m, hm, hle⟩ := ih hS'
      rcases ord.le_total x m with h | h
      · exact ⟨m, Finset.mem_cons.mpr (Or.inr hm), fun s hs => by
          rcases Finset.mem_cons.mp hs with rfl | hs'
          · exact h
          · exact hle s hs'⟩
      · exact ⟨x, Finset.mem_cons_self x S', fun s hs => by
          rcases Finset.mem_cons.mp hs with rfl | hs'
          · exact ord.le_refl _
          · exact ord.le_trans s m x (hle s hs') h⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hS'
      exact ⟨x, Finset.mem_cons_self x S', fun s hs => by
        simp [hS'] at hs; exact hs ▸ ord.le_refl _⟩

/-- a ≤ b ∧ b < c → a < c. -/
private lemma le_lt_trans' {I : Type*} (ord : SemanticOrdering I) (a b c : I) :
    ord.le a b → ord.lt b c → ord.lt a c :=
  fun hab ⟨hbc, hncb⟩ =>
    ⟨ord.le_trans a b c hab hbc, fun hca => hncb (ord.le_trans c a b hca hab)⟩

/-- a < b ∧ b ≤ c → a < c. -/
private lemma lt_le_trans' {I : Type*} (ord : SemanticOrdering I) (a b c : I) :
    ord.lt a b → ord.le b c → ord.lt a c :=
  fun ⟨hab, hnba⟩ hbc =>
    ⟨ord.le_trans a b c hab hbc, fun hca => hnba (ord.le_trans b c a hbc hca)⟩

/-- lt is irreflexive. -/
private lemma lt_irrefl' {I : Type*} (ord : SemanticOrdering I) (m : I) :
    ¬ ord.lt m m :=
  fun ⟨_, h⟩ => h (ord.le_refl m)

/-- b ≠ true → b = false. -/
private theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬ (b = true)) :
    b = false := by cases b <;> simp_all

/-- If m dominates X ∩ Y and Y \ X, it dominates all of Y. -/
private lemma dom_all_of_inter_sdiff {I : Type*} [DecidableEq I]
    (ord : SemanticOrdering I) (m : I) (X Y : Finset I)
    (h_cap : ∀ c ∈ X ∩ Y, ord.lt c m)
    (h_sdiff : ∀ y ∈ Y \ X, ord.lt y m) :
    ∀ y ∈ Y, ord.lt y m := by
  intro y hy
  by_cases hyx : y ∈ X
  · exact h_cap y (Finset.mem_inter.mpr ⟨hyx, hy⟩)
  · exact h_sdiff y (Finset.mem_sdiff.mpr ⟨hy, hyx⟩)

/-- If m dominates Y \ X and field \ (X ∪ Y), it dominates field \ X. -/
private lemma dom_fX_of_sdiff_comp {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (m : I) (X Y : Finset I)
    (h_yx : ∀ y ∈ Y \ X, ord.lt y m)
    (h_comp : ∀ c ∈ field ord i \ (X ∪ Y), ord.lt c m) :
    ∀ c ∈ field ord i \ X, ord.lt c m := by
  intro c hc
  by_cases hc_y : c ∈ Y
  · exact h_yx c (Finset.mem_sdiff.mpr ⟨hc_y, (Finset.mem_sdiff.mp hc).2⟩)
  · exact h_comp c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
      fun h => Finset.mem_union.mp h |>.elim (Finset.mem_sdiff.mp hc).2 hc_y⟩)

/-- (X ∪ Y) \ (X ∩ Y) = (X \ Y) ∪ (Y \ X). -/
private lemma mem_symdiff_iff {I : Type*} [DecidableEq I]
    (X Y : Finset I) (s : I) :
    s ∈ (X ∪ Y) \ (X ∩ Y) ↔ s ∈ (X \ Y) ∪ (Y \ X) := by
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨hx | hy, hni⟩
    · exact Or.inl ⟨hx, fun hy => hni ⟨hx, hy⟩⟩
    · exact Or.inr ⟨hy, fun hx => hni ⟨hx, hy⟩⟩
  · rintro (⟨hx, hny⟩ | ⟨hy, hnx⟩)
    · exact ⟨Or.inl hx, fun ⟨_, hy⟩ => hny hy⟩
    · exact ⟨Or.inr hy, fun ⟨hx, _⟩ => hnx hx⟩

/-- X ≠ Y → (X \ Y) ∪ (Y \ X) is nonempty. -/
private lemma symdiff_nonempty {I : Type*} [DecidableEq I]
    (X Y : Finset I) (h : X ≠ Y) : ((X \ Y) ∪ (Y \ X)).Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  apply h; ext x
  constructor
  · intro hx
    by_contra hy
    have : x ∈ (X \ Y) ∪ (Y \ X) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hx, hy⟩))
    rw [h_empty] at this; simp at this
  · intro hy
    by_contra hx
    have : x ∈ (X \ Y) ∪ (Y \ X) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hy, hx⟩))
    rw [h_empty] at this; simp at this

/-! ### Facts 11–12: ⊐ on Degrees -/

/-- Fact 12a: ⊐ is irreflexive on sets.
i' ∈ X \ X is impossible, so no witness exists. -/
theorem strictlyBetter_irrefl {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) :
    ¬ strictlyBetter ord i X X := by
  intro ⟨i', hi', _, _, _⟩
  simp at hi'

/-- If X ∼ Y, then ¬(X ⊐ Y).
Under equivCond1, any witness i' ∈ X\Y is matched by i'' ∈ Y\X with
i' ≤ i'', contradicting i'' < i'. Under equivCond2, the witness is
dominated by an X∩Y or field\(X∪Y) element, contradicting the inner
disjunct of ⊐. -/
theorem degreeEquiv_not_strictlyBetter {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y : Finset I) :
    degreeEquiv ord i X Y → ¬ strictlyBetter ord i X Y := by
  intro h_eq ⟨i', h_sdiff, _, h_ymx, h_inner⟩
  rcases h_eq with ⟨h_match, _⟩ | h2
  · -- equivCond1: i' ∈ X\Y is matched by i'' ∈ Y\X with i' ≤ i''
    obtain ⟨i'', h_i''_sdiff, h_le⟩ := h_match i' h_sdiff
    exact (h_ymx i'' h_i''_sdiff).2 h_le
  · -- equivCond2: i' ∈ (X ∪ Y) \ (X ∩ Y), dominated by X∩Y and field\(X∪Y)
    have h_symdiff : i' ∈ (X ∪ Y) \ (X ∩ Y) :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp h_sdiff).1),
         fun h => (Finset.mem_sdiff.mp h_sdiff).2 (Finset.mem_inter.mp h).2⟩
    obtain ⟨⟨i₁, h_i₁_mem, h_le₁⟩, ⟨i₂, h_i₂_mem, h_le₂⟩⟩ := h2 i' h_symdiff
    rcases h_inner with h_cap | h_comp
    · exact (h_cap i₁ h_i₁_mem).2 h_le₁
    · exact (h_comp i₂ h_i₂_mem).2 h_le₂

/-- Fact 11: ⊐ respects ∼ on the right.
If X ⊐ Y and Y ∼ Z (with all sets in the field), then X ⊐ Z.
Under left inner: m dominates all of Y, m ∉ Z is forced, and
matching through Y∼Z extends domination to Z\Y.
Under right inner: m dominates field\X; if m ∉ Z, Z\X ⊆ field\X;
if m ∈ Z, use Y∼Z to find alternative witness in X\Z. -/
theorem strictlyBetter_respects_right {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I)
    (_hXf : X ⊆ field ord i) (hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    strictlyBetter ord i X Y → degreeEquiv ord i Y Z →
    strictlyBetter ord i X Z := by
  rintro ⟨m, hm_sd, hm_f, hm_yx, hm_inner⟩ hyz
  have hm_x := (Finset.mem_sdiff.mp hm_sd).1
  have hm_ny := (Finset.mem_sdiff.mp hm_sd).2
  rcases hm_inner with h_left | h_right
  · -- LEFT INNER: m dominates all of Y
    have m_dom_Y := dom_all_of_inter_sdiff ord m X Y h_left hm_yx
    -- z ∈ Z, z ∉ Y → lt z m (via Y∼Z matching + m_dom_Y)
    have z_ny_lt : ∀ z, z ∈ Z → z ∉ Y → ord.lt z m := by
      intro z hz hny
      rcases hyz with ⟨_, hyz_b⟩ | hyz2
      · obtain ⟨y', hy', hle⟩ := hyz_b z (Finset.mem_sdiff.mpr ⟨hz, hny⟩)
        exact le_lt_trans' ord z y' m hle (m_dom_Y y' (Finset.mem_sdiff.mp hy').1)
      · obtain ⟨⟨c, hc, hle⟩, _⟩ := hyz2 z
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hz),
            fun h => hny (Finset.mem_inter.mp h).1⟩)
        exact le_lt_trans' ord z c m hle (m_dom_Y c (Finset.mem_inter.mp hc).1)
    -- m ∉ Z forced
    have hm_nz : m ∉ Z :=
      fun hm_z => absurd (z_ny_lt m hm_z hm_ny) (lt_irrefl' ord m)
    refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_x, hm_nz⟩, hm_f, ?_, Or.inl ?_⟩
    · intro z hz
      by_cases hz_y : z ∈ Y
      · exact hm_yx z (Finset.mem_sdiff.mpr ⟨hz_y, (Finset.mem_sdiff.mp hz).2⟩)
      · exact z_ny_lt z (Finset.mem_sdiff.mp hz).1 hz_y
    · intro c hc
      by_cases hc_y : c ∈ Y
      · exact m_dom_Y c hc_y
      · exact z_ny_lt c (Finset.mem_inter.mp hc).2 hc_y
  · -- RIGHT INNER: m dominates field \ X
    have m_dom_fX := dom_fX_of_sdiff_comp ord i m X Y hm_yx h_right
    -- Helper: w ∈ X forced when m_dom_fX w gives lt w m, contradicting le m w
    have forced_in_X (w : I) (hw_f : w ∈ field ord i) (hle : ord.le m w) :
        w ∈ X := by
      by_contra h
      exact (m_dom_fX w (Finset.mem_sdiff.mpr ⟨hw_f, h⟩)).2 hle
    by_cases hm_z : m ∈ Z
    · -- m ∈ Z ∩ X: find alternative witness via Y∼Z
      -- Helper: once we have witness w ∈ X\Z with le m w, build the ⊐ proof
      suffices ∃ w, w ∈ X \ Z ∧ w ∈ field ord i ∧ ord.le m w from by
        obtain ⟨w, hw_sd, hw_f, hle⟩ := this
        refine ⟨w, hw_sd, hw_f, ?_, Or.inr ?_⟩
        · intro z hz; exact lt_le_trans' ord z m w
            (m_dom_fX z (Finset.mem_sdiff.mpr ⟨hZf (Finset.mem_sdiff.mp hz).1,
              (Finset.mem_sdiff.mp hz).2⟩)) hle
        · intro c hc; exact lt_le_trans' ord c m w
            (m_dom_fX c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
              fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h))⟩)) hle
      rcases hyz with ⟨_, hyz_b⟩ | hyz2
      · -- cond1: m ∈ Z\Y → ∃ y₀ ∈ Y\Z, le m y₀; y₀ ∈ X forced
        obtain ⟨y₀, hy₀, hle⟩ := hyz_b m (Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩)
        exact ⟨y₀, Finset.mem_sdiff.mpr ⟨forced_in_X y₀ (hYf (Finset.mem_sdiff.mp hy₀).1) hle,
          (Finset.mem_sdiff.mp hy₀).2⟩, hYf (Finset.mem_sdiff.mp hy₀).1, hle⟩
      · -- cond2: ∃ c₂ ∈ field\(Y∪Z), le m c₂; c₂ ∈ X forced
        obtain ⟨_, ⟨c₂, hc₂, hle⟩⟩ := hyz2 m
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hm_z),
            fun h => hm_ny (Finset.mem_inter.mp h).1⟩)
        exact ⟨c₂, Finset.mem_sdiff.mpr ⟨forced_in_X c₂ (Finset.mem_sdiff.mp hc₂).1 hle,
          fun h => (Finset.mem_sdiff.mp hc₂).2 (Finset.mem_union.mpr (Or.inr h))⟩,
          (Finset.mem_sdiff.mp hc₂).1, hle⟩
    · -- m ∉ Z: witness = m ∈ X\Z
      refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_x, hm_z⟩, hm_f, ?_, Or.inr ?_⟩
      · intro z hz; exact m_dom_fX z (Finset.mem_sdiff.mpr
          ⟨hZf (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩)
      · intro c hc; exact m_dom_fX c (Finset.mem_sdiff.mpr
          ⟨(Finset.mem_sdiff.mp hc).1,
           fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h))⟩)

/-- Fact 11: ⊐ respects ∼ on the left.
If X ⊐ Y and X ∼ Z (with all sets in the field), then Z ⊐ Y.
Under left inner: m dominates all of Y; use X∼Z to find
a witness in Z\Y (either m itself or a matched element).
Under right inner: m dominates field\X; m ∈ Z is forced
(matching m ∈ X\Z through X∼Z yields z ∈ field\X < m,
contradicting le m z); elements of Y\Z ∩ X use X∼Z
matching to field\X for domination. -/
theorem strictlyBetter_respects_left {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I)
    (hXf : X ⊆ field ord i) (_hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    strictlyBetter ord i X Y → degreeEquiv ord i X Z →
    strictlyBetter ord i Z Y := by
  rintro ⟨m, hm_sd, hm_f, hm_yx, hm_inner⟩ hxz
  have hm_x := (Finset.mem_sdiff.mp hm_sd).1
  have hm_ny := (Finset.mem_sdiff.mp hm_sd).2
  rcases hm_inner with h_left | h_right
  · -- LEFT INNER: m dominates all of Y
    have m_dom_Y := dom_all_of_inter_sdiff ord m X Y h_left hm_yx
    by_cases hm_z : m ∈ Z
    · -- m ∈ Z: witness m ∈ Z\Y
      refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩, hm_f, ?_, Or.inl ?_⟩
      · intro y hy; exact m_dom_Y y (Finset.mem_sdiff.mp hy).1
      · intro c hc; exact m_dom_Y c (Finset.mem_inter.mp hc).2
    · -- m ∉ Z: use X∼Z to find w ∈ Z with le m w, w ∉ Y forced
      -- Once we have w, the proof is uniform
      suffices ∃ w, w ∈ Z \ Y ∧ w ∈ field ord i ∧ ord.le m w from by
        obtain ⟨w, hw_sd, hw_f, hle⟩ := this
        refine ⟨w, hw_sd, hw_f, ?_, Or.inl ?_⟩
        · intro y hy; exact lt_le_trans' ord y m w
            (m_dom_Y y (Finset.mem_sdiff.mp hy).1) hle
        · intro c hc; exact lt_le_trans' ord c m w
            (m_dom_Y c (Finset.mem_inter.mp hc).2) hle
      -- Helper: w ∉ Y when m_dom_Y w and le m w (lt w m contradicts le m w)
      have not_in_Y (w : I) (hle : ord.le m w) : w ∉ Y :=
        fun h => (m_dom_Y w h).2 hle
      rcases hxz with ⟨hxz_a, _⟩ | hxz2
      · obtain ⟨z₀, hz₀, hle⟩ := hxz_a m (Finset.mem_sdiff.mpr ⟨hm_x, hm_z⟩)
        exact ⟨z₀, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz₀).1, not_in_Y z₀ hle⟩,
          hZf (Finset.mem_sdiff.mp hz₀).1, hle⟩
      · obtain ⟨⟨z₁, hz₁, hle⟩, _⟩ := hxz2 m
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl hm_x),
            fun h => hm_z (Finset.mem_inter.mp h).2⟩)
        exact ⟨z₁, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hz₁).2, not_in_Y z₁ hle⟩,
          hXf (Finset.mem_inter.mp hz₁).1, hle⟩
  · -- RIGHT INNER: m dominates field \ X
    have m_dom_fX := dom_fX_of_sdiff_comp ord i m X Y hm_yx h_right
    -- c ∈ X\Z → lt c m (via X∼Z matching to field\X, then m_dom_fX)
    have lt_via_xz : ∀ c, c ∈ X → c ∉ Z → ord.lt c m := by
      intro c hc_x hc_nz
      rcases hxz with ⟨hxz_a, _⟩ | hxz2
      · obtain ⟨z', hz', hle⟩ := hxz_a c (Finset.mem_sdiff.mpr ⟨hc_x, hc_nz⟩)
        exact le_lt_trans' ord c z' m hle (m_dom_fX z'
          (Finset.mem_sdiff.mpr ⟨hZf (Finset.mem_sdiff.mp hz').1,
            (Finset.mem_sdiff.mp hz').2⟩))
      · obtain ⟨_, ⟨c', hc', hle⟩⟩ := hxz2 c
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl hc_x),
            fun h => hc_nz (Finset.mem_inter.mp h).2⟩)
        exact le_lt_trans' ord c c' m hle (m_dom_fX c'
          (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc').1,
            fun h => (Finset.mem_sdiff.mp hc').2 (Finset.mem_union.mpr (Or.inl h))⟩))
    -- m ∈ Z forced
    have hm_z : m ∈ Z := by
      by_contra hm_nz; exact absurd (lt_via_xz m hm_x hm_nz) (lt_irrefl' ord m)
    -- Witness m ∈ Z\Y
    refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩, hm_f, ?_, Or.inr ?_⟩
    · intro y hy
      by_cases hy_x : y ∈ X
      · exact lt_via_xz y hy_x (Finset.mem_sdiff.mp hy).2
      · exact hm_yx y (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1, hy_x⟩)
    · intro c hc
      by_cases hc_x : c ∈ X
      · exact lt_via_xz c hc_x
          (fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h)))
      · exact m_dom_fX c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1, hc_x⟩)

/-- Fact 12b: ⊐ is transitive on sets.
Given witnesses m₁ (X⊐Y) and m₂ (Y⊐Z), split on which is higher.
If m₂ ≤ m₁: m₁ cannot be in Z (else m₁ ∈ Z\Y with ¬(m₁ < m₂)),
so m₁ ∈ X\Z is the witness for X⊐Z.
If m₁ ≤ m₂: m₂ must be in X (else m₂ ∈ Y\X with ¬(m₂ < m₁)),
so m₂ ∈ X\Z is the witness for X⊐Z. -/
theorem strictlyBetter_trans {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I) :
    strictlyBetter ord i X Y → strictlyBetter ord i Y Z →
    strictlyBetter ord i X Z := by
  rintro ⟨m₁, hm₁_sd, hm₁_f, hm₁_yx, hm₁_inner⟩
         ⟨m₂, hm₂_sd, hm₂_f, hm₂_zy, hm₂_inner⟩
  have hm₁_x := (Finset.mem_sdiff.mp hm₁_sd).1
  have hm₁_ny := (Finset.mem_sdiff.mp hm₁_sd).2
  have hm₂_y := (Finset.mem_sdiff.mp hm₂_sd).1
  have hm₂_nz := (Finset.mem_sdiff.mp hm₂_sd).2
  -- Key helper: z ∈ Z\X → lt z m₁ (when m₂ ≤ m₁)
  have zx_lt_m1 (hle : ord.le m₂ m₁) (z : I) (hz : z ∈ Z \ X) : ord.lt z m₁ := by
    have hz_z := (Finset.mem_sdiff.mp hz).1
    have hz_nx := (Finset.mem_sdiff.mp hz).2
    by_cases hz_y : z ∈ Y
    · exact hm₁_yx z (Finset.mem_sdiff.mpr ⟨hz_y, hz_nx⟩)
    · exact lt_le_trans' ord z m₂ m₁ (hm₂_zy z (Finset.mem_sdiff.mpr ⟨hz_z, hz_y⟩)) hle
  -- Key helper: z ∈ Z\X → lt z m₂ (when m₁ ≤ m₂)
  have zx_lt_m2 (hle : ord.le m₁ m₂) (z : I) (hz : z ∈ Z \ X) : ord.lt z m₂ := by
    have hz_z := (Finset.mem_sdiff.mp hz).1
    have hz_nx := (Finset.mem_sdiff.mp hz).2
    by_cases hz_y : z ∈ Y
    · exact lt_le_trans' ord z m₁ m₂
        (hm₁_yx z (Finset.mem_sdiff.mpr ⟨hz_y, hz_nx⟩)) hle
    · exact hm₂_zy z (Finset.mem_sdiff.mpr ⟨hz_z, hz_y⟩)
  rcases ord.le_total m₂ m₁ with hle | hle
  · -- Case: m₂ ≤ m₁. Witness = m₁.
    -- m₁ ∉ Z: lt m₁ m₂ ∧ le m₂ m₁ → lt m₁ m₁
    have hm₁_nz : m₁ ∉ Z := fun h =>
      absurd (lt_le_trans' ord m₁ m₂ m₁
        (hm₂_zy m₁ (Finset.mem_sdiff.mpr ⟨h, hm₁_ny⟩)) hle) (lt_irrefl' ord m₁)
    refine ⟨m₁, Finset.mem_sdiff.mpr ⟨hm₁_x, hm₁_nz⟩, hm₁_f, zx_lt_m1 hle, ?_⟩
    -- Inner disjunct: follows from X⊐Y's inner
    rcases hm₁_inner with h_cap | h_comp
    · -- Left: ∀ X∩Y < m₁ → ∀ X∩Z < m₁
      left; intro c hc
      have hc_x := (Finset.mem_inter.mp hc).1
      have hc_z := (Finset.mem_inter.mp hc).2
      by_cases hc_y : c ∈ Y
      · exact h_cap c (Finset.mem_inter.mpr ⟨hc_x, hc_y⟩)
      · exact lt_le_trans' ord c m₂ m₁
          (hm₂_zy c (Finset.mem_sdiff.mpr ⟨hc_z, hc_y⟩)) hle
    · -- Right: ∀ field\(X∪Y) < m₁ → ∀ field\(X∪Z) < m₁
      right; intro c hc
      have hc_f := (Finset.mem_sdiff.mp hc).1
      have hc_nxz := (Finset.mem_sdiff.mp hc).2
      have hc_nx : c ∉ X := fun h => hc_nxz (Finset.mem_union.mpr (Or.inl h))
      have hc_nz : c ∉ Z := fun h => hc_nxz (Finset.mem_union.mpr (Or.inr h))
      by_cases hc_y : c ∈ Y
      · exact hm₁_yx c (Finset.mem_sdiff.mpr ⟨hc_y, hc_nx⟩)
      · exact h_comp c (Finset.mem_sdiff.mpr
          ⟨hc_f, fun h => Finset.mem_union.mp h |>.elim hc_nx hc_y⟩)
  · -- Case: m₁ ≤ m₂. Witness = m₂.
    -- m₂ ∈ X: lt m₂ m₁ ∧ le m₁ m₂ → lt m₂ m₂
    have hm₂_x : m₂ ∈ X := by
      by_contra h; exact absurd (lt_le_trans' ord m₂ m₁ m₂
        (hm₁_yx m₂ (Finset.mem_sdiff.mpr ⟨hm₂_y, h⟩)) hle) (lt_irrefl' ord m₂)
    refine ⟨m₂, Finset.mem_sdiff.mpr ⟨hm₂_x, hm₂_nz⟩, hm₂_f, zx_lt_m2 hle, ?_⟩
    -- Inner disjunct: follows from Y⊐Z's inner
    rcases hm₂_inner with h_cap | h_comp
    · -- Left: ∀ Y∩Z < m₂ → ∀ X∩Z < m₂
      left; intro c hc
      have hc_x := (Finset.mem_inter.mp hc).1
      have hc_z := (Finset.mem_inter.mp hc).2
      by_cases hc_y : c ∈ Y
      · exact h_cap c (Finset.mem_inter.mpr ⟨hc_y, hc_z⟩)
      · exact hm₂_zy c (Finset.mem_sdiff.mpr ⟨hc_z, hc_y⟩)
    · -- Right: ∀ field\(Y∪Z) < m₂ → ∀ field\(X∪Z) < m₂
      right; intro c hc
      have hc_f := (Finset.mem_sdiff.mp hc).1
      have hc_nxz := (Finset.mem_sdiff.mp hc).2
      have hc_nx : c ∉ X := fun h => hc_nxz (Finset.mem_union.mpr (Or.inl h))
      have hc_nz : c ∉ Z := fun h => hc_nxz (Finset.mem_union.mpr (Or.inr h))
      by_cases hc_y : c ∈ Y
      · exact lt_le_trans' ord c m₁ m₂
          (hm₁_yx c (Finset.mem_sdiff.mpr ⟨hc_y, hc_nx⟩)) hle
      · exact h_comp c (Finset.mem_sdiff.mpr
          ⟨hc_f, fun h => Finset.mem_union.mp h |>.elim hc_y hc_nz⟩)

/-- Fact 12c: ⊐ is total on nonequivalent sets.
For any X, Y ⊆ I_i, either X ∼ Y or X ⊐ Y or Y ⊐ X.

The proof finds the maximum element m of the symmetric difference
(X\Y)∪(Y\X), then case-splits on whether all elements on the
other side are strictly below m. If yes, we get ⊐; if no, we
get ∼ via one of the two equivalence conditions. -/
theorem strictlyBetter_total {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y : Finset I)
    (hX : X ⊆ field ord i) (hY : Y ⊆ field ord i) :
    degreeEquiv ord i X Y ∨ strictlyBetter ord i X Y ∨
    strictlyBetter ord i Y X := by
  by_cases h_eq : X = Y
  · exact Or.inl (h_eq ▸ degreeEquiv_refl ord i X)
  · obtain ⟨m, hm, hm_max⟩ := exists_le_max ord _ (symdiff_nonempty X Y h_eq)
    -- Helper: any element of the symdiff ≤ m
    have hm_max' : ∀ s ∈ (X \ Y) ∪ (Y \ X), ord.le s m := hm_max
    rcases Finset.mem_union.mp hm with hm_xy | hm_yx
    · -- m ∈ X\Y: either equivCond1, or strictlyBetter X Y
      have hm_field : m ∈ field ord i := hX (Finset.mem_sdiff.mp hm_xy).1
      by_cases h_all_yx : ∀ y ∈ Y \ X, ord.lt y m
      · -- All Y\X < m: check inner disjunct
        by_cases h_cap : ∀ c ∈ X ∩ Y, ord.lt c m
        · exact Or.inr (Or.inl ⟨m, hm_xy, hm_field, h_all_yx, Or.inl h_cap⟩)
        · by_cases h_comp : ∀ c ∈ field ord i \ (X ∪ Y), ord.lt c m
          · exact Or.inr (Or.inl ⟨m, hm_xy, hm_field, h_all_yx, Or.inr h_comp⟩)
          · -- Neither inner holds: equivCond2
            push Not at h_cap h_comp
            obtain ⟨c₁, hc₁_mem, hc₁_nlt⟩ := h_cap
            obtain ⟨c₂, hc₂_mem, hc₂_nlt⟩ := h_comp
            have hc₁_ge := ord.le_of_not_lt hc₁_nlt
            have hc₂_ge := ord.le_of_not_lt hc₂_nlt
            exact Or.inl (Or.inr (fun s hs => by
              have h_le_sm := hm_max' s ((mem_symdiff_iff X Y s).mp hs)
              exact ⟨⟨c₁, hc₁_mem, ord.le_trans s m c₁ h_le_sm hc₁_ge⟩,
                     ⟨c₂, hc₂_mem, ord.le_trans s m c₂ h_le_sm hc₂_ge⟩⟩))
      · -- ∃ y₀ ∈ Y\X with ¬(lt y₀ m): equivCond1
        push Not at h_all_yx
        obtain ⟨y₀, hy₀_mem, hy₀_nlt⟩ := h_all_yx
        have hy₀_ge := ord.le_of_not_lt hy₀_nlt
        exact Or.inl (Or.inl
          ⟨fun x hx => ⟨y₀, hy₀_mem,
              ord.le_trans x m y₀
                (hm_max' x (Finset.mem_union.mpr (Or.inl hx))) hy₀_ge⟩,
           fun y hy => ⟨m, hm_xy,
              hm_max' y (Finset.mem_union.mpr (Or.inr hy))⟩⟩)
    · -- m ∈ Y\X: symmetric case — either equivCond1, or strictlyBetter Y X
      have hm_field : m ∈ field ord i := hY (Finset.mem_sdiff.mp hm_yx).1
      by_cases h_all_xy : ∀ x ∈ X \ Y, ord.lt x m
      · -- All X\Y < m: check inner disjunct
        by_cases h_cap : ∀ c ∈ Y ∩ X, ord.lt c m
        · exact Or.inr (Or.inr ⟨m, hm_yx, hm_field, h_all_xy, Or.inl h_cap⟩)
        · by_cases h_comp : ∀ c ∈ field ord i \ (Y ∪ X), ord.lt c m
          · exact Or.inr (Or.inr ⟨m, hm_yx, hm_field, h_all_xy, Or.inr h_comp⟩)
          · -- Neither inner holds: equivCond2
            push Not at h_cap h_comp
            obtain ⟨c₁, hc₁_mem, hc₁_nlt⟩ := h_cap
            obtain ⟨c₂, hc₂_mem, hc₂_nlt⟩ := h_comp
            have hc₁_ge := ord.le_of_not_lt hc₁_nlt
            have hc₂_ge := ord.le_of_not_lt hc₂_nlt
            exact Or.inl (Or.inr (fun s hs => by
              have h_le_sm := hm_max' s ((mem_symdiff_iff X Y s).mp hs)
              exact ⟨⟨c₁, by rw [Finset.inter_comm]; exact hc₁_mem,
                      ord.le_trans s m c₁ h_le_sm hc₁_ge⟩,
                     ⟨c₂, by rw [Finset.union_comm]; exact hc₂_mem,
                      ord.le_trans s m c₂ h_le_sm hc₂_ge⟩⟩))
      · -- ∃ x₀ ∈ X\Y with ¬(lt x₀ m): equivCond1
        push Not at h_all_xy
        obtain ⟨x₀, hx₀_mem, hx₀_nlt⟩ := h_all_xy
        have hx₀_ge := ord.le_of_not_lt hx₀_nlt
        exact Or.inl (Or.inl
          ⟨fun x hx => ⟨m, hm_yx,
              hm_max' x (Finset.mem_union.mpr (Or.inl hx))⟩,
           fun y hy => ⟨x₀, hx₀_mem,
              ord.le_trans y m x₀
                (hm_max' y (Finset.mem_union.mpr (Or.inr hy))) hx₀_ge⟩⟩)

/-! ### Fact 8c: ∼ Transitivity (via Totality + Respects) -/

/-- Fact 8c: ∼ is transitive (for sets in the field).
Indirect proof: if ¬(X∼Z), totality gives X⊐Z or Z⊐X.
- X⊐Z: respects_right(X,Z,Y) with Z∼Y gives X⊐Y, contradicting X∼Y.
- Z⊐X: respects_right(Z,X,Y) with X∼Y gives Z⊐Y, contradicting Y∼Z.
This avoids the direct Schröder-Bernstein bouncing chain argument. -/
theorem degreeEquiv_trans {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I)
    (hXf : X ⊆ field ord i) (hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    degreeEquiv ord i X Y → degreeEquiv ord i Y Z →
    degreeEquiv ord i X Z := by
  intro hxy hyz
  by_contra h_neq
  rcases strictlyBetter_total ord i X Z hXf hZf with h | h | h
  · exact h_neq h
  · -- X ⊐ Z, Z ∼ Y → X ⊐ Y, contradicts X ∼ Y
    exact degreeEquiv_not_strictlyBetter ord i X Y hxy
      (strictlyBetter_respects_right ord i X Z Y hXf hZf hYf h
        (degreeEquiv_symm ord i Y Z hyz))
  · -- Z ⊐ X, X ∼ Y → Z ⊐ Y, contradicts Y ∼ Z
    exact degreeEquiv_not_strictlyBetter ord i Z Y
      (degreeEquiv_symm ord i Y Z hyz)
      (strictlyBetter_respects_right ord i Z X Y hZf hXf hYf h hxy)

/-- The metalinguistic setoid: ∼ as a Mathlib `Setoid` on field-subsets.
The carrier is `{X : Finset I // X ⊆ field ord i}` because
transitivity requires the ⊆ field hypothesis (via totality). -/
def metalinguisticSetoid {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) :
    Setoid {X : Finset I // X ⊆ field ord i} where
  r X Y := degreeEquiv ord i X.1 Y.1
  iseqv := {
    refl := fun X => degreeEquiv_refl ord i X.1
    symm := fun {X Y} h => degreeEquiv_symm ord i X.1 Y.1 h
    trans := fun {X Y Z} hxy hyz =>
      degreeEquiv_trans ord i X.1 Y.1 Z.1 X.2 Y.2 Z.2 hxy hyz
  }

/-! ### Metalinguistic Degree Type -/

/-- The type of metalinguistic degrees: equivalence classes of
interpretation sets under ∼.

A metalinguistic degree is a *set of sets of interpretations* —
all the interpretation sets that are "ranked as high" as each other.
The degree of a sentence A is `deg(⟦A⟧_i)`. -/
def MetaDegree (I : Type*) [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) :=
  Quotient (metalinguisticSetoid ord i)

/-- Compute the metalinguistic degree of an interpretation set. -/
def deg {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X : Finset I) (hX : X ⊆ field ord i) :
    MetaDegree I ord i :=
  Quotient.mk (metalinguisticSetoid ord i) ⟨X, hX⟩

/-- The metalinguistic degree of a formula's denotation. -/
def formulaDeg {I W Pred Entity : Type*} [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    MetaDegree I ord i :=
  deg ord i (denotation interpFn φ ord i w) (Finset.filter_subset _ _)

/-! ### Facts 9–10: Correspondence with Revised Semantics -/

/-- Membership in `field`: j ∈ I_i iff j ≤ i. -/
private theorem mem_field_iff {I : Type*} [Fintype I] [DecidableEq I]
    {ord : SemanticOrdering I} {i j : I} :
    j ∈ field ord i ↔ ord.le j i := by
  simp [field]

/-- Membership in `denotation`: j ∈ ⟦φ⟧_i iff j ≤ i and ⟦φ⟧^j = 1. -/
private theorem mem_denotation_iff {I W Pred Entity : Type*}
    [Fintype I] [DecidableEq I]
    {interpFn : I → Interpretation W Pred Entity}
    {φ : MFormula Pred Entity}
    {ord : SemanticOrdering I} {i j : I} {w : W} :
    j ∈ denotation interpFn φ ord i w ↔
    ord.le j i ∧ evalRevised interpFn φ ord j w = true := by
  simp [denotation, field]

/-- Fact 10: revised MC holds iff denotation of A ⊐ denotation of B.
⟦A ≻ B⟧^{≤,i,w}_revised = 1 iff ⟦A⟧_i ⊐ ⟦B⟧_i. -/
theorem mc_iff_degree_gt {I W Pred Entity : Type*}
    [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (A B : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    evalRevised interpFn (.mc A B) ord i w = true ↔
    strictlyBetter ord i (denotation interpFn A ord i w)
      (denotation interpFn B ord i w) := by
  rw [evalRevised_mc_iff]
  constructor
  · -- Forward: ∃ i' with le, A true, B false, domination → strictlyBetter
    rintro ⟨i', h_le, h_A, h_B, h_dom⟩
    refine ⟨i', ?_, ?_, ?_, ?_⟩
    · -- i' ∈ denotation A \ denotation B
      exact Finset.mem_sdiff.mpr
        ⟨mem_denotation_iff.mpr ⟨h_le, h_A⟩,
         fun h => absurd (mem_denotation_iff.mp h).2 (by simp [h_B])⟩
    · -- i' ∈ field
      exact mem_field_iff.mpr h_le
    · -- ∀ i'' ∈ Y \ X, lt i'' i'
      intro i'' h_mem
      obtain ⟨h_inY, h_ninX⟩ := Finset.mem_sdiff.mp h_mem
      obtain ⟨h_le'', h_B''⟩ := mem_denotation_iff.mp h_inY
      rcases h_dom with h1 | h2
      · exact h1 i'' h_le'' h_B''
      · exact h2 i'' h_le'' (bool_eq_false_of_ne_true fun h =>
          h_ninX (mem_denotation_iff.mpr ⟨h_le'', h⟩))
    · -- inner disjunct
      rcases h_dom with h1 | h2
      · left; intro i'' h_mem
        obtain ⟨h_le'', h_B''⟩ := mem_denotation_iff.mp (Finset.mem_inter.mp h_mem).2
        exact h1 i'' h_le'' h_B''
      · right; intro i'' h_mem
        have h_sd := Finset.mem_sdiff.mp h_mem
        have h_le'' := mem_field_iff.mp h_sd.1
        exact h2 i'' h_le'' (bool_eq_false_of_ne_true fun h =>
          h_sd.2 (Finset.mem_union.mpr (Or.inl (mem_denotation_iff.mpr ⟨h_le'', h⟩))))
  · -- Backward: strictlyBetter → evalRevised_mc conditions
    rintro ⟨i', h_sdiff, h_field, h_ymx, h_inner⟩
    obtain ⟨h_inX, h_ninY⟩ := Finset.mem_sdiff.mp h_sdiff
    obtain ⟨h_le, h_A⟩ := mem_denotation_iff.mp h_inX
    have h_B : evalRevised interpFn B ord i' w = false :=
      bool_eq_false_of_ne_true fun h =>
        h_ninY (mem_denotation_iff.mpr ⟨h_le, h⟩)
    refine ⟨i', h_le, h_A, h_B, ?_⟩
    rcases h_inner with h1 | h2
    · -- X ∩ Y all below → all B-true in field below
      left; intro i'' h_le'' h_B''
      by_cases h_A'' : evalRevised interpFn A ord i'' w = true
      · exact h1 i'' (Finset.mem_inter.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_A''⟩,
           mem_denotation_iff.mpr ⟨h_le'', h_B''⟩⟩)
      · exact h_ymx i'' (Finset.mem_sdiff.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_B''⟩,
           fun h => h_A'' (mem_denotation_iff.mp h).2⟩)
    · -- field \ (X ∪ Y) all below → all A-false in field below
      right; intro i'' h_le'' h_A''
      by_cases h_B'' : evalRevised interpFn B ord i'' w = true
      · exact h_ymx i'' (Finset.mem_sdiff.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_B''⟩,
           fun h => absurd (mem_denotation_iff.mp h).2 (by simp [h_A''])⟩)
      · exact h2 i'' (Finset.mem_sdiff.mpr
          ⟨mem_field_iff.mpr h_le'',
           fun h => Finset.mem_union.mp h |>.elim
             (fun h => absurd (mem_denotation_iff.mp h).2 (by simp [h_A'']))
             (fun h => absurd (mem_denotation_iff.mp h).2 (by simp [h_B'']))⟩)

/-- Fact 9: ME holds iff denotations have the same degree.
⟦A ≈ B⟧^{≤,i,w}_revised = 1 iff ⟦A⟧_i ∼ ⟦B⟧_i.
This connects the Boolean evaluation function `evalRevised` to the
algebraic degree structure. Forward direction uses `strictlyBetter_total`. -/
theorem me_iff_same_degree {I W Pred Entity : Type*}
    [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (A B : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    evalRevised interpFn (A.me B) ord i w = true ↔
    degreeEquiv ord i (denotation interpFn A ord i w)
      (denotation interpFn B ord i w) := by
  set X := denotation interpFn A ord i w
  set Y := denotation interpFn B ord i w
  -- ME = ¬MC(A,B) ∧ ¬MC(B,A)
  have h_unfold : evalRevised interpFn (A.me B) ord i w =
    (!(evalRevised interpFn (.mc A B) ord i w) &&
     !(evalRevised interpFn (.mc B A) ord i w)) := rfl
  have hX : X ⊆ field ord i := by
    intro j hj; exact Finset.mem_of_subset (Finset.filter_subset _ _) hj
  have hY : Y ⊆ field ord i := by
    intro j hj; exact Finset.mem_of_subset (Finset.filter_subset _ _) hj
  constructor
  · -- Forward: ME → degreeEquiv via totality.
    -- If ¬MC(A,B) and ¬MC(B,A), then by mc_iff_degree_gt,
    -- ¬(X ⊐ Y) and ¬(Y ⊐ X). By totality, X ∼ Y.
    intro h_me
    rw [h_unfold] at h_me
    have h_nmc1 : evalRevised interpFn (.mc A B) ord i w ≠ true := by
      intro h; simp [h] at h_me
    have h_nmc2 : evalRevised interpFn (.mc B A) ord i w ≠ true := by
      intro h; simp [h] at h_me
    have h_nsb1 : ¬ strictlyBetter ord i X Y :=
      fun h => h_nmc1 ((mc_iff_degree_gt interpFn A B ord i w).mpr h)
    have h_nsb2 : ¬ strictlyBetter ord i Y X :=
      fun h => h_nmc2 ((mc_iff_degree_gt interpFn B A ord i w).mpr h)
    rcases strictlyBetter_total ord i X Y hX hY with h | h | h
    · exact h
    · exact absurd h h_nsb1
    · exact absurd h h_nsb2
  · -- Backward: degreeEquiv → ME
    intro h_eq
    rw [h_unfold]
    have h1 : evalRevised interpFn (.mc A B) ord i w ≠ true :=
      fun h => degreeEquiv_not_strictlyBetter ord i X Y h_eq
        ((mc_iff_degree_gt interpFn A B ord i w).mp h)
    have h2 : evalRevised interpFn (.mc B A) ord i w ≠ true :=
      fun h => degreeEquiv_not_strictlyBetter ord i Y X
        (degreeEquiv_symm ord i X Y h_eq)
        ((mc_iff_degree_gt interpFn B A ord i w).mp h)
    cases heq1 : evalRevised interpFn (.mc A B) ord i w <;>
    cases heq2 : evalRevised interpFn (.mc B A) ord i w <;> simp_all

/-! ### Fact 13: Extremal Degrees -/

/-- Fact 13a: the full field I_i is the maximum degree.
deg(⊤) = {I_i}: the tautology's denotation is the whole field,
and nothing is strictly better than I_i. -/
theorem field_is_max {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I)
    (hX : X ⊆ field ord i) :
    ¬ strictlyBetter ord i X (field ord i) ∨
    degreeEquiv ord i X (field ord i) := by
  left
  rintro ⟨i', hi', _⟩
  exact (Finset.mem_sdiff.mp hi').2 (hX (Finset.mem_sdiff.mp hi').1)

/-- Fact 13b: the empty set is the minimum degree.
deg(⊥) = {∅}: the contradiction's denotation is empty,
and nothing is strictly worse than ∅. -/
theorem empty_is_min {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) :
    ¬ strictlyBetter ord i (∅ : Finset I) X ∨
    degreeEquiv ord i X ∅ := by
  left
  rintro ⟨i', hi', _⟩
  simp at hi'

/-! ### Types (shared across models) -/

/-- One world. -/
inductive W | w0
  deriving DecidableEq, Repr, Fintype

/-- Two predicates: linguist and philosopher. -/
inductive Pred | linguist | philosopher
  deriving DecidableEq, Repr, Fintype

/-- One entity: Ann. -/
inductive Entity | ann
  deriving DecidableEq, Repr, Fintype

/-- "Ann is a linguist" -/
abbrev La : MFormula Pred Entity := .atom .linguist .ann

/-- "Ann is a philosopher" -/
abbrev Pa : MFormula Pred Entity := .atom .philosopher .ann

/-- "Ann is more a linguist than a philosopher" -/
abbrev La_mc_Pa : MFormula Pred Entity := .mc La Pa

/-! ### Model 1: Three interpretations (linear order) -/

/-- Three interpretations: i₀ < i₁ < i₂. -/
inductive I3 | i0 | i1 | i2
  deriving DecidableEq, Repr, Fintype

/-- Linear ordering: i0 ≤ i1 ≤ i2. -/
def ord₃ : SemanticOrdering I3 :=
  SemanticOrdering.ofBool
    (λ i j => match i, j with
      | .i0, _ => true
      | .i1, .i0 => false
      | .i1, _ => true
      | .i2, .i2 => true
      | .i2, _ => false)
    (by intro i; cases i <;> rfl)
    (by intro i j k hij hjk; cases i <;> cases j <;> cases k <;> simp_all)
    (by intro i j; cases i <;> cases j <;> simp)

/-- Interpretation function:
- i₀: Ann is a philosopher, not a linguist
- i₁: Ann is a linguist, not a philosopher
- i₂: Ann is both -/
def interp₃ : I3 → Interpretation W Pred Entity
  | .i0 => ⟨λ P _ _ => match P with | .linguist => false | .philosopher => true⟩
  | .i1 => ⟨λ P _ _ => match P with | .linguist => true  | .philosopher => false⟩
  | .i2 => ⟨λ _ _ _ => true⟩

/-! ### Observations on Model 1 -/

/-- Observation 1a: MCs are consistent with truth of both constituents.
At i₂, Ann is both a linguist and a philosopher, yet "Ann is more a
linguist than a philosopher" is true — the (La∧¬Pa)-interpretation i₁
outranks the (Pa∧¬La)-interpretation i₀. -/
theorem obs1a_mc_consistent_with_both :
    eval interp₃ La_mc_Pa ord₃ .i2 .w0 = true ∧
    eval interp₃ La ord₃ .i2 .w0 = true ∧
    eval interp₃ Pa ord₃ .i2 .w0 = true := by decide

/-- Observation 2: A ≻ B, B ⊨ A.
If the MC holds and Ann is a philosopher, she is a linguist. -/
theorem obs2_mc_B_entails_A :
    ∀ (i : I3),
      eval interp₃ La_mc_Pa ord₃ i .w0 = true →
      eval interp₃ Pa ord₃ i .w0 = true →
      eval interp₃ La ord₃ i .w0 = true := by decide

/-! ### Model 2: Two interpretations (tied) for borderline cases -/

/-- Two interpretations for borderline / nonclassicality witnesses. -/
inductive I2 | j0 | j1
  deriving DecidableEq, Repr, Fintype

/-- Tied ordering: j0 ≡ j1 (both maximal). -/
def tiedOrd : SemanticOrdering I2 :=
  SemanticOrdering.ofBool
    (λ _ _ => true)
    (by intro i; cases i <;> rfl)
    (by intro i j k _ _; cases i <;> cases j <;> cases k <;> rfl)
    (by intro i j; left; cases i <;> cases j <;> rfl)

/-- j₀: La true, Pa false; j₁: La false, Pa true. -/
def interp₂ : I2 → Interpretation W Pred Entity
  | .j0 => ⟨λ P _ _ => match P with | .linguist => true  | .philosopher => false⟩
  | .j1 => ⟨λ P _ _ => match P with | .linguist => false | .philosopher => true⟩

/-- Observation 5: A ≈ ¬A is satisfiable (not contradictory).
With tied interpretations where one makes La true and the other
makes La false, "Ann is (exactly) as much a linguist as not"
is coherent — it expresses a borderline case. -/
theorem obs5_me_neg_consistent :
    eval interp₂ (La.me (.neg La)) tiedOrd .j0 .w0 = true := by decide

/-- ¬La -/
abbrev NLa : MFormula Pred Entity := .neg La

/-! ### Assertoric Content and Acceptance-Preservation -/

/- Observation 3 (acceptance-preservation): A ∧ ¬B ⊩ A ≻ B.
If assertoric content of (La ∧ ¬Pa) holds, then assertoric content of
La ≻ Pa holds. On ord₃, the premise fails (Pa is true at i₂), so
the implication holds vacuously. We verify the substantive case on a
model where the premise holds. -/

/-- For substantive Obs 3: i₂ is linguist only. -/
def interp₃' : I3 → Interpretation W Pred Entity
  | .i0 => ⟨λ P _ _ => match P with | .linguist => false | .philosopher => true⟩
  | .i1 => ⟨λ P _ _ => match P with | .linguist => true  | .philosopher => true⟩
  | .i2 => ⟨λ P _ _ => match P with | .linguist => true  | .philosopher => false⟩

theorem obs3_acceptance :
    assertoricContent interp₃' (.conj La (.neg Pa)) ord₃ .w0 = true →
    assertoricContent interp₃' La_mc_Pa ord₃ .w0 = true := by decide

/-- The tautology La ∨ ¬La has assertoric content 1 on the tied model. -/
theorem tautology_accepted :
    assertoricContent interp₂ (.disj La (.neg La)) tiedOrd .w0 = true := by
  decide

/-- Nonclassicality of acceptance-preservation:
(La ≻ ¬La) ∨ (¬La ≻ La) does NOT have assertoric content 1 on the
tied model. At both maximal interpretations (j₀ ≡ j₁), neither
direction of MC holds because the interpretations are tied.

This is the key result paralleling informational entailment for
epistemic modals ([yalcin-2007]). -/
theorem mc_disj_not_accepted :
    assertoricContent interp₂ (.disj (.mc La (.neg La)) (.mc (.neg La) La))
      tiedOrd .w0 = false := by decide

/-! ### Degree Modifiers (§6.1) -/

/-- Distance function for ord₃: close(i) includes interpretations at the
same level or one level below.
- d(i₀) = {i₀}
- d(i₁) = {i₀, i₁}
- d(i₂) = {i₁, i₂} -/
def dist₃ : DistanceFunction I3 ord₃ where
  close := λ i i' => match i, i' with
    | .i0, .i0 => true
    | .i1, .i0 => true
    | .i1, .i1 => true
    | .i2, .i1 => true
    | .i2, .i2 => true
    | _, _ => false
  centered := by intro i; cases i <;> rfl
  topBounded := by decide
  convex := by decide
  noncontractive := by decide

/-- very La is true at i₂: all interpretations reasonably close to i₂
(namely i₁ and i₂) make La true. -/
theorem very_la_at_top :
    evalVery interp₃ La ord₃ dist₃ .i2 .w0 = true := by decide

/-- very La is false at i₁: i₀ is reasonably close to i₁ but
makes La false. -/
theorem very_la_false_at_mid :
    evalVery interp₃ La ord₃ dist₃ .i1 .w0 = false := by decide

/-- sorta La holds at i₁: some close interpretation (i₁ itself) makes
La true, even though another close interpretation (i₀) does not. -/
theorem sorta_la_at_mid :
    evalSorta interp₃ La ord₃ dist₃ .i1 .w0 = true := by decide

/-- sorta La is false at i₀: d(i₀) = {i₀}, and La is false at i₀. -/
theorem sorta_la_false_at_bot :
    evalSorta interp₃ La ord₃ dist₃ .i0 .w0 = false := by decide

/-! ### Degree Modifier: mostly (§6.1) -/

/-- mostly La is true at i₂: there is a reasonably high level (i₁) where
La is uniformly true, and the only A-false level (i₀) is below it. -/
theorem mostly_la_at_top :
    evalMostly interp₃ La ord₃ dist₃ .i2 .w0 = true := by decide

/-- mostly La is false at i₁: i₀ is the only candidate level below i₁ in
d(i₁), but La is false at i₀. -/
theorem mostly_la_false_at_mid :
    evalMostly interp₃ La ord₃ dist₃ .i1 .w0 = false := by decide

/-! ### Bridge: No Reversal and Ordinary Comparison (§7) -/

/-! ### Two-Entity Model: No Reversal (§7) -/

/-- Two entities for gradable adjective models. -/
inductive Entity2 | ann | ben
  deriving DecidableEq, Repr, Fintype

/-- Single predicate: tall. -/
inductive Pred1 | tall
  deriving DecidableEq, Repr, Fintype

/-- NR model for "Ann is taller than Ben":
- i₀: neither Ann nor Ben is tall (empty extension)
- i₁: Ann is tall, Ben is not (Ann enters the extension first)
- i₂: both are tall

Satisfies No Reversal: extensions are monotonically nested
({} ⊆ {ann} ⊆ {ann, ben}). Uses the same 3-interpretation
linear order `ord₃` from Model 1. -/
def interpNR : I3 → Interpretation W Pred1 Entity2
  | .i0 => ⟨λ _ _ _ => false⟩
  | .i1 => ⟨λ _ _ e => match e with | .ann => true | .ben => false⟩
  | .i2 => ⟨λ _ _ _ => true⟩

/-- "Ann is tall" -/
abbrev Ta : MFormula Pred1 Entity2 := .atom .tall .ann

/-- "Ben is tall" -/
abbrev Tb : MFormula Pred1 Entity2 := .atom .tall .ben

/-- No Reversal holds for `tall` on the two-entity model.
Since Ann enters the extension before Ben (at i₁ vs i₂), there is no
interpretation where Ben is tall but Ann is not. NR is satisfied
because the extensions are monotonically nested.

Compare with `nr_trivial_single_entity` above, which holds vacuously
on a single-entity model. Here NR constrains the relationship between
two distinct entities' extensions across the ordering. -/
theorem nr_tall_ann_ben :
    noReversal interpNR ord₃ .tall .w0 .ann .ben := by
  intro i i' _ h1 h2 h3; cases i <;> cases i' <;> simp [interpNR] at *

/-- Ann is taller than Ben: the MC `tall(ann) ≻ tall(ben)` is true
at i₁ and i₂. Witness: i₁ (Ann is tall, Ben is not). -/
theorem ann_taller_i1 :
    eval interpNR (.mc Ta Tb) ord₃ .i1 .w0 = true := by decide

/-- The reverse MC — Ben taller than Ann — is false everywhere.
There is no interpretation where Ben is tall but Ann is not. -/
theorem ben_not_taller :
    ∀ (i : I3), eval interpNR (.mc Tb Ta) ord₃ i .w0 = false := by decide

/-- Bridge: under NR, the full MC (eq. 48, with domination clause)
gives the same result as the delineation comparative (eq. 128,
just ∃ i' ≤ i : Fa ∧ ¬Fb, without domination clause).

NR makes clause (ii) of the MC redundant: if Fa is true and Fb is
false at i, then for any i' ≤ i where Fb becomes true, Fa must also
be true — so there are no (Fb∧¬Fa)-witnesses to worry about.

This connects metalinguistic comparatives to [klein-1980]'s
delineation comparative (see `Delineation.lean`). -/
theorem mc_equals_delineation_under_nr :
    ∀ (i : I3),
      -- Full MC with domination clause
      eval interpNR (.mc Ta Tb) ord₃ i .w0 =
      -- Delineation: just check for a witness (no domination needed)
      (decide (∃ i' : I3, ord₃.le i' i ∧
        (interpNR i').ext .tall .w0 .ann = true ∧
        (interpNR i').ext .tall .w0 .ben = false) : Bool) := by decide

/-- NR-violating model: Ann and Ben "swap" across interpretations.
- i₀: Ann tall, Ben not
- i₁: Ben tall, Ann not (reversal!)
- i₂: both tall -/
def interpNR_bad : I3 → Interpretation W Pred1 Entity2
  | .i0 => ⟨λ _ _ e => match e with | .ann => true | .ben => false⟩
  | .i1 => ⟨λ _ _ e => match e with | .ann => false | .ben => true⟩
  | .i2 => ⟨λ _ _ _ => true⟩

/-- No Reversal fails on the violating model (for e₁=ben, e₂=ann):
Ben is tall at i₁ and Ann is not, but at i₀ ≤ i₁ where Ann is tall,
Ben is not — a reversal. -/
theorem nr_fails_bad :
    ¬ noReversal interpNR_bad ord₃ .tall .w0 .ben .ann := by
  intro h; exact absurd (h .i1 .i0 rfl rfl rfl rfl) (by decide)

/-- Without NR, MC and delineation diverge: the MC `Ta ≻ Tb` is
FALSE at i₂ (the (Tb∧¬Ta)-witness i₁ outranks the (Ta∧¬Tb)-witness
i₀, violating the domination clause), but the simple delineation
condition (∃ Fa∧¬Fb) is TRUE (i₀ is a witness). -/
theorem mc_delineation_diverge_without_nr :
    eval interpNR_bad (.mc Ta Tb) ord₃ .i2 .w0 = false ∧
    (decide (∃ i' : I3, ord₃.le i' .i2 ∧
      (interpNR_bad i').ext .tall .w0 .ann = true ∧
      (interpNR_bad i').ext .tall .w0 .ben = false) : Bool) = true :=
  ⟨by decide, by decide⟩

/-! ### Metalinguistic Conditional (§6.3) -/

/-- La → Pa fails at i₂ on Model 1: the La-restricted ordering ≤_{La}
includes i₁ (where La is true but Pa is false), so there exists
a ranked La-interpretation that does not satisfy Pa.

This shows → is NOT the material conditional — La and Pa are
both true at i₂, but the conditional is false because it quantifies
over all ranked La-interpretations, not just the current one. -/
theorem mcond_la_pa_false :
    evalMCond interp₃ La Pa ord₃ .i2 .w0 = false := by decide

/-- Observation M1 (§6.3): ⊨ A → (A ≻ ¬A).

"If Pluto is a planet, then it's more a planet than not" is classically
valid. On ≤_A (restricted to A-interpretations), A ≻ ¬A trivially holds:
every A-interpretation makes A true, so the (A∧¬(¬A))-witness exists,
and there are no (¬A∧¬A)-witnesses in the restricted ordering.

This parallels the validity of epistemic "if p then probably p"
([yalcin-2007]). -/
theorem mcond_m1 :
    ∀ (i : I3),
      evalMCond interp₃ La (.mc La NLa) ord₃ i .w0 = true := by decide

/-! ### ME Transitivity: Basic vs Revised Semantics ([kocurek-2024-supplement] §B) -/

/-! ### ME transitivity counterexample

The basic semantics fails to validate ME transitivity:
`A ≈ B, B ≈ C ⊭ A ≈ C` ([kocurek-2024-supplement] §B). Model 4 provides a minimal
counterexample.

Key insight: the (La∧¬Ca)-witness l has no matching (Ca∧¬La)-witness,
so `La ≻ Ca` holds vacuously under the basic semantics. The revised
semantics blocks this: l must dominate either all Ca-interpretations
(i and j are above it) or all ¬La-interpretations (k is above it),
and it can do neither. -/

/-- Three predicates for the transitivity counterexample. -/
inductive Pred3 | linguist | philosopher | psychologist
  deriving DecidableEq, Repr, Fintype

/-- Four interpretations for the transitivity counterexample. -/
inductive I4 | i | j | k | l
  deriving DecidableEq, Repr, Fintype

/-- Ordering: l < j ≡ k < i (three levels).
j and k are tied at the middle level — this is essential for the
equatives La ≈ Pa and Pa ≈ Ca to hold (witnesses block each other). -/
def ord₄ : SemanticOrdering I4 :=
  SemanticOrdering.ofBool
    (λ x y => match x, y with
      | .l, _ => true
      | .j, .l => false
      | .j, _ => true
      | .k, .l => false
      | .k, _ => true
      | .i, .i => true
      | .i, _ => false)
    (by intro x; cases x <;> rfl)
    (by intro x y z hxy hyz; cases x <;> cases y <;> cases z <;> simp_all)
    (by intro x y; cases x <;> cases y <;> simp)

/-- Interpretation function for transitivity counterexample:
- i: all three true  (linguist, philosopher, psychologist)
- j: linguist and psychologist only (philosopher false)
- k: philosopher only (linguist and psychologist false)
- l: linguist and philosopher only (psychologist false)

The (La∧¬Pa)-witness j and (Pa∧¬La)-witness k are at the same level,
ensuring neither MC direction holds for La vs Pa (and similarly for
Pa vs Ca). But the only (La∧¬Ca)-witness is l at the bottom, with no
(Ca∧¬La)-witness anywhere. -/
def interp₄ : I4 → Interpretation W Pred3 Entity
  | .i => ⟨λ _ _ _ => true⟩
  | .j => ⟨λ P _ _ => match P with
    | .linguist => true | .philosopher => false | .psychologist => true⟩
  | .k => ⟨λ P _ _ => match P with
    | .linguist => false | .philosopher => true | .psychologist => false⟩
  | .l => ⟨λ P _ _ => match P with
    | .linguist => true | .philosopher => true | .psychologist => false⟩

/-- "Ann is a linguist" (3-predicate model) -/
abbrev La₄ : MFormula Pred3 Entity := .atom .linguist .ann

/-- "Ann is a philosopher" (3-predicate model) -/
abbrev Pa₄ : MFormula Pred3 Entity := .atom .philosopher .ann

/-- "Ann is a psychologist" -/
abbrev Ca₄ : MFormula Pred3 Entity := .atom .psychologist .ann

/-! #### Basic semantics: transitivity fails -/

/-- A ≈ B holds: Ann is as much a linguist as a philosopher.
The (La∧¬Pa)-witness j and (Pa∧¬La)-witness k are tied at the middle
level, blocking both MC directions. -/
theorem me_basic_la_pa :
    eval interp₄ (La₄.me Pa₄) ord₄ .i .w0 = true := by decide

/-- B ≈ C holds: Ann is as much a philosopher as a psychologist.
The (Pa∧¬Ca)-witnesses k, l and (Ca∧¬Pa)-witness j are balanced:
k is tied with j, blocking both MC directions. -/
theorem me_basic_pa_ca :
    eval interp₄ (Pa₄.me Ca₄) ord₄ .i .w0 = true := by decide

/-- A ≈ C FAILS: basic semantics predicts Ann is MORE a linguist
than a psychologist. ME transitivity is violated. -/
theorem me_basic_la_ca_fails :
    eval interp₄ (La₄.me Ca₄) ord₄ .i .w0 = false := by decide

/-- The failure mechanism: La ≻ Ca holds in the basic semantics.
The (La∧¬Ca)-witness l dominates all (Ca∧¬La)-interpretations
vacuously — there are none (Ca is true only at i and j, where La
is also true). -/
theorem mc_basic_la_gt_ca :
    eval interp₄ (.mc La₄ Ca₄) ord₄ .i .w0 = true := by decide

/-! #### Revised semantics: transitivity restored -/

/-- Under the revised semantics, La ≻ Ca is blocked: the (La∧¬Ca)-
witness l cannot dominate all Ca-interpretations (i and j are above
it) or all ¬La-interpretations (k is above it). -/
theorem mc_revised_la_ca_blocked :
    evalRevised interp₄ (.mc La₄ Ca₄) ord₄ .i .w0 = false := by decide

/-- ME transitivity is restored: A ≈ C holds under the revised
semantics, as required by transitivity from A ≈ B and B ≈ C. -/
theorem me_revised_la_ca :
    evalRevised interp₄ (La₄.me Ca₄) ord₄ .i .w0 = true := by decide

/-- The revised semantics preserves A ≈ B (no regression). -/
theorem me_revised_la_pa :
    evalRevised interp₄ (La₄.me Pa₄) ord₄ .i .w0 = true := by decide

/-- The revised semantics preserves B ≈ C (no regression). -/
theorem me_revised_pa_ca :
    evalRevised interp₄ (Pa₄.me Ca₄) ord₄ .i .w0 = true := by decide

/-! #### Agreement on Model 1 -/

/-- On Model 1 (linear ordering), the revised MC agrees with the basic
MC. The two diverge only when the revised semantics' stronger domination
clause matters — on a linear ordering with no ties at critical levels,
the basic witnesses satisfy the revised conditions too. -/
theorem revised_agrees_model1 :
    ∀ (x : I3),
      eval interp₃ La_mc_Pa ord₃ x .w0 =
      evalRevised interp₃ La_mc_Pa ord₃ x .w0 := by decide

end RudolphKocurek2024
