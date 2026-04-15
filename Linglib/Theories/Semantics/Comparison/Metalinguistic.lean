import Linglib.Core.Semantics.CommonGround
import Linglib.Core.IntensionalLogic.Rigidity

/-!
# Metalinguistic Gradability
@cite{rudolph-kocurek-2024}

Semantic expressivist framework for metalinguistic comparatives ("Ann is more
a linguist than a philosopher"), metalinguistic equatives, degree modifiers
(`very much`, `sorta`, `mostly`), and metalinguistic conditionals.

## Core Idea

Speakers express not only factual commitments (about the world) but also
**interpretive commitments** (about how to interpret language). The common
ground is generalized from sets of worlds to sets of **ordering-world pairs**
⟨≤, w⟩, where ≤ is a total preorder over interpretations (a **semantic
ordering**). Assertions update this enriched common ground.

## Formal System

Truth is evaluated relative to a triple ⟨≤, i, w⟩:
- `≤` : semantic ordering (total preorder on interpretations)
- `i` : the current interpretation
- `w` : the world of evaluation

An **interpretation** maps names and predicates to world-indexed extensions.
Ordinary sentences ignore ≤; metalinguistic operators quantify over it.

## Operators

- `A ≻ B` (MC): ∃ (A∧¬B)-interp ranked ≤ i, above all (B∧¬A)-interps ≤ i
- `A ≈ B` (ME): ¬(A ≻ B) ∧ ¬(B ≻ A)
- `A ≫ B` (much more): like ≻ but with "far below" (≪) instead of <
- `very A` := A ≫ ¬A — true on all reasonably close interpretations
- `sorta A` := ¬very(¬A) — true on some reasonably close interpretation
- `mostly A` := ∃ reasonably high level where A is uniformly true
- `A → B` (metalinguistic conditional): restricts ordering to A-interps
- `evalRevised`: revised MC for ME transitivity (Supplement §B) —
  strengthened domination clause blocks vacuous comparatives

## Entailment

Two notions:
- **Truth-preservation** (⊨): preserves truth at all ⟨≤, i, w⟩
- **Acceptance-preservation** (⊩): preserves assertoric content |A|
  (A is true at all ≤-maximal interpretations)

⊩ is nonclassical: `A ⊩ A ≻ ¬A` and `¬A ⊩ ¬A ≻ A`, but
`A ∨ ¬A ⊮ (A ≻ ¬A) ∨ (¬A ≻ A)`. This parallels informational
entailment for epistemic modals (@cite{yalcin-2007}).
-/

namespace Semantics.Comparison.Metalinguistic

-- ════════════════════════════════════════════════════════════════
-- § 0. Helpers
-- ════════════════════════════════════════════════════════════════

/-- Boolean universal quantification over a finite type. -/
private def bAll (I : Type) [Fintype I] (p : I → Bool) : Bool :=
  decide (∀ i : I, p i = true)

/-- Boolean existential quantification over a finite type. -/
private def bAny (I : Type) [Fintype I] (p : I → Bool) : Bool :=
  decide (∃ i : I, p i = true)


-- ════════════════════════════════════════════════════════════════
-- § 1. Interpretations and Semantic Orderings
-- ════════════════════════════════════════════════════════════════

/-- An interpretation maps predicate symbols to world-indexed extensions.

For the finite decidable models we work with, an interpretation is simply
a function from predicates and entities to Bool at each world. -/
structure Interpretation (W : Type) (Pred : Type) (Entity : Type) where
  /-- Extension of predicate P at world w: the set of entities P applies to. -/
  ext : Pred → W → Entity → Bool

/-- A semantic ordering is a total preorder on a set of interpretations.

Represents a speaker's relative interpretive commitments: `le i j` means
the speaker is at least as committed to j as to i.

`le` is Prop-valued with `DecidableRel` for decidable computation.
Use `ofBool` for the common case of defining orderings via pattern matching. -/
structure SemanticOrdering (I : Type) where
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

variable {I : Type} (ord : SemanticOrdering I)

/-- Bool-valued le for computation (eval, native_decide). -/
def leB (i j : I) : Bool := decide (ord.le i j)

/-- Strict ordering (Prop): i is ranked strictly below j. -/
def lt (i j : I) : Prop := ord.le i j ∧ ¬ ord.le j i

/-- Decidability of the strict ordering. -/
instance decRelLt : DecidableRel ord.lt :=
  fun i j => show Decidable (ord.le i j ∧ ¬ ord.le j i) from inferInstance

/-- Bool-valued strict ordering for computation. -/
def ltB (i j : I) : Bool := ord.leB i j && !ord.leB j i

/-- Equivalence: i and j are ranked at the same level. -/
def equiv (i j : I) : Prop := ord.le i j ∧ ord.le j i

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
def SemanticOrdering.ofBool {I : Type} (f : I → I → Bool)
    (h_refl : ∀ i, f i i = true)
    (h_trans : ∀ i j k, f i j = true → f j k = true → f i k = true)
    (h_total : ∀ i j, f i j = true ∨ f j i = true) :
    SemanticOrdering I where
  le i j := f i j = true
  le_refl := h_refl
  le_trans := h_trans
  le_total := h_total
  decRel _ _ := inferInstance


-- ════════════════════════════════════════════════════════════════
-- § 2. Evaluation Index and Formulas
-- ════════════════════════════════════════════════════════════════

/-- A metalinguistic formula over predicates and entities.

The language includes atomic predication, boolean connectives,
and the metalinguistic comparative ≻ (`.mc`). -/
inductive MFormula (Pred Entity : Type) where
  | atom : Pred → Entity → MFormula Pred Entity
  | neg : MFormula Pred Entity → MFormula Pred Entity
  | conj : MFormula Pred Entity → MFormula Pred Entity → MFormula Pred Entity
  | disj : MFormula Pred Entity → MFormula Pred Entity → MFormula Pred Entity
  | mc : MFormula Pred Entity → MFormula Pred Entity → MFormula Pred Entity
  deriving DecidableEq

namespace MFormula

variable {Pred Entity : Type}

/-- Material conditional (within the object language). -/
def impl (A B : MFormula Pred Entity) : MFormula Pred Entity :=
  .disj (.neg A) B

/-- Metalinguistic equative: A ≈ B := ¬(A ≻ B) ∧ ¬(B ≻ A). -/
def me (A B : MFormula Pred Entity) : MFormula Pred Entity :=
  .conj (.neg (.mc A B)) (.neg (.mc B A))

/-- Weak metalinguistic comparative: A ≥ B := (A ≻ B) ∨ (A ≈ B). -/
def wmc (A B : MFormula Pred Entity) : MFormula Pred Entity :=
  .disj (.mc A B) (me A B)

end MFormula


-- ════════════════════════════════════════════════════════════════
-- § 3. Semantics (§4.2 of the paper)
-- ════════════════════════════════════════════════════════════════

/-- Evaluate a formula at an index ⟨≤, i, w⟩.

- Atomic: true iff the entity is in the predicate's extension at w under i.
- MC (A ≻ B): true iff ∃ i' ≤ i with (A∧¬B) true at i', and
  ∀ i'' ≤ i, (B∧¬A) true at i'' implies i'' < i'. -/
def eval {I W Pred Entity : Type} [Fintype I]
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


-- ════════════════════════════════════════════════════════════════
-- § 4. Assertoric Content and Entailment
-- ════════════════════════════════════════════════════════════════

/-- Is interpretation i maximal in the ordering? -/
def isMaximal {I : Type} [Fintype I] (ord : SemanticOrdering I) (i : I) : Bool :=
  bAll I λ i' => !ord.ltB i i'

/-- Assertoric content: A is true at all ≤-maximal interpretations.

|A|^{≤,w} = 1 iff ∀ i, i is maximal → ⟦A⟧^{≤,i,w} = 1.
A speaker accepts A iff on every ordering-world pair they leave open,
A is true at every top-ranked interpretation. -/
def assertoricContent {I W Pred Entity : Type} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity) (ord : SemanticOrdering I) (w : W) : Bool :=
  bAll I λ i => !(isMaximal ord i) || eval interpFn φ ord i w

/-- Truth-preservation (⊨): for all ⟨≤, i, w⟩, if premises are true then
conclusion is true. Classical; validates Observations 1, 2, 4, 5. -/
def truthPreserves {I W Pred Entity : Type} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (premises : List (MFormula Pred Entity))
    (conclusion : MFormula Pred Entity) : Prop :=
  ∀ (ord : SemanticOrdering I) (i : I) (w : W),
    (premises.all (λ φ => eval interpFn φ ord i w)) = true →
    eval interpFn conclusion ord i w = true

/-- Acceptance-preservation (⊩): for all ⟨≤, w⟩, if assertoric content of
all premises holds, then assertoric content of conclusion holds.
Nonclassical; validates Observation 3 (A ∧ ¬B ⊩ A ≻ B). -/
def acceptancePreserves {I W Pred Entity : Type} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (premises : List (MFormula Pred Entity))
    (conclusion : MFormula Pred Entity) : Prop :=
  ∀ (ord : SemanticOrdering I) (w : W),
    (premises.all (λ φ => assertoricContent interpFn φ ord w)) = true →
    assertoricContent interpFn conclusion ord w = true


-- ════════════════════════════════════════════════════════════════
-- § 5. Distance Functions and Degree Modifiers (§6.1)
-- ════════════════════════════════════════════════════════════════

/-- A distance function for a semantic ordering.

Maps each interpretation to the set of interpretations "reasonably close"
to it. Used to define `very much`, `sorta`, `mostly`. -/
structure DistanceFunction (I : Type) (ord : SemanticOrdering I) where
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
def farBelow {I : Type} (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i j : I) : Bool :=
  ord.leB i j && !d.close j i

/-- Much more (A ≫ B): like A ≻ B but with ≪ instead of <.

⟦A ≫ B⟧ = 1 iff ∃ i' ≤ i with (A∧¬B) true at i', and
∀ i'' ≤ i with (B∧¬A) true at i'', i'' ≪ i'. -/
def evalMuchMore {I W Pred Entity : Type} [Fintype I]
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
def evalVery {I W Pred Entity : Type} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i : I) (w : W) : Bool :=
  evalMuchMore interpFn φ (.neg φ) ord d i w

/-- sorta A := ¬ very ¬A.
True iff some reasonably close interpretation makes A true.

Reduces to: ∃ i' ∈ d(i), ⟦A⟧^{i',w} = 1. -/
def evalSorta {I W Pred Entity : Type} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i : I) (w : W) : Bool :=
  !evalVery interpFn (.neg φ) ord d i w

/-- mostly A (eq. 97 of @cite{rudolph-kocurek-2024}).
True iff there is a reasonably high level (strictly below the top,
within the distance threshold) where A is uniformly true, and all
A-false levels below the current interpretation are ranked below it.

`mostly A` is compatible with A and with ¬A (unlike `very`). It entails
`sorta A`. And `mostly A ∧ mostly ¬A` is contradictory. -/
def evalMostly {I W Pred Entity : Type} [Fintype I]
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

/-- No Reversal constraint (van Benthem 1990; §7 of @cite{rudolph-kocurek-2024}).

If entity e₁ is in the extension of P and e₂ is not at interpretation i,
then for all i' ≤ i where e₂ enters the extension, e₁ must also be in
the extension.

When NR holds for gradable adjectives, the MC `Fa ≻ Gb` simplifies to
the **delineation comparative**: ∃ i' ≤ i with Fa∧¬Gb — the second clause
of the MC semantics (about dominating all (B∧¬A)-witnesses) becomes
redundant. This connects metalinguistic comparatives to
@cite{klein-1980} and @cite{kamp-1975}. See
`Theories/Semantics/Comparison/Delineation.lean` for the delineation
framework. -/
def noReversal {I W Pred Entity : Type}
    (interpFn : I → Interpretation W Pred Entity)
    (ord : SemanticOrdering I)
    (P : Pred) (w : W) (e1 e2 : Entity) : Prop :=
  ∀ (i i' : I),
    ord.le i' i →
    (interpFn i).ext P w e1 = true →
    (interpFn i).ext P w e2 = false →
    (interpFn i').ext P w e2 = true →
    (interpFn i').ext P w e1 = true


-- ════════════════════════════════════════════════════════════════
-- § 5a. Revised Semantics (Supplement §B)
-- ════════════════════════════════════════════════════════════════

/-- Evaluate a formula under the revised MC semantics (Supplement §B of
@cite{rudolph-kocurek-2024}).

The basic semantics (`eval`) fails ME transitivity: `A ≈ B, B ≈ C ⊭ A ≈ C`.
The revised semantics strengthens the MC: the (A∧¬B)-witness must dominate
either **all B-interpretations** or **all ¬A-interpretations**, not merely
all (B∧¬A)-interpretations. This prevents cases where the basic MC holds
vacuously due to the absence of (B∧¬A)-witnesses while (A∧B) or (¬A∧¬B)
interpretations remain undominated.

Formally (simplified form): `A ≻ B` iff ∃ i' ≤ i with A∧¬B at i', and
either (a) ∀ i'' ≤ i: ⟦B⟧^{i''} → i'' < i', or
(b) ∀ i'' ≤ i: ⟦¬A⟧^{i''} → i'' < i'.

Properties (Supplement §B):
- All basic entailment patterns (Fact 3 a-n) are preserved (Fact 5)
- ME transitivity is validated: `A ≈ B, B ≈ C ⊨ A ≈ C` (Fact 6)
- Interdefinable with basic semantics (Fact 7):
  `A >_basic B = (A∧¬B) >_revised (B∧¬A)` -/
def evalRevised {I W Pred Entity : Type} [Fintype I]
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


-- ════════════════════════════════════════════════════════════════
-- § 5b. Metalinguistic Conditional (§6.3)
-- ════════════════════════════════════════════════════════════════

/-- Evaluate a formula with a raw ordering relation.

Like `eval`, but takes `le : I → I → Bool` directly rather than
a `SemanticOrdering`. Needed for metalinguistic conditionals, where
the consequent is evaluated relative to a restricted ordering ≤_A
that may not satisfy totality (since non-A interpretations are
dropped). Agrees with `eval` when given `ord.le`. -/
def evalGen {I W Pred Entity : Type} [Fintype I]
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
def restrictLE {I W Pred Entity : Type} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (A : MFormula Pred Entity)
    (le : I → I → Bool) (w : W) : I → I → Bool :=
  λ i j => le i j && evalGen interpFn A le i w && evalGen interpFn A le j w

/-- Metalinguistic conditional (eq. 120 of @cite{rudolph-kocurek-2024}).

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
def evalMCond {I W Pred Entity : Type} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (A B : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) : Bool :=
  let le := ord.leB
  let leA := restrictLE interpFn A le w
  bAll I λ i' =>
    !(le i' i && evalGen interpFn A le i' w) ||
    evalGen interpFn B leA i' w


-- ════════════════════════════════════════════════════════════════
-- § 6. Connection to Common Ground
-- ════════════════════════════════════════════════════════════════

open Core.CommonGround (ContextSet HasContextSet)

/-- An ordering-world pair: the enriched index for metalinguistic CG.

The common ground is a set of ordering-world pairs ⟨≤, w⟩ compatible
with speakers' factual AND interpretive commitments. -/
structure OrderingWorldPair (I W : Type) where
  ord : SemanticOrdering I
  world : W

/-- The metalinguistic common ground: a set of ordering-world pairs.

Generalizes Stalnaker's context set (= set of worlds) to include
interpretive commitments. Projects to a classical context set via
existential quantification over orderings. -/
abbrev MetalinguisticCG (I W : Type) := OrderingWorldPair I W → Prop

namespace MetalinguisticCG

variable {I W : Type}

/-- Project to a classical context set by existentially quantifying
over semantic orderings. A world w is in the context set iff some
ordering paired with w is in the metalinguistic CG. -/
def toContextSet (cg : MetalinguisticCG I W) : ContextSet W :=
  λ w => ∃ ord, cg ⟨ord, w⟩

/-- Update with assertoric content: keep pairs where |A| holds. -/
def updateAssertoric {Pred Entity : Type} [Fintype I]
    (interpFn : I → Interpretation W Pred Entity)
    (cg : MetalinguisticCG I W) (φ : MFormula Pred Entity) :
    MetalinguisticCG I W :=
  λ pair => cg pair ∧ assertoricContent interpFn φ pair.ord pair.world = true

end MetalinguisticCG

/-- MetalinguisticCG projects to a ContextSet via HasContextSet. -/
instance {I W : Type} : HasContextSet (MetalinguisticCG I W) W where
  toContextSet := MetalinguisticCG.toContextSet


-- ════════════════════════════════════════════════════════════════
-- § 7. Revised MC Characterization (for MetalinguisticDegree.lean)
-- ════════════════════════════════════════════════════════════════

-- Bridge between leB/ltB and Prop-valued le/lt
private theorem leB_iff {I : Type} (ord : SemanticOrdering I) (i j : I) :
    ord.leB i j = true ↔ ord.le i j := by
  simp [SemanticOrdering.leB, decide_eq_true_eq]

private theorem ltB_iff {I : Type} (ord : SemanticOrdering I) (i j : I) :
    ord.ltB i j = true ↔ ord.lt i j := by
  simp [SemanticOrdering.ltB, SemanticOrdering.leB, SemanticOrdering.lt,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]

-- Converts Bool disjunction to implication form
private theorem bGuard (a b c : Bool) :
    (!(a && b)) = true ∨ c = true ↔ (a = true → b = true → c = true) := by
  cases a <;> cases b <;> cases c <;> simp

private theorem bGuardNeg (a d c : Bool) :
    (!(a && !d)) = true ∨ c = true ↔ (a = true → d = false → c = true) := by
  cases a <;> cases d <;> cases c <;> simp

/-- Prop-level characterization of revised MC (`evalRevised` on `.mc A B`).
Converts Boolean `bAny`/`bAll` wrappers to standard Prop quantifiers. -/
theorem evalRevised_mc_iff {I W Pred Entity : Type} [Fintype I]
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


end Semantics.Comparison.Metalinguistic
