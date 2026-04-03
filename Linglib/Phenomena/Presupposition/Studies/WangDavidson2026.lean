import Linglib.Theories.Semantics.Exhaustification.Trivalent
import Linglib.Theories.Semantics.Exhaustification.InnocentExclusion
import Linglib.Core.Logic.Truth3
import Linglib.Core.Semantics.Presupposition

/-!
# Wang & Davidson (2026): Presupposition Filtering in Disjunction
@cite{wang-davidson-2026}

Yiqian Wang and Kathryn Davidson, "Presupposition filtering in
disjunction: The role of exclusive interpretation."
*Proceedings of Sinn und Bedeutung* 30.

## Summary

The paper asks whether exclusive interpretation of disjunction (via
scalar implicature / exhaustification) affects presupposition
projection. The answer, both theoretically and empirically, is:

**Most theories predict yes, but the experiment finds no.**

## Theoretical Contribution (§3)

The paper surveys combinations of:
- Exhaustification theories: bivalent EXH, trivalent EXH¹, EXH²
- Projection theories: Strong Kleene, George 2008, classic dynamic
  semantics

These divide into two classes:

- **Type A**: increasing exclusivity *reduces* filtering
  (bivalent EXH + SK/George/dynamic; EXH² + any projection)
- **Type B**: exclusivity has *no effect* on filtering
  (EXH¹ + any projection)

The core mechanism: under Strong Kleene, inclusive disjunction
(`Truth3.join`) can return `.true` even when one disjunct is
undefined — so a true first disjunct "filters" the second's
presupposition failure. Exclusive disjunction (`Truth3.xor`)
cannot: it returns `.indet` whenever either input is `.indet`.

### Feed-forward assumption (§5)

The Type A prediction for bivalent EXH depends on a **feed-forward**
assumption: the strengthened (exclusive) truth conditions must be
computed early enough to be visible to the projection computation.
Without this, bivalent EXH + SK would not predict Type A because
the projection computation would see only the original inclusive
truth conditions. This assumption is architecturally non-trivial —
see @cite{wang-davidson-2026} §5.

## Empirical Contribution (§4)

Mandarin experiment using *huozhe* ('or'), manipulating exclusivity
via environmental monotonicity (UE → more exclusive, DE → less).
Two presupposition triggers: *jie* 'quit' and *zhidao* 'know'.

**Key result**: PREDICATE × MONOTONICITY interaction is not significant
(p = .30, BF₁₀ = 0.52). No evidence that exclusivity modulates
filtering. This challenges Type A theories and is consistent with
Type B (EXH¹).

**Secondary finding**: filtering (a)symmetry depends on trigger.
*jie* shows asymmetric filtering (PREDICATE × ORDER: p = .01);
*zhidao* shows symmetric filtering (uniform, p = .99 for PREDICATE).
-/

namespace Phenomena.Presupposition.Studies.WangDavidson2026

open Core.Duality (Truth3 Prop3)
open Core.Presupposition (PrProp)
open Exhaustification.InnocentExclusion
open Exhaustification.Trivalent


-- ════════════════════════════════════════════════════════════════
-- § 1. The Strong Kleene prediction (§3.1.1)
-- ════════════════════════════════════════════════════════════════

/-!
### Inclusive vs exclusive disjunction under Strong Kleene

The fundamental asymmetry: inclusive disjunction can "see past" an
undefined disjunct when the other is true. Exclusive cannot.

This single fact drives the Type A prediction for bivalent EXH + SK:
since `InnocentExclusion.disj_exh_eq_exor` shows Exh strengthens ∨ to ⊻,
and `Truth3.xor_indet_iff` shows ⊻ propagates undefinedness
unconditionally, exhaustification eliminates filtering.
-/

/-- Inclusive disjunction allows filtering: a true first disjunct
    absorbs the second's presupposition failure. -/
theorem sk_inclusive_filters : Truth3.join .true .indet = .true := rfl

/-- Exclusive disjunction does not filter: even when one disjunct
    is true, an undefined partner makes the result undefined. -/
theorem sk_exclusive_no_filter : Truth3.xor .true .indet = .indet := rfl

/-- The filtering contrast is symmetric: both `join` and `xor` are
    commutative, so the direction doesn't matter for SK.

    This is what @cite{kalomoiros-schwarz-2024} call "symmetric
    projection" — filtering is equally (un)available in both
    directions. -/
theorem sk_filtering_symmetric :
    Truth3.join .indet .true = .true ∧ Truth3.xor .indet .true = .indet :=
  ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § 1b. PrProp bridge: filtering vs non-filtering disjunction
-- ════════════════════════════════════════════════════════════════

/-!
### PrProp exclusive disjunction

`PrProp.xor` requires both presuppositions to hold — it never
filters presupposition failure from either disjunct. This mirrors
the SK XOR truth table (Figure 2 in the paper).

Note: SK *inclusive* filtering (`Truth3.join .true .indet = .true`)
is an emergent property of the SK truth table, not a `PrProp`
connective. The contrast is between `Truth3.join` (filters) and
`Truth3.xor` (does not filter), verified in §1 above.
-/

section PrPropBridge

variable {W : Type*}

/-- `PrProp.xor` does not filter: when q's presupposition fails,
    the result is always undefined regardless of p. -/
theorem prprop_exclusive_no_filter (p q : PrProp W) (w : W)
    (hq : q.presup w = false) :
    (PrProp.xor p q).eval w = .indet :=
  PrProp.eval_xor_no_filter p q w hq

end PrPropBridge


-- ════════════════════════════════════════════════════════════════
-- § 2. Type A / Type B classification (§3.3)
-- ════════════════════════════════════════════════════════════════

/-- Theory classification from §3.3:
    theories are grouped by their prediction about the effect of
    exclusivity on presupposition filtering across disjunction. -/
inductive TheoryClass where
  /-- Increasing exclusivity *reduces* filtering. -/
  | typeA
  /-- Exclusivity has *no effect* on filtering. -/
  | typeB
  deriving DecidableEq, Repr

/-- Exhaustification strategy: bivalent (@cite{fox-2007}) or trivalent
    (@cite{spector-sudo-2017}). -/
inductive ExhStrategy where
  | bivalent   -- Fox 2007
  | exh1       -- Spector & Sudo 2017, weak negation
  | exh2       -- Spector & Sudo 2017, strong negation
  deriving DecidableEq, Repr

/-- Semantic presupposition projection theory. -/
inductive ProjectionTheory where
  | strongKleene       -- Strong Kleene truth tables
  | george2008         -- George's algorithm
  | dynamicSemantics   -- Classic CCP (Heim 1983)
  deriving DecidableEq, Repr

/-- Classify a combination of exhaustification + projection theory
    into Type A or Type B.

    Type A (exclusivity reduces filtering):
    - bivalent EXH + any of the three projection theories
    - EXH² + any projection theory

    Type B (no effect of exclusivity):
    - EXH¹ + any projection theory -/
def classify (exh : ExhStrategy) (_proj : ProjectionTheory) : TheoryClass :=
  match exh with
  | .bivalent => .typeA
  | .exh2     => .typeA
  | .exh1     => .typeB

/-- EXH¹ is always Type B regardless of projection theory. -/
theorem exh1_always_typeB (proj : ProjectionTheory) :
    classify .exh1 proj = .typeB := by
  cases proj <;> rfl

/-- Bivalent EXH is always Type A regardless of projection theory. -/
theorem bivalent_always_typeA (proj : ProjectionTheory) :
    classify .bivalent proj = .typeA := by
  cases proj <;> rfl

/-- EXH² is always Type A regardless of projection theory. -/
theorem exh2_always_typeA (proj : ProjectionTheory) :
    classify .exh2 proj = .typeA := by
  cases proj <;> rfl


-- ════════════════════════════════════════════════════════════════
-- § 3. Bridge to Fox 2007 (§3.1)
-- ════════════════════════════════════════════════════════════════

/-!
### Bivalent EXH strengthens inclusive to exclusive

The bridge from bivalent EXH to the SK prediction:
1. `InnocentExclusion.disj_exh_eq_exor`: Exh(Alt)(p∨q) = p ⊕ q
2. The exclusive truth conditions, when lifted to Truth3 via SK,
   yield `Truth3.xor` — which propagates `#` unconditionally
3. Therefore: bivalent EXH + SK → no filtering (Type A prediction)

This chain depends on the **feed-forward assumption** (§5):
the strengthened exclusive truth conditions must be visible to the
projection computation. Without it, projection would see only the
original inclusive conditions and filtering would be unaffected.
-/

/-- Fox 2007 already proves that bivalent EXH strengthens
    inclusive to exclusive disjunction (reexported for context). -/
theorem bivalent_exh_yields_xor :
    ∀ w : PQWorld, exhB pqDomain disjAlts pOrQ w =
      (pOrQ w && !pAndQ w) :=
  disj_exh_eq_exor

/-- The classical exclusive disjunction (Bool XOR) agrees with
    Strong Kleene XOR on defined inputs. -/
theorem bool_xor_lifts_to_sk (a b : Bool) :
    Truth3.xor (Truth3.ofBool a) (Truth3.ofBool b) =
    Truth3.ofBool (a ^^ b) :=
  Truth3.xor_ofBool a b


-- ════════════════════════════════════════════════════════════════
-- § 4. EXH¹ vs EXH² on disjunction (§3.2)
-- ════════════════════════════════════════════════════════════════

/-!
### Trivalent exhaustification and presupposition inheritance

The bathroom disjunction verification from `Trivalent.lean` shows:
- EXH¹ preserves filtering at the critical world (`pOnly`)
- EXH² destroys filtering at the critical world (`pOnly`)

This drives the Type A/B split. The mechanism:
- EXH¹ uses **weak negation** (`~# = true`), so the conjunction
  alternative's undefinedness at `pOnly` is harmlessly "negated"
- EXH² uses **strong negation** (`~# = #`), so the conjunction
  alternative's undefinedness propagates upward as a new
  presupposition requirement
-/

/-- Re-export: EXH¹ preserves filtering (Type B). -/
theorem exh1_preserves_filtering :
    exh1 bDomain bathAlts inclDisj .pOnly = .true :=
  exh1_disjunction_pOnly

/-- Re-export: EXH² destroys filtering (Type A). -/
theorem exh2_destroys_filtering :
    exh2 bDomain bathAlts inclDisj .pOnly = .indet :=
  exh2_disjunction_pOnly


-- ════════════════════════════════════════════════════════════════
-- § 5. Experimental data (§4)
-- ════════════════════════════════════════════════════════════════

/-- Monotonicity environment, used as between-subjects factor.
    UE = unembedded disjunction (more exclusive readings);
    DE = disjunction in conditional antecedent (fewer exclusive readings). -/
inductive Monotonicity where
  | UE  -- upward-entailing (unembedded disjunction)
  | DE  -- downward-entailing (conditional antecedent)
  deriving DecidableEq, Repr

/-- Predicate type: whether test sentence contains presupposition trigger. -/
inductive Predicate where
  | ps    -- presuppositional trigger present
  | noPs  -- non-presuppositional counterpart
  deriving DecidableEq, Repr

/-- Order of trigger in disjunction. -/
inductive Order where
  | first   -- trigger in first disjunct
  | second  -- trigger in second disjunct
  deriving DecidableEq, Repr

/-- Presupposition triggers used in the experiment. -/
inductive Trigger where
  | jie     -- 戒 'quit' (change-of-state, strong projector)
  | zhidao  -- 知道 'know' (factive, weaker projector)
  deriving DecidableEq, Repr

/-- Experimental finding summary. -/
structure Finding where
  description : String
  significant : Bool

/-- Norming task validation: the monotonicity manipulation successfully
    modulates exclusivity (Fisher's exact test, p = .011).
    UE: 23.3% exclusive responses; DE: 0% exclusive responses. -/
def normingValidation : Finding where
  description := "Norming task: exclusive responses UE 23.3% vs DE 0%, p = .011"
  significant := true

/-- The critical null result: PREDICATE × MONOTONICITY is not significant.
    p = .30 (frequentist), BF₁₀ = 0.52 (Bayesian).
    No evidence that exclusivity modulates filtering. -/
def mainResult : Finding where
  description := "PREDICATE × MONOTONICITY interaction: p = .30, BF₁₀ = 0.52"
  significant := false

/-- Control validation: the paradigm detects presuppositional
    definedness costs. CONTEXT manipulation is significant (p < .001). -/
def controlValidation : Finding where
  description := "CONTEXT (EI vs S) main effect: p < .001"
  significant := true

/-- *jie* shows asymmetric filtering: PREDICATE × ORDER is significant
    (β = −1.81, SE = 0.72, p = .01). R-to-L filtering is weaker
    than L-to-R. -/
def jieAsymmetry : Finding where
  description := "jie PREDICATE × ORDER: β = −1.81, SE = 0.72, p = .01"
  significant := true

/-- *zhidao* shows symmetric filtering: PREDICATE × ORDER is not
    significant (p = .40), and PREDICATE main effect p = .99
    (uniform filtering). -/
def zhidaoSymmetry : Finding where
  description := "zhidao PREDICATE × ORDER: p = .40; PREDICATE: p = .99"
  significant := false

/-- The norming task confirms the manipulation is effective. -/
theorem norming_validates_manipulation :
    normingValidation.significant = true := rfl

/-- The null result is consistent with Type B theories (EXH¹). -/
theorem null_result_consistent_with_typeB :
    mainResult.significant = false := rfl

/-- The null result challenges all Type A theories:
    three bivalent EXH + projection combinations and EXH² + any. -/
theorem null_result_challenges_typeA :
    mainResult.significant = false ∧
    classify .bivalent .strongKleene = .typeA ∧
    classify .bivalent .george2008 = .typeA ∧
    classify .bivalent .dynamicSemantics = .typeA ∧
    classify .exh2 .strongKleene = .typeA :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- End-to-end argumentation chain: Fox 2007 computes exclusive
    truth conditions → SK propagates undefinedness → Type A predicted →
    experiment finds no effect → challenges bivalent EXH + SK.

    This links `InnocentExclusion.disj_exh_eq_exor`, `Truth3.xor_indet_iff`,
    the Type A classification, and the null experimental result. -/
theorem end_to_end_bivalent_sk_challenged :
    -- (1) Bivalent EXH yields exclusive disjunction
    (∀ w : PQWorld, exhB pqDomain disjAlts pOrQ w = (pOrQ w && !pAndQ w)) ∧
    -- (2) SK XOR propagates undefinedness
    (Truth3.xor .true .indet = .indet) ∧
    -- (3) This combination is classified Type A
    (classify .bivalent .strongKleene = .typeA) ∧
    -- (4) The experiment finds no effect (challenging Type A)
    (mainResult.significant = false) :=
  ⟨disj_exh_eq_exor, rfl, rfl, rfl⟩


end Phenomena.Presupposition.Studies.WangDavidson2026
