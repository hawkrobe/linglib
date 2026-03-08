import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2

/-!
# Compositional CDRT Fragment
@cite{muskens-1996}

§III.4 and §IV: Lexical translations (T₀) and generalized coordination
for a fragment of English in Compositional DRT.

## Semantic Types (Table 2, p. 164)

| Muskens Type | Lean Type | Description |
|--------------|-----------|-------------|
| `et` | `E → Prop` | Static predicate |
| `e(et)` | `E → E → Prop` | Static relation |
| `s(st)` | `DRS S` | Dynamic proposition |
| `[π]` | `Dref S E → DRS S` | Dynamic predicate |
| `[[π]]` | `DynPred S E → DRS S` | Dynamic quantifier |

## Composition

Meanings compose via function application (T₂) and sequencing (T₃).
These are native Lean operations, so the composition rules T₁–T₅
need no special formalization — they are just function application,
`dseq`, and λ-abstraction.

## Generalized Coordination (§IV)

`and` = sequencing applied pointwise; `or` = DRS disjunction applied
pointwise. The same schema works at every syntactic category (S, VP, NP).
-/

namespace Semantics.Dynamic.CDRT.Fragment

open Semantics.Dynamic.Core.DynamicTy2

variable {S E : Type*}

-- ════════════════════════════════════════════════════════════════
-- § 1. Semantic Types
-- ════════════════════════════════════════════════════════════════

/-- Dynamic one-place predicate: type `[π]` in @cite{muskens-1996}. -/
abbrev DynPred (S E : Type*) := Dref S E → DRS S

/-- Dynamic generalized quantifier: type `[[π]]` in @cite{muskens-1996}. -/
abbrev DynQuant (S E : Type*) := DynPred S E → DRS S

-- ════════════════════════════════════════════════════════════════
-- § 2. T₀ Basic Translations (p. 165)
-- ════════════════════════════════════════════════════════════════

/-- Common noun: `farmer ↝ λv[|farmer v]`.
    Type: `[π]` (dynamic one-place predicate). -/
def cn (P : E → Prop) : DynPred S E :=
  λ u => test (atom1 P u)

/-- Intransitive verb: `stink ↝ λv[|stinks v]`.
    Type: `[π]` (same as common noun). -/
def iv (P : E → Prop) : DynPred S E :=
  λ u => test (atom1 P u)

/-- Transitive verb: `love ↝ λQλv(Q(λv'[|v loves v']))`.
    Type: `[[π]] → [π]`. Takes an NP (object) and produces a VP. -/
def tv (R : E → E → Prop) : DynQuant S E → DynPred S E :=
  λ Q u => Q (λ v => test (atom2 R u v))

/-- Indefinite determiner: `aⁿ ↝ λP'λP([uₙ]; P'(uₙ); P(uₙ))`.
    Type: `[π] → [[π]]`. Takes a noun, produces a quantifier.
    Introduces discourse referent `u`. -/
def detA [AssignmentStructure S E] (u : Dref S E) : DynPred S E → DynQuant S E :=
  λ noun vp => dseq (AssignmentStructure.randomAssign u) (dseq (noun u) (vp u))

/-- Universal determiner: `everyⁿ ↝ λP'λP(([uₙ]; P'(uₙ)) ⇒ P(uₙ))`.
    Type: `[π] → [[π]]`. Dynamic implication gives universal force. -/
def detEvery [AssignmentStructure S E] (u : Dref S E) : DynPred S E → DynQuant S E :=
  λ noun vp =>
    test (dimpl (dseq (AssignmentStructure.randomAssign u) (noun u)) (vp u))

/-- Negative determiner: `noⁿ ↝ λP'λP[|not([uₙ]; P'(uₙ); P(uₙ))]`.
    Type: `[π] → [[π]]`. -/
def detNo [AssignmentStructure S E] (u : Dref S E) : DynPred S E → DynQuant S E :=
  λ noun vp =>
    test (dneg (dseq (AssignmentStructure.randomAssign u) (dseq (noun u) (vp u))))

/-- Proper name NP: `Maryⁿ ↝ λP.P(Mary)`.
    Type: `[[π]]`. Applies the VP directly to the name's dref. -/
def properNP (name : Dref S E) : DynQuant S E :=
  λ P => P name

/-- Pronoun NP: `heₙ ↝ λP.P(uₙ)`.
    Type: `[[π]]`. Picks up the dref from the antecedent. -/
def pro (u : Dref S E) : DynQuant S E :=
  λ P => P u

/-- Conditional: `if ↝ λpq[|p ⇒ q]`.
    Type: `DRS → DRS → DRS`. -/
def cond : DRS S → DRS S → DRS S :=
  λ p q => test (dimpl p q)

/-- Auxiliary negation: `doesn't ↝ λPλQ[|not Q(P)]` (T₀, p. 165).
    Type: `[π] → [[π]] → DRS`. Takes VP (P) then subject NP (Q),
    matching @cite{muskens-1996}'s argument order. -/
def auxNeg : DynPred S E → DynQuant S E → DRS S :=
  λ P Q => test (dneg (Q P))

-- ════════════════════════════════════════════════════════════════
-- § 3. Generalized Coordination (§IV, p. 176–178)
-- ════════════════════════════════════════════════════════════════

/-! `and` = generalized sequencing; `or` = generalized DRS disjunction.
The same schema works at every syntactic category by applying the
Boolean operation pointwise to the innermost DRS layer. -/

/-- Sentence-level `and`: `K₁ and K₂ = K₁; K₂`. -/
def andS : DRS S → DRS S → DRS S := dseq

/-- Sentence-level `or`: `K₁ or K₂ = [K₁ or K₂]` (disjunction test). -/
def orS : DRS S → DRS S → DRS S :=
  λ D₁ D₂ => test (ddisj D₁ D₂)

/-- VP-level `and`: `λv(P₁(v); P₂(v))`. -/
def andVP : DynPred S E → DynPred S E → DynPred S E :=
  λ P₁ P₂ u => dseq (P₁ u) (P₂ u)

/-- VP-level `or`: `λv[P₁(v) or P₂(v)]`. -/
def orVP : DynPred S E → DynPred S E → DynPred S E :=
  λ P₁ P₂ u => test (ddisj (P₁ u) (P₂ u))

/-- NP-level `and`: `λP(Q₁(P); Q₂(P))`. -/
def andNP : DynQuant S E → DynQuant S E → DynQuant S E :=
  λ Q₁ Q₂ P => dseq (Q₁ P) (Q₂ P)

/-- NP-level `or`: `λP[Q₁(P) or Q₂(P)]`. -/
def orNP : DynQuant S E → DynQuant S E → DynQuant S E :=
  λ Q₁ Q₂ P => test (ddisj (Q₁ P) (Q₂ P))

-- ════════════════════════════════════════════════════════════════
-- § 4. Example Derivations
-- ════════════════════════════════════════════════════════════════

section Examples

variable [AssignmentStructure S E]
variable (u₁ u₂ : Dref S E)
variable (man woman : E → Prop) (adores abhors : E → E → Prop)

/--
Example derivation: "A¹ man adores a² woman. She₂ abhors him₁."

Translation (p. 167, derivation tree (39)):
  `[u₁]; [man u₁]; [u₂]; [woman u₂]; [u₁ adores u₂]; [u₂ abhors u₁]`

Truth conditions (formula (24)):
  `∃x₁ x₂ (man(x₁) ∧ woman(x₂) ∧ adores(x₁,x₂) ∧ abhors(x₂,x₁))`
-/
def exampleText : DRS S :=
  -- "A man adores a woman"
  let sentence1 := detA u₁ (cn man) (tv adores (detA u₂ (cn woman)))
  -- "She abhors him" (pronouns pick up u₂, u₁)
  let sentence2 := pro u₂ (tv abhors (pro u₁))
  -- Text = sentence₁ ; sentence₂
  dseq sentence1 sentence2

/--
Example: "Every¹ farmer who owns a² donkey beats it₂."

The donkey sentence, with universal force from `detEvery`
and anaphoric `it₂` picking up the dref from the indefinite.
Translation: `([u₁]; [farmer u₁]; [u₂]; [donkey u₂]; [u₁ owns u₂]) ⇒ [u₁ beats u₂]`
-/
def donkeySentence
    (farmer donkey_ : E → Prop) (owns beats : E → E → Prop) : DRS S :=
  detEvery u₁
    -- Restrictor: "farmer who owns a donkey"
    (λ v => dseq (cn farmer v) (detA u₂ (cn donkey_) (λ w => test (atom2 owns v w))))
    -- Nuclear scope: "beats it"
    (tv beats (pro u₂))

/--
Example: "A² cat catches a¹ fish and eats it₁." (§IV, p. 179, tree (56))

VP coordination with cross-conjunct anaphora: `it₁` in "eats it₁"
picks up the dref introduced by "a¹ fish" in "catches a¹ fish".

This works because `andVP` sequences the VP meanings, so the dref
introduced by the first conjunct is accessible in the second.
-/
def vpCoordExample
    (cat fish : E → Prop) (catches eats : E → E → Prop) : DRS S :=
  detA u₂ (cn cat)
    (andVP
      (tv catches (detA u₁ (cn fish)))  -- "catches a¹ fish"
      (tv eats (pro u₁)))               -- "eats it₁"

end Examples

-- ════════════════════════════════════════════════════════════════
-- § 5. Coordination preserves anaphoric accessibility
-- ════════════════════════════════════════════════════════════════

/-- VP `and` is definitionally sequencing at the dref argument. -/
theorem andVP_eq_dseq (P₁ P₂ : DynPred S E) (u : Dref S E) :
    andVP P₁ P₂ u = dseq (P₁ u) (P₂ u) := rfl

/-- VP `or` is definitionally disjunction at the dref argument. -/
theorem orVP_eq_test_ddisj (P₁ P₂ : DynPred S E) (u : Dref S E) :
    orVP P₁ P₂ u = test (ddisj (P₁ u) (P₂ u)) := rfl

/-- Sentence `and` is sequencing. -/
theorem andS_eq_dseq : @andS S = dseq := rfl

end Semantics.Dynamic.CDRT.Fragment
