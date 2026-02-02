/-
# English Scale Library

English Horn scales for RSA and NeoGricean models.

## Scales Included

**Quantifier Scales (Horn)**:
- ⟨some, all⟩
- ⟨some, most, all⟩
- ⟨or, and⟩

**Modal Scales (Fauconnier)**:
- ⟨might, must⟩ / ⟨possible, necessary⟩
- ⟨allowed, required⟩

**Degree Scales (Kennedy)**:
- ⟨warm, hot⟩
- ⟨good, excellent⟩

**Numeral Scales**:
- ⟨one, two, three, ...⟩

## References

- Horn, L. R. (1972). On the semantic properties of logical operators in English.
- Fauconnier, G. (1975). Pragmatic scales and logical structure.
- Kennedy, C. (2007). Vagueness and grammar.
-/

import Mathlib.Data.Rat.Defs

namespace Fragments.English.Scales

-- ============================================================================
-- Scale Structure
-- ============================================================================

/--
A Horn scale: ordered list of scalar alternatives from weak to strong.

The key property: each item entails all weaker items.
⟨some, all⟩: "all" entails "some"
-/
structure Scale (α : Type) where
  /-- Items from weakest to strongest -/
  items : List α
  /-- Name for display -/
  name : String := ""

/-- Get alternatives (items strictly stronger than x) -/
def Scale.alternatives {α : Type} [BEq α] (s : Scale α) (x : α) : List α :=
  match s.items.dropWhile (· != x) with
  | [] => []
  | _ :: rest => rest

/-- Get the strongest item -/
def Scale.strongest {α : Type} (s : Scale α) : Option α :=
  s.items.getLast?

/-- Get the weakest item -/
def Scale.weakest {α : Type} (s : Scale α) : Option α :=
  s.items.head?

/-- Is x weaker than y on this scale? -/
def Scale.weaker {α : Type} [BEq α] (s : Scale α) (x y : α) : Bool :=
  let findIdx (item : α) := s.items.findIdx? (· == item)
  match findIdx x, findIdx y with
  | some i, some j => i < j
  | _, _ => false

-- ============================================================================
-- Quantifier Scales
-- ============================================================================

/-- Basic quantifier expressions -/
inductive QuantExpr where
  | some_ | most | all
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The ⟨some, all⟩ scale -/
def someAll : Scale QuantExpr :=
  { items := [.some_, .all]
  , name := "⟨some, all⟩"
  }

/-- The ⟨some, most, all⟩ scale -/
def someMostAll : Scale QuantExpr :=
  { items := [.some_, .most, .all]
  , name := "⟨some, most, all⟩"
  }

-- ============================================================================
-- Connective Scales
-- ============================================================================

/-- Connective expressions -/
inductive ConnExpr where
  | or_ | and_
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The ⟨or, and⟩ scale -/
def orAnd : Scale ConnExpr :=
  { items := [.or_, .and_]
  , name := "⟨or, and⟩"
  }

-- ============================================================================
-- Modal Scales
-- ============================================================================

/-- Modal expressions -/
inductive ModalExpr where
  | might | must
  | possible | necessary
  | allowed | required
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The ⟨might, must⟩ scale -/
def mightMust : Scale ModalExpr :=
  { items := [.might, .must]
  , name := "⟨might, must⟩"
  }

/-- The ⟨possible, necessary⟩ scale -/
def possibleNecessary : Scale ModalExpr :=
  { items := [.possible, .necessary]
  , name := "⟨possible, necessary⟩"
  }

/-- The ⟨allowed, required⟩ scale -/
def allowedRequired : Scale ModalExpr :=
  { items := [.allowed, .required]
  , name := "⟨allowed, required⟩"
  }

-- ============================================================================
-- Degree Scales
-- ============================================================================

/-- Degree/gradable adjective expressions -/
inductive DegreeExpr where
  | warm | hot
  | good | excellent
  | like | love
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The ⟨warm, hot⟩ scale -/
def warmHot : Scale DegreeExpr :=
  { items := [.warm, .hot]
  , name := "⟨warm, hot⟩"
  }

/-- The ⟨good, excellent⟩ scale -/
def goodExcellent : Scale DegreeExpr :=
  { items := [.good, .excellent]
  , name := "⟨good, excellent⟩"
  }

/-- The ⟨like, love⟩ scale -/
def likeLove : Scale DegreeExpr :=
  { items := [.like, .love]
  , name := "⟨like, love⟩"
  }

-- ============================================================================
-- Evaluative Scales (for politeness, reviews, etc.)
-- ============================================================================

/--
Evaluative adjective expressions for quality judgments.

This scale is used in:
- Yoon et al. (2020) politeness model
- Review/feedback contexts

The scale goes from strongly negative to strongly positive:
⟨terrible, bad, good, amazing⟩
-/
inductive EvalExpr where
  | terrible | bad | good | amazing
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The ⟨terrible, bad, good, amazing⟩ evaluative scale -/
def terribleAmazing : Scale EvalExpr :=
  { items := [.terrible, .bad, .good, .amazing]
  , name := "⟨terrible, bad, good, amazing⟩"
  }

/-- Negated evaluative: "not terrible", "not amazing", etc. -/
inductive NegatedEvalExpr where
  | notTerrible | notBad | notGood | notAmazing
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Convert evaluative to negated form -/
def EvalExpr.negate : EvalExpr → NegatedEvalExpr
  | .terrible => .notTerrible
  | .bad => .notBad
  | .good => .notGood
  | .amazing => .notAmazing

/-- Get the base (unnegated) form -/
def NegatedEvalExpr.base : NegatedEvalExpr → EvalExpr
  | .notTerrible => .terrible
  | .notBad => .bad
  | .notGood => .good
  | .notAmazing => .amazing

/--
Combined evaluative utterance type (positive + negated).

This is the full utterance set for politeness scenarios:
8 utterances = 4 positive + 4 negated.
-/
inductive EvalUtterance where
  | pos : EvalExpr → EvalUtterance
  | neg : NegatedEvalExpr → EvalUtterance
  deriving Repr, DecidableEq, BEq, Inhabited

/-- All evaluative utterances (positive and negated) -/
def allEvalUtterances : List EvalUtterance := [
  .pos .terrible, .pos .bad, .pos .good, .pos .amazing,
  .neg .notTerrible, .neg .notBad, .neg .notGood, .neg .notAmazing
]

/-- Is this a negated utterance? -/
def EvalUtterance.isNegated : EvalUtterance → Bool
  | .pos _ => false
  | .neg _ => true

-- ============================================================================
-- Numeral Scales
-- ============================================================================

/-- Build a numeral scale from 1 to n -/
def numerals (n : Nat) : Scale Nat :=
  { items := List.range n |>.map (· + 1)
  , name := s!"⟨1, ..., {n}⟩"
  }

-- ============================================================================
-- Scale Operations
-- ============================================================================

/-- Compute scalar implicature: x implicates ¬y for each stronger y -/
def scalarImplicatures {α : Type} [BEq α] [Repr α] (s : Scale α) (x : α) : List (String × α) :=
  (s.alternatives x).map fun y => (s!"¬{repr y}", y)

-- ============================================================================
-- Examples
-- ============================================================================

#eval someAll.alternatives QuantExpr.some_
-- Expected: [all]

#eval someMostAll.alternatives QuantExpr.some_
-- Expected: [most, all]

#eval someAll.weaker QuantExpr.some_ QuantExpr.all
-- Expected: true

#eval numerals 5
-- Expected: Scale with items [1, 2, 3, 4, 5]

end Fragments.English.Scales
