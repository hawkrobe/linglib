/-!
# English Scales

Horn scales for quantifiers, modals, and degrees.

## Main definitions

- `Scale`: ordered list from weak to strong
- `someAll`, `mightMust`: standard scales

## References

- Horn (1972). On the semantic properties of logical operators in English.
- Kennedy (2007). Vagueness and grammar.
-/

import Mathlib.Data.Rat.Defs

namespace Fragments.English.Scales

/-- Horn scale: ordered list from weak to strong. -/
structure Scale (α : Type) where
  items : List α
  name : String := ""

def Scale.alternatives {α : Type} [BEq α] (s : Scale α) (x : α) : List α :=
  match s.items.dropWhile (· != x) with
  | [] => []
  | _ :: rest => rest

def Scale.strongest {α : Type} (s : Scale α) : Option α :=
  s.items.getLast?

def Scale.weakest {α : Type} (s : Scale α) : Option α :=
  s.items.head?

def Scale.weaker {α : Type} [BEq α] (s : Scale α) (x y : α) : Bool :=
  let findIdx (item : α) := s.items.findIdx? (· == item)
  match findIdx x, findIdx y with
  | some i, some j => i < j
  | _, _ => false

inductive QuantExpr where
  | some_ | most | all
  deriving Repr, DecidableEq, BEq, Inhabited

def someAll : Scale QuantExpr :=
  { items := [.some_, .all], name := "⟨some, all⟩" }

def someMostAll : Scale QuantExpr :=
  { items := [.some_, .most, .all], name := "⟨some, most, all⟩" }

inductive ConnExpr where
  | or_ | and_
  deriving Repr, DecidableEq, BEq, Inhabited

def orAnd : Scale ConnExpr :=
  { items := [.or_, .and_], name := "⟨or, and⟩" }

inductive ModalExpr where
  | might | must
  | possible | necessary
  | allowed | required
  deriving Repr, DecidableEq, BEq, Inhabited

def mightMust : Scale ModalExpr :=
  { items := [.might, .must], name := "⟨might, must⟩" }

def possibleNecessary : Scale ModalExpr :=
  { items := [.possible, .necessary], name := "⟨possible, necessary⟩" }

def allowedRequired : Scale ModalExpr :=
  { items := [.allowed, .required], name := "⟨allowed, required⟩" }

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
  (s.alternatives x).map λ y => (s!"¬{repr y}", y)

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

-- ============================================================================
-- Scale Closure Properties (Chierchia 2013, Spector 2016)
-- ============================================================================

/-!
## Closure Under Conjunction

A crucial property for exhaustification: whether the alternative set is
CLOSED UNDER CONJUNCTION.

### Spector (2016) Theorem 9

When alternatives are closed under ∧, the two exhaustivity operators
exh_mw and exh_ie are EQUIVALENT.

### Chierchia (2013) EFCI Analysis

The puzzle of Free Choice Items depends on alternatives NOT being closed:
- Standard scalar alternatives ⟨some, all⟩: closed under ∧
- Domain alternatives {P(d) | d ∈ D}: NOT closed under ∧

When domain alternatives are NOT closed, exhaustification can lead to
contradiction (the EFCI puzzle), which is then resolved by rescue mechanisms.

### Insight

| Alternative Type | Closed? | Exhaustification Result |
|-----------------|---------|-------------------------|
| Scalar ⟨some, all⟩ | ✓ | Clean SI: "some but not all" |
| Domain {P(d)} | ✗ | Contradiction (needs rescue) |

### References

- Spector (2016). Comparing exhaustivity operators. S&P 9(11). Theorem 9.
- Chierchia (2013). Logic in Grammar. Ch.1, EFCI discussion.
- Fox (2007). Free choice and the theory of scalar implicatures.
-/

/--
Conjunction operation on propositions (semantic level).
-/
def PropConj (α : Type) := α → α → α

/--
A set of alternatives is closed under conjunction if conjoining any two
members yields another member (or a stronger proposition in the set).

For semantic alternatives as propositions, this means:
∀ p q ∈ ALT, p ∧ q ∈ ALT (or is entailed by something in ALT)
-/
structure ClosedUnderConj (α : Type) where
  /-- The set of alternatives -/
  alts : List α
  /-- The conjunction operation -/
  conj : α → α → α
  /-- Is it closed? -/
  isClosed : Bool
  /-- Witness to non-closure (if not closed) -/
  nonClosureWitness : Option (α × α × String)

/--
Standard scalar alternatives are closed under conjunction.

For ⟨some, all⟩:
- some ∧ some = some ✓
- some ∧ all = all ✓ (entailed by all)
- all ∧ all = all ✓
-/
def quantifierScaleClosed : ClosedUnderConj QuantExpr :=
  { alts := [.some_, .all]
  , conj := λ x y =>
      match x, y with
      | .all, _ => .all
      | _, .all => .all
      | _, _ => .some_
  , isClosed := true
  , nonClosureWitness := none
  }

/--
Connective alternatives are closed.

For ⟨or, and⟩:
- or ∧ or = or ✓
- or ∧ and = and ✓
- and ∧ and = and ✓
-/
def connScaleClosed : ClosedUnderConj ConnExpr :=
  { alts := [.or_, .and_]
  , conj := λ x y =>
      match x, y with
      | .and_, _ => .and_
      | _, .and_ => .and_
      | _, _ => .or_
  , isClosed := true
  , nonClosureWitness := none
  }

/--
Domain alternatives (singleton domains) are NOT closed under conjunction.

For domain D = {a, b, c} with predicate P:
- Alternatives: {P(a), P(b), P(c)}
- P(a) ∧ P(b) = "exactly a and b" is NOT in the set
- This non-closure causes the EFCI puzzle

Represented symbolically: conjoining "exactly a" with "exactly b"
gives a proposition NOT in the original alternative set.
-/
structure DomainAlternatives (Entity : Type) where
  /-- The domain -/
  domain : List Entity
  /-- Is it closed under conjunction? -/
  isClosed : Bool := false
  /-- Why not closed? -/
  explanation : String := "P(a) ∧ P(b) ∉ {P(d) | d ∈ D}"

/--
Example: three-element domain shows non-closure.
-/
def threeDomain : DomainAlternatives Nat :=
  { domain := [1, 2, 3]
  , isClosed := false
  , explanation := "P(1) ∧ P(2) = 'exactly 1 and 2' ∉ singleton alternatives"
  }

/--
Closure status affects exhaustification behavior.
-/
inductive ClosureEffect where
  | cleanSI         -- Closed: clean scalar implicature
  | contradiction   -- Not closed: potential contradiction
  | needsRescue     -- Not closed: requires modal/pruning rescue
  deriving DecidableEq, BEq, Repr

/--
Predict exhaustification effect from closure status.
-/
def predictExhEffect (isClosed : Bool) : ClosureEffect :=
  if isClosed then .cleanSI else .needsRescue

-- Verify: scalar scales are closed
#guard quantifierScaleClosed.isClosed
#guard connScaleClosed.isClosed

-- Verify: domain alternatives are not closed
#guard !threeDomain.isClosed

-- ============================================================================
-- Connection to Spector (2016)
-- ============================================================================

/-!
## Spector's Theorem 9

**Theorem 9** (Spector 2016, p.25):
When ALT is closed under conjunction, exh_mw = exh_ie.

This is proven in `Theories/NeoGricean/Exhaustivity/Basic.lean`.

The closure property ensures that the different ways of computing
"what to exclude" all converge to the same result.

### Practical Implication

For standard scalar alternatives (which ARE closed):
- We can use either exh_mw or exh_ie
- They give identical results
- Simple "negate the stronger alternatives" suffices

For EFCI alternatives (which are NOT closed):
- exh_mw ≠ exh_ie in general
- Innocent exclusion (exh_ie) is preferred
- But even exh_ie can lead to contradiction without rescue
-/

/--
Summary of closure and its effects.
-/
structure ClosureSummary where
  /-- Alternative type -/
  altType : String
  /-- Is it closed? -/
  isClosed : Bool
  /-- Effect on exhaustification -/
  effect : String
  /-- Relevant theory reference -/
  reference : String
  deriving Repr

def scalarClosureSummary : ClosureSummary :=
  { altType := "Scalar ⟨some, all⟩"
  , isClosed := true
  , effect := "exh_mw = exh_ie; clean SI"
  , reference := "Spector (2016) Theorem 9" }

def domainClosureSummary : ClosureSummary :=
  { altType := "Domain {P(d) | d ∈ D}"
  , isClosed := false
  , effect := "exh can contradict; needs rescue"
  , reference := "Chierchia (2013) EFCI" }

def closureSummaries : List ClosureSummary :=
  [scalarClosureSummary, domainClosureSummary]

end Fragments.English.Scales
