/-!
# English Determiners

Quantifier lexicon with syntactic and semantic properties.

## Main definitions

- `QForce`: quantificational force
- `QuantEntry`: unified lexical entry

## References

- Horn (1972). On the semantic properties of logical operators in English.
-/

import Linglib.Core.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Fragments.English.Determiners

inductive QForce where
  | universal
  | existential
  | definite
  | negative
  | proportional
  deriving DecidableEq, Repr, BEq

inductive Monotonicity where
  | increasing
  | decreasing
  | nonMonotone
  deriving DecidableEq, Repr, BEq

/-- Unified lexical entry for quantifiers/determiners. -/
structure QuantifierEntry where
  form : String
  qforce : QForce
  numberRestriction : Option Number := none
  allowsMass : Bool := false
  monotonicity : Monotonicity := .increasing
  gqtThreshold : ℚ := 0
  ptPrototype : ℚ := 0
  ptSpread : ℚ := 2
  deriving Repr, BEq

def none_ : QuantifierEntry :=
  { form := "none", qforce := .negative, allowsMass := true, monotonicity := .decreasing
  , gqtThreshold := 0, ptPrototype := 0, ptSpread := 1 }

def few : QuantifierEntry :=
  { form := "few", qforce := .proportional, numberRestriction := some .pl
  , monotonicity := .decreasing, gqtThreshold := 1/3, ptPrototype := 1/5, ptSpread := 2 }

def some_ : QuantifierEntry :=
  { form := "some", qforce := .existential, allowsMass := true, monotonicity := .increasing
  , gqtThreshold := 0, ptPrototype := 1/3, ptSpread := 3 }

def half : QuantifierEntry :=
  { form := "half", qforce := .proportional, allowsMass := true, monotonicity := .nonMonotone
  , gqtThreshold := 1/2, ptPrototype := 1/2, ptSpread := 2 }

/-- "most" - more than half -/
def most : QuantifierEntry :=
  { form := "most"
  , qforce := .proportional
  , numberRestriction := some .pl
  , allowsMass := true
  , monotonicity := .increasing
  , gqtThreshold := 1/2  -- threshold is >1/2
  , ptPrototype := 4/5
  , ptSpread := 2
  }

/-- "all" - everything satisfies -/
def all : QuantifierEntry :=
  { form := "all"
  , qforce := .universal
  , numberRestriction := some .pl
  , allowsMass := true
  , monotonicity := .increasing
  , gqtThreshold := 1
  , ptPrototype := 1
  , ptSpread := 1
  }

/-- "every" - universal, singular -/
def every : QuantifierEntry :=
  { form := "every"
  , qforce := .universal
  , numberRestriction := some .sg
  , monotonicity := .increasing
  , gqtThreshold := 1
  , ptPrototype := 1
  , ptSpread := 1
  }

/-- "each" - universal, distributive -/
def each : QuantifierEntry :=
  { form := "each"
  , qforce := .universal
  , numberRestriction := some .sg
  , monotonicity := .increasing
  , gqtThreshold := 1
  , ptPrototype := 1
  , ptSpread := 1
  }

/-- "many" - a large number -/
def many : QuantifierEntry :=
  { form := "many"
  , qforce := .proportional
  , numberRestriction := some .pl
  , monotonicity := .increasing
  , gqtThreshold := 1/2
  , ptPrototype := 3/4
  , ptSpread := 2
  }

-- ============================================================================
-- Definite Determiners (less relevant for quantity scales)
-- ============================================================================

def the : QuantifierEntry :=
  { form := "the", qforce := .definite, allowsMass := true }

def this : QuantifierEntry :=
  { form := "this", qforce := .definite, numberRestriction := some .sg }

def that : QuantifierEntry :=
  { form := "that", qforce := .definite, numberRestriction := some .sg }

def these : QuantifierEntry :=
  { form := "these", qforce := .definite, numberRestriction := some .pl }

def those : QuantifierEntry :=
  { form := "those", qforce := .definite, numberRestriction := some .pl }

def a : QuantifierEntry :=
  { form := "a", qforce := .existential, numberRestriction := some .sg }

def an : QuantifierEntry :=
  { form := "an", qforce := .existential, numberRestriction := some .sg }

-- ============================================================================
-- Lexicon Access
-- ============================================================================

/-- All quantifier entries -/
def allQuantifiers : List QuantifierEntry := [
  none_, few, some_, half, most, all, every, each, many
]

/-- All determiner entries (including definites) -/
def allDeterminers : List QuantifierEntry := [
  the, this, that, these, those, a, an
] ++ allQuantifiers

/-- Lookup by form -/
def lookup (form : String) : Option QuantifierEntry :=
  allDeterminers.find? λ d => d.form == form

-- ============================================================================
-- Scalar Quantity Words (for RSA quantity domains)
-- ============================================================================

/--
The 6-word quantity scale used in van Tiel et al. (2021).

This is a projection of the full lexicon for quantity-focused analyses.
-/
inductive QuantityWord where
  | none_ | few | some_ | half | most | all
  deriving Repr, DecidableEq, BEq, Inhabited

instance : Fintype QuantityWord where
  elems := {.none_, .few, .some_, .half, .most, .all}
  complete := λ x => by cases x <;> simp

/-- Get the lexical entry for a quantity word -/
def QuantityWord.entry : QuantityWord → QuantifierEntry
  | .none_ => Fragments.English.Determiners.none_
  | .few => Fragments.English.Determiners.few
  | .some_ => Fragments.English.Determiners.some_
  | .half => Fragments.English.Determiners.half
  | .most => Fragments.English.Determiners.most
  | .all => Fragments.English.Determiners.all

/-- Get monotonicity from the entry -/
def QuantityWord.monotonicity (q : QuantityWord) : Monotonicity :=
  q.entry.monotonicity

/-- Get GQT threshold (scaled to domain size n) -/
def QuantityWord.gqtThreshold (n : Nat) (q : QuantityWord) : Nat :=
  let frac := q.entry.gqtThreshold
  -- Special case: "some" means ≥1, not ≥0
  if q == .some_ then 1
  -- Special case: "most" means >half, i.e., ≥(n/2 + 1)
  else if q == .most then n / 2 + 1
  else (frac * n).floor.toNat

/-- Get PT prototype (scaled to domain size n) -/
def QuantityWord.ptPrototype (n : Nat) (q : QuantityWord) : Nat :=
  let frac := q.entry.ptPrototype
  (frac * n).floor.toNat

/-- Get PT spread -/
def QuantityWord.ptSpread (q : QuantityWord) : ℚ :=
  q.entry.ptSpread

/-- All quantity words as a list -/
def QuantityWord.toList : List QuantityWord :=
  [.none_, .few, .some_, .half, .most, .all]

-- ============================================================================
-- Scales (Horn Scales)
-- ============================================================================

/--
A Horn scale: ordered alternatives from weak to strong.

The key property: each item entails all weaker items.
-/
structure Scale where
  /-- Items from weakest to strongest -/
  items : List QuantityWord
  /-- Name for display -/
  name : String := ""

/-- The ⟨some, all⟩ scale -/
def someAllScale : Scale :=
  { items := [.some_, .all], name := "⟨some, all⟩" }

/-- The ⟨some, most, all⟩ scale -/
def someMostAllScale : Scale :=
  { items := [.some_, .most, .all], name := "⟨some, most, all⟩" }

/-- Get alternatives (items strictly stronger than x) -/
def Scale.alternatives (s : Scale) (x : QuantityWord) : List QuantityWord :=
  match s.items.dropWhile (· != x) with
  | [] => []
  | _ :: rest => rest

/-- Is x weaker than y on this scale? -/
def Scale.weaker (s : Scale) (x y : QuantityWord) : Bool :=
  let findIdx (item : QuantityWord) := s.items.findIdx? (· == item)
  match findIdx x, findIdx y with
  | some i, some j => i < j
  | _, _ => false

-- ============================================================================
-- GQT Semantics
-- ============================================================================

/-- GQT meaning: binary truth based on threshold and monotonicity -/
def QuantityWord.gqtMeaning (n : Nat) (q : QuantityWord) (t : Fin (n + 1)) : Bool :=
  let θ := q.gqtThreshold n
  match q.monotonicity with
  | .increasing => t.val ≥ θ
  | .decreasing => t.val ≤ θ
  | .nonMonotone => t.val == θ  -- exactly at threshold (simplified)

/-- GQT meaning as rational -/
def QuantityWord.gqtMeaningRat (n : Nat) (q : QuantityWord) (t : Fin (n + 1)) : ℚ :=
  if q.gqtMeaning n t then 1 else 0

/-- GQT meaning is always non-negative -/
theorem QuantityWord.gqtMeaningRat_nonneg (n : Nat) (q : QuantityWord) (t : Fin (n + 1)) :
    0 ≤ q.gqtMeaningRat n t := by
  simp only [gqtMeaningRat]
  split_ifs <;> norm_num

-- ============================================================================
-- PT Semantics
-- ============================================================================

/-- Approximate Gaussian exp(-x²) with rational arithmetic -/
private def approxGaussian (x : ℚ) : ℚ :=
  let xSq := x * x
  if xSq ≤ 1/4 then 1 - xSq / 2
  else if xSq ≤ 1 then 3/4 - xSq / 4
  else if xSq ≤ 4 then 1/2 - xSq / 8
  else if xSq ≤ 9 then 1/4 - xSq / 36
  else 1/100

/-- PT meaning: gradient truth based on distance from prototype -/
def QuantityWord.ptMeaning (n : Nat) (q : QuantityWord) (t : Fin (n + 1)) : ℚ :=
  let p := q.ptPrototype n
  let d := q.ptSpread
  let distance : ℚ := (t.val : ℚ) - (p : ℚ)
  let normalized := distance / d
  approxGaussian normalized

/-- Helper: approxGaussian always returns non-negative values -/
private theorem approxGaussian_nonneg (x : ℚ) : 0 ≤ approxGaussian x := by
  simp only [approxGaussian]
  split_ifs with h1 h2 h3 h4
  · have : x * x ≤ 1/4 := h1; linarith
  · have : x * x ≤ 1 := h2; linarith
  · have : x * x ≤ 4 := h3; linarith
  · have : x * x ≤ 9 := h4; linarith
  · norm_num

/-- PT meaning is always non-negative -/
theorem QuantityWord.ptMeaning_nonneg (n : Nat) (q : QuantityWord) (t : Fin (n + 1)) :
    0 ≤ q.ptMeaning n t := by
  simp only [ptMeaning]
  exact approxGaussian_nonneg _

-- ============================================================================
-- Conversion to Core.Word
-- ============================================================================

def QuantifierEntry.toWord (d : QuantifierEntry) : Word :=
  { form := d.form
  , cat := .D
  , features := { number := d.numberRestriction }
  }

-- ============================================================================
-- Examples
-- ============================================================================

#eval some_.monotonicity           -- increasing
#eval QuantityWord.some_.gqtThreshold 10  -- 1
#eval QuantityWord.most.gqtThreshold 10   -- 5 (> half of 10)
#eval QuantityWord.all.ptPrototype 10     -- 10

#eval someAllScale.alternatives .some_  -- [all]
#eval someMostAllScale.alternatives .some_  -- [most, all]

end Fragments.English.Determiners
