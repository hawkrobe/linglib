import Linglib.Core.Basic
import Linglib.Theories.TruthConditional.Determiner.Quantifier
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# English Determiners

Quantifier lexicon with syntactic and semantic properties.

## Main definitions

- `QForce`: quantificational force
- `QuantEntry`: unified lexical entry

## References

- Horn (1972). On the semantic properties of logical operators in English.
-/

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

/-- Weak/strong classification (B&C §4.3, Table II).
    Weak determiners allow there-insertion: "There are some cats."
    Strong determiners don't: "*There is every cat." -/
inductive Strength where
  | weak
  | strong
  deriving DecidableEq, Repr, BEq

/-- Unified lexical entry for quantifiers/determiners. -/
structure QuantifierEntry where
  form : String
  qforce : QForce
  numberRestriction : Option Number := none
  allowsMass : Bool := false
  monotonicity : Monotonicity := .increasing
  strength : Strength := .weak
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
  , strength := .strong  -- B&C Table II: *"There are most cats"
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
  , strength := .strong  -- B&C Table II: *"There is all cats"
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
  , strength := .strong  -- B&C Table II: *"There is every cat"
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
  , strength := .strong  -- B&C Table II: *"There is each cat"
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
-- Numerical Determiners (Barwise & Cooper 1981; van de Pol et al. 2023)
-- ============================================================================

/-- Numerical determiner entry. Parameterized by threshold n.
    These are the class of determiners van de Pol et al. (2023) show
    satisfy all three semantic universals (and have low MDL). -/
structure NumericalDetEntry where
  form : String
  qforce : QForce
  monotonicity : Monotonicity
  /-- The numerical threshold -/
  threshold : Nat
  deriving Repr, BEq

/-- "at least n" — upward monotone in scope, conservative, quantity -/
def atLeast (n : Nat) : NumericalDetEntry :=
  { form := s!"at least {n}", qforce := .proportional
  , monotonicity := .increasing, threshold := n }

/-- "at most n" — downward monotone in scope, conservative, quantity -/
def atMost (n : Nat) : NumericalDetEntry :=
  { form := s!"at most {n}", qforce := .proportional
  , monotonicity := .decreasing, threshold := n }

/-- "exactly n" — non-monotone (neither UE nor DE), conservative, quantity -/
def exactlyN (n : Nat) : NumericalDetEntry :=
  { form := s!"exactly {n}", qforce := .proportional
  , monotonicity := .nonMonotone, threshold := n }

/-- "more than n" — upward monotone, conservative, quantity -/
def moreThan (n : Nat) : NumericalDetEntry :=
  { form := s!"more than {n}", qforce := .proportional
  , monotonicity := .increasing, threshold := n }

/-- "fewer than n" — downward monotone, conservative, quantity -/
def fewerThan (n : Nat) : NumericalDetEntry :=
  { form := s!"fewer than {n}", qforce := .proportional
  , monotonicity := .decreasing, threshold := n }

-- ============================================================================
-- Definite Determiners (less relevant for quantity scales)
-- ============================================================================

def the : QuantifierEntry :=
  { form := "the", qforce := .definite, allowsMass := true, strength := .strong }

def this : QuantifierEntry :=
  { form := "this", qforce := .definite, numberRestriction := some .sg, strength := .strong }

def that : QuantifierEntry :=
  { form := "that", qforce := .definite, numberRestriction := some .sg, strength := .strong }

def these : QuantifierEntry :=
  { form := "these", qforce := .definite, numberRestriction := some .pl, strength := .strong }

def those : QuantifierEntry :=
  { form := "those", qforce := .definite, numberRestriction := some .pl, strength := .strong }

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
  , cat := .DET
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

-- ============================================================================
-- Canonical GQ Denotations (from TruthConditional.Determiner.Quantifier)
-- ============================================================================

/-!
## Compositional Generalized Quantifier Semantics

The **single source of truth** for model-theoretic GQ denotations is
`TruthConditional.Determiner.Quantifier`. This section re-exports those
denotations and connects them to the `QuantityWord` scale.

### Thread map

From a `QuantityWord` you can reach:
- **Compositional denotations**: `QuantityWord.gqDenotation` → `every_sem`, `some_sem`, etc.
- **Semantic universals** (B&C 1981): `Conservative`, `ScopeUpwardMono`, `ScopeDownwardMono`
  — all in `Core.Quantification`. `Quantity`, `SatisfiesUniversals` in
  `TruthConditional.Determiner.Quantifier`
- **Proved properties**: `every_conservative`, `some_scope_up`, `no_scope_down`, etc.
- **Duality operations** (B&C §4.11): `Core.Quantification.outerNeg`, `innerNeg`, `dualQ`
  with `outerNeg_up_to_down`, `outerNeg_down_to_up`, `innerNeg_up_to_down` (C9)
- **Strength** (B&C Table II): `Strength` enum, `Core.Quantification.IntersectionCondition`,
  `QSymmetric`, `RestrictorUpwardMono` (persistence),
  `intersection_conservative_symmetric` (C5)
- **Threshold semantics**: `QuantityWord.gqtMeaning` (scalar GQT representation)
- **Prototype semantics**: `QuantityWord.ptMeaning` (gradient PT representation)
- **RSA domains**: `RSA.Domains.Quantity` (pragmatic reasoning over quantity scales)
- **Monotonicity**: `TruthConditional.Sentence.Entailment.Monotonicity` (polarity)
- **Complexity**: `Core.Conjectures.simplicity_explains_universals` (van de Pol et al. 2023)
-/

section CanonicalGQDenotations
open TruthConditional (Model)
open TruthConditional.Determiner.Quantifier

variable {m : Model} [FiniteModel m]

/-- Map quantity words to their canonical model-theoretic GQ denotation.
    These are the compositional `(e→t) → ((e→t) → t)` meanings from
    Montague/Barwise & Cooper, proved conservative and monotone in
    `TruthConditional.Determiner.Quantifier`. -/
def QuantityWord.gqDenotation (q : QuantityWord)
    (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  match q with
  | .none_ => no_sem m
  | .some_ => some_sem m
  | .all   => every_sem m
  | .most  => most_sem m
  | .few   => sorry -- TODO: "few" = below contextual threshold
  | .half  => sorry -- TODO: "half" = |R∩S| = |R|/2

-- ============================================================================
-- Monotonicity bridges (gap G): enum value ∧ semantic property
-- ============================================================================

open Core.Quantification in
/-- Every: monotonicity metadata says `.increasing` and semantics is scope-↑. -/
theorem every_mono_bridge : every.monotonicity = .increasing ∧
    ScopeUpwardMono (every_sem m) :=
  ⟨rfl, every_scope_up⟩

open Core.Quantification in
/-- Some: monotonicity metadata says `.increasing` and semantics is scope-↑. -/
theorem some_mono_bridge : some_.monotonicity = .increasing ∧
    ScopeUpwardMono (some_sem m) :=
  ⟨rfl, some_scope_up⟩

open Core.Quantification in
/-- None: monotonicity metadata says `.decreasing` and semantics is scope-↓. -/
theorem none_mono_bridge : none_.monotonicity = .decreasing ∧
    ScopeDownwardMono (no_sem m) :=
  ⟨rfl, no_scope_down⟩

open Core.Quantification in
/-- All: monotonicity metadata says `.increasing` and semantics is scope-↑.
    (All and every share `every_sem`.) -/
theorem all_mono_bridge : all.monotonicity = .increasing ∧
    ScopeUpwardMono (every_sem m) :=
  ⟨rfl, every_scope_up⟩

-- ============================================================================
-- Conservativity bridges (gap G): gqDenotation identity ∧ conservative
-- ============================================================================

open Core.Quantification in
/-- All maps to `every_sem` and `every_sem` is conservative. -/
theorem all_conservative_bridge :
    QuantityWord.gqDenotation .all m = every_sem m ∧
    Conservative (every_sem m) :=
  ⟨rfl, every_conservative⟩

open Core.Quantification in
/-- Some maps to `some_sem` and `some_sem` is conservative. -/
theorem some_conservative_bridge :
    QuantityWord.gqDenotation .some_ m = some_sem m ∧
    Conservative (some_sem m) :=
  ⟨rfl, some_conservative⟩

open Core.Quantification in
/-- None maps to `no_sem` and `no_sem` is conservative. -/
theorem none_conservative_bridge :
    QuantityWord.gqDenotation .none_ m = no_sem m ∧
    Conservative (no_sem m) :=
  ⟨rfl, no_conservative⟩

open Core.Quantification in
/-- Most maps to `most_sem` and `most_sem` is conservative. -/
theorem most_conservative_bridge :
    QuantityWord.gqDenotation .most m = most_sem m ∧
    Conservative (most_sem m) :=
  ⟨rfl, most_conservative⟩

-- ============================================================================
-- Symmetry bridges (gap G): weak ↔ symmetric (P&W Ch.6)
-- ============================================================================

open Core.Quantification in
/-- Some: weak (allows there-insertion) and symmetric. -/
theorem some_symmetry_bridge : some_.strength = .weak ∧
    QSymmetric (some_sem m) := ⟨rfl, some_symmetric⟩

open Core.Quantification in
/-- None: weak and symmetric. -/
theorem none_symmetry_bridge : none_.strength = .weak ∧
    QSymmetric (no_sem m) := ⟨rfl, no_symmetric⟩

open Core.Quantification TruthConditional in
/-- Every: strong and NOT symmetric. -/
theorem every_not_symmetric_bridge : every.strength = .strong ∧
    ¬QSymmetric (every_sem (m := toyModel)) := ⟨rfl, every_not_symmetric⟩

-- ============================================================================
-- Anti-additivity bridges (restrictor NPI licensing)
-- ============================================================================

open Core.Quantification in
/-- "Every"/"all" is left-anti-additive in the restrictor: every(A∪B, C) = every(A,C) ∧ every(B,C).
    This licenses strong NPIs in the restrictor of "every":
    "Everyone who ever lifted a finger..." Cross-ref: `every_laa`. -/
theorem every_laa_bridge :
    QuantityWord.gqDenotation .all m = every_sem m ∧
    LeftAntiAdditive (every_sem m) :=
  ⟨rfl, every_laa⟩

open Core.Quantification in
/-- "No"/"none" is left-anti-additive in the restrictor: no(A∪B, C) = no(A,C) ∧ no(B,C).
    Also scope-downward-monotone (licenses weak NPIs in scope).
    Cross-ref: `no_laa`, `no_scope_down`. -/
theorem none_laa_bridge :
    QuantityWord.gqDenotation .none_ m = no_sem m ∧
    LeftAntiAdditive (no_sem m) ∧
    ScopeDownwardMono (no_sem m) :=
  ⟨rfl, no_laa, no_scope_down⟩

end CanonicalGQDenotations

end Fragments.English.Determiners
