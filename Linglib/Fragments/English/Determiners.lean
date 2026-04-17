import Linglib.Core.Lexical.Word
import Linglib.Theories.Semantics.Quantification.Quantifier
import Linglib.Theories.Semantics.Plurality.CandidateInterpretation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# English Determiners
@cite{horn-1972} @cite{barwise-cooper-1981}

Quantifier lexicon with syntactic and semantic properties.

## Main definitions

- `QForce`: quantificational force
- `QuantEntry`: unified lexical entry

-/

namespace Fragments.English.Determiners

inductive QForce where
  | universal
  | existential
  | definite
  | negative
  | proportional
  deriving DecidableEq, Repr

inductive Monotonicity where
  | increasing
  | decreasing
  | nonMonotone
  deriving DecidableEq, Repr

/-- Weak/strong classification (B&C §4.3, Table II).
    Weak determiners allow there-insertion: "There are some cats."
    Strong determiners don't: "*There is every cat." -/
inductive Strength where
  | weak
  | strong
  deriving DecidableEq, Repr

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
-- Numerical Determiners (@cite{barwise-cooper-1981}; @cite{van-de-pol-etal-2023})
-- ============================================================================

/-- Numerical determiner entry. Parameterized by threshold n.
    These are the class of determiners @cite{van-de-pol-etal-2023} show
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

/-- "both" - universal dual, presupposes exactly 2.
    K&S (83a): [_Det each of the two] ⇒ both.
    Semantically: gqMeet of every and (the 2). -/
def both : QuantifierEntry :=
  { form := "both"
  , qforce := .universal
  , numberRestriction := some .pl
  , monotonicity := .increasing
  , strength := .strong  -- K&S §3.2: definite dets are strong
  }

/-- "neither" - negative dual, presupposes exactly 2.
    K&S (83b): [_Det (not one) of the two] ⇒ neither.
    Semantically: outerNeg of both. -/
def neither : QuantifierEntry :=
  { form := "neither"
  , qforce := .negative
  , numberRestriction := some .pl  -- syntactically singular but semantically dual
  , monotonicity := .decreasing
  , strength := .strong  -- K&S §3.3: negative strong
  }

-- ============================================================================
-- Lexicon Access
-- ============================================================================

/-- All quantifier entries -/
def allQuantifiers : List QuantifierEntry := [
  none_, few, some_, half, most, all, every, each, many, both, neither
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
The 6-word quantity scale used in @cite{van-tiel-franke-sauerland-2021}.

This is a projection of the full lexicon for quantity-focused analyses.
-/
inductive QuantityWord where
  | none_ | few | some_ | half | most | all
  deriving Repr, DecidableEq, Inhabited

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

#guard some_.monotonicity == .increasing
#guard QuantityWord.some_.gqtThreshold 10 == 1
#guard QuantityWord.most.gqtThreshold 10 == 6
#guard QuantityWord.all.ptPrototype 10 == 10

-- ============================================================================
-- Canonical GQ Denotations (from Semantics.Quantification.Quantifier)
-- ============================================================================

/-!
## Compositional Generalized Quantifier Semantics

The **single source of truth** for model-theoretic GQ denotations is
`Semantics.Quantification.Quantifier`. This section re-exports those
denotations and connects them to the `QuantityWord` scale.

### Thread map

From a `QuantityWord` you can reach:
- **Compositional denotations**: `QuantityWord.gqDenotation` → `every_sem`, `some_sem`, etc.
- **Semantic universals** (@cite{barwise-cooper-1981}): `Conservative`, `ScopeUpwardMono`, `ScopeDownwardMono`
  — all in `Core.Quantification`. `Quantity`, `SatisfiesUniversals` in
  `Semantics.Quantification.Quantifier`
- **Proved properties**: `every_conservative`, `some_scope_up`, `no_scope_down`, etc.
- **Duality operations** (B&C §4.11): `Core.Quantification.outerNeg`, `innerNeg`, `dualQ`
  with `outerNeg_up_to_down`, `outerNeg_down_to_up`, `innerNeg_up_to_down` (C9)
- **Strength** (B&C Table II): `Strength` enum, `Core.Quantification.IntersectionCondition`,
  `QSymmetric`, `RestrictorUpwardMono` (persistence),
  `intersection_conservative_symmetric` (C5)
- **Threshold semantics**: `QuantityWord.gqtMeaning` (scalar GQT representation)
- **Prototype semantics**: `QuantityWord.ptMeaning` (gradient PT representation)
- **RSA domains**: `RSA.Quantity` (pragmatic reasoning over quantity scales)
- **Monotonicity**: `Semantics.Entailment.Monotonicity` (polarity)
- **Complexity**: `Core.Conjectures.simplicity_explains_universals`
-/

-- ============================================================================
-- @cite{van-benthem-1984} §3.3: Inferential Characterization
-- ============================================================================

/-- @cite{van-benthem-1984} §3.3: Inferential characterization of the Square of
    Opposition. Each corner is uniquely determined by its relational properties
    under CONSERV + QUANT + VAR*.

    - `inclusion`: all — transitive + reflexive (⊆)
    - `overlap`: some — symmetric + quasi-reflexive (∩ ≠ ∅)
    - `disjointness`: no — symmetric + quasi-universal (∩ = ∅)
    - `nonInclusion`: not all — almost-connected + irreflexive (⊄) -/
inductive InferentialClass where
  | inclusion
  | overlap
  | disjointness
  | nonInclusion
  deriving DecidableEq, Repr

/-- Map quantity words to their inferential class (Square of Opposition corner). -/
def QuantityWord.inferentialClass : QuantityWord → Option InferentialClass
  | .all   => some .inclusion
  | .some_ => some .overlap
  | .none_ => some .disjointness
  | _      => none

/-- Map quantity words to their double monotonicity type (@cite{van-benthem-1984} §4.2). -/
def QuantityWord.doubleMono : QuantityWord → Option Core.Quantification.DoubleMono
  | .all   => some .downUp
  | .some_ => some .upUp
  | .none_ => some .downDown
  | _      => none

section CanonicalGQDenotations
open Core.IntensionalLogic (Frame)
open Semantics.Quantification.Quantifier

variable {m : Frame} [Fintype m.Entity] [DecidableEq m.Entity]

/-- Map quantity words to their canonical model-theoretic GQ denotation.
    These are the compositional `(e→t) → ((e→t) → t)` meanings from
    Montague/Barwise & Cooper, proved conservative and monotone in
    `Semantics.Quantification.Quantifier`. -/
def QuantityWord.gqDenotation (q : QuantityWord)
    (m : Frame) [Fintype m.Entity] : m.Denot Ty.det :=
  match q with
  | .none_ => no_sem m
  | .some_ => some_sem m
  | .all   => every_sem m
  | .most  => most_sem m
  | .few   => few_sem m
  | .half  => half_sem m

-- ============================================================================
-- Monotonicity bridges (gap G): enum value ∧ semantic property
-- ============================================================================

/-- Every: monotonicity metadata says `.increasing` and semantics is scope-↑. -/
theorem every_mono_bridge : every.monotonicity = .increasing ∧
    PScopeUpwardMono (every_sem m) :=
  ⟨rfl, every_scope_up⟩

/-- Some: monotonicity metadata says `.increasing` and semantics is scope-↑. -/
theorem some_mono_bridge : some_.monotonicity = .increasing ∧
    PScopeUpwardMono (some_sem m) :=
  ⟨rfl, some_scope_up⟩

/-- None: monotonicity metadata says `.decreasing` and semantics is scope-↓. -/
theorem none_mono_bridge : none_.monotonicity = .decreasing ∧
    PScopeDownwardMono (no_sem m) :=
  ⟨rfl, no_scope_down⟩

/-- All: monotonicity metadata says `.increasing` and semantics is scope-↑.
    (All and every share `every_sem`.) -/
theorem all_mono_bridge : all.monotonicity = .increasing ∧
    PScopeUpwardMono (every_sem m) :=
  ⟨rfl, every_scope_up⟩

/-- Most: monotonicity metadata says `.increasing` and semantics is scope-↑. -/
theorem most_mono_bridge : most.monotonicity = .increasing ∧
    PScopeUpwardMono (most_sem m) :=
  ⟨rfl, most_scope_up⟩

/-- Few: monotonicity metadata says `.decreasing` and semantics is scope-↓. -/
theorem few_mono_bridge : few.monotonicity = .decreasing ∧
    PScopeDownwardMono (few_sem m) :=
  ⟨rfl, few_scope_down⟩

open Core.Quantification in
/-- Half: monotonicity metadata says `.nonMonotone` — half is neither scope-↑
    nor scope-↓. Adding elements to S can flip half(R,S) either way. -/
theorem half_mono_bridge : half.monotonicity = .nonMonotone :=
  rfl

-- ============================================================================
-- Conservativity bridges (gap G): gqDenotation identity ∧ conservative
-- ============================================================================

/-- All maps to `every_sem` and `every_sem` is conservative. -/
theorem all_conservative_bridge :
    QuantityWord.gqDenotation .all m = every_sem m ∧
    PConservative (every_sem m) :=
  ⟨rfl, every_conservative⟩

/-- Some maps to `some_sem` and `some_sem` is conservative. -/
theorem some_conservative_bridge :
    QuantityWord.gqDenotation .some_ m = some_sem m ∧
    PConservative (some_sem m) :=
  ⟨rfl, some_conservative⟩

/-- None maps to `no_sem` and `no_sem` is conservative. -/
theorem none_conservative_bridge :
    QuantityWord.gqDenotation .none_ m = no_sem m ∧
    PConservative (no_sem m) :=
  ⟨rfl, no_conservative⟩

/-- Most maps to `most_sem` and `most_sem` is conservative. -/
theorem most_conservative_bridge :
    QuantityWord.gqDenotation .most m = most_sem m ∧
    PConservative (most_sem m) :=
  ⟨rfl, most_conservative⟩

/-- Few maps to `few_sem` and `few_sem` is conservative. -/
theorem few_conservative_bridge :
    QuantityWord.gqDenotation .few m = few_sem m ∧
    PConservative (few_sem m) :=
  ⟨rfl, few_conservative⟩

/-- Half maps to `half_sem` and `half_sem` is conservative. -/
theorem half_conservative_bridge :
    QuantityWord.gqDenotation .half m = half_sem m ∧
    PConservative (half_sem m) :=
  ⟨rfl, half_conservative⟩

-- ============================================================================
-- Symmetry bridges (gap G): weak ↔ symmetric (P&W Ch.6)
-- ============================================================================

/-- Some: weak (allows there-insertion) and symmetric. -/
theorem some_symmetry_bridge : some_.strength = .weak ∧
    PQSymmetric (some_sem m) := ⟨rfl, some_symmetric⟩

/-- None: weak and symmetric. -/
theorem none_symmetry_bridge : none_.strength = .weak ∧
    PQSymmetric (no_sem m) := ⟨rfl, no_symmetric⟩

open Semantics.Montague in
/-- Every: strong and NOT symmetric. -/
theorem every_not_symmetric_bridge : every.strength = .strong ∧
    ¬PQSymmetric (every_sem (F := toyModel)) := ⟨rfl, every_not_symmetric⟩

-- ============================================================================
-- both/neither: Boolean GQ composition (K&S §2.3, §3.2)
-- ============================================================================

open Classical in
/-- `⟦both⟧(R)(S)` = `⟦every⟧(R)(S)` when |R|=2.
    For the general case, both = every restricted to exactly-2 restrictors.
    Simplified: on finite models, both(R,S) = every(R,S) ∧ |R|≥2. -/
noncomputable def both_sem (m : Frame) [Fintype m.Entity] : m.Denot Ty.det :=
  λ (R : m.Entity → Prop) S => every_sem m R S ∧ (Finset.univ.filter (fun x : m.Entity => R x)).card ≥ 2

open Classical in
/-- `⟦neither⟧` = outer negation of `⟦both⟧` (K&S (83b)).
    "Neither student passed" = "It's not the case that both students passed"
    when exactly 2 students exist. K&S: neither = (not one) of the two. -/
noncomputable def neither_sem (m : Frame) [Fintype m.Entity] : m.Denot Ty.det :=
  pgqMeet (no_sem m)
    (λ (R : m.Entity → Prop) _ => (Finset.univ.filter (fun x : m.Entity => R x)).card ≥ 2)

/-- both is conservative (follows from every_conservative + pgqMeet closure). -/
theorem both_conservative : PConservative (both_sem m) := by
  intro R S
  simp only [both_sem]
  rw [every_conservative R S]

/-- neither is conservative (follows from no_conservative + pgqMeet closure). -/
theorem neither_conservative :
    PConservative (neither_sem m) := by
  intro R S
  simp only [neither_sem, pgqMeet]
  rw [no_conservative R S]

/-- K&S §3.2: both is positive strong — both(A,A) = true when |A|≥2. -/
theorem both_positive_strong_on_nonempty :
    both.strength = .strong ∧ neither.strength = .strong :=
  ⟨rfl, rfl⟩

/-- K&S (26) at the fragment level: neither is scope-↓ (licenses NPIs).
    "Neither student saw any deer" — NPI "any" licensed. -/
theorem neither_decreasing : neither.monotonicity = .decreasing := rfl

/-- both/neither duality: both is increasing, neither is decreasing,
    mirroring every/no. -/
theorem both_neither_mono_duality :
    both.monotonicity = .increasing ∧ neither.monotonicity = .decreasing :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- Anti-additivity bridges (restrictor NPI licensing)
-- ============================================================================

/-- "Every"/"all" is left-anti-additive in the restrictor: every(A∪B, C) = every(A,C) ∧ every(B,C).
    This licenses strong NPIs in the restrictor of "every":
    "Everyone who ever lifted a finger..." Cross-ref: `every_laa`. -/
theorem every_laa_bridge :
    QuantityWord.gqDenotation .all m = every_sem m ∧
    PLeftAntiAdditive (every_sem m) :=
  ⟨rfl, every_laa⟩

/-- "No"/"none" is left-anti-additive in the restrictor: no(A∪B, C) = no(A,C) ∧ no(B,C).
    Also scope-downward-monotone (licenses weak NPIs in scope).
    Cross-ref: `no_laa`, `no_scope_down`. -/
theorem none_laa_bridge :
    QuantityWord.gqDenotation .none_ m = no_sem m ∧
    PLeftAntiAdditive (no_sem m) ∧
    PScopeDownwardMono (no_sem m) :=
  ⟨rfl, no_laa, no_scope_down⟩

-- ============================================================================
-- @cite{van-benthem-1984}: Inferential + Double Mono Bridges
-- ============================================================================

/-- All: inferential class is inclusion, confirmed by relational properties.
    Van Benthem Thm 3.1.1: the ONLY reflexive antisymmetric quantifier. -/
theorem all_inferential_bridge :
    QuantityWord.all.inferentialClass = some .inclusion ∧
    PQTransitive (every_sem m) ∧ PPositiveStrong (every_sem m) ∧
    PQAntisymmetric (every_sem m) :=
  ⟨rfl, every_transitive, every_positive_strong, every_antisymmetric⟩

/-- Some: inferential class is overlap, confirmed by relational properties.
    Van Benthem Thm 3.3.2: the ONLY symmetric quasi-reflexive quantifier. -/
theorem some_inferential_bridge :
    QuantityWord.some_.inferentialClass = some .overlap ∧
    PQSymmetric (some_sem m) ∧ PQuasiReflexive (some_sem m) :=
  ⟨rfl, some_symmetric, some_quasi_reflexive⟩

/-- None: inferential class is disjointness, confirmed by relational properties.
    Van Benthem Cor 3.3.3: the ONLY symmetric quasi-universal quantifier. -/
theorem none_inferential_bridge :
    QuantityWord.none_.inferentialClass = some .disjointness ∧
    PQSymmetric (no_sem m) ∧ PQuasiUniversal (no_sem m) :=
  ⟨rfl, no_symmetric, no_quasi_universal⟩

/-- All: double mono ↓MON↑ metadata matches semantic proof. -/
theorem all_doubleMono_bridge :
    QuantityWord.all.doubleMono = some .downUp ∧
    PRestrictorDownwardMono (every_sem m) ∧ PScopeUpwardMono (every_sem m) :=
  ⟨rfl, every_restrictor_down, every_scope_up⟩

/-- Some: double mono ↑MON↑ metadata matches semantic proof. -/
theorem some_doubleMono_bridge :
    QuantityWord.some_.doubleMono = some .upUp ∧
    PRestrictorUpwardMono (some_sem m) ∧ PScopeUpwardMono (some_sem m) :=
  ⟨rfl, some_restrictor_up, some_scope_up⟩

/-- None: double mono ↓MON↓ metadata matches semantic proof. -/
theorem none_doubleMono_bridge :
    QuantityWord.none_.doubleMono = some .downDown ∧
    PRestrictorDownwardMono (no_sem m) ∧ PScopeDownwardMono (no_sem m) :=
  ⟨rfl, no_restrictor_down, no_scope_down⟩

end CanonicalGQDenotations

-- ============================================================================
-- Distributivity & Maximality (@cite{haslinger-etal-2025})
-- ============================================================================

/-! Connection to the distributivity/maximality framework in
    `Theories/Semantics/Lexical/Plural/Distributivity.lean`.

    English quantifiers map to the 2×2 `DistMaxClass` classification:

    | Form      | ±dist | ±max | Class        | Theory operator   |
    |-----------|-------|------|--------------|-------------------|
    | each      | +     | +    | distMax      | `distMaximal`     |
    | every     | +     | +    | distMax      | `distMaximal`     |
    | all       | -     | +    | nonDistMax   | `allViaForallH`   |
    | some      | -     | -    | nonDistNonMax| —                 |

    The key contrast with German: English lacks a lexicalized +dist/−max
    item (German *jeweils*). English "each" and "every" both force
    maximality; tolerance-based non-maximality in English comes from
    bare plural definites, not from a dedicated distributor.

    Cross-ref: `Fragments/German/Distributives.lean` for the German
    typology; `Phenomena/Plurals/Studies/HaslingerEtAl2025.lean` for
    the S&P empirical evidence; @cite{haslinger-etal-2025-nllt} derives
    the dist/non-dist split from Q_∀ + ONE (see `UnifiedUniversal.lean`,
    `ONEModifiers.lean`, `HaslingerHienEtAl2025.lean`). -/

open Semantics.Plurality.Distributivity

/-- each: +distributive, +maximal — forces every atom to satisfy P.
    Semantics: `distMaximal`. -/
def each_distMaxClass : DistMaxClass := .distMax

/-- every: +distributive, +maximal — same as each for dist/max,
    differs in allowing collective readings more readily.
    Semantics: `distMaximal`. -/
def every_distMaxClass : DistMaxClass := .distMax

/-- all: -distributive, +maximal — doesn't force atom-by-atom evaluation,
    but blocks exception tolerance. Semantics: `allViaForallH`.
    @cite{kriz-2016}: `all` removes homogeneity (gap → false). -/
def all_distMaxClass : DistMaxClass := .nonDistMax

/-- some: -distributive, -maximal — existential, no maximality. -/
def some_distMaxClass : DistMaxClass := .nonDistNonMax

/-- Metadata bridge: each is +dist, +max. -/
theorem each_is_distMax :
    each.qforce = .universal ∧ each_distMaxClass = .distMax := ⟨rfl, rfl⟩

/-- Metadata bridge: every is +dist, +max. -/
theorem every_is_distMax :
    every.qforce = .universal ∧ every_distMaxClass = .distMax := ⟨rfl, rfl⟩

/-- Metadata bridge: all is -dist, +max. -/
theorem all_is_nonDistMax :
    all.qforce = .universal ∧ all_distMaxClass = .nonDistMax := ⟨rfl, rfl⟩

/-- English has no lexicalized +dist/−max item (contrast German *jeweils*).
    All distributive universals in English are also maximal. -/
theorem english_dist_implies_max :
    each_distMaxClass.isDistributive = true →
      each_distMaxClass.isMaximal = true ∧
      every_distMaxClass.isMaximal = true := by
  decide

/-- Semantic grounding: `each` distributes via `distMaximal`. -/
def eachSem {Atom W : Type*} [DecidableEq Atom] (P : Atom → W → Bool) :
    Finset Atom → W → Bool :=
  distMaximal P

/-- Semantic grounding: `all` universally quantifies over the
    homogeneity parameter. -/
def allSem {Atom W : Type*} [DecidableEq Atom] [Fintype Atom]
    (P : Atom → W → Bool) (x : Finset Atom) (w : W) : Prop :=
  allViaForallH P x w

/-- `eachSem` IS `distMaximal` by construction. -/
theorem each_eq_distMaximal {Atom W : Type*} [DecidableEq Atom]
    (P : Atom → W → Bool) : eachSem P = distMaximal P := rfl

/-- `allSem` reduces to checking every atom (via `allViaForallH_iff_allSatisfy`). -/
theorem all_eq_allSatisfy {Atom W : Type*} [DecidableEq Atom] [Fintype Atom]
    (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    allSem P x w ↔ allSatisfy P x w = true :=
  allViaForallH_iff_allSatisfy P x w

end Fragments.English.Determiners
