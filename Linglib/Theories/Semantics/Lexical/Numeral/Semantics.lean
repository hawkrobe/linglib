import Linglib.Core.Scale
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier

/-!
# Unified Numeral Semantics

Consolidates numeral theory infrastructure into a single module. All numeral meanings
(bare + modified) flow through `maxMeaning`. The only theory disagreement is the
`OrderingRel` for bare numerals:

| Theory      | Bare "three" | `bareRel`  |
|-------------|-------------|------------|
| Lower-bound | ≥3          | `.ge`      |
| Exact       | =3          | `.eq`      |

Modified numerals are theory-independent — everyone agrees "more than 3" means `.gt`.

## Sections

1. Ordering relations and modifier classification (Kennedy 2015)
2. Unified meaning function (`maxMeaning`)
3. BareNumeral type and NumeralExpr
4. Alternative sets (Kennedy §4.1)
5. Class A/B theorems, anti-Horn-scale argument
6. Theory parameterization (`NumeralTheory`)
7. Theory instances (`LowerBound`, `Exact`)
8. Derived properties (ambiguity, monotonicity, RSA)
9. Comparison infrastructure and theorems
10. GQT bridge theorems
11. CumminsFranke bridge
12. Aliases
13. Verification

## References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
  *Semantics & Pragmatics* 8(10), 1–44.
- Goodman & Stuhlmüller (2013). Knowledge and Implicature.
- Blok, D. (2015). The semantics and pragmatics of directional numeral modifiers.
-/

namespace Semantics.Lexical.Numeral

-- ============================================================================
-- Section 1: Ordering Relations and Modifier Classification
-- ============================================================================

/-- The 5 ordering relations used in Kennedy's maximality framework.

Each modified numeral selects one of these relations:
- `.eq`: bare numerals ("three" = max = 3)
- `.gt`: "more than" (max > 3)
- `.lt`: "fewer than" (max < 3)
- `.ge`: "at least" (max ≥ 3)
- `.le`: "at most" (max ≤ 3) -/
inductive OrderingRel where
  | eq  -- =  (bare numeral)
  | gt  -- >  (more than)
  | lt  -- <  (fewer than)
  | ge  -- ≥  (at least)
  | le  -- ≤  (at most)
  deriving Repr, DecidableEq, BEq

/-- Class A (strict) vs Class B (non-strict) modified numerals.

The distinction predicts ignorance implicature patterns:
- Class A (>, <): EXCLUDE the bare-numeral world → no ignorance
- Class B (≥, ≤): INCLUDE the bare-numeral world → ignorance -/
inductive ModifierClass where
  | classA  -- strict: >, <
  | classB  -- non-strict: ≥, ≤
  deriving Repr, DecidableEq, BEq

/-- Upper vs lower bound direction.

- `.upper`: constrains from above (at most, fewer than)
- `.lower`: constrains from below (at least, more than) -/
inductive BoundDirection where
  | upper  -- at most, fewer than, up to
  | lower  -- at least, more than, from...on
  deriving Repr, DecidableEq, BEq

/-- Derive the modifier class from an ordering relation. -/
def modifierClassOf : OrderingRel → ModifierClass
  | .eq => .classB
  | .gt => .classA
  | .lt => .classA
  | .ge => .classB
  | .le => .classB

/-- Derive bound direction from an ordering relation. -/
def boundDirectionOf : OrderingRel → BoundDirection
  | .eq => .lower
  | .gt => .lower
  | .lt => .upper
  | .ge => .lower
  | .le => .upper

-- ============================================================================
-- Section 2: Unified Meaning Function
-- ============================================================================

/-- The unified meaning function for all numeral expressions (Kennedy 2015).

`maxMeaning rel m n` is true iff cardinality `n` stands in relation `rel` to
threshold `m`. This captures Kennedy's:

  ⟦modifier m⟧ = λP. max{d | #P ≥ d} REL m

where `n` plays the role of `max{d | #P ≥ d}` and `m` is the numeral.

At the cardinality level, `maxMeaning .eq` also plays the role of Bylinina & Nouwen's (2020)
MANY operator (Hackl 2000): `MANY(n) = λcard. card = n`. A proper MANY over plural
individuals (Link 1983) awaits mereological infrastructure; at the `Nat` abstraction the
two are definitionally equal. -/
@[simp] def maxMeaning (rel : OrderingRel) (m : Nat) (n : Nat) : Bool :=
  match rel with
  | .eq => n == m
  | .gt => n > m
  | .lt => n < m
  | .ge => n ≥ m
  | .le => n ≤ m

/-- Bare numeral meaning: max = m (exact cardinality). -/
abbrev bareMeaning (m : Nat) (n : Nat) : Bool := maxMeaning .eq m n

/-- "More than m": max > m. -/
abbrev moreThanMeaning (m : Nat) (n : Nat) : Bool := maxMeaning .gt m n

/-- "Fewer than m": max < m. -/
abbrev fewerThanMeaning (m : Nat) (n : Nat) : Bool := maxMeaning .lt m n

/-- "At least m": max ≥ m. -/
abbrev atLeastMeaning (m : Nat) (n : Nat) : Bool := maxMeaning .ge m n

/-- "At most m": max ≤ m. -/
abbrev atMostMeaning (m : Nat) (n : Nat) : Bool := maxMeaning .le m n

-- ============================================================================
-- Section 3: BareNumeral and NumeralExpr
-- ============================================================================

/-- Bare numeral utterances (one through five). -/
inductive BareNumeral where
  | one | two | three | four | five
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert BareNumeral to its numeric value. -/
def BareNumeral.toNat : BareNumeral → Nat
  | .one => 1 | .two => 2 | .three => 3 | .four => 4 | .five => 5

instance : ToString BareNumeral where
  toString
    | .one => "one" | .two => "two" | .three => "three"
    | .four => "four" | .five => "five"

/-- A numeral expression: either a bare numeral or a modified numeral. -/
inductive NumeralExpr where
  | bare (n : Nat)
  | modified (rel : OrderingRel) (n : Nat)
  deriving Repr, DecidableEq, BEq

/-- Meaning of a numeral expression, parameterized by the bare-numeral theory. -/
def NumeralExpr.meaning (bareRel : OrderingRel) : NumeralExpr → Nat → Bool
  | .bare m, n => maxMeaning bareRel m n
  | .modified rel m, n => maxMeaning rel m n

-- ============================================================================
-- Section 4: Alternative Sets (Kennedy §4.1)
-- ============================================================================

/-- A numeral alternative in Kennedy's framework.

Instead of the traditional Horn scale ⟨1, 2, 3, ...⟩, the relevant
alternatives for numeral n are:

  {bare n, more than n, at least n}  (lower-bound direction)
  {bare n, fewer than n, at most n}  (upper-bound direction) -/
inductive NumeralAlternative where
  | bare (n : Nat)
  | modified (rel : OrderingRel) (n : Nat)
  deriving Repr, DecidableEq, BEq

/-- Lower-bound alternative set. -/
def lowerAlternatives (n : Nat) : List NumeralAlternative :=
  [.bare n, .modified .gt n, .modified .ge n]

/-- Upper-bound alternative set. -/
def upperAlternatives (n : Nat) : List NumeralAlternative :=
  [.bare n, .modified .lt n, .modified .le n]

/-- Get the meaning of a numeral alternative. -/
def NumeralAlternative.meaning : NumeralAlternative → Nat → Bool
  | .bare m => maxMeaning .eq m
  | .modified rel m => maxMeaning rel m

-- ============================================================================
-- Section 5: Class A/B Theorems and Anti-Horn-Scale Argument
-- ============================================================================

/-- Class A modifiers EXCLUDE the bare-numeral world. -/
theorem classA_gt_excludes_bare (m : Nat) :
    maxMeaning .gt m m = false := by
  simp [maxMeaning]

theorem classA_lt_excludes_bare (m : Nat) :
    maxMeaning .lt m m = false := by
  simp [maxMeaning]

/-- Class B modifiers INCLUDE the bare-numeral world. -/
theorem classB_ge_includes_bare (m : Nat) :
    maxMeaning .ge m m = true := by
  simp [maxMeaning]

theorem classB_le_includes_bare (m : Nat) :
    maxMeaning .le m m = true := by
  simp [maxMeaning]

/-- Bare numeral entails "at least n" (Class B ≥). -/
theorem classB_entailed_by_bare (m n : Nat) :
    bareMeaning m n = true → atLeastMeaning m n = true := by
  simp [bareMeaning, atLeastMeaning, maxMeaning]
  intro h; omega

/-- Bare numeral does NOT entail "more than n" (Class A >). -/
theorem classA_not_entailed_by_bare (m : Nat) :
    bareMeaning m m = true ∧ moreThanMeaning m m = false := by
  simp [bareMeaning, moreThanMeaning, maxMeaning]

/-- Exact bare numerals are NOT monotonic. -/
theorem bare_not_monotonic :
    bareMeaning 3 3 = true ∧ bareMeaning 2 3 = false := by
  simp [bareMeaning, maxMeaning]

/-- Bare numerals do not form a traditional Horn scale. -/
theorem numerals_not_horn_scalar :
    (bareMeaning 3 3 = true ∧ bareMeaning 2 3 = false) ∧
    (bareMeaning 2 2 = true ∧ bareMeaning 3 2 = false) := by
  simp [bareMeaning, maxMeaning]

/-- "At least n" is strictly weaker than "bare n" (under bilateral semantics). -/
theorem atLeast_strictly_weaker_than_bare :
    (bareMeaning 3 3 = true ∧ atLeastMeaning 3 3 = true) ∧
    (atLeastMeaning 3 4 = true ∧ bareMeaning 3 4 = false) := by
  simp [bareMeaning, atLeastMeaning, maxMeaning]

/-- "More than n" and "bare n" have disjoint denotations. -/
theorem moreThan_disjoint_from_bare :
    (bareMeaning 3 3 = true ∧ moreThanMeaning 3 3 = false) ∧
    (bareMeaning 3 4 = false ∧ moreThanMeaning 3 4 = true) := by
  simp [bareMeaning, moreThanMeaning, maxMeaning]

-- ============================================================================
-- Section 6: Theory Parameterization
-- ============================================================================

/-- Standard list of numeral utterances for RSA scenarios. -/
def standardNumWords : List BareNumeral := [.one, .two, .three]

/-- Standard list of world states (cardinalities 0-3). -/
def standardWorlds : List Nat := [0, 1, 2, 3]

/--
A semantic theory for number words.

Each theory specifies a `bareRel` — the ordering relation for bare numerals.
All meanings are derived via `maxMeaning`:

- Bare numeral meaning: `maxMeaning T.bareRel w.toNat n`
- Modified numeral meaning: `maxMeaning rel m n` (theory-independent)
-/
structure NumeralTheory where
  /-- Name of the theory -/
  name : String
  /-- Academic citation -/
  citation : String
  /-- The key parameter: which ordering relation for bare numerals -/
  bareRel : OrderingRel
  /-- Utterances to consider (default: one, two, three) -/
  utterances : List BareNumeral := standardNumWords
  /-- World states to consider (default: 0, 1, 2, 3) -/
  worlds : List Nat := standardWorlds

/-- Derivational direction for the at-least/exactly relationship (Bylinina & Nouwen 2020 §5–6).

The four views on numeral semantics differ in which reading is basic:
- `exactFromAtLeast`: base meaning is at-least (≥n), exact derived via EXH or scalar implicature.
  Corresponds to `LowerBound` / Horn (1972) / the modifier–number view.
- `atLeastFromExact`: base meaning is exact (=n), at-least derived via type-shift or
  relaxing maximality. Corresponds to `Exact` / Kennedy (2015) / the degree quantifier view. -/
inductive DerivationalDirection where
  | exactFromAtLeast
  | atLeastFromExact
  deriving DecidableEq, BEq, Repr

/-- Derive the derivational direction from a theory's `bareRel`. -/
def NumeralTheory.derivationalDirection (T : NumeralTheory) : DerivationalDirection :=
  if T.bareRel == .ge then .exactFromAtLeast
  else .atLeastFromExact

/-- Derived bare-numeral meaning from `bareRel`. -/
def NumeralTheory.meaning (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Bool :=
  maxMeaning T.bareRel w.toNat n

/-- Derived meaning for general numeral expressions. -/
def NumeralTheory.exprMeaning (T : NumeralTheory) (e : NumeralExpr) (n : Nat) : Bool :=
  e.meaning T.bareRel n

-- ============================================================================
-- Section 7: Theory Instances
-- ============================================================================

/-- Lower-bound numeral theory (Horn 1972).

"Two" means ≥2. The exact interpretation emerges via scalar implicature. -/
def LowerBound : NumeralTheory where
  name := "Lower-bound"
  citation := "Horn 1972"
  bareRel := .ge

/-- Exact numeral theory (Kennedy 2015).

"Two" means =2 (via maximality). No RSA strengthening needed for bare numerals. -/
def Exact : NumeralTheory where
  name := "Exact"
  citation := "Kennedy 2015"
  bareRel := .eq

/-- Lower-bound meaning is `maxMeaning .ge`. -/
theorem lowerBound_meaning_eq (w : BareNumeral) (n : Nat) :
    LowerBound.meaning w n = maxMeaning .ge w.toNat n := rfl

/-- Exact meaning is `maxMeaning .eq`. -/
theorem exact_meaning_eq (w : BareNumeral) (n : Nat) :
    Exact.meaning w n = maxMeaning .eq w.toNat n := rfl

/-- Lower-bound derives exact from at-least (Horn 1972; Bylinina & Nouwen 2020 §5). -/
theorem lowerBound_exactFromAtLeast :
    LowerBound.derivationalDirection = .exactFromAtLeast := by native_decide

/-- Exact derives at-least from exact (Kennedy 2015; Bylinina & Nouwen 2020 §6). -/
theorem exact_atLeastFromExact :
    Exact.derivationalDirection = .atLeastFromExact := by native_decide

-- ============================================================================
-- Section 7b: Type-Shifting (Kennedy 2015 §3.1)
-- ============================================================================

/-! ## De-Fregean Type-Shifting: Exact → Lower-Bound

Kennedy (2015, §3.1) shows that the lower-bound meaning of bare numerals can
be **derived** from the exact (de-Fregean) meaning via Partee's (1987) BE + iota
type-shifting operations. The de-Fregean meaning `max{n | D(n)} = m` is basic;
applying BE derives a property `λn. n = m`; applying iota and existential closure
yields `∃x[P(x) ∧ #(x) = m]`, which is the one-sided (lower-bound) truth condition.

Key fact: `maxMeaning .ge m n ↔ ∃ k ≥ m, maxMeaning .eq k n`. The lower-bound
reading says "the max is at least m", which holds iff there exists some k ≥ m
such that the max is exactly k. This is the formal content of the type-shift. -/

/-- Type-lower the exact meaning to get the lower-bound meaning.
    Corresponds to Kennedy's derivation via BE + iota + existential closure.
    `typeLower exact m n = true` iff `∃ k ≥ m, exact k n = true`.
    We compute this over a bounded range [m, maxN]. -/
def typeLower (exact : Nat → Nat → Bool) (maxN : Nat) (m : Nat) (n : Nat) : Bool :=
  (List.range (maxN + 1)).any λ k => k ≥ m && exact k n

/-- The lower-bound theory is derivable from the exact theory via type-shifting.
    For each bare numeral and each standard world, the lower-bound meaning
    equals the type-lowered exact meaning. This formalizes Kennedy's (2015) claim
    that `atLeastFromExact` is not just a label but a derivational fact:
    `maxMeaning .ge m n = typeLower (maxMeaning .eq) 3 m n` for standard worlds. -/
theorem lowerBound_from_exact_typeshift :
    standardWorlds.all λ n =>
      [BareNumeral.one, .two, .three].all λ w =>
        LowerBound.meaning w n == typeLower (maxMeaning .eq) 3 w.toNat n := by
  native_decide

/-- **Why this is the only type-shift**: the equivalence `∃ k ≥ m, n = k ↔ n ≥ m`
    is a tautology of linear orders on ℕ.

    Partee's BE extracts singletons from the GQ; existential closure binds the
    degree variable; the result is uniquely determined by the linear order on
    degrees. No other Partee shift + closure mode produces a different reading:
    - BE is the unique GQ→property lowering preserving content
    - Universal closure would give `∀ k ≥ m, n = k`, which is false for all n
      when there exist distinct k₁ ≥ m and k₂ ≥ m (i.e., always for m < maxN)
    - The equivalence is a fact about ℕ, not a design choice -/
theorem typeLower_uniqueness (m n : Nat) :
    (∃ k, k ≥ m ∧ n = k) ↔ n ≥ m := by
  constructor
  · rintro ⟨k, hk, rfl⟩; exact hk
  · intro h; exact ⟨n, h, rfl⟩

/-- Universal closure fails: `∀ k ≥ m, n = k` is unsatisfiable when there
    exist distinct k₁, k₂ ≥ m. This rules out the alternative to existential closure. -/
theorem universal_closure_fails :
    ¬(∃ n, ∀ k, k ≥ 2 → k ≤ 3 → n = k) := by
  rintro ⟨n, h⟩
  have h2 := h 2 (by omega) (by omega)
  have h3 := h 3 (by omega) (by omega)
  omega

-- ============================================================================
-- Section 7c: EXH–Type-Shifting Duality (Spector 2013 §6.2 vs Kennedy 2015 §3.1)
-- ============================================================================

/-! ## EXH and Type-Shifting Are Inverses

Spector (2013, §6.2) proposes that the exact reading of bare numerals arises from
a covert exhaustivity operator: `EXH(≥n) = ≥n ∧ ¬(≥n+1) = (=n)`. Kennedy (2015,
§3.1) proposes the reverse: the lower-bound reading arises from type-shifting the
exact meaning: `typeShift(=n) = ∃k≥n.(=k) = (≥n)`.

These are inverse operations on the same pair of meanings:

```
    exact ——typeShift——→ lower-bound
      ↑                       |
      └────────EXH────────────┘
```

For RSA, only the **pair** {exact, lower-bound} matters — the listener marginalizes
over both regardless of which is "basic". But type-shifting is preferable to EXH
because:

1. **Independently motivated**: Partee (1987) type-shifting applies to all NPs,
   not just numerals. It's part of the grammar regardless.
2. **No free parameters**: The lower-bound meaning is the unique output of
   type-shifting (proved: `typeLower_uniqueness`, `universal_closure_fails`).
   EXH requires specifying an alternative set.
3. **No distribution problems**: EXH must be stipulated as optionally present/absent
   at various syntactic positions. Type-shifted meanings are always grammatically
   available (Partee's universal).
4. **Quality filter does the work**: In RSA, the quality filter selects between
   type-shifted meanings based on the speaker's epistemic state. EXH insertion
   requires an additional mechanism for the listener to reason about. -/

/-- Scalar exhaustification for numerals.
    `exhNumeral m n` = "the max count is at least m AND NOT at least m+1"
    = "the max count is exactly m".
    This is Spector's (2013, §6.2) EXH applied to the numeral scalar alternative set
    {`≥k` : k is a numeral}. -/
def exhNumeral (_maxN : Nat) (m : Nat) (n : Nat) : Bool :=
  maxMeaning .ge m n && !(maxMeaning .ge (m + 1) n)

/-- **EXH(lower-bound) = exact**: Exhaustifying the lower-bound meaning
    produces the exact meaning. This is the forward direction of the duality. -/
theorem exh_lowerBound_eq_exact :
    standardWorlds.all λ n =>
      [BareNumeral.one, .two, .three].all λ w =>
        exhNumeral 3 w.toNat n == maxMeaning .eq w.toNat n := by
  native_decide

/-- **typeShift(exact) = lower-bound**: Type-shifting the exact meaning
    produces the lower-bound meaning. This is the backward direction.
    (Already proved as `lowerBound_from_exact_typeshift`; restated for symmetry.) -/
theorem typeShift_exact_eq_lowerBound :
    standardWorlds.all λ n =>
      [BareNumeral.one, .two, .three].all λ w =>
        typeLower (maxMeaning .eq) 3 w.toNat n == maxMeaning .ge w.toNat n := by
  native_decide

/-- **The EXH–type-shift round-trip is the identity on exact meanings.**
    `typeShift(EXH(typeShift(exact))) = typeShift(exact) = lower-bound`.
    Equivalently: starting from exact, type-shifting then exhaustifying
    recovers exact. -/
theorem exh_typeShift_roundtrip :
    standardWorlds.all λ n =>
      [BareNumeral.one, .two, .three].all λ w =>
        exhNumeral 3 w.toNat n == maxMeaning .eq w.toNat n &&
        typeLower (maxMeaning .eq) 3 w.toNat n == maxMeaning .ge w.toNat n := by
  native_decide

/-- **EXH is redundant given type-shifting.** The pair {exact, lower-bound}
    is obtainable from exact alone (via type-shifting) without EXH.
    Since type-shifting is independently motivated (Partee 1987) and produces
    the unique derived meaning (`typeLower_uniqueness`), EXH is not needed
    to generate the ambiguity that RSA marginalizes over.

    Formally: the set of meanings available under Kennedy + type-shifting
    equals the set available under LB + EXH. -/
theorem typeShift_subsumes_exh :
    standardWorlds.all λ n =>
      [BareNumeral.one, .two, .three].all λ w =>
        -- Kennedy + typeShift produces both exact and lower-bound
        (maxMeaning .eq w.toNat n == maxMeaning .eq w.toNat n) &&
        (typeLower (maxMeaning .eq) 3 w.toNat n == maxMeaning .ge w.toNat n) &&
        -- LB + EXH produces the same pair
        (exhNumeral 3 w.toNat n == maxMeaning .eq w.toNat n) &&
        (maxMeaning .ge w.toNat n == maxMeaning .ge w.toNat n) := by
  native_decide

-- ============================================================================
-- Section 8: Derived Properties
-- ============================================================================

/-- Strength ordering: `w₁` is stronger than `w₂` if `w₁` entails `w₂`. -/
def NumeralTheory.strongerThan (T : NumeralTheory) (w₁ w₂ : BareNumeral) : Prop :=
  ∀ n, T.meaning w₁ n → T.meaning w₂ n

/-- Decidable strength comparison. -/
def NumeralTheory.isStrongerThan (T : NumeralTheory) (w₁ w₂ : BareNumeral) : Bool :=
  T.worlds.all λ n => !T.meaning w₁ n || T.meaning w₂ n

/-- Count worlds compatible with an utterance. -/
def NumeralTheory.compatibleCount (T : NumeralTheory) (w : BareNumeral) : Nat :=
  (T.worlds.filter (T.meaning w)).length

/-- List of worlds compatible with an utterance. -/
def NumeralTheory.compatibleWorlds (T : NumeralTheory) (w : BareNumeral) : List Nat :=
  T.worlds.filter (T.meaning w)

/-- Is there semantic ambiguity for this utterance? -/
def NumeralTheory.hasAmbiguity (T : NumeralTheory) (w : BareNumeral) : Bool :=
  T.compatibleCount w > 1

/-- Monotonicity: larger numerals are stronger. -/
def NumeralTheory.isMonotonic (T : NumeralTheory) : Prop :=
  T.strongerThan .three .two ∧ T.strongerThan .two .one

/-- Decidable monotonicity check. -/
def NumeralTheory.checkMonotonic (T : NumeralTheory) : Bool :=
  T.isStrongerThan .three .two && T.isStrongerThan .two .one

/-- A theory is scalar if numerals form a Horn scale. -/
def NumeralTheory.isScalar (T : NumeralTheory) : Prop :=
  T.isMonotonic ∧
  ∀ w₁ w₂ : BareNumeral, T.strongerThan w₁ w₂ → T.strongerThan w₂ w₁ → w₁ = w₂

-- Lower-Bound Properties

/-- "two" is compatible with both 2 and 3 (ambiguity exists). -/
theorem lowerBound_two_ambiguous :
    LowerBound.compatibleWorlds .two = [2, 3] := by native_decide

/-- Lower-bound has ambiguity for "two". -/
theorem lowerBound_two_has_ambiguity :
    LowerBound.hasAmbiguity .two = true := by native_decide

/-- "three" entails "two" in lower-bound semantics. -/
theorem lowerBound_three_stronger_than_two :
    LowerBound.isStrongerThan .three .two = true := by native_decide

/-- "two" entails "one" in lower-bound semantics. -/
theorem lowerBound_two_stronger_than_one :
    LowerBound.isStrongerThan .two .one = true := by native_decide

/-- Lower-bound semantics is monotonic. -/
theorem lowerBound_is_monotonic :
    LowerBound.checkMonotonic = true := by native_decide

theorem lowerBound_one_count : LowerBound.compatibleCount .one = 3 := by native_decide
theorem lowerBound_two_count : LowerBound.compatibleCount .two = 2 := by native_decide
theorem lowerBound_three_count : LowerBound.compatibleCount .three = 1 := by native_decide

-- Exact Properties

/-- "two" is compatible with only world 2 (exact meaning). -/
theorem exact_two_worlds :
    Exact.compatibleWorlds .two = [2] := by native_decide

/-- No ambiguity for bare numerals. -/
theorem exact_no_ambiguity :
    Exact.hasAmbiguity .two = false := by native_decide

/-- Exact differs from LowerBound on bare numerals. -/
theorem exact_differs_from_lowerBound :
    Exact.compatibleWorlds .two ≠ LowerBound.compatibleWorlds .two := by native_decide

/-- The key divergence: ambiguity. -/
theorem ambiguity_differs :
    LowerBound.hasAmbiguity .two = true ∧
    Exact.hasAmbiguity .two = false := by native_decide

/-- Under Exact, only one world compatible. -/
theorem exact_no_rsa_strengthening_needed :
    Exact.compatibleCount .two = 1 := by native_decide

/-- Exact is not monotonic. -/
theorem exact_not_monotonic :
    Exact.checkMonotonic = false := by native_decide

theorem exact_three_not_stronger :
    Exact.isStrongerThan .three .two = false := by native_decide

/-- Summary: Exact vs LowerBound bare numerals. -/
theorem bare_numeral_summary :
    (Exact.hasAmbiguity .two = false) ∧
    (Exact.compatibleCount .two = 1) ∧
    (LowerBound.hasAmbiguity .two = true) ∧
    (LowerBound.compatibleCount .two = 2) := by native_decide

-- ============================================================================
-- Section 9: Comparison Infrastructure
-- ============================================================================

/-- Do two theories agree on utterance `w` in world `n`? -/
def theoriesAgreeAt (T₁ T₂ : NumeralTheory) (w : BareNumeral) (n : Nat) : Bool :=
  T₁.meaning w n == T₂.meaning w n

/-- Do two theories agree on utterance `w` across all worlds? -/
def theoriesAgreeOn (T₁ T₂ : NumeralTheory) (w : BareNumeral) : Bool :=
  T₁.worlds.all λ n => theoriesAgreeAt T₁ T₂ w n

/-- Find worlds where two theories diverge. -/
def divergingWorlds (T₁ T₂ : NumeralTheory) (w : BareNumeral) : List Nat :=
  T₁.worlds.filter λ n => !theoriesAgreeAt T₁ T₂ w n

/-- Do two theories agree on all utterances in all worlds? -/
def theoriesEquivalent (T₁ T₂ : NumeralTheory) : Bool :=
  T₁.utterances.all λ w => theoriesAgreeOn T₁ T₂ w

/-- Ambiguity difference. -/
def hasMoreAmbiguity (T₁ T₂ : NumeralTheory) (w : BareNumeral) : Bool :=
  T₁.compatibleCount w > T₂.compatibleCount w

-- Key Divergence Theorems

theorem lowerBound_exact_differ_on_two :
    LowerBound.meaning .two 3 = true ∧ Exact.meaning .two 3 = false := by native_decide

theorem divergence_at_three :
    divergingWorlds LowerBound Exact .two = [3] := by native_decide

theorem agreement_at_two :
    theoriesAgreeAt LowerBound Exact .two 2 = true := by native_decide

theorem theories_not_equivalent :
    theoriesEquivalent LowerBound Exact = false := by native_decide

-- Ambiguity Comparison

theorem lowerBound_more_ambiguous_two :
    hasMoreAmbiguity LowerBound Exact .two = true := by native_decide

theorem ambiguity_count_differs :
    LowerBound.compatibleCount .two = 2 ∧ Exact.compatibleCount .two = 1 := by native_decide

theorem ambiguity_presence_differs :
    LowerBound.hasAmbiguity .two = true ∧ Exact.hasAmbiguity .two = false := by native_decide

-- Monotonicity Comparison

theorem monotonicity_differs :
    LowerBound.checkMonotonic = true ∧ Exact.checkMonotonic = false := by native_decide

-- Implicature Potential

theorem only_lowerBound_supports_implicature :
    (LowerBound.compatibleCount .two > 1 ∧ LowerBound.isStrongerThan .three .two)
    ∧
    (Exact.compatibleCount .two = 1) := by native_decide

-- Empirical Adjudication (G&S 2013)

theorem lowerBound_consistent_with_cancellation :
    LowerBound.hasAmbiguity .two = true := by native_decide

theorem exact_inconsistent_with_cancellation :
    Exact.hasAmbiguity .two = false := by native_decide

theorem summary_comparison :
    (LowerBound.compatibleCount .two = 2 ∧ Exact.compatibleCount .two = 1)
    ∧
    (LowerBound.checkMonotonic = true ∧ Exact.checkMonotonic = false)
    ∧
    (LowerBound.meaning .two 3 = true ∧ Exact.meaning .two 3 = false) := by native_decide

-- Class A/B Modified Numeral Comparison

theorem classA_classB_diverge_on_bare_world :
    (maxMeaning .gt 3 3 = false) ∧
    (maxMeaning .ge 3 3 = true) ∧
    (maxMeaning .lt 3 3 = false) ∧
    (maxMeaning .le 3 3 = true) := by
  simp [maxMeaning]

theorem classB_strictly_weaker_than_bare :
    (maxMeaning .ge 3 3 = true) ∧
    (maxMeaning .ge 3 4 = true) ∧
    (maxMeaning .eq 3 4 = false) ∧
    (maxMeaning .gt 3 3 = false) := by
  simp [maxMeaning]

-- ============================================================================
-- Section 10: Grounding Theorems
-- ============================================================================

theorem bare_eq_exact_one (n : Nat) :
    bareMeaning 1 n = Exact.meaning .one n := rfl

theorem bare_eq_exact_two (n : Nat) :
    bareMeaning 2 n = Exact.meaning .two n := rfl

theorem bare_eq_exact_three (n : Nat) :
    bareMeaning 3 n = Exact.meaning .three n := rfl

theorem atLeast_eq_lowerBound_one (n : Nat) :
    atLeastMeaning 1 n = LowerBound.meaning .one n := rfl

theorem atLeast_eq_lowerBound_two (n : Nat) :
    atLeastMeaning 2 n = LowerBound.meaning .two n := rfl

theorem atLeast_eq_lowerBound_three (n : Nat) :
    atLeastMeaning 3 n = LowerBound.meaning .three n := rfl

-- GQT Bridge (Bylinina & Nouwen 2020)
--
-- The GQT numeral quantifiers in Quantifier.lean (`exactly_n_sem`, `at_least_n_sem`,
-- `at_most_n_sem`) compute the same truth values as `maxMeaning` applied to the
-- intersection cardinality. This connects B&N's quantifier view (type ⟨⟨e,t⟩,⟨e,t⟩,t⟩)
-- to the Kennedy maximality view (type ⟨d,t⟩) that `maxMeaning` implements.

open Semantics.Montague Semantics.Lexical.Determiner in
/-- GQT "at least n" agrees with `maxMeaning .ge` on intersection cardinality. -/
theorem gqt_atLeast_agrees (m : Model) [Quantifier.FiniteModel m]
    (n : Nat) (R S : m.Entity → Bool) :
    Quantifier.at_least_n_sem m n R S =
    maxMeaning .ge n (Quantifier.FiniteModel.elements.filter (λ x => R x && S x)).length := by
  rfl

open Semantics.Montague Semantics.Lexical.Determiner in
/-- GQT "at most n" agrees with `maxMeaning .le` on intersection cardinality. -/
theorem gqt_atMost_agrees (m : Model) [Quantifier.FiniteModel m]
    (n : Nat) (R S : m.Entity → Bool) :
    Quantifier.at_most_n_sem m n R S =
    maxMeaning .le n (Quantifier.FiniteModel.elements.filter (λ x => R x && S x)).length := by
  rfl

private theorem decide_eq_beq (a b : Nat) : decide (a = b) = (a == b) := by
  by_cases h : a = b <;> simp [h]

open Semantics.Montague Semantics.Lexical.Determiner in
/-- GQT "exactly n" agrees with `maxMeaning .eq` on intersection cardinality. -/
theorem gqt_exactly_agrees (m : Model) [Quantifier.FiniteModel m]
    (n : Nat) (R S : m.Entity → Bool) :
    Quantifier.exactly_n_sem m n R S =
    maxMeaning .eq n (Quantifier.FiniteModel.elements.filter (λ x => R x && S x)).length := by
  unfold Quantifier.exactly_n_sem maxMeaning
  exact decide_eq_beq _ _

-- ============================================================================
-- Section 11: CumminsFranke Bridge
-- ============================================================================

/-- "More than m" via maximality = `n > m`. -/
theorem moreThan_eq_cumminsFranke (m n : Nat) :
    moreThanMeaning m n = decide (n > m) := by
  simp [moreThanMeaning, maxMeaning]

-- ============================================================================
-- Section 12: Aliases (used across NegationScope, Operations, RSA)
-- ============================================================================

abbrev Bilateral := Exact
abbrev DeFregean := Exact
abbrev NumWord := BareNumeral
def lowerBoundMeaning (w : BareNumeral) (n : Nat) : Bool := LowerBound.meaning w n
def bilateralMeaning (w : BareNumeral) (n : Nat) : Bool := Exact.meaning w n
abbrev deFregeanMeaning := bilateralMeaning
abbrev exactMeaning := bilateralMeaning

-- ============================================================================
-- Section 13: Verification
-- ============================================================================

theorem bare_exact_match : bareMeaning 3 3 = true := by native_decide
theorem bare_rejects_lower : bareMeaning 3 2 = false := by native_decide
theorem bare_rejects_higher : bareMeaning 3 4 = false := by native_decide

theorem moreThan_above : moreThanMeaning 3 4 = true := by native_decide
theorem moreThan_equal : moreThanMeaning 3 3 = false := by native_decide

theorem fewerThan_below : fewerThanMeaning 3 2 = true := by native_decide
theorem fewerThan_equal : fewerThanMeaning 3 3 = false := by native_decide

theorem atLeast_equal : atLeastMeaning 3 3 = true := by native_decide
theorem atLeast_above : atLeastMeaning 3 4 = true := by native_decide
theorem atLeast_below : atLeastMeaning 3 2 = false := by native_decide

theorem atMost_equal : atMostMeaning 3 3 = true := by native_decide
theorem atMost_below : atMostMeaning 3 2 = true := by native_decide
theorem atMost_above : atMostMeaning 3 4 = false := by native_decide

-- ============================================================================
-- Section 14: Core.Scale Bridge Theorems
-- ============================================================================

/-! ### maxMeaning as ℕ-pullback of Core.Scale degree properties

`maxMeaning` computes over `ℕ` independently — it works, but the degree
properties in `Core.Scale` (`atLeastDeg`, `moreThanDeg`, etc.) are the
canonical scale-level definitions. These bridge theorems prove that
`maxMeaning` is the `Bool`/decidable restriction of Core.Scale degree
properties, connecting ℕ-level computation to scale-level definitions.

This means density predictions (`moreThan_noMaxInf`, `atLeast_hasMaxInf`)
flow compositionally from `Core.Scale` through numeral semantics. -/

open Core.Scale in
/-- `maxMeaning .ge m n = true` iff `atLeastDeg id m n`. -/
theorem maxMeaning_ge_iff_atLeastDeg (m n : ℕ) :
    maxMeaning .ge m n = true ↔ atLeastDeg id m n := by
  simp [maxMeaning, atLeastDeg]

open Core.Scale in
/-- `maxMeaning .gt m n = true` iff `moreThanDeg id m n`. -/
theorem maxMeaning_gt_iff_moreThanDeg (m n : ℕ) :
    maxMeaning .gt m n = true ↔ moreThanDeg id m n := by
  simp [maxMeaning, moreThanDeg]

open Core.Scale in
/-- `maxMeaning .eq m n = true` iff `eqDeg id m n`. -/
theorem maxMeaning_eq_iff_eqDeg (m n : ℕ) :
    maxMeaning .eq m n = true ↔ eqDeg id m n := by
  simp [maxMeaning, eqDeg]

open Core.Scale in
/-- `maxMeaning .le m n = true` iff `atMostDeg id m n`. -/
theorem maxMeaning_le_iff_atMostDeg (m n : ℕ) :
    maxMeaning .le m n = true ↔ atMostDeg id m n := by
  simp [maxMeaning, atMostDeg]

open Core.Scale in
/-- `maxMeaning .lt m n = true` iff `lessThanDeg id m n`. -/
theorem maxMeaning_lt_iff_lessThanDeg (m n : ℕ) :
    maxMeaning .lt m n = true ↔ lessThanDeg id m n := by
  simp [maxMeaning, lessThanDeg]

-- ============================================================================
-- Section 14: Numeral Expression Semantics (from HasDegree)
-- ============================================================================

open Core.Scale in

/-- Literal/exact semantics for numeral expressions.
    "six feet" is true of x iff μ_height(x) = 183. -/
def numeralExact {E : Type} [HasDegree E] (stated : ℚ) (entity : E) : Bool :=
  HasDegree.degree entity == stated

open Core.Scale in

/-- "At least n" semantics (lower-bound reading). -/
def numeralAtLeast {E : Type} [HasDegree E] (threshold : ℚ) (entity : E) : Bool :=
  HasDegree.degree entity ≥ threshold

open Core.Scale in

/-- Approximate match with tolerance (for vagueness/imprecision). -/
def numeralApprox {E : Type} [HasDegree E] (stated : ℚ) (tolerance : ℚ) (entity : E) : Bool :=
  let actual := HasDegree.degree entity
  (stated - tolerance ≤ actual) && (actual ≤ stated + tolerance)

-- ============================================================================
-- Section 15: Measure Predicates (Compositional Sentence Semantics)
-- ============================================================================

open Core.Scale in

/-- A measure predicate maps entities to degrees along some dimension. -/
structure MeasurePredicate (E : Type) where
  dimension : String
  μ : E → ℚ

open Core.Scale in

/-- Construct a MeasurePredicate from a HasDegree instance -/
def MeasurePredicate.fromHasDegree (E : Type) [HasDegree E] (dim : String) : MeasurePredicate E :=
  { dimension := dim, μ := HasDegree.degree }

/-- A degree phrase denotes a specific degree value.
    "1000 dollars" denotes the degree 1000 (in dollar units). -/
structure DegreePhrase where
  value : ℚ
  unit : String := ""
  deriving Repr, DecidableEq, BEq

/-- Construct a degree phrase from a rational number -/
def DegreePhrase.ofRat (n : ℚ) (unit : String := "") : DegreePhrase :=
  { value := n, unit := unit }

/-- Construct a degree phrase from a natural number -/
def DegreePhrase.ofNat (n : Nat) (unit : String := "") : DegreePhrase :=
  { value := n, unit := unit }

/-- Compositional semantics for measure sentences.
    ⟦X measure-pred degree-phrase⟧ = μ(X) = d -/
def measureSentence {E : Type} (pred : MeasurePredicate E) (entity : E) (deg : DegreePhrase) : Bool :=
  pred.μ entity == deg.value

open Core.Scale in

/-- Compositional semantics using HasDegree directly. -/
def measureSentence' {E : Type} [HasDegree E] (entity : E) (deg : DegreePhrase) : Bool :=
  HasDegree.degree entity == deg.value

-- Grounding Theorems

open Core.Scale in

/-- The compositional measure sentence semantics equals the simple numeral check. -/
theorem measureSentence_eq_numeralExact {E : Type} [HasDegree E]
    (entity : E) (deg : DegreePhrase) :
    measureSentence' entity deg = numeralExact deg.value entity := rfl

open Core.Scale in

/-- MeasurePredicate.fromHasDegree produces the HasDegree measure function. -/
theorem fromHasDegree_μ {E : Type} [HasDegree E] (dim : String) :
    (MeasurePredicate.fromHasDegree E dim).μ = HasDegree.degree := rfl

open Core.Scale in

/-- Measure sentences compose correctly with HasDegree-derived predicates. -/
theorem measureSentence_fromHasDegree {E : Type} [HasDegree E]
    (dim : String) (entity : E) (deg : DegreePhrase) :
    measureSentence (MeasurePredicate.fromHasDegree E dim) entity deg =
    numeralExact deg.value entity := rfl

-- ============================================================================
-- Section 16: Numeral with Precision Mode
-- ============================================================================

open Semantics.Lexical.Numeral.Precision in

/-- Numeral semantics with precision mode.
    "1000 dollars" under exact mode: true iff cost = 1000
    "1000 dollars" under approximate mode: true iff Round(cost) = 1000 -/
def numeralWithPrecision {E : Type} [Core.Scale.HasDegree E]
    (stated : ℚ) (entity : E) (mode : PrecisionMode) (base : ℚ := 10) : Bool :=
  matchesPrecision mode stated (Core.Scale.HasDegree.degree entity) base

end Semantics.Lexical.Numeral
