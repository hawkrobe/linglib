import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Numerals.Precision
import Linglib.Theories.Semantics.Quantification.Quantifier

/-!
# Unified Numeral Semantics
@cite{blok-2015} @cite{goodman-stuhlmuller-2013} @cite{horn-1972} @cite{kennedy-2015} @cite{hackl-2000} @cite{link-1983} @cite{spector-2013}

Consolidates numeral theory infrastructure into a single module. Modified
numeral meanings are five named `Prop` functions (`bareMeaning`,
`moreThanMeaning`, `fewerThanMeaning`, `atLeastMeaning`, `atMostMeaning`),
each a thin wrapper over the corresponding mathlib `Nat` relation, with
`Decidable` instances derived from `Nat`'s. The only theory disagreement is
the bare-numeral semantics:

| Theory      | Bare "three" | `bareSemantics`     |
|-------------|--------------|---------------------|
| Lower-bound | ≥3           | `atLeastMeaning`    |
| Exact       | =3           | `bareMeaning`       |

Modified numerals are theory-independent — everyone agrees "more than 3" means `> 3`.

## Sections

1. Modifier classification (Class A/B, Bound direction)
2. Numeral meaning functions (5 named Bool wrappers)
3. BareNumeral type and NumeralExpr
4. Alternative sets (Kennedy §4.1)
5. Class A/B theorems, anti-Horn-scale argument
6. Theory parameterization (`NumeralTheory`)
7. Theory instances (`LowerBound`, `Exact`)
7b. Type-shifting (Kennedy §3.1)
7c. EXH-typeshift duality (Spector §6.2)
8. Derived properties (ambiguity, monotonicity, RSA)
9. Comparison infrastructure and theorems
10. GQT bridge theorems
11. CumminsFranke bridge
12. Aliases
13. Verification
14. Core.Scale Bridge Theorems (Bool ↔ Prop)
15. Cardinality as ℚ-valued Degree (`HasDegree Nat`)
16. Numeral Expression Semantics (HasDegree-based)
17. Measure Predicates (compositional sentence semantics)
18. Numeral with Precision Mode

-/

namespace Semantics.Numerals

-- ============================================================================
-- Section 1: Modifier Classification
-- ============================================================================

/-- Class A (strict) vs Class B (non-strict) modified numerals.

The distinction predicts ignorance implicature patterns:
- Class A (>, <): EXCLUDE the bare-numeral world → no ignorance
- Class B (≥, ≤): INCLUDE the bare-numeral world → ignorance -/
inductive ModifierClass where
  | classA  -- strict: >, <
  | classB  -- non-strict: ≥, ≤
  deriving Repr, DecidableEq

/-- Upper vs lower bound direction.

- `.upper`: constrains from above (at most, fewer than)
- `.lower`: constrains from below (at least, more than) -/
inductive BoundDirection where
  | upper  -- at most, fewer than, up to
  | lower  -- at least, more than, from...on
  deriving Repr, DecidableEq

-- ============================================================================
-- Section 2: Numeral Meaning Functions
-- ============================================================================

/-! Five named meanings, one per modifier. Each is a thin `Prop` wrapper over
the corresponding mathlib relation on `Nat`. They capture Kennedy's

  ⟦modifier m⟧ = λP. max{d | #P ≥ d} REL m

where `n` plays the role of `max{d | #P ≥ d}` and `m` is the numeral.
`bareMeaning` is the exact (Kennedy) reading; the lower-bound (Horn) reading
of bare numerals is `atLeastMeaning`, exposed via the `NumeralTheory`
parameterization in §6. Each definition unfolds to a mathlib `Nat` relation,
so the corresponding `Decidable` instance is inferred from `Nat`'s instances
and unfolded definitions. -/

/-- Bare numeral meaning (exact reading): max = m. -/
@[simp] def bareMeaning (m n : Nat) : Prop := n = m

/-- "More than m": max > m. -/
@[simp] def moreThanMeaning (m n : Nat) : Prop := n > m

/-- "Fewer than m": max < m. -/
@[simp] def fewerThanMeaning (m n : Nat) : Prop := n < m

/-- "At least m": max ≥ m. -/
@[simp] def atLeastMeaning (m n : Nat) : Prop := n ≥ m

/-- "At most m": max ≤ m. -/
@[simp] def atMostMeaning (m n : Nat) : Prop := n ≤ m

instance (m n : Nat) : Decidable (bareMeaning m n) := by unfold bareMeaning; infer_instance
instance (m n : Nat) : Decidable (moreThanMeaning m n) := by unfold moreThanMeaning; infer_instance
instance (m n : Nat) : Decidable (fewerThanMeaning m n) := by unfold fewerThanMeaning; infer_instance
instance (m n : Nat) : Decidable (atLeastMeaning m n) := by unfold atLeastMeaning; infer_instance
instance (m n : Nat) : Decidable (atMostMeaning m n) := by unfold atMostMeaning; infer_instance

-- ============================================================================
-- Section 3: BareNumeral and NumeralExpr
-- ============================================================================

/-- Bare numeral utterances (one through five). -/
inductive BareNumeral where
  | one | two | three | four | five
  deriving DecidableEq, Repr, Inhabited

/-- Convert BareNumeral to its numeric value. -/
def BareNumeral.toNat : BareNumeral → Nat
  | .one => 1 | .two => 2 | .three => 3 | .four => 4 | .five => 5

instance : ToString BareNumeral where
  toString
    | .one => "one" | .two => "two" | .three => "three"
    | .four => "four" | .five => "five"

/-- A numeral expression: a bare numeral or one of the four modifications. -/
inductive NumeralExpr where
  | bare (n : Nat)
  | atLeast (n : Nat)
  | moreThan (n : Nat)
  | atMost (n : Nat)
  | fewerThan (n : Nat)
  deriving Repr, DecidableEq

/-- Meaning of a numeral expression, parameterized by the bare-numeral
    semantics (theory choice: Kennedy `bareMeaning` or Horn `atLeastMeaning`). -/
def NumeralExpr.meaning (bare : Nat → Nat → Prop) : NumeralExpr → Nat → Prop
  | .bare m, n => bare m n
  | .atLeast m, n => atLeastMeaning m n
  | .moreThan m, n => moreThanMeaning m n
  | .atMost m, n => atMostMeaning m n
  | .fewerThan m, n => fewerThanMeaning m n

-- ============================================================================
-- Section 4: Alternative Sets (Kennedy §4.1)
-- ============================================================================

/-- A numeral alternative in Kennedy's framework.

Instead of the traditional Horn scale ⟨1, 2, 3,...⟩, the relevant
alternatives for numeral n are:

  {bare n, more than n, at least n} (lower-bound direction)
  {bare n, fewer than n, at most n} (upper-bound direction) -/
inductive NumeralAlternative where
  | bare (n : Nat)
  | atLeast (n : Nat)
  | moreThan (n : Nat)
  | atMost (n : Nat)
  | fewerThan (n : Nat)
  deriving Repr, DecidableEq

/-- Lower-bound alternative set. -/
def lowerAlternatives (n : Nat) : List NumeralAlternative :=
  [.bare n, .moreThan n, .atLeast n]

/-- Upper-bound alternative set. -/
def upperAlternatives (n : Nat) : List NumeralAlternative :=
  [.bare n, .fewerThan n, .atMost n]

/-- Get the meaning of a numeral alternative. -/
def NumeralAlternative.meaning : NumeralAlternative → Nat → Prop
  | .bare m => bareMeaning m
  | .atLeast m => atLeastMeaning m
  | .moreThan m => moreThanMeaning m
  | .atMost m => atMostMeaning m
  | .fewerThan m => fewerThanMeaning m

instance (a : NumeralAlternative) (n : Nat) : Decidable (a.meaning n) := by
  cases a <;> simp only [NumeralAlternative.meaning] <;> infer_instance

-- ============================================================================
-- Section 5: Class A/B Theorems and Anti-Horn-Scale Argument
-- ============================================================================

/-- Class A modifiers EXCLUDE the bare-numeral world. -/
theorem classA_gt_excludes_bare (m : Nat) :
    ¬ moreThanMeaning m m := by
  simp only [moreThanMeaning, gt_iff_lt, Nat.lt_irrefl, not_false_eq_true]

theorem classA_lt_excludes_bare (m : Nat) :
    ¬ fewerThanMeaning m m := by
  simp only [fewerThanMeaning, Nat.lt_irrefl, not_false_eq_true]

/-- Class B modifiers INCLUDE the bare-numeral world. -/
theorem classB_ge_includes_bare (m : Nat) :
    atLeastMeaning m m := by
  simp only [atLeastMeaning, ge_iff_le, le_refl]

theorem classB_le_includes_bare (m : Nat) :
    atMostMeaning m m := by
  simp only [atMostMeaning, le_refl]

/-- Bare numeral entails "at least n" (Class B ≥). -/
theorem classB_entailed_by_bare (m n : Nat) :
    bareMeaning m n → atLeastMeaning m n := by
  simp only [bareMeaning, atLeastMeaning, ge_iff_le]
  omega

/-- Bare numeral does NOT entail "more than n" (Class A >). -/
theorem classA_not_entailed_by_bare (m : Nat) :
    bareMeaning m m ∧ ¬ moreThanMeaning m m := by
  refine ⟨?_, ?_⟩
  · simp only [bareMeaning]
  · exact classA_gt_excludes_bare m

/-- Exact bare numerals are NOT monotonic. -/
theorem bare_not_monotonic :
    bareMeaning 3 3 ∧ ¬ bareMeaning 2 3 := by decide

/-- Bare numerals do not form a traditional Horn scale. -/
theorem numerals_not_horn_scalar :
    (bareMeaning 3 3 ∧ ¬ bareMeaning 2 3) ∧
    (bareMeaning 2 2 ∧ ¬ bareMeaning 3 2) := by decide

/-- "At least n" is strictly weaker than "bare n" (under bilateral semantics). -/
theorem atLeast_strictly_weaker_than_bare :
    (bareMeaning 3 3 ∧ atLeastMeaning 3 3) ∧
    (atLeastMeaning 3 4 ∧ ¬ bareMeaning 3 4) := by decide

/-- "More than n" and "bare n" have disjoint denotations. -/
theorem moreThan_disjoint_from_bare :
    (bareMeaning 3 3 ∧ ¬ moreThanMeaning 3 3) ∧
    (¬ bareMeaning 3 4 ∧ moreThanMeaning 3 4) := by decide

-- ============================================================================
-- Section 6: Theory Parameterization
-- ============================================================================

/-- Standard list of numeral utterances for RSA scenarios. -/
def standardNumWords : List BareNumeral := [.one, .two, .three]

/-- Standard list of world states (cardinalities 0-3). -/
def standardWorlds : List Nat := [0, 1, 2, 3]

/-- Derivational direction for the at-least/exactly relationship (@cite{bylinina-nouwen-2020} §5–6).

The four views on numeral semantics differ in which reading is basic:
- `exactFromAtLeast`: base meaning is at-least (≥n), exact derived via EXH or scalar implicature.
  Corresponds to `LowerBound` / @cite{horn-1972} / the modifier–number view.
- `atLeastFromExact`: base meaning is exact (=n), at-least derived via type-shift or
  relaxing maximality. Corresponds to `Exact` / @cite{kennedy-2015} / the degree quantifier view. -/
inductive DerivationalDirection where
  | exactFromAtLeast
  | atLeastFromExact
  deriving DecidableEq, Repr

/--
A semantic theory for bare number words.

The theory is parameterized by `bareSemantics` — the meaning function for bare
numerals. The two canonical instances (§7) supply `atLeastMeaning` (Horn,
lower-bound) or `bareMeaning` (Kennedy, exact). Modified numerals are
theory-independent and route through the named `*Meaning` functions of §2.
-/
structure NumeralTheory where
  /-- Name of the theory -/
  name : String
  /-- Academic citation -/
  citation : String
  /-- Meaning function for bare numerals (one of `bareMeaning` / `atLeastMeaning`). -/
  bareSemantics : Nat → Nat → Prop
  /-- Decidability witness for `bareSemantics` (so derived `compatibleCount`/`isStrongerThan`
      can compute by `decide`). -/
  bareDec : ∀ m n, Decidable (bareSemantics m n)
  /-- Which reading is basic; the other is derived (EXH or type-shift). -/
  derivationalDirection : DerivationalDirection
  /-- Utterances to consider (default: one, two, three) -/
  utterances : List BareNumeral := standardNumWords
  /-- World states to consider (default: 0, 1, 2, 3) -/
  worlds : List Nat := standardWorlds

attribute [instance] NumeralTheory.bareDec

/-- Derived bare-numeral meaning. -/
def NumeralTheory.meaning (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Prop :=
  T.bareSemantics w.toNat n

instance (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Decidable (T.meaning w n) := by
  unfold NumeralTheory.meaning; infer_instance

/-- Derived meaning for general numeral expressions. -/
def NumeralTheory.exprMeaning (T : NumeralTheory) (e : NumeralExpr) (n : Nat) : Prop :=
  e.meaning T.bareSemantics n

instance (T : NumeralTheory) (e : NumeralExpr) (n : Nat) : Decidable (T.exprMeaning e n) := by
  unfold NumeralTheory.exprMeaning NumeralExpr.meaning
  cases e <;> infer_instance

-- ============================================================================
-- Section 7: Theory Instances
-- ============================================================================

/-- Lower-bound numeral theory.

"Two" means ≥2. The exact interpretation emerges via scalar implicature. -/
def LowerBound : NumeralTheory where
  name := "Lower-bound"
  citation := "Horn 1972"
  bareSemantics := atLeastMeaning
  bareDec := fun _ _ => inferInstance
  derivationalDirection := .exactFromAtLeast

/-- Exact numeral theory.

"Two" means =2 (via maximality). No RSA strengthening needed for bare numerals. -/
def Exact : NumeralTheory where
  name := "Exact"
  citation := "Kennedy 2015"
  bareSemantics := bareMeaning
  bareDec := fun _ _ => inferInstance
  derivationalDirection := .atLeastFromExact

/-- Lower-bound meaning is `atLeastMeaning`. -/
theorem lowerBound_meaning_eq (w : BareNumeral) (n : Nat) :
    LowerBound.meaning w n = atLeastMeaning w.toNat n := rfl

/-- Exact meaning is `bareMeaning`. -/
theorem exact_meaning_eq (w : BareNumeral) (n : Nat) :
    Exact.meaning w n = bareMeaning w.toNat n := rfl

-- ============================================================================
-- Section 7b: Type-Shifting (@cite{kennedy-2015} §3.1)
-- ============================================================================

/-! ## De-Fregean Type-Shifting: Exact → Lower-Bound

@cite{kennedy-2015} shows that the lower-bound meaning of bare numerals can
be **derived** from the exact (de-Fregean) meaning via @cite{partee-1987}'s BE + iota
type-shifting operations. The de-Fregean meaning `max{n | D(n)} = m` is basic;
applying BE derives a property `λn. n = m`; applying iota and existential closure
yields `∃x[P(x) ∧ #(x) = m]`, which is the one-sided (lower-bound) truth condition.

Key fact: `atLeastMeaning m n ↔ ∃ k ≥ m, bareMeaning k n`. The lower-bound
reading says "the max is at least m", which holds iff there exists some k ≥ m
such that the max is exactly k. This is the formal content of the type-shift. -/

/-- Type-lower the exact meaning to get the lower-bound meaning.
    Corresponds to Kennedy's derivation via BE + iota + existential closure.
    `typeLower exact m n` iff `∃ k ≥ m, exact k n`.
    We compute this over a bounded range [m, maxN]. -/
def typeLower (exact : Nat → Nat → Prop) (maxN : Nat) (m : Nat) (n : Nat) : Prop :=
  ∃ k ∈ List.range (maxN + 1), k ≥ m ∧ exact k n

instance (exact : Nat → Nat → Prop) [∀ k n, Decidable (exact k n)]
    (maxN m n : Nat) : Decidable (typeLower exact maxN m n) := by
  unfold typeLower; infer_instance

/-- The lower-bound theory is derivable from the exact theory via type-shifting.
    For each bare numeral and each standard world, the lower-bound meaning
    equals the type-lowered exact meaning. This formalizes @cite{kennedy-2015}'s claim
    that `atLeastFromExact` is not just a label but a derivational fact:
    `atLeastMeaning m n ↔ typeLower bareMeaning 3 m n` for standard worlds. -/
theorem lowerBound_from_exact_typeshift :
    ∀ n ∈ standardWorlds, ∀ w ∈ [BareNumeral.one, .two, .three],
      LowerBound.meaning w n ↔ typeLower bareMeaning 3 w.toNat n := by
  decide

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
-- Section 7c: EXH–Type-Shifting Duality (@cite{spector-2013} §6.2 vs @cite{kennedy-2015})
-- ============================================================================

/-! ## EXH and Type-Shifting Are Inverses

@cite{spector-2013} (§6.2) presents an approach (from @cite{chierchia-fox-spector-2012}) where the exact reading of bare numerals arises from
a covert exhaustivity operator: `EXH(≥n) = ≥n ∧ ¬(≥n+1) = (=n)`. @cite{kennedy-2015} proposes the reverse: the lower-bound reading arises from type-shifting the
exact meaning: `typeShift(=n) = ∃k≥n.(=k) = (≥n)`.

These are inverse operations on the same pair of meanings:

```
    exact ——typeShift——→ lower-bound
      ↑ |
      └────────EXH────────────┘
```

For RSA, only the **pair** {exact, lower-bound} matters — the listener marginalizes
over both regardless of which is "basic". But type-shifting is preferable to EXH
because:

1. **Independently motivated**: @cite{partee-1987} type-shifting applies to all NPs,
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
    This is the EXH from @cite{spector-2013} (§6.2) applied to the numeral scalar alternative set
    {`≥k` : k is a numeral}. -/
def exhNumeral (_maxN : Nat) (m : Nat) (n : Nat) : Prop :=
  atLeastMeaning m n ∧ ¬ atLeastMeaning (m + 1) n

instance (maxN m n : Nat) : Decidable (exhNumeral maxN m n) := by
  unfold exhNumeral; infer_instance

/-- **EXH(lower-bound) = exact**: Exhaustifying the lower-bound meaning
    produces the exact meaning. This is the forward direction of the duality. -/
theorem exh_lowerBound_eq_exact :
    ∀ n ∈ standardWorlds, ∀ w ∈ [BareNumeral.one, .two, .three],
      exhNumeral 3 w.toNat n ↔ bareMeaning w.toNat n := by
  decide

/-- **typeShift(exact) = lower-bound**: Type-shifting the exact meaning
    produces the lower-bound meaning. This is the backward direction.
    (Already proved as `lowerBound_from_exact_typeshift`; restated for symmetry.) -/
theorem typeShift_exact_eq_lowerBound :
    ∀ n ∈ standardWorlds, ∀ w ∈ [BareNumeral.one, .two, .three],
      typeLower bareMeaning 3 w.toNat n ↔ atLeastMeaning w.toNat n := by
  decide

/-- **The EXH–type-shift round-trip is the identity on exact meanings.**
    `typeShift(EXH(typeShift(exact))) = typeShift(exact) = lower-bound`.
    Equivalently: starting from exact, type-shifting then exhaustifying
    recovers exact. -/
theorem exh_typeShift_roundtrip :
    ∀ n ∈ standardWorlds, ∀ w ∈ [BareNumeral.one, .two, .three],
      (exhNumeral 3 w.toNat n ↔ bareMeaning w.toNat n) ∧
      (typeLower bareMeaning 3 w.toNat n ↔ atLeastMeaning w.toNat n) := by
  decide

/-- **EXH is redundant given type-shifting.** The pair {exact, lower-bound}
    is obtainable from exact alone (via type-shifting) without EXH.
    Since type-shifting is independently motivated and produces
    the unique derived meaning (`typeLower_uniqueness`), EXH is not needed
    to generate the ambiguity that RSA marginalizes over.

    Formally: the set of meanings available under Kennedy + type-shifting
    equals the set available under LB + EXH. -/
theorem typeShift_subsumes_exh :
    ∀ n ∈ standardWorlds, ∀ w ∈ [BareNumeral.one, .two, .three],
      -- Kennedy + typeShift produces both exact and lower-bound
      (bareMeaning w.toNat n ↔ bareMeaning w.toNat n) ∧
      (typeLower bareMeaning 3 w.toNat n ↔ atLeastMeaning w.toNat n) ∧
      -- LB + EXH produces the same pair
      (exhNumeral 3 w.toNat n ↔ bareMeaning w.toNat n) ∧
      (atLeastMeaning w.toNat n ↔ atLeastMeaning w.toNat n) := by
  decide

-- ============================================================================
-- Section 8: Derived Properties
-- ============================================================================

/-- Strength ordering: `w₁` is stronger than `w₂` if `w₁` entails `w₂`. -/
def NumeralTheory.strongerThan (T : NumeralTheory) (w₁ w₂ : BareNumeral) : Prop :=
  ∀ n, T.meaning w₁ n → T.meaning w₂ n

/-- Decidable strength comparison over `T.worlds` (used by `decide` proofs over
    finite world lists; quantifies only over `T.worlds`). -/
def NumeralTheory.isStrongerThan (T : NumeralTheory) (w₁ w₂ : BareNumeral) : Prop :=
  ∀ n ∈ T.worlds, T.meaning w₁ n → T.meaning w₂ n

instance (T : NumeralTheory) (w₁ w₂ : BareNumeral) : Decidable (T.isStrongerThan w₁ w₂) := by
  unfold NumeralTheory.isStrongerThan; infer_instance

/-- List of worlds compatible with an utterance. -/
def NumeralTheory.compatibleWorlds (T : NumeralTheory) (w : BareNumeral) : List Nat :=
  T.worlds.filter (fun n => decide (T.meaning w n))

/-- Count worlds compatible with an utterance. -/
def NumeralTheory.compatibleCount (T : NumeralTheory) (w : BareNumeral) : Nat :=
  (T.compatibleWorlds w).length

/-- Is there semantic ambiguity for this utterance? -/
def NumeralTheory.hasAmbiguity (T : NumeralTheory) (w : BareNumeral) : Prop :=
  T.compatibleCount w > 1

instance (T : NumeralTheory) (w : BareNumeral) : Decidable (T.hasAmbiguity w) := by
  unfold NumeralTheory.hasAmbiguity; infer_instance

/-- Monotonicity: larger numerals are stronger. -/
def NumeralTheory.isMonotonic (T : NumeralTheory) : Prop :=
  T.strongerThan .three .two ∧ T.strongerThan .two .one

/-- Decidable monotonicity check (quantifies over `T.worlds` rather than all of ℕ). -/
def NumeralTheory.checkMonotonic (T : NumeralTheory) : Prop :=
  T.isStrongerThan .three .two ∧ T.isStrongerThan .two .one

instance (T : NumeralTheory) : Decidable T.checkMonotonic := by
  unfold NumeralTheory.checkMonotonic; infer_instance

/-- A theory is scalar if numerals form a Horn scale. -/
def NumeralTheory.isScalar (T : NumeralTheory) : Prop :=
  T.isMonotonic ∧
  ∀ w₁ w₂ : BareNumeral, T.strongerThan w₁ w₂ → T.strongerThan w₂ w₁ → w₁ = w₂

-- Lower-Bound Properties

/-- "two" is compatible with both 2 and 3 (ambiguity exists). -/
theorem lowerBound_two_ambiguous :
    LowerBound.compatibleWorlds .two = [2, 3] := by decide

/-- Lower-bound has ambiguity for "two". -/
theorem lowerBound_two_has_ambiguity :
    LowerBound.hasAmbiguity .two := by decide

/-- "three" entails "two" in lower-bound semantics. -/
theorem lowerBound_three_stronger_than_two :
    LowerBound.isStrongerThan .three .two := by decide

/-- "two" entails "one" in lower-bound semantics. -/
theorem lowerBound_two_stronger_than_one :
    LowerBound.isStrongerThan .two .one := by decide

/-- Lower-bound semantics is monotonic. -/
theorem lowerBound_is_monotonic :
    LowerBound.checkMonotonic := by decide

theorem lowerBound_one_count : LowerBound.compatibleCount .one = 3 := by decide
theorem lowerBound_two_count : LowerBound.compatibleCount .two = 2 := by decide
theorem lowerBound_three_count : LowerBound.compatibleCount .three = 1 := by decide

-- Exact Properties

/-- "two" is compatible with only world 2 (exact meaning). -/
theorem exact_two_worlds :
    Exact.compatibleWorlds .two = [2] := by decide

/-- No ambiguity for bare numerals. -/
theorem exact_no_ambiguity :
    ¬ Exact.hasAmbiguity .two := by decide

/-- Exact differs from LowerBound on bare numerals. -/
theorem exact_differs_from_lowerBound :
    Exact.compatibleWorlds .two ≠ LowerBound.compatibleWorlds .two := by decide

/-- The key divergence: ambiguity. -/
theorem ambiguity_differs :
    LowerBound.hasAmbiguity .two ∧ ¬ Exact.hasAmbiguity .two := by decide

/-- Under Exact, only one world compatible. -/
theorem exact_no_rsa_strengthening_needed :
    Exact.compatibleCount .two = 1 := by decide

/-- Exact is not monotonic. -/
theorem exact_not_monotonic :
    ¬ Exact.checkMonotonic := by decide

theorem exact_three_not_stronger :
    ¬ Exact.isStrongerThan .three .two := by decide

/-- Summary: Exact vs LowerBound bare numerals. -/
theorem bare_numeral_summary :
    (¬ Exact.hasAmbiguity .two) ∧
    (Exact.compatibleCount .two = 1) ∧
    (LowerBound.hasAmbiguity .two) ∧
    (LowerBound.compatibleCount .two = 2) := by decide

-- ============================================================================
-- Section 9: Comparison Infrastructure
-- ============================================================================

/-- Do two theories agree on utterance `w` in world `n`? -/
def theoriesAgreeAt (T₁ T₂ : NumeralTheory) (w : BareNumeral) (n : Nat) : Prop :=
  T₁.meaning w n ↔ T₂.meaning w n

instance (T₁ T₂ : NumeralTheory) (w : BareNumeral) (n : Nat) :
    Decidable (theoriesAgreeAt T₁ T₂ w n) := by
  unfold theoriesAgreeAt; infer_instance

/-- Do two theories agree on utterance `w` across all worlds (in `T₁.worlds`)? -/
def theoriesAgreeOn (T₁ T₂ : NumeralTheory) (w : BareNumeral) : Prop :=
  ∀ n ∈ T₁.worlds, theoriesAgreeAt T₁ T₂ w n

instance (T₁ T₂ : NumeralTheory) (w : BareNumeral) :
    Decidable (theoriesAgreeOn T₁ T₂ w) := by
  unfold theoriesAgreeOn; infer_instance

/-- Find worlds where two theories diverge. -/
def divergingWorlds (T₁ T₂ : NumeralTheory) (w : BareNumeral) : List Nat :=
  T₁.worlds.filter (fun n => decide ¬ theoriesAgreeAt T₁ T₂ w n)

/-- Do two theories agree on all utterances in all worlds? -/
def theoriesEquivalent (T₁ T₂ : NumeralTheory) : Prop :=
  ∀ w ∈ T₁.utterances, theoriesAgreeOn T₁ T₂ w

instance (T₁ T₂ : NumeralTheory) : Decidable (theoriesEquivalent T₁ T₂) := by
  unfold theoriesEquivalent; infer_instance

/-- Ambiguity difference. -/
def hasMoreAmbiguity (T₁ T₂ : NumeralTheory) (w : BareNumeral) : Prop :=
  T₁.compatibleCount w > T₂.compatibleCount w

instance (T₁ T₂ : NumeralTheory) (w : BareNumeral) : Decidable (hasMoreAmbiguity T₁ T₂ w) := by
  unfold hasMoreAmbiguity; infer_instance

-- Key Divergence Theorems

theorem lowerBound_exact_differ_on_two :
    LowerBound.meaning .two 3 ∧ ¬ Exact.meaning .two 3 := by decide

theorem divergence_at_three :
    divergingWorlds LowerBound Exact .two = [3] := by decide

theorem agreement_at_two :
    theoriesAgreeAt LowerBound Exact .two 2 := by decide

theorem theories_not_equivalent :
    ¬ theoriesEquivalent LowerBound Exact := by decide

-- Ambiguity Comparison

theorem lowerBound_more_ambiguous_two :
    hasMoreAmbiguity LowerBound Exact .two := by decide

theorem ambiguity_count_differs :
    LowerBound.compatibleCount .two = 2 ∧ Exact.compatibleCount .two = 1 := by decide

theorem ambiguity_presence_differs :
    LowerBound.hasAmbiguity .two ∧ ¬ Exact.hasAmbiguity .two := by decide

-- Monotonicity Comparison

theorem monotonicity_differs :
    LowerBound.checkMonotonic ∧ ¬ Exact.checkMonotonic := by decide

-- Implicature Potential

theorem only_lowerBound_supports_implicature :
    (LowerBound.compatibleCount .two > 1 ∧ LowerBound.isStrongerThan .three .two)
    ∧
    (Exact.compatibleCount .two = 1) := by decide

-- Empirical Adjudication (@cite{goodman-stuhlmuller-2013})

theorem lowerBound_consistent_with_cancellation :
    LowerBound.hasAmbiguity .two := by decide

theorem exact_inconsistent_with_cancellation :
    ¬ Exact.hasAmbiguity .two := by decide

theorem summary_comparison :
    (LowerBound.compatibleCount .two = 2 ∧ Exact.compatibleCount .two = 1)
    ∧
    (LowerBound.checkMonotonic ∧ ¬ Exact.checkMonotonic)
    ∧
    (LowerBound.meaning .two 3 ∧ ¬ Exact.meaning .two 3) := by decide

-- Class A/B Modified Numeral Comparison

theorem classA_classB_diverge_on_bare_world :
    (¬ moreThanMeaning 3 3) ∧
    (atLeastMeaning 3 3) ∧
    (¬ fewerThanMeaning 3 3) ∧
    (atMostMeaning 3 3) := by decide

theorem classB_strictly_weaker_than_bare :
    (atLeastMeaning 3 3) ∧
    (atLeastMeaning 3 4) ∧
    (¬ bareMeaning 3 4) ∧
    (¬ moreThanMeaning 3 3) := by decide

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

-- GQT Bridge (@cite{bylinina-nouwen-2020})
--
-- The GQT numeral quantifiers in Quantifier.lean (`exactly_n_sem`, `at_least_n_sem`,
-- `at_most_n_sem`) compute the same truth values as the named numeral meanings
-- applied to the intersection cardinality. This connects B&N's quantifier view
-- (type ⟨⟨e,t⟩,⟨e,t⟩,t⟩) to the Kennedy maximality view (type ⟨d,t⟩).

open Classical Core.IntensionalLogic Semantics.Quantification in
/-- GQT "at least n" agrees with `atLeastMeaning` on intersection cardinality. -/
theorem gqt_atLeast_agrees (m : Frame) [Fintype m.Entity]
    (n : Nat) (R S : m.Entity → Prop) :
    Quantifier.at_least_n_sem m n R S ↔
    atLeastMeaning n (Quantifier.count (fun x : m.Entity => R x ∧ S x)) := by
  simp only [Quantifier.at_least_n_sem, atLeastMeaning]

open Classical Core.IntensionalLogic Semantics.Quantification in
/-- GQT "at most n" agrees with `atMostMeaning` on intersection cardinality. -/
theorem gqt_atMost_agrees (m : Frame) [Fintype m.Entity]
    (n : Nat) (R S : m.Entity → Prop) :
    Quantifier.at_most_n_sem m n R S ↔
    atMostMeaning n (Quantifier.count (fun x : m.Entity => R x ∧ S x)) := by
  simp only [Quantifier.at_most_n_sem, atMostMeaning]

open Classical Core.IntensionalLogic Semantics.Quantification in
/-- GQT "exactly n" agrees with `bareMeaning` on intersection cardinality. -/
theorem gqt_exactly_agrees (m : Frame) [Fintype m.Entity]
    (n : Nat) (R S : m.Entity → Prop) :
    Quantifier.exactly_n_sem m n R S ↔
    bareMeaning n (Quantifier.count (fun x : m.Entity => R x ∧ S x)) := by
  simp only [Quantifier.exactly_n_sem, bareMeaning]

-- ============================================================================
-- Section 11: CumminsFranke Bridge
-- ============================================================================

/-- "More than m" is `n > m`. -/
theorem moreThan_iff_gt (m n : Nat) :
    moreThanMeaning m n ↔ n > m := Iff.rfl

-- ============================================================================
-- Section 12: Aliases (used across NegationScope, Operations, RSA)
-- ============================================================================

abbrev Bilateral := Exact
abbrev DeFregean := Exact
abbrev NumWord := BareNumeral
def lowerBoundMeaning (w : BareNumeral) (n : Nat) : Prop := LowerBound.meaning w n
def bilateralMeaning (w : BareNumeral) (n : Nat) : Prop := Exact.meaning w n
abbrev deFregeanMeaning := bilateralMeaning
abbrev exactMeaning := bilateralMeaning

instance (w : BareNumeral) (n : Nat) : Decidable (lowerBoundMeaning w n) := by
  unfold lowerBoundMeaning; infer_instance
instance (w : BareNumeral) (n : Nat) : Decidable (bilateralMeaning w n) := by
  unfold bilateralMeaning; infer_instance

-- ============================================================================
-- Section 13: Verification
-- ============================================================================

theorem bare_exact_match : bareMeaning 3 3 := by decide
theorem bare_rejects_lower : ¬ bareMeaning 3 2 := by decide
theorem bare_rejects_higher : ¬ bareMeaning 3 4 := by decide

theorem moreThan_above : moreThanMeaning 3 4 := by decide
theorem moreThan_equal : ¬ moreThanMeaning 3 3 := by decide

theorem fewerThan_below : fewerThanMeaning 3 2 := by decide
theorem fewerThan_equal : ¬ fewerThanMeaning 3 3 := by decide

theorem atLeast_equal : atLeastMeaning 3 3 := by decide
theorem atLeast_above : atLeastMeaning 3 4 := by decide
theorem atLeast_below : ¬ atLeastMeaning 3 2 := by decide

theorem atMost_equal : atMostMeaning 3 3 := by decide
theorem atMost_below : atMostMeaning 3 2 := by decide
theorem atMost_above : ¬ atMostMeaning 3 4 := by decide

-- ============================================================================
-- Section 14: Core.Scale Bridge Theorems
-- ============================================================================

/-! ### Numeral meanings as ℕ-pullbacks of Core.Scale degree properties

The numeral meaning functions compute over `ℕ` independently, but the degree
properties in `Core.Scale` (`atLeastDeg`, `moreThanDeg`, etc.) are the
canonical scale-level definitions. These bridge theorems prove that each
named meaning is the ℕ-instantiation of the corresponding Core.Scale degree
property, connecting ℕ-level computation to scale-level definitions. Density
predictions (`moreThan_noMaxInf`, `atLeast_hasMaxInf`) flow compositionally
from `Core.Scale` through numeral semantics. -/

open Core.Scale in
/-- `atLeastMeaning m n` iff `atLeastDeg id m n`. -/
theorem atLeastMeaning_iff_atLeastDeg (m n : ℕ) :
    atLeastMeaning m n ↔ atLeastDeg id m n := by
  simp only [atLeastMeaning, atLeastDeg, id_eq]

open Core.Scale in
/-- `moreThanMeaning m n` iff `moreThanDeg id m n`. -/
theorem moreThanMeaning_iff_moreThanDeg (m n : ℕ) :
    moreThanMeaning m n ↔ moreThanDeg id m n := by
  simp only [moreThanMeaning, moreThanDeg, id_eq]

open Core.Scale in
/-- `bareMeaning m n` iff `eqDeg id m n`. -/
theorem bareMeaning_iff_eqDeg (m n : ℕ) :
    bareMeaning m n ↔ eqDeg id m n := by
  simp only [bareMeaning, eqDeg, id_eq]

open Core.Scale in
/-- `atMostMeaning m n` iff `atMostDeg id m n`. -/
theorem atMostMeaning_iff_atMostDeg (m n : ℕ) :
    atMostMeaning m n ↔ atMostDeg id m n := by
  simp only [atMostMeaning, atMostDeg, id_eq]

open Core.Scale in
/-- `fewerThanMeaning m n` iff `lessThanDeg id m n`. -/
theorem fewerThanMeaning_iff_lessThanDeg (m n : ℕ) :
    fewerThanMeaning m n ↔ lessThanDeg id m n := by
  simp only [fewerThanMeaning, lessThanDeg, id_eq]

-- ============================================================================
-- Section 15: Cardinality as ℚ-valued Degree
-- ============================================================================

/-! Bare cardinalities `(n : ℕ)` participate in the `HasDegree` framework via
the cast `(· : ℚ)`. The α codomain is `outParam`, so this single instance
suffices — Lean infers α = ℚ from the `degree` body. The Bool↔Prop bridges
to `Core.Scale` live in §14; cast-based bridges are obtainable directly
through `Nat.cast_lt` / `Nat.cast_le` / `Nat.cast_inj` when needed. -/

open Core.Scale in
/-- Cardinality (Nat) as a ℚ-valued degree. -/
instance CardinalityDegree : HasDegree Nat ℚ where
  degree := λ n => (n : ℚ)

-- ============================================================================
-- Section 16: Numeral Expression Semantics (from HasDegree)
-- ============================================================================

open Core.Scale in

/-- Literal/exact semantics for numeral expressions.
    "six feet" is true of x iff μ_height(x) = 183. -/
def numeralExact {E α : Type} [HasDegree E α] [BEq α]
    (stated : α) (entity : E) : Bool :=
  HasDegree.degree entity == stated

open Core.Scale in

/-- "At least n" semantics (lower-bound reading). -/
def numeralAtLeast {E α : Type} [HasDegree E α] [LE α] [DecidableLE α]
    (threshold : α) (entity : E) : Bool :=
  decide (threshold ≤ HasDegree.degree entity)

open Core.Scale in

/-- Approximate match with tolerance (for vagueness/imprecision). -/
def numeralApprox {E α : Type} [HasDegree E α] [Sub α] [Add α] [LE α] [DecidableLE α]
    (stated : α) (tolerance : α) (entity : E) : Bool :=
  let actual := HasDegree.degree entity
  decide (stated - tolerance ≤ actual) && decide (actual ≤ stated + tolerance)

-- ============================================================================
-- Section 17: Measure Predicates (Compositional Sentence Semantics)
-- ============================================================================

open Core.Scale in

/-- A measure predicate maps entities to degrees along some dimension. -/
structure MeasurePredicate (E : Type) where
  dimension : String
  μ : E → ℚ

open Core.Scale in

/-- Construct a MeasurePredicate from a HasDegree instance -/
def MeasurePredicate.fromHasDegree (E : Type) [HasDegree E ℚ] (dim : String) : MeasurePredicate E :=
  { dimension := dim, μ := HasDegree.degree }

/-- A degree phrase denotes a specific degree value.
    "1000 dollars" denotes the degree 1000 (in dollar units). -/
structure DegreePhrase where
  value : ℚ
  unit : String := ""
  deriving Repr, DecidableEq

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
def measureSentence' {E : Type} [HasDegree E ℚ] (entity : E) (deg : DegreePhrase) : Bool :=
  HasDegree.degree entity == deg.value

-- Grounding Theorems

open Core.Scale in

/-- The compositional measure sentence semantics equals the simple numeral check. -/
theorem measureSentence_eq_numeralExact {E : Type} [HasDegree E ℚ]
    (entity : E) (deg : DegreePhrase) :
    measureSentence' entity deg = numeralExact deg.value entity := rfl

open Core.Scale in

/-- MeasurePredicate.fromHasDegree produces the HasDegree measure function. -/
theorem fromHasDegree_μ {E : Type} [HasDegree E ℚ] (dim : String) :
    (MeasurePredicate.fromHasDegree E dim).μ = HasDegree.degree := rfl

open Core.Scale in

/-- Measure sentences compose correctly with HasDegree-derived predicates. -/
theorem measureSentence_fromHasDegree {E : Type} [HasDegree E ℚ]
    (dim : String) (entity : E) (deg : DegreePhrase) :
    measureSentence (MeasurePredicate.fromHasDegree E dim) entity deg =
    numeralExact deg.value entity := rfl

-- ============================================================================
-- Section 18: Numeral with Precision Mode
-- ============================================================================

open Semantics.Numerals.Precision in

/-- Numeral semantics with precision mode.
    "1000 dollars" under exact mode: true iff cost = 1000
    "1000 dollars" under approximate mode: true iff Round(cost) = 1000 -/
def numeralWithPrecision {E : Type} [Core.Scale.HasDegree E ℚ]
    (stated : ℚ) (entity : E) (mode : PrecisionMode) (base : ℚ := 10) : Bool :=
  matchesPrecision mode stated (Core.Scale.HasDegree.degree entity) base

end Semantics.Numerals
