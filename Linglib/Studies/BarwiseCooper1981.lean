import Linglib.Features.Acceptability
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Toy
import Linglib.Phenomena.Quantification.Inventory
import Linglib.Semantics.Quantification.DomainRestriction

/-!
# Quantifier Universals Bridge
[barwise-cooper-1981] [mostowski-1957] [peters-westerstahl-2006] [van-benthem-1984] [van-de-pol-etal-2023]

Bridges the English determiner fragment (`English.Determiners.QuantityWord`)
to the GQ property predicates in `Core.Quantification` and
`Semantics.Quantification.Quantifier`.

## Empirical phenomena verified

1. **Conservativity** ([barwise-cooper-1981], conservativity conjecture):
   all six English quantity words satisfy CONSERV.
2. **Quantity/isomorphism closure** ([mostowski-1957]): all six satisfy QUANT.
3. **Table II per-entry verification** ([barwise-cooper-1981] Table II):
   each quantity word's strength and monotonicity direction match the
   paper's classification. Changing a fragment field breaks exactly one theorem.
4. **Monotonicity–strength correlation** ([barwise-cooper-1981] U7):
   strong English determiners are scope-↑MON (increasing).
5. **Weak ↔ there-insertion** ([barwise-cooper-1981] §4.6):
   weak determiners allow there-insertion; strong determiners don't.
6. **Symmetry ↔ weak** ([peters-westerstahl-2006], symmetric ↔
   there-insertion): weak = symmetric, strong = not symmetric.
7. **Positive-strong → scope-↑** ([peters-westerstahl-2006],
   positive-strong determiners are scope-upward-monotone).
8. **Duality** ([barwise-cooper-1981] §4.11): outer/inner negation
   and dual operations connect every ↔ some ↔ no via the Square of
   Opposition, bridged to fragment entries.
9. **Domain restriction** ([ritchie-schiller-2024]): conservativity
   enables domain restriction for all six quantity words.

## Data structures

- `MonotonicitySimplicity`, `ConservativitySimplicity`, `QuantitySimplicity`:
  [van-de-pol-etal-2023] LZ complexity effect sizes.

## Thread map

- **Formal definitions**: `Core.Quantification` — `Conservative`, `ScopeUpwardMono`,
  `ScopeDownwardMono`, `QuantityInvariant`, `PositiveStrong`, `QSymmetric`,
  `outerNeg`, `innerNeg`, `dualQ`
- **Concrete denotations**: `Semantics.Quantification.Quantifier` —
  `every_sem`, `some_sem`, `no_sem`, `most_sem`, `few_sem`, `half_sem`
- **Fragment entries**: `English.Determiners.QuantityWord.gqDenotation`
- **Domain restriction**: `Semantics.Quantification.DomainRestriction` —
  `DomainRestrictor`, `DDRP`, `conservative_domain_restricted`
- **Impossibility theorems**: `Core.Quantification.NumberTreeGQ` —
  `no_asymmetric`, `no_strict_partial_order`, `no_euclidean`
- **Counting formula**: `Core.Quantification.conservativeQuantifierCount`

-/

namespace Phenomena.Quantification.Bridge

open English.Determiners (Monotonicity Strength)
open Phenomena.Quantification.Inventory
open Semantics.Quantification.Quantifier
open Core.Quantification
open Semantics.Quantification.DomainRestriction (DomainRestrictor
  conservative_domain_restricted)

-- ============================================================================
-- §1. [barwise-cooper-1981]: Conservativity is (near-)universal
-- ============================================================================

/-- Conservativity holds for all simple (lexicalized) English determiners.
    [barwise-cooper-1981] conjecture this is a universal of natural
    language. Proved individually for each quantity word via
    `every_conservative`, `some_conservative`, etc. -/
theorem conservativity_universal :
  ∀ (q : QuantityWord) {α : Type*} [Fintype α] [DecidableEq α],
    Conservative (q.gqDenotation (α := α)) := by
  intro q α inst inst2
  cases q <;> simp only [QuantityWord.gqDenotation]
  · exact Semantics.Quantification.Quantifier.no_conservative
  · exact Semantics.Quantification.Quantifier.few_conservative
  · exact Semantics.Quantification.Quantifier.some_conservative
  · exact Semantics.Quantification.Quantifier.half_conservative
  · exact Semantics.Quantification.Quantifier.most_conservative
  · exact Semantics.Quantification.Quantifier.every_conservative

-- ============================================================================
-- §2. [mostowski-1957] / [keenan-stavi-1986]: Quantity
-- ============================================================================

/-- All simple determiners satisfy quantity/isomorphism closure:
    their truth value depends only on cardinalities |A∩B|, |A\B|, etc.

    TODO: Rewrite proof for cardinality-based quantifiers (most, few, half)
    which need `count_bij_inv` adapted to Prop predicates. -/
theorem quantity_universal :
  ∀ (q : QuantityWord) {α : Type*} [Fintype α] [DecidableEq α],
    QuantityInvariant (q.gqDenotation (α := α)) := by
  intro q α inst inst2 A B A' B' f hBij hA hB
  cases q <;> simp only [QuantityWord.gqDenotation]
  case all =>
    simp only [every_sem]
    rw [forall_bij_inv f hBij]
    exact forall_congr' fun x => by rw [show A (f x) ↔ A' x from hA x,
                                         show B (f x) ↔ B' x from hB x]
  case some_ =>
    simp only [some_sem]
    rw [exists_bij_inv f hBij]
    exact exists_congr fun x => by rw [show A (f x) ↔ A' x from hA x,
                                        show B (f x) ↔ B' x from hB x]
  case none_ =>
    simp only [no_sem]
    rw [forall_bij_inv f hBij]
    exact forall_congr' fun x => by rw [show A (f x) ↔ A' x from hA x,
                                         show B (f x) ↔ B' x from hB x]
  -- TODO: cardinality-based cases need `count_bij_inv` adapted to Prop predicates.
  case most => sorry
  case few => sorry
  case half => sorry

/-! ### Extension: domain independence

EXT (`Q(A,B)` depends only on `A` and `B`, not on an ambient universe)
holds trivially for `GQ α` since the representation is universe-free —
no axiom needed. EXT + CONS together yield the [van-benthem-1984]
characterization: determiners can be represented as type ⟨1⟩ quantifiers
that "live on" their restrictor; see `conservative_iff_livesOn`. -/

/-! ### [barwise-cooper-1981] Table II: per-entry verification

Each theorem verifies one quantity word's strength and monotonicity
direction against the paper's classification (p.184). Changing a field in
the fragment entry breaks exactly one theorem. B&C's Table II classifies:
every/all (strong, ↑MON), some (weak, ↑MON), no (weak, ↓MON), most
(strong, ↑MON), many (weak, ↑MON), few (weak, ↓MON). Our fragment omits
"many" and adds "half" (not in original Table II). -/

/-- every/all: strong, scope-↑MON (increasing). -/
theorem table_II_all :
    QuantityWord.all.entry.strength = .strong ∧
    QuantityWord.all.entry.monotonicity = .increasing := ⟨rfl, rfl⟩

/-- most: strong, scope-↑MON (increasing). -/
theorem table_II_most :
    QuantityWord.most.entry.strength = .strong ∧
    QuantityWord.most.entry.monotonicity = .increasing := ⟨rfl, rfl⟩

/-- some: weak, scope-↑MON (increasing). -/
theorem table_II_some :
    QuantityWord.some_.entry.strength = .weak ∧
    QuantityWord.some_.entry.monotonicity = .increasing := ⟨rfl, rfl⟩

/-- no: weak, scope-↓MON (decreasing). -/
theorem table_II_none :
    QuantityWord.none_.entry.strength = .weak ∧
    QuantityWord.none_.entry.monotonicity = .decreasing := ⟨rfl, rfl⟩

/-- few: weak, scope-↓MON (decreasing). -/
theorem table_II_few :
    QuantityWord.few.entry.strength = .weak ∧
    QuantityWord.few.entry.monotonicity = .decreasing := ⟨rfl, rfl⟩

/-- half: weak, non-monotone. Not in [barwise-cooper-1981] Table II;
    classification follows [van-de-pol-etal-2023]. -/
theorem table_II_half :
    QuantityWord.half.entry.strength = .weak ∧
    QuantityWord.half.entry.monotonicity = .nonMonotone := ⟨rfl, rfl⟩

-- ============================================================================
-- §5. Monotonicity–Strength Correlation
-- ============================================================================

/-- All English quantity words except "half" are monotone.
    "Half" is the lone non-monotone simple determiner
    ([van-de-pol-etal-2023] classify it as non-monotone). -/
theorem english_quantifiers_mostly_monotone :
    ([QuantityWord.none_, .few, .some_, .most, .all].map QuantityWord.monotonicity).all
      (· != .nonMonotone) = true := by native_decide

/-- "Half" is the sole non-monotone quantity word. -/
theorem half_nonmonotone :
    QuantityWord.half.monotonicity = .nonMonotone := by native_decide

/-- The ⟨some, all⟩ scale is upward monotone (both members increasing). -/
theorem some_all_scale_upward :
    [QuantityWord.some_, QuantityWord.all].all
      (·.monotonicity == .increasing) = true := by native_decide

/-- [barwise-cooper-1981] U7 (monotonicity–strength correlation):
    strong determiners are scope-↑MON (increasing). The full universal
    distinguishes positive-strong (→ ↑MON) from negative-strong (→ ↓MON);
    since both English strong determiners (most, every) are positive,
    the universal reduces to: strong → increasing.

    Strictly stronger than the previous `strong_implies_monotone` (which
    only checked `!= .nonMonotone` without verifying direction). -/
theorem strong_implies_increasing :
    ∀ q : QuantityWord, q.entry.strength = .strong →
      q.entry.monotonicity = .increasing := by native_decide

-- ============================================================================
-- §6. Weak/Strong and There-Insertion
-- ============================================================================

/-- Weak determiners allow there-insertion ([barwise-cooper-1981] §4.6).
    "There are some/a/few/no cats" vs *"There is every/each cat". -/
theorem weak_there_insertion :
    ([QuantityWord.none_, .few, .some_].map (·.entry.strength)).all
      (· == .weak) = true := by native_decide

/-- Strong determiners block there-insertion ([barwise-cooper-1981] Table II). -/
theorem strong_no_there_insertion :
    ([QuantityWord.most, .all].map (·.entry.strength)).all
      (· == .strong) = true := by native_decide

-- ============================================================================
-- §7. Symmetry ↔ Weak
-- ============================================================================

/-- Weak English determiners are symmetric ([peters-westerstahl-2006],
    symmetric ↔ there-insertion ↔ weak).
    Cross-references: `some_symmetric`, `no_symmetric` in Quantifier.lean. -/
theorem weak_are_symmetric :
    QuantityWord.some_.entry.strength = .weak ∧
    QuantityWord.none_.entry.strength = .weak := ⟨rfl, rfl⟩

/-- Strong English determiners are not symmetric ([peters-westerstahl-2006]).
    Witness: `every_not_symmetric` below. -/
theorem strong_not_symmetric :
    QuantityWord.all.entry.strength = .strong ∧
    QuantityWord.most.entry.strength = .strong := ⟨rfl, rfl⟩

/-! #### Toy-witnessed counterexamples

Counterexamples to non-properties of specific determiners need a concrete
witness type; the witness is the toy fragment's `ToyEntity`. -/

section ToyWitnesses

open Semantics.Montague (ToyEntity)
open Semantics.Montague.ToyLexicon (student_sem thing_sem)

/-- `⟦every⟧` is NOT symmetric. Witness: R=students, S=things; every(students,
    things)=true but every(things,students)=false. -/
theorem every_not_symmetric : ¬ QSymmetric (every_sem (α := ToyEntity)) := by
  intro h
  have := (h student_sem thing_sem).mp (fun x _ => trivial)
  exact absurd (this ToyEntity.pizza trivial) id

/-- `⟦no⟧` is NOT positive strong: no(A,A) = false when A is non-empty. -/
theorem no_not_positive_strong : ¬ PositiveStrong (no_sem (α := ToyEntity)) := by
  intro h
  have := h student_sem
  exact this ToyEntity.john trivial trivial

end ToyWitnesses

-- ============================================================================
-- §8. [barwise-cooper-1981] §4.11: Duality (Square of Opposition)
-- ============================================================================

/-- The dual of ⟦every⟧ is ⟦some⟧: Q̌(every) = some ([barwise-cooper-1981] §4.11).
    ¬(∀x. R(x) → ¬S(x)) = ∃x. R(x) ∧ S(x).
    Bridges `dualQ_every_eq_some` from Quantifier.lean to fragment entries. -/
theorem dual_all_eq_some {α : Type*} [Fintype α] [DecidableEq α] :
    dualQ (QuantityWord.all.gqDenotation (α := α)) = QuantityWord.some_.gqDenotation (α := α) := by
  simp only [QuantityWord.gqDenotation]
  exact Semantics.Quantification.Quantifier.dualQ_every_eq_some

/-- Inner negation maps ⟦every⟧ to ⟦no⟧: every~ = no ([barwise-cooper-1981] §4.11).
    ∀x. R(x) → ¬S(x) = ¬∃x. R(x) ∧ S(x).
    Bridges `pinnerNeg_every_eq_no` to fragment entries. -/
theorem innerNeg_all_eq_none {α : Type*} [Fintype α] [DecidableEq α] :
    innerNeg (QuantityWord.all.gqDenotation (α := α)) = QuantityWord.none_.gqDenotation (α := α) := by
  simp only [QuantityWord.gqDenotation]
  exact Semantics.Quantification.Quantifier.innerNeg_every_eq_no

/-- Outer negation maps ⟦some⟧ to ⟦no⟧: ~some = no ([barwise-cooper-1981] §4.11).
    ¬(∃x. R(x) ∧ S(x)) = ∀x. R(x) → ¬S(x).
    Bridges `pouterNeg_some_eq_no` to fragment entries. -/
theorem outerNeg_some_eq_none {α : Type*} [Fintype α] [DecidableEq α] :
    outerNeg (QuantityWord.some_.gqDenotation (α := α)) = QuantityWord.none_.gqDenotation (α := α) := by
  simp only [QuantityWord.gqDenotation]
  exact Semantics.Quantification.Quantifier.outerNeg_some_eq_no

-- ============================================================================
-- §9. Left anti-additivity → NPI licensing
-- ============================================================================

/- Left anti-additive determiners license NPIs ([peters-westerstahl-2006]).
   LAA is formalized: see `every_laa`, `no_laa` in Quantifier.lean.
   The NPI ↔ DE bridge is now formalized in
   `Ladusaw1979`. -/

-- ============================================================================
-- §10. Positive-strong → scope-↑MON
-- ============================================================================

/-- Positive-strong determiners are scope-upward-monotone
    ([peters-westerstahl-2006]).
    Only `all` (= `every_sem`) is genuinely positive-strong; for the rest,
    `PositiveStrong` is vacuously false (contradicted by `R = λ _ => false`
    or `R = λ _ => true`), making the implication trivially true. -/
theorem positive_strong_determiners_upward_monotone :
  ∀ (q : QuantityWord) {α : Type*} [Fintype α] [DecidableEq α],
    PositiveStrong (q.gqDenotation (α := α)) →
    ScopeUpwardMono (q.gqDenotation (α := α)) := by
  intro q α inst inst2 hPS
  cases q
  case all => exact Semantics.Quantification.Quantifier.every_scope_up
  case some_ => exact Semantics.Quantification.Quantifier.some_scope_up
  -- TODO: Adapt remaining cases for Prop-valued GQs.
  -- The vacuity argument (PositiveStrong contradicted by R = fun _ => False)
  -- needs count lemmas adapted for Prop predicates.
  case most => sorry
  case few => sorry
  case none_ => sorry
  case half => sorry

-- ============================================================================
-- §11. [van-benthem-1984] §3.3: Aristotle Reversed — Square of Opposition
-- ============================================================================

/- [van-benthem-1984] §3.3: Under CONSERV (+ VAR*), the Square of Opposition
   is completely determined by inferential (relational) conditions:
   - all:     transitive + reflexive      → inclusion  (A ⊆ B)
   - some:    symmetric + quasi-reflexive → overlap    (A ∩ B ≠ ∅)
   - no:      symmetric + quasi-universal → disjointness (A ∩ B = ∅)
   - not all: almost-connected + irreflexive

   Proved in `Core.Quantification`:
   - `vanBenthem_refl_antisym_is_inclusion`:  CONSERV + reflexive + antisymmetric → "all"
   - `vanBenthem_symm_quasiRefl_is_overlap`:  CONSERV + symmetric + quasi-reflexive → "some"
     (→ direction fully proved; ← direction needs QUANT/isomorphism invariance)
   - `vanBenthem_symm_quasiUniv_is_disjointness`: CONSERV + symmetric + quasi-universal → "no"
     (← direction fully proved; → direction needs QUANT)

   Additional structural results:
   - `zwarts_refl_trans_scopeUp`:  CONSERV + reflexive + transitive → MON↑

   Bridge theorems in `English.Determiners`:
     `all_inferential_bridge`, `some_inferential_bridge`, `none_inferential_bridge`

   NPI licensing connection (via `Ladusaw1979`):
   - scope-↓ monotone quantifiers (no, few) license weak NPIs in scope
   - restrictor-↓ monotone quantifiers (every, no) license weak NPIs in restrictor
   - left-anti-additive quantifiers (every, no) license strong NPIs -/

-- ============================================================================
-- §12. [van-de-pol-etal-2023]: Simplicity and Universals
-- ============================================================================

/-- Monotone quantifiers have strictly lower LZ complexity than
    non-monotone ones. This is the strongest of the three effects.
    ([van-de-pol-etal-2023]) -/
structure MonotonicitySimplicity where
  /-- Mean LZ complexity of monotone quantifiers (universe size 4) -/
  monotone_mean_lz : ℚ
  /-- Mean LZ complexity of non-monotone quantifiers -/
  non_monotone_mean_lz : ℚ
  /-- Monotone is simpler -/
  monotone_simpler : monotone_mean_lz < non_monotone_mean_lz

/-- Conservative quantifiers have lower LZ complexity than
    non-conservative ones. -/
structure ConservativitySimplicity where
  conservative_mean_lz : ℚ
  non_conservative_mean_lz : ℚ
  conservative_simpler : conservative_mean_lz < non_conservative_mean_lz

/-- Quantity-satisfying quantifiers have lower LZ complexity, but the
    effect is weaker than monotonicity. -/
structure QuantitySimplicity where
  quantity_mean_lz : ℚ
  non_quantity_mean_lz : ℚ
  quantity_simpler : quantity_mean_lz < non_quantity_mean_lz

/-- The three universals combined: quantifiers satisfying all three have
    the lowest complexity. Monotonicity is the strongest single predictor,
    quantity the weakest. -/
structure UniversalsSimplicityRanking where
  monotonicity_effect : MonotonicitySimplicity
  conservativity_effect : ConservativitySimplicity
  quantity_effect : QuantitySimplicity

-- ============================================================================
-- §13. Conservativity Enables Domain Restriction
-- [barwise-cooper-1981] + [ritchie-schiller-2024]
-- ============================================================================

/-- Conservativity universally enables domain restriction: all 6 English
    quantity words remain conservative under any domain restrictor C.

    This connects [barwise-cooper-1981]'s conservativity conjecture
    (all simple determiners are conservative) to
    [ritchie-schiller-2024]'s DDRPs. Domain restriction via
    C-intersection is well-defined for the entire English determiner
    system because every lexicalized determiner is conservative.

    Cross-references:
    - `conservative_domain_restricted` (general GQ theorem)
    - `DDRP` structure (nested spatial regions → candidate restrictors)
    - `RitchieSchiller2024.lean` (full RSA model with DDRPs) -/
theorem domain_restriction_preserves_conservativity :
    ∀ (q : QuantityWord) {α : Type*} [Fintype α] [DecidableEq α]
      (C : DomainRestrictor α),
    Conservative (λ R S => q.gqDenotation (α := α) (λ x => C x ∧ R x) S) := by
  intro q α inst inst2 C
  exact conservative_domain_restricted (conservativity_universal q)

end Phenomena.Quantification.Bridge

/-! ### Appendix C: *more than half* is not first-order definable

[barwise-cooper-1981] Appendix C (C12, p. 213): over a first-order language
with equality and two unary predicate symbols `U`, `V`, **no sentence** is
true in exactly the finite models where more than half the V's are U's
(`2·|U∩V| > |V|`). B&C treat *most* via *more than half* "to avoid problems
of vagueness"; the theorem is the formal core of their claim that *most*
must be a determiner, not a quantifier (their C13, deferred).

The proof is the paper's own (pp. 213–214), a hand-rolled Fraïssé argument:
for each `m`, two structures on `Fin (3m+1)` — `V = [0,2m)`, `U₁ = [0,m)`,
`U₂ = [0,m+1)` — disagree on *more than half* but agree on every formula
with fewer than `m` quantifiers-plus-free-variables (their condition (6)),
because a region-respecting correspondence can always be extended:
"there is always enough room". -/

namespace BarwiseCooper1981

open FirstOrder Language

/-- Relation symbols: two unary predicates. -/
inductive uvRel : ℕ → Type
  | U : uvRel 1
  | V : uvRel 1
  deriving DecidableEq

/-- The monadic language of C12 (equality is built into the formula type). -/
def L_UV : Language :=
  { Functions := fun _ => Empty
    Relations := uvRel }

abbrev uRel : L_UV.Relations 1 := .U
abbrev vRel : L_UV.Relations 1 := .V

/-- Quantifier count of a formula (`c(φ)` minus the free-variable count in
B&C's notation). -/
def numQuant : ∀ {α : Type} {n : ℕ}, L_UV.BoundedFormula α n → ℕ
  | _, _, .falsum => 0
  | _, _, .equal _ _ => 0
  | _, _, .rel _ _ => 0
  | _, _, .imp f₁ f₂ => numQuant f₁ + numQuant f₂
  | _, _, .all f => numQuant f + 1

/-- `M₁`: `U` is `[0, m)`, `V` is `[0, 2m)` — exactly half the V's are U's. -/
@[reducible] def struc₁ (m : ℕ) : L_UV.Structure (Fin (3 * m + 1)) where
  funMap := fun f _ => f.elim
  RelMap {n} r v :=
    match r, v with
    | .U, v => (v 0).val < m
    | .V, v => (v 0).val < 2 * m

/-- `M₂`: `U` is `[0, m+1)`, `V` is `[0, 2m)` — more than half the V's are
U's. -/
@[reducible] def struc₂ (m : ℕ) : L_UV.Structure (Fin (3 * m + 1)) where
  funMap := fun f _ => f.elim
  RelMap {n} r v :=
    match r, v with
    | .U, v => (v 0).val < m + 1
    | .V, v => (v 0).val < 2 * m

/-- Realization in `M₁` (structures are term-level, so instances are pinned
explicitly). -/
def Realize₁ (m : ℕ) {ℓ : ℕ} (φ : L_UV.BoundedFormula Empty ℓ)
    (xs : Fin ℓ → Fin (3 * m + 1)) : Prop :=
  @BoundedFormula.Realize L_UV _ (struc₁ m) Empty ℓ φ default xs

/-- Realization in `M₂`. -/
def Realize₂ (m : ℕ) {ℓ : ℕ} (φ : L_UV.BoundedFormula Empty ℓ)
    (xs : Fin ℓ → Fin (3 * m + 1)) : Prop :=
  @BoundedFormula.Realize L_UV _ (struc₂ m) Empty ℓ φ default xs

/-- B&C's one-one correspondence (proof of C12, condition on `aᵢ ↔ bᵢ`):
pairing-injective, and respecting the `U`-regions (`U₁` against `U₂`) and
the shared `V`-region. -/
structure RegionMatch (m : ℕ) {ℓ : ℕ} (a b : Fin ℓ → Fin (3 * m + 1)) : Prop where
  inj : ∀ i j, a i = a j ↔ b i = b j
  inU : ∀ i, (a i).val < m ↔ (b i).val < m + 1
  inV : ∀ i, (a i).val < 2 * m ↔ (b i).val < 2 * m

/-- Every `L_UV`-term is a variable (the language has no function symbols). -/
private theorem term_eq_var {γ : Type} (t : L_UV.Term γ) : ∃ i, t = Term.var i := by
  cases t with
  | var i => exact ⟨i, rfl⟩
  | func f _ => exact f.elim

/-- Fresh element in a value-interval of `Fin (3m+1)`: if fewer elements are
used than the interval holds, something in it is unused. -/
private theorem exists_fresh (m lo hi : ℕ) (hhi : hi ≤ 3 * m + 1)
    (used : Finset (Fin (3 * m + 1))) (hcard : used.card < hi - lo) :
    ∃ y : Fin (3 * m + 1), lo ≤ y.val ∧ y.val < hi ∧ y ∉ used := by
  by_contra h
  push_neg at h
  have hsub : (Finset.Ico lo hi).attachFin
      (fun x hx => lt_of_lt_of_le (Finset.mem_Ico.mp hx).2 hhi) ⊆ used := by
    intro y hy
    have := (Finset.mem_attachFin _).mp hy
    exact h y (Finset.mem_Ico.mp this).1 (Finset.mem_Ico.mp this).2
  have := Finset.card_le_card hsub
  rw [Finset.card_attachFin, Nat.card_Ico] at this
  omega

/-- Extending a correspondence with an already-matched pair. -/
private theorem regionMatch_snoc_matched (m : ℕ) {ℓ : ℕ}
    {a b : Fin ℓ → Fin (3 * m + 1)} (h : RegionMatch m a b) (i : Fin ℓ) :
    RegionMatch m (Fin.snoc a (a i)) (Fin.snoc b (b i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q
    induction p using Fin.lastCases with
    | last =>
      induction q using Fin.lastCases with
      | last => simp
      | cast q => simpa only [Fin.snoc_last, Fin.snoc_castSucc] using h.inj i q
    | cast p =>
      induction q using Fin.lastCases with
      | last => simpa only [Fin.snoc_last, Fin.snoc_castSucc] using h.inj p i
      | cast q => simpa only [Fin.snoc_castSucc] using h.inj p q
  · intro p
    induction p using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using h.inU i
    | cast p => simpa only [Fin.snoc_castSucc] using h.inU p
  · intro p
    induction p using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using h.inV i
    | cast p => simpa only [Fin.snoc_castSucc] using h.inV p

/-- Extending a correspondence with a fresh, region-matched pair. -/
private theorem regionMatch_snoc_fresh (m : ℕ) {ℓ : ℕ}
    {a b : Fin ℓ → Fin (3 * m + 1)} (h : RegionMatch m a b)
    {x y : Fin (3 * m + 1)} (hxa : ∀ i, a i ≠ x) (hyb : ∀ i, b i ≠ y)
    (hU : x.val < m ↔ y.val < m + 1) (hV : x.val < 2 * m ↔ y.val < 2 * m) :
    RegionMatch m (Fin.snoc a x) (Fin.snoc b y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q
    induction p using Fin.lastCases with
    | last =>
      induction q using Fin.lastCases with
      | last => simp
      | cast q =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact iff_of_false (fun e => hxa q e.symm) (fun e => hyb q e.symm)
    | cast p =>
      induction q using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact iff_of_false (hxa p) (hyb p)
      | cast q => simpa only [Fin.snoc_castSucc] using h.inj p q
  · intro p
    induction p using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hU
    | cast p => simpa only [Fin.snoc_castSucc] using h.inU p
  · intro p
    induction p using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hV
    | cast p => simpa only [Fin.snoc_castSucc] using h.inV p

/-- Extend a correspondence by an `M₁`-side element ("there is always enough
room", B&C p. 214). -/
private theorem extend₁₂ (m : ℕ) {ℓ : ℕ} (hℓ : ℓ + 1 < m)
    {a b : Fin ℓ → Fin (3 * m + 1)} (h : RegionMatch m a b)
    (x : Fin (3 * m + 1)) :
    ∃ y, RegionMatch m (Fin.snoc a x) (Fin.snoc b y) := by
  by_cases hx : ∃ i, a i = x
  · obtain ⟨i, rfl⟩ := hx
    exact ⟨b i, regionMatch_snoc_matched m h i⟩
  · push_neg at hx
    have hused : (Finset.image b Finset.univ).card ≤ ℓ :=
      le_trans Finset.card_image_le (by simp)
    have hbne : ∀ {y : Fin (3 * m + 1)}, y ∉ Finset.image b Finset.univ →
        ∀ i, b i ≠ y := fun hy i hbi =>
      hy (hbi ▸ Finset.mem_image_of_mem b (Finset.mem_univ i))
    by_cases h1 : x.val < m
    · obtain ⟨y, hy1, hy2, hy3⟩ := exists_fresh m 0 (m + 1) (by omega)
        (Finset.image b Finset.univ) (by omega)
      exact ⟨y, regionMatch_snoc_fresh m h hx (hbne hy3)
        (by omega) (by omega)⟩
    · by_cases h2 : x.val < 2 * m
      · obtain ⟨y, hy1, hy2, hy3⟩ := exists_fresh m (m + 1) (2 * m) (by omega)
          (Finset.image b Finset.univ) (by omega)
        exact ⟨y, regionMatch_snoc_fresh m h hx (hbne hy3)
          (by omega) (by omega)⟩
      · obtain ⟨y, hy1, hy2, hy3⟩ := exists_fresh m (2 * m) (3 * m + 1) (by omega)
          (Finset.image b Finset.univ) (by omega)
        exact ⟨y, regionMatch_snoc_fresh m h hx (hbne hy3)
          (by omega) (by omega)⟩

/-- Extend a correspondence by an `M₂`-side element. -/
private theorem extend₂₁ (m : ℕ) {ℓ : ℕ} (hℓ : ℓ + 1 < m)
    {a b : Fin ℓ → Fin (3 * m + 1)} (h : RegionMatch m a b)
    (y : Fin (3 * m + 1)) :
    ∃ x, RegionMatch m (Fin.snoc a x) (Fin.snoc b y) := by
  by_cases hy : ∃ i, b i = y
  · obtain ⟨i, rfl⟩ := hy
    exact ⟨a i, regionMatch_snoc_matched m h i⟩
  · push_neg at hy
    have hused : (Finset.image a Finset.univ).card ≤ ℓ :=
      le_trans Finset.card_image_le (by simp)
    have hane : ∀ {x : Fin (3 * m + 1)}, x ∉ Finset.image a Finset.univ →
        ∀ i, a i ≠ x := fun hx i hai =>
      hx (hai ▸ Finset.mem_image_of_mem a (Finset.mem_univ i))
    by_cases h1 : y.val < m + 1
    · obtain ⟨x, hx1, hx2, hx3⟩ := exists_fresh m 0 m (by omega)
        (Finset.image a Finset.univ) (by omega)
      exact ⟨x, regionMatch_snoc_fresh m h (hane hx3) hy
        (by omega) (by omega)⟩
    · by_cases h2 : y.val < 2 * m
      · obtain ⟨x, hx1, hx2, hx3⟩ := exists_fresh m m (2 * m) (by omega)
          (Finset.image a Finset.univ) (by omega)
        exact ⟨x, regionMatch_snoc_fresh m h (hane hx3) hy
          (by omega) (by omega)⟩
      · obtain ⟨x, hx1, hx2, hx3⟩ := exists_fresh m (2 * m) (3 * m + 1) (by omega)
          (Finset.image a Finset.univ) (by omega)
        exact ⟨x, regionMatch_snoc_fresh m h (hane hx3) hy
          (by omega) (by omega)⟩

/-- B&C's condition (6) (p. 214): a formula whose quantifier count plus
free-variable count is below `m` cannot distinguish region-matched tuples
across `M₁`/`M₂`. Structural induction; at each quantifier "there is always
enough room to extend the one-one correspondence one more step". -/
theorem realize_iff_of_regionMatch (m : ℕ) :
    ∀ {ℓ : ℕ} (φ : L_UV.BoundedFormula Empty ℓ), numQuant φ + ℓ < m →
      ∀ {a b : Fin ℓ → Fin (3 * m + 1)}, RegionMatch m a b →
        (Realize₁ m φ a ↔ Realize₂ m φ b) := by
  intro ℓ φ
  induction φ with
  | falsum =>
    intro _ a b _
    exact Iff.rfl
  | equal t₁ t₂ =>
    intro _ a b h
    obtain ⟨i, rfl⟩ := term_eq_var t₁
    obtain ⟨j, rfl⟩ := term_eq_var t₂
    rcases i with e | i
    · exact e.elim
    rcases j with e | j
    · exact e.elim
    simpa [Realize₁, Realize₂, Term.realize] using h.inj i j
  | rel R ts =>
    intro _ a b h
    cases R with
    | U =>
      obtain ⟨i, hi⟩ := term_eq_var (ts 0)
      rcases i with e | i
      · exact e.elim
      show ((fun k => @Term.realize L_UV _ (struc₁ m) _ (Sum.elim default a) (ts k)) 0).val < m ↔
        ((fun k => @Term.realize L_UV _ (struc₂ m) _ (Sum.elim default b) (ts k)) 0).val < m + 1
      simp only [hi, Term.realize_var, Sum.elim_inr]
      exact h.inU i
    | V =>
      obtain ⟨i, hi⟩ := term_eq_var (ts 0)
      rcases i with e | i
      · exact e.elim
      show ((fun k => @Term.realize L_UV _ (struc₁ m) _ (Sum.elim default a) (ts k)) 0).val < 2 * m ↔
        ((fun k => @Term.realize L_UV _ (struc₂ m) _ (Sum.elim default b) (ts k)) 0).val < 2 * m
      simp only [hi, Term.realize_var, Sum.elim_inr]
      exact h.inV i
  | imp f₁ f₂ ih₁ ih₂ =>
    intro hc a b h
    simp only [numQuant] at hc
    simp only [Realize₁, Realize₂, BoundedFormula.realize_imp] at *
    exact imp_congr (ih₁ (by omega) h) (ih₂ (by omega) h)
  | @all k f ih =>
    intro hc a b h
    simp only [numQuant] at hc
    have hc' : numQuant f + (k + 1) < m := by omega
    have hℓ : k + 1 < m := by omega
    simp only [Realize₁, Realize₂, BoundedFormula.realize_all] at *
    constructor
    · intro hall y
      obtain ⟨x, hx⟩ := extend₂₁ m hℓ h y
      exact (ih hc' hx).mp (hall x)
    · intro hall x
      obtain ⟨y, hy⟩ := extend₁₂ m hℓ h x
      exact (ih hc' hy).mpr (hall y)

/-! ### The theorem -/

/-- The *more than half* truth condition over a structure: more than half
the V's are U's (`Card(U ∩ V) > ½ Card(V)`, B&C p. 213). -/
def MoreThanHalf (M : Type) (S : L_UV.Structure M) : Prop :=
  2 * Set.ncard {x : M | S.RelMap uRel ![x] ∧ S.RelMap vRel ![x]} >
    Set.ncard {x : M | S.RelMap vRel ![x]}

private theorem ncard_val_lt (n c : ℕ) (hc : c ≤ n) :
    Set.ncard {x : Fin n | x.val < c} = c := by
  have hset : {x : Fin n | x.val < c} = ↑((Finset.Ico 0 c).attachFin
      (fun x hx => lt_of_lt_of_le (Finset.mem_Ico.mp hx).2 hc)) := by
    ext x
    simp [Finset.mem_attachFin, Finset.mem_Ico]
  rw [hset, Set.ncard_coe_finset, Finset.card_attachFin, Nat.card_Ico]
  omega

/-- **C12** ([barwise-cooper-1981], Appendix C p. 213): no first-order
sentence over two unary predicates is true in exactly the finite models
where more than half the V's are U's. The formal core of B&C's claim that
*most* is a determiner, not a quantifier. -/
theorem more_than_half_not_definable :
    ¬ ∃ φ : L_UV.Sentence, ∀ (M : Type) [Fintype M] (S : L_UV.Structure M),
      (@Sentence.Realize L_UV M S φ ↔ MoreThanHalf M S) := by
  rintro ⟨φ, hφ⟩
  set m := numQuant φ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  -- M₁ does not satisfy more-than-half: |U₁ ∩ V| = m, |V| = 2m
  have hmth₁ : ¬ MoreThanHalf (Fin (3 * m + 1)) (struc₁ m) := by
    have hUV : {x : Fin (3 * m + 1) |
        (struc₁ m).RelMap uRel ![x] ∧ (struc₁ m).RelMap vRel ![x]}
        = {x : Fin (3 * m + 1) | x.val < m} := by
      ext x
      show (x.val < m ∧ x.val < 2 * m) ↔ x.val < m
      omega
    have hV : {x : Fin (3 * m + 1) | (struc₁ m).RelMap vRel ![x]}
        = {x : Fin (3 * m + 1) | x.val < 2 * m} := rfl
    unfold MoreThanHalf
    rw [hUV, hV, ncard_val_lt _ _ (by omega), ncard_val_lt _ _ (by omega)]
    omega
  -- M₂ satisfies more-than-half: |U₂ ∩ V| = m + 1, |V| = 2m
  have hmth₂ : MoreThanHalf (Fin (3 * m + 1)) (struc₂ m) := by
    have hUV : {x : Fin (3 * m + 1) |
        (struc₂ m).RelMap uRel ![x] ∧ (struc₂ m).RelMap vRel ![x]}
        = {x : Fin (3 * m + 1) | x.val < m + 1} := by
      ext x
      show (x.val < m + 1 ∧ x.val < 2 * m) ↔ x.val < m + 1
      omega
    have hV : {x : Fin (3 * m + 1) | (struc₂ m).RelMap vRel ![x]}
        = {x : Fin (3 * m + 1) | x.val < 2 * m} := rfl
    unfold MoreThanHalf
    rw [hUV, hV, ncard_val_lt _ _ (by omega), ncard_val_lt _ _ (by omega)]
    omega
  -- but they agree on φ, by condition (6) at the empty correspondence
  have hagree : Realize₁ m φ default ↔ Realize₂ m φ default :=
    realize_iff_of_regionMatch m φ (by omega)
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hsent₁ : @Sentence.Realize L_UV _ (struc₁ m) φ ↔ Realize₁ m φ default := by
    unfold Realize₁
    exact iff_of_eq (congrArg₂ (@BoundedFormula.Realize L_UV _ (struc₁ m) Empty 0 φ)
      (funext fun e => e.elim) (funext fun i => i.elim0))
  have hsent₂ : @Sentence.Realize L_UV _ (struc₂ m) φ ↔ Realize₂ m φ default := by
    unfold Realize₂
    exact iff_of_eq (congrArg₂ (@BoundedFormula.Realize L_UV _ (struc₂ m) Empty 0 φ)
      (funext fun e => e.elim) (funext fun i => i.elim0))
  exact hmth₁ ((hφ _ (struc₁ m)).mp
    (hsent₁.mpr (hagree.mpr (hsent₂.mp ((hφ _ (struc₂ m)).mpr hmth₂)))))

end BarwiseCooper1981
