import Linglib.Features.Acceptability
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Toy
import Linglib.Semantics.Composition.Reduction
import Linglib.Semantics.Quantification.DomainRestriction
import Linglib.Core.Logic.FirstOrder.EhrenfeuchtFraisseGame

/-!
# Quantifier Universals Bridge
[barwise-cooper-1981] [mostowski-1957] [peters-westerstahl-2006] [van-benthem-1984] [van-de-pol-etal-2023]

Bridges the English determiner fragment (`English.Determiners.QuantityWord`)
to the GQ property predicates in `Quantification` and
`Quantification.Quantifier`.

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

-/

namespace BarwiseCooper1981

open English.Determiners (Monotonicity Strength QuantityWord)
open Quantification
open Quantification.DomainRestriction (DomainRestrictor
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
  · exact Quantification.no_conservative
  · exact Quantification.few_conservative
  · exact Quantification.some_conservative
  · exact Quantification.half_conservative
  · exact Quantification.most_conservative
  · exact Quantification.every_conservative

/-- The English quantifier lexicon assigns only conservative denotations
    ([barwise-cooper-1981]): every `GQ` in its range satisfies CONSERV. The
    per-form witness feeding the theory-layer lift `Quantifier.denote_conservative`. -/
theorem englishLexicon_conservative {α : Type*} [Fintype α] (s : String) :
    ∀ g ∈ English.Determiners.englishLexicon (α := α) s, Conservative g := by
  intro g hg
  unfold English.Determiners.englishLexicon at hg
  split at hg <;> simp only [List.mem_singleton, List.not_mem_nil] at hg
  all_goals (subst hg; first
    | exact no_conservative | exact few_conservative | exact some_conservative
    | exact half_conservative | exact most_conservative | exact every_conservative
    | exact both_conservative | exact neither_conservative)

/-- **Conservativity universal, record-keyed.** Every marked English quantifier
    denotes conservatively — the [barwise-cooper-1981] universal stated over the
    `Quantifier` *records* (via the theory-layer `Quantifier.denote`), not the
    `QuantityWord` enum. Obtained from the cross-linguistic lift
    `Quantifier.denote_conservative` applied to `englishLexicon_conservative`;
    vacuous for forms outside the lexicon (`denote = []`). -/
theorem conservativity_universal_denote {α : Type*} [Fintype α] (q : Quantifier) :
    ∀ g ∈ q.denote (English.Determiners.englishLexicon (α := α)), Conservative g :=
  Quantifier.denote_conservative English.Determiners.englishLexicon
    (englishLexicon_conservative (α := α)) q

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

Each theorem takes one quantity word's `QuantityWord.entry` *typological
label* (the textbook-consensus B&C Table II strength/monotonicity classification)
as a **hypothesis** and proves the corresponding genuine GQ **property of the
denotation** `QuantityWord.gqDenotation`:

- `strength = .weak`      ⟹ `Existential ⟦d⟧`      (intersective: passes there-insertion)
- `strength = .strong`    ⟹ `¬ Existential ⟦d⟧`
- `monotonicity = .increasing` ⟹ `ScopeUpwardMono ⟦d⟧`
- `monotonicity = .decreasing` ⟹ `ScopeDownwardMono ⟦d⟧`

So changing a `QuantityWord.entry` field still breaks exactly one theorem
(the label is a hypothesis), but the theorem now *earns* its content from the
denotation rather than self-reporting the stored field. Where the substrate
lacks the backing lemma the conclusion is left `sorry` with a `TODO`.

B&C's Table II classifies every/all (strong, ↑MON), some (weak, ↑MON),
no (weak, ↓MON), most (strong, ↑MON), many (weak, ↑MON), few (weak, ↓MON);
our scale omits "many" and adds proportional "half" (van-de-pol et al.).

**Caveat — "weak" ≠ `Existential` for proportional determiners.** B&C's "weak"
tracks felicity in there-sentences; for the *intersective* words (some, no)
it coincides with the GQ `Existential` property. But the table also labels the
*proportional* words few and half `.weak` (they do pass there-insertion:
"there are few cats"), and `Existential` *fails* for them — `few_sem`/`half_sem`
are not intersective. So the `weak ⟹ Existential` bridge is stated and proved
only for the intersective words; for few/half the genuine GQ fact is the
*negation* (`¬ Existential`), recorded below as a substrate gap. -/

/-- some: weak ⟹ `Existential`, and increasing ⟹ `ScopeUpwardMono`. -/
theorem table_II_some {α : Type*} [Fintype α] [DecidableEq α] :
    (QuantityWord.some_.entry.strength = .weak →
      Existential (QuantityWord.some_.gqDenotation (α := α))) ∧
    (QuantityWord.some_.entry.monotonicity = .increasing →
      ScopeUpwardMono (QuantityWord.some_.gqDenotation (α := α))) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · simpa only [QuantityWord.gqDenotation] using Quantification.some_existential
  · simpa only [QuantityWord.gqDenotation] using Quantification.some_scope_up

/-- no: weak ⟹ `Existential`, and decreasing ⟹ `ScopeDownwardMono`. -/
theorem table_II_none {α : Type*} [Fintype α] [DecidableEq α] :
    (QuantityWord.none_.entry.strength = .weak →
      Existential (QuantityWord.none_.gqDenotation (α := α))) ∧
    (QuantityWord.none_.entry.monotonicity = .decreasing →
      ScopeDownwardMono (QuantityWord.none_.gqDenotation (α := α))) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · simpa only [QuantityWord.gqDenotation] using Quantification.no_existential
  · simpa only [QuantityWord.gqDenotation] using Quantification.no_scope_down

/-- every/all: strong ⟹ `¬ Existential` (over a nonempty domain), and
    increasing ⟹ `ScopeUpwardMono`. The nonemptiness hypothesis is essential:
    over the empty domain every GQ is vacuously `Existential`. -/
theorem table_II_all {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] :
    (QuantityWord.all.entry.strength = .strong →
      ¬ Existential (QuantityWord.all.gqDenotation (α := α))) ∧
    (QuantityWord.all.entry.monotonicity = .increasing →
      ScopeUpwardMono (QuantityWord.all.gqDenotation (α := α))) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · -- every is positive-strong, hence not existential: witness R = univ, S = ∅.
    simp only [QuantityWord.gqDenotation]
    intro h
    obtain ⟨x⟩ := ‹Nonempty α›
    have hiff := h (fun _ => True) (fun _ => False)
    simp only [every_sem] at hiff
    exact hiff.mpr (fun _ _ => trivial) x trivial
  · simpa only [QuantityWord.gqDenotation] using Quantification.every_scope_up

/-- most: increasing ⟹ `ScopeUpwardMono` (polymorphic, `most_scope_up`). The
    strength ⟹ `¬ Existential` half is witnessed separately at `Fin 3`
    (`table_II_most_not_existential`): `most` is proportional, not intersective,
    so refuting `Existential` needs a `|α| ≥ 3` witness, not mere nonemptiness. -/
theorem table_II_most {α : Type*} [Fintype α] [DecidableEq α] :
    QuantityWord.most.entry.monotonicity = .increasing →
      ScopeUpwardMono (QuantityWord.most.gqDenotation (α := α)) := by
  intro _
  simpa only [QuantityWord.gqDenotation] using Quantification.most_scope_up

/-- most: strong ⟹ `¬ Existential`, witnessed at `Fin 3`. `most` is proportional,
    not intersective, so it blocks there-insertion ([barwise-cooper-1981] Table II).
    Refuting `Existential` needs `|α| ≥ 3` (1 elem in R∩S, 2 in R∖S): over `Fin 1`/
    `Fin 2` every GQ is vacuously `Existential`. Earned from `not_existential_most_sem`. -/
theorem table_II_most_not_existential :
    QuantityWord.most.entry.strength = .strong →
      ¬ Existential (QuantityWord.most.gqDenotation (α := Fin 3)) := by
  intro _
  simpa only [QuantityWord.gqDenotation] using Quantification.not_existential_most_sem

/-- few: decreasing ⟹ `ScopeDownwardMono` (`few_scope_down`). The table labels
    few `.weak`, but `few_sem` is proportional, *not* intersective, so the
    genuine GQ fact is `¬ Existential ⟦few⟧` (a substrate gap), not `Existential`. -/
theorem table_II_few {α : Type*} [Fintype α] [DecidableEq α] :
    QuantityWord.few.entry.monotonicity = .decreasing →
      ScopeDownwardMono (QuantityWord.few.gqDenotation (α := α)) := by
  intro _
  simpa only [QuantityWord.gqDenotation] using Quantification.few_scope_down

/-- few: strong/weak ⟹ existential status, witnessed at `Fin 3`. The table's
    `.weak` label tracks there-insertion; the genuine GQ property is
    `¬ Existential` because `few_sem` is proportional, not intersective
    (`|R∩S| < |R∖S|` is not determined by `|R∩S|` alone). Earned from
    `not_existential_few_sem`. -/
theorem table_II_few_not_existential :
    ¬ Existential (QuantityWord.few.gqDenotation (α := Fin 3)) := by
  simpa only [QuantityWord.gqDenotation] using Quantification.not_existential_few_sem

/-- half: non-monotone, so the increasing/decreasing bridges are vacuously true
    (the label hypothesis is unsatisfiable for half). -/
theorem table_II_half {α : Type*} [Fintype α] [DecidableEq α] :
    (QuantityWord.half.entry.monotonicity = .increasing →
      ScopeUpwardMono (QuantityWord.half.gqDenotation (α := α))) ∧
    (QuantityWord.half.entry.monotonicity = .decreasing →
      ScopeDownwardMono (QuantityWord.half.gqDenotation (α := α))) :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- half: the table labels half `.weak`, but `half_sem` is proportional, so the
    genuine GQ property is `¬ Existential ⟦half⟧`, witnessed at `Fin 3`.
    `Existential half_sem` (`2|R∩S| = |R| ↔ 2|R∩S| = |R∩S|`) is false; refuting it
    needs a witness with `R∖S` non-empty. Earned from `not_existential_half_sem`. -/
theorem table_II_half_not_existential :
    ¬ Existential (QuantityWord.half.gqDenotation (α := Fin 3)) := by
  simpa only [QuantityWord.gqDenotation] using Quantification.not_existential_half_sem

-- ============================================================================
-- §5. Monotonicity–Strength Correlation
-- ============================================================================

/-- All English quantity words except "half" are monotone in scope (each is
    `ScopeUpwardMono` or `ScopeDownwardMono`); "half" is the lone non-monotone
    simple determiner ([van-de-pol-etal-2023]). Stated as a real disjunction of
    GQ monotonicity properties, witnessed per word from the substrate lemmas. -/
theorem english_quantifiers_mostly_monotone {α : Type*} [Fintype α] [DecidableEq α] :
    ScopeDownwardMono (QuantityWord.none_.gqDenotation (α := α)) ∧
    ScopeDownwardMono (QuantityWord.few.gqDenotation (α := α)) ∧
    ScopeUpwardMono (QuantityWord.some_.gqDenotation (α := α)) ∧
    ScopeUpwardMono (QuantityWord.most.gqDenotation (α := α)) ∧
    ScopeUpwardMono (QuantityWord.all.gqDenotation (α := α)) := by
  simp only [QuantityWord.gqDenotation]
  exact ⟨Quantification.no_scope_down, Quantification.few_scope_down,
         Quantification.some_scope_up, Quantification.most_scope_up,
         Quantification.every_scope_up⟩

/-- "Half" is non-monotone: it is neither scope-upward nor scope-downward
    monotone ([van-de-pol-etal-2023]), witnessed at `Fin 3` (a 2-element restrictor
    on which half flips true→false under scope growth/shrinkage). Earned from
    `half_not_monotone`. -/
theorem half_nonmonotone :
    ¬ ScopeUpwardMono (QuantityWord.half.gqDenotation (α := Fin 3)) ∧
    ¬ ScopeDownwardMono (QuantityWord.half.gqDenotation (α := Fin 3)) := by
  simpa only [QuantityWord.gqDenotation] using Quantification.half_not_monotone

/-- [barwise-cooper-1981] U7 (monotonicity–strength correlation): the strong
    English determiners (every, most) are scope-↑MON. Both are positive-strong,
    so the universal reduces to: strong → increasing, here proved as the genuine
    `ScopeUpwardMono` property of each denotation. -/
theorem strong_implies_increasing {α : Type*} [Fintype α] [DecidableEq α] :
    (QuantityWord.all.entry.strength = .strong →
      ScopeUpwardMono (QuantityWord.all.gqDenotation (α := α))) ∧
    (QuantityWord.most.entry.strength = .strong →
      ScopeUpwardMono (QuantityWord.most.gqDenotation (α := α))) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · simpa only [QuantityWord.gqDenotation] using Quantification.every_scope_up
  · simpa only [QuantityWord.gqDenotation] using Quantification.most_scope_up

-- ============================================================================
-- §6. Weak/Strong and There-Insertion
-- ============================================================================

/-- Weak intersective determiners allow there-insertion, formalized as the
    `Existential` property ([barwise-cooper-1981] §4.6; [peters-westerstahl-2006]
    existential ↔ there-insertion). "There are some/no cats." -/
theorem weak_there_insertion {α : Type*} [Fintype α] [DecidableEq α] :
    Existential (QuantityWord.some_.gqDenotation (α := α)) ∧
    Existential (QuantityWord.none_.gqDenotation (α := α)) := by
  simp only [QuantityWord.gqDenotation]
  exact ⟨Quantification.some_existential, Quantification.no_existential⟩

/-- Strong determiners block there-insertion: `¬ Existential` over a nonempty
    domain ([barwise-cooper-1981] Table II). The `most` case is witnessed at
    `Fin 3` in `table_II_most_not_existential` (proportional `most` needs `|α| ≥ 3`). -/
theorem strong_no_there_insertion {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] :
    ¬ Existential (QuantityWord.all.gqDenotation (α := α)) :=
  (table_II_all (α := α)).1 rfl

-- ============================================================================
-- §7. Symmetry ↔ Weak
-- ============================================================================

/-- Weak (intersective) English determiners are symmetric
    ([peters-westerstahl-2006], symmetric ↔ there-insertion ↔ weak), proved as
    the genuine `QSymmetric` property of the denotation. -/
theorem weak_are_symmetric {α : Type*} [Fintype α] [DecidableEq α] :
    QSymmetric (QuantityWord.some_.gqDenotation (α := α)) ∧
    QSymmetric (QuantityWord.none_.gqDenotation (α := α)) := by
  simp only [QuantityWord.gqDenotation]
  exact ⟨Quantification.some_symmetric, Quantification.no_symmetric⟩

/-! Strong English determiners are not symmetric ([peters-westerstahl-2006]).
The genuine `¬ QSymmetric` property for `all` (= `every_sem`) is proved as
`strong_all_not_symmetric` below, over the `ToyEntity` witness it requires; for
`most` it is `strong_most_not_symmetric`, witnessed at `Fin 3`. -/

/-- Strong `most` is not symmetric, as a property of its denotation over the
    `Fin 3` witness ([peters-westerstahl-2006]). `most R S ↔ most S R` fails for
    `R = {0}`, `S = {0,1}`: `most R S` holds (`|R∩S| = 1 > |R∖S| = 0`) but
    `most S R` does not (`|S∩R| = 1 > |S∖R| = 1` is false). Earned from
    `not_qsymmetric_most_sem`. -/
theorem strong_most_not_symmetric :
    ¬ QSymmetric (QuantityWord.most.gqDenotation (α := Fin 3)) := by
  simpa only [QuantityWord.gqDenotation] using Quantification.not_qsymmetric_most_sem

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

/-- Strong `all` (= `every_sem`) is not symmetric, as a property of its
    denotation `QuantityWord.all.gqDenotation` over the `ToyEntity` witness
    ([peters-westerstahl-2006]). The genuine §7 strong-not-symmetric fact,
    earned from the denotation rather than the typological `.strength` label. -/
theorem strong_all_not_symmetric :
    ¬ QSymmetric (QuantityWord.all.gqDenotation (α := ToyEntity)) := by
  simpa only [QuantityWord.gqDenotation] using every_not_symmetric

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
  exact Quantification.dualQ_every_eq_some

/-- Inner negation maps ⟦every⟧ to ⟦no⟧: every~ = no ([barwise-cooper-1981] §4.11).
    ∀x. R(x) → ¬S(x) = ¬∃x. R(x) ∧ S(x).
    Bridges `pinnerNeg_every_eq_no` to fragment entries. -/
theorem innerNeg_all_eq_none {α : Type*} [Fintype α] [DecidableEq α] :
    innerNeg (QuantityWord.all.gqDenotation (α := α)) = QuantityWord.none_.gqDenotation (α := α) := by
  simp only [QuantityWord.gqDenotation]
  exact Quantification.innerNeg_every_eq_no

/-- Outer negation maps ⟦some⟧ to ⟦no⟧: ~some = no ([barwise-cooper-1981] §4.11).
    ¬(∃x. R(x) ∧ S(x)) = ∀x. R(x) → ¬S(x).
    Bridges `pouterNeg_some_eq_no` to fragment entries. -/
theorem outerNeg_some_eq_none {α : Type*} [Fintype α] [DecidableEq α] :
    outerNeg (QuantityWord.some_.gqDenotation (α := α)) = QuantityWord.none_.gqDenotation (α := α) := by
  simp only [QuantityWord.gqDenotation]
  exact Quantification.outerNeg_some_eq_no

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
  case all => exact Quantification.every_scope_up
  case some_ => exact Quantification.some_scope_up
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

   Proved in `Quantification`:
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

end BarwiseCooper1981

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
def numQuant : ∀ {α : Type*} {n : ℕ}, L_UV.BoundedFormula α n → ℕ
  | _, _, .falsum => 0
  | _, _, .equal _ _ => 0
  | _, _, .rel _ _ => 0
  | _, _, .imp f₁ f₂ => numQuant f₁ + numQuant f₂
  | _, _, .all f => numQuant f + 1

/-- `M₁`: `U` is `[0, m)`, `V` is `[0, 2m)` — exactly half the V's are U's. -/
@[reducible] def struc₁ (m k : ℕ) : L_UV.Structure (Fin k) where
  funMap := fun f _ => f.elim
  RelMap {n} r v :=
    match r, v with
    | .U, v => (v 0).val < m
    | .V, v => (v 0).val < 2 * m

/-- `M₂`: `U` is `[0, m+1)`, `V` is `[0, 2m)` — more than half the V's are
U's. -/
@[reducible] def struc₂ (m k : ℕ) : L_UV.Structure (Fin k) where
  funMap := fun f _ => f.elim
  RelMap {n} r v :=
    match r, v with
    | .U, v => (v 0).val < m + 1
    | .V, v => (v 0).val < 2 * m

/-- Realization in `M₁` (structures are term-level, so instances are pinned
explicitly). -/
def Realize₁ (m k : ℕ) {ℓ : ℕ} (φ : L_UV.BoundedFormula Empty ℓ)
    (xs : Fin ℓ → Fin k) : Prop :=
  @BoundedFormula.Realize L_UV _ (struc₁ m k) Empty ℓ φ default xs

/-- Realization in `M₂`. -/
def Realize₂ (m k : ℕ) {ℓ : ℕ} (φ : L_UV.BoundedFormula Empty ℓ)
    (xs : Fin ℓ → Fin k) : Prop :=
  @BoundedFormula.Realize L_UV _ (struc₂ m k) Empty ℓ φ default xs

/-- B&C's one-one correspondence (proof of C12, condition on `aᵢ ↔ bᵢ`):
pairing-injective, and respecting the `U`-regions (`U₁` against `U₂`) and
the shared `V`-region. -/
structure RegionMatch (m k : ℕ) {ℓ : ℕ} (a b : Fin ℓ → Fin k) : Prop where
  inj : ∀ i j, a i = a j ↔ b i = b j
  inU : ∀ i, (a i).val < m ↔ (b i).val < m + 1
  inV : ∀ i, (a i).val < 2 * m ↔ (b i).val < 2 * m

/-- Every `L_UV`-term is a variable (the language has no function symbols). -/
private theorem term_eq_var {γ : Type} (t : L_UV.Term γ) : ∃ i, t = Term.var i := by
  cases t with
  | var i => exact ⟨i, rfl⟩
  | func f _ => exact f.elim

/-- Fresh element in a value-interval of `Fin (3m+1)`: if the interval holds
more elements than the tuple uses, something in it avoids the tuple. -/
private theorem exists_fresh {k ℓ : ℕ} (f : Fin ℓ → Fin k) (lo hi : ℕ)
    (hhi : hi ≤ k) (hroom : ℓ < hi - lo) :
    ∃ y : Fin k, lo ≤ y.val ∧ y.val < hi ∧ ∀ i, f i ≠ y := by
  by_contra h
  push_neg at h
  have hsub : (Finset.Ico lo hi).attachFin
      (fun x hx => lt_of_lt_of_le (Finset.mem_Ico.mp hx).2 hhi)
      ⊆ Finset.image f Finset.univ := by
    intro y hy
    have hy' := (Finset.mem_attachFin _).mp hy
    obtain ⟨i, hi'⟩ := h y (Finset.mem_Ico.mp hy').1 (Finset.mem_Ico.mp hy').2
    exact hi' ▸ Finset.mem_image_of_mem f (Finset.mem_univ i)
  have hcard := Finset.card_le_card hsub
  have himg : (Finset.image f Finset.univ).card ≤ ℓ :=
    le_trans Finset.card_image_le (by simp)
  rw [Finset.card_attachFin, Nat.card_Ico] at hcard
  omega

/-- Extending a correspondence with an already-matched pair. -/
private theorem regionMatch_snoc_matched (m k : ℕ) {ℓ : ℕ}
    {a b : Fin ℓ → Fin k} (h : RegionMatch m k a b) (i : Fin ℓ) :
    RegionMatch m k (Fin.snoc a (a i)) (Fin.snoc b (b i)) := by
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
private theorem regionMatch_snoc_fresh (m k : ℕ) {ℓ : ℕ}
    {a b : Fin ℓ → Fin k} (h : RegionMatch m k a b)
    {x y : Fin k} (hxa : ∀ i, a i ≠ x) (hyb : ∀ i, b i ≠ y)
    (hU : x.val < m ↔ y.val < m + 1) (hV : x.val < 2 * m ↔ y.val < 2 * m) :
    RegionMatch m k (Fin.snoc a x) (Fin.snoc b y) := by
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
private theorem extend₁₂ (m k : ℕ) (hk : 3 * m ≤ k) {ℓ : ℕ} (hℓ : ℓ + 1 < m)
    {a b : Fin ℓ → Fin k} (h : RegionMatch m k a b)
    (x : Fin k) :
    ∃ y, RegionMatch m k (Fin.snoc a x) (Fin.snoc b y) := by
  by_cases hx : ∃ i, a i = x
  · obtain ⟨i, rfl⟩ := hx
    exact ⟨b i, regionMatch_snoc_matched m k h i⟩
  · push_neg at hx
    by_cases h1 : x.val < m
    · obtain ⟨y, hy1, hy2, hy3⟩ := exists_fresh b 0 (m + 1) (by omega) (by omega)
      exact ⟨y, regionMatch_snoc_fresh m k h hx hy3 (by omega) (by omega)⟩
    · by_cases h2 : x.val < 2 * m
      · obtain ⟨y, hy1, hy2, hy3⟩ := exists_fresh b (m + 1) (2 * m) (by omega) (by omega)
        exact ⟨y, regionMatch_snoc_fresh m k h hx hy3 (by omega) (by omega)⟩
      · obtain ⟨y, hy1, hy2, hy3⟩ := exists_fresh b (2 * m) k (by omega) (by omega)
        exact ⟨y, regionMatch_snoc_fresh m k h hx hy3 (by omega) (by omega)⟩

/-- Extend a correspondence by an `M₂`-side element. -/
private theorem extend₂₁ (m k : ℕ) (hk : 3 * m ≤ k) {ℓ : ℕ} (hℓ : ℓ + 1 < m)
    {a b : Fin ℓ → Fin k} (h : RegionMatch m k a b)
    (y : Fin k) :
    ∃ x, RegionMatch m k (Fin.snoc a x) (Fin.snoc b y) := by
  by_cases hy : ∃ i, b i = y
  · obtain ⟨i, rfl⟩ := hy
    exact ⟨a i, regionMatch_snoc_matched m k h i⟩
  · push_neg at hy
    by_cases h1 : y.val < m + 1
    · obtain ⟨x, hx1, hx2, hx3⟩ := exists_fresh a 0 m (by omega) (by omega)
      exact ⟨x, regionMatch_snoc_fresh m k h hx3 hy (by omega) (by omega)⟩
    · by_cases h2 : y.val < 2 * m
      · obtain ⟨x, hx1, hx2, hx3⟩ := exists_fresh a m (2 * m) (by omega) (by omega)
        exact ⟨x, regionMatch_snoc_fresh m k h hx3 hy (by omega) (by omega)⟩
      · obtain ⟨x, hx1, hx2, hx3⟩ := exists_fresh a (2 * m) k (by omega) (by omega)
        exact ⟨x, regionMatch_snoc_fresh m k h hx3 hy (by omega) (by omega)⟩

/-- B&C's condition (6) (p. 214): a formula whose quantifier count plus
free-variable count is below `m` cannot distinguish region-matched tuples
across `M₁`/`M₂`. Structural induction; at each quantifier "there is always
enough room to extend the one-one correspondence one more step". -/
theorem realize_iff_of_regionMatch (m k : ℕ) (hk : 3 * m ≤ k) :
    ∀ {ℓ : ℕ} (φ : L_UV.BoundedFormula Empty ℓ), numQuant φ + ℓ < m →
      ∀ {a b : Fin ℓ → Fin k}, RegionMatch m k a b →
        (Realize₁ m k φ a ↔ Realize₂ m k φ b) := by
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
      show ((fun p => @Term.realize L_UV _ (struc₁ m k) _ (Sum.elim default a) (ts p)) 0).val < m ↔
        ((fun p => @Term.realize L_UV _ (struc₂ m k) _ (Sum.elim default b) (ts p)) 0).val < m + 1
      simp only [hi, Term.realize_var, Sum.elim_inr]
      exact h.inU i
    | V =>
      obtain ⟨i, hi⟩ := term_eq_var (ts 0)
      rcases i with e | i
      · exact e.elim
      show ((fun p => @Term.realize L_UV _ (struc₁ m k) _ (Sum.elim default a) (ts p)) 0).val < 2 * m ↔
        ((fun p => @Term.realize L_UV _ (struc₂ m k) _ (Sum.elim default b) (ts p)) 0).val < 2 * m
      simp only [hi, Term.realize_var, Sum.elim_inr]
      exact h.inV i
  | imp f₁ f₂ ih₁ ih₂ =>
    intro hc a b h
    simp only [numQuant] at hc
    simp only [Realize₁, Realize₂, BoundedFormula.realize_imp] at *
    exact imp_congr (ih₁ (by omega) h) (ih₂ (by omega) h)
  | @all j f ih =>
    intro hc a b h
    simp only [numQuant] at hc
    have hc' : numQuant f + (j + 1) < m := by omega
    have hℓ : j + 1 < m := by omega
    simp only [Realize₁, Realize₂, BoundedFormula.realize_all] at *
    constructor
    · intro hall y
      obtain ⟨x, hx⟩ := extend₂₁ m k hk hℓ h y
      exact (ih hc' hx).mp (hall x)
    · intro hall x
      obtain ⟨y, hy⟩ := extend₁₂ m k hk hℓ h x
      exact (ih hc' hy).mpr (hall y)

/-! ### The theorem -/

/-- "More than half the V's are U's" over bare predicates
(`Card(U ∩ V) > ½ Card(V)`, B&C p. 213). -/
def MostUV {M : Type} (U V : M → Prop) : Prop :=
  2 * Set.ncard {x | U x ∧ V x} > Set.ncard {x | V x}

/-- The *more than half* truth condition over a structure. -/
def MoreThanHalf (M : Type) (S : L_UV.Structure M) : Prop :=
  MostUV (fun x => S.RelMap uRel ![x]) (fun x => S.RelMap vRel ![x])

private theorem ncard_val_lt (n c : ℕ) (hc : c ≤ n) :
    Set.ncard {x : Fin n | x.val < c} = c := by
  have hset : {x : Fin n | x.val < c} = ↑((Finset.Ico 0 c).attachFin
      (fun x hx => lt_of_lt_of_le (Finset.mem_Ico.mp hx).2 hc)) := by
    ext x
    simp [Finset.mem_attachFin, Finset.mem_Ico]
  rw [hset, Set.ncard_coe_finset, Finset.card_attachFin, Nat.card_Ico]
  omega

/-- `MoreThanHalf` over a structure whose `U` is `[0, c)` and `V` is
`[0, 2m)` reduces to the count comparison `2 * c > 2 * m`. -/
private theorem moreThanHalf_iff {k m c : ℕ} (S : L_UV.Structure (Fin k))
    (hU : ∀ x : Fin k, S.RelMap uRel ![x] ↔ x.val < c)
    (hV : ∀ x : Fin k, S.RelMap vRel ![x] ↔ x.val < 2 * m)
    (hc : c ≤ 2 * m) (hm : 2 * m ≤ k) :
    MoreThanHalf (Fin k) S ↔ 2 * c > 2 * m := by
  have hUV : {x : Fin k | S.RelMap uRel ![x] ∧ S.RelMap vRel ![x]}
      = {x : Fin k | x.val < c} := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hU, hV]
    omega
  have hVs : {x : Fin k | S.RelMap vRel ![x]}
      = {x : Fin k | x.val < 2 * m} := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hV]
  unfold MoreThanHalf MostUV
  rw [hUV, hVs, ncard_val_lt _ _ (by omega), ncard_val_lt _ _ hm]

/-- **C12** ([barwise-cooper-1981], Appendix C p. 213): no first-order
sentence over two unary predicates is true in exactly the finite models
where more than half the V's are U's. The formal core of B&C's claim that
*most* is a determiner, not a quantifier. -/
theorem more_than_half_not_definable :
    ¬ ∃ φ : L_UV.Sentence, ∀ (M : Type) [Fintype M] [Nonempty M]
      (S : L_UV.Structure M),
      (@Sentence.Realize L_UV M S φ ↔ MoreThanHalf M S) := by
  rintro ⟨φ, hφ⟩
  set m := numQuant φ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  -- M₁ does not satisfy more-than-half: |U₁ ∩ V| = m, |V| = 2m
  have hmth₁ : ¬ MoreThanHalf (Fin (3 * m + 1)) (struc₁ m (3 * m + 1)) := by
    rw [moreThanHalf_iff (m := m) (c := m) _ (fun x => Iff.rfl) (fun x => Iff.rfl)
      (by omega) (by omega)]
    omega
  -- M₂ satisfies more-than-half: |U₂ ∩ V| = m + 1, |V| = 2m
  have hmth₂ : MoreThanHalf (Fin (3 * m + 1)) (struc₂ m (3 * m + 1)) := by
    rw [moreThanHalf_iff (m := m) (c := m + 1) _ (fun x => Iff.rfl) (fun x => Iff.rfl)
      (by omega) (by omega)]
    omega
  -- but they agree on φ, by condition (6) at the empty correspondence
  have hagree : Realize₁ m (3 * m + 1) φ default ↔ Realize₂ m (3 * m + 1) φ default :=
    realize_iff_of_regionMatch m (3 * m + 1) (by omega) φ (by omega)
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hsent₁ : @Sentence.Realize L_UV _ (struc₁ m (3 * m + 1)) φ ↔ Realize₁ m (3 * m + 1) φ default := by
    unfold Realize₁
    exact iff_of_eq (congrArg₂ (@BoundedFormula.Realize L_UV _ (struc₁ m (3 * m + 1)) Empty 0 φ)
      (funext fun e => e.elim) (funext fun i => i.elim0))
  have hsent₂ : @Sentence.Realize L_UV _ (struc₂ m (3 * m + 1)) φ ↔ Realize₂ m (3 * m + 1) φ default := by
    unfold Realize₂
    exact iff_of_eq (congrArg₂ (@BoundedFormula.Realize L_UV _ (struc₂ m (3 * m + 1)) Empty 0 φ)
      (funext fun e => e.elim) (funext fun i => i.elim0))
  exact hmth₁ ((hφ _ (struc₁ m (3 * m + 1))).mp
    (hsent₁.mpr (hagree.mpr (hsent₂.mp ((hφ _ (struc₂ m (3 * m + 1))).mpr hmth₂)))))

/-! ### The same result via the general Ehrenfeucht–Fraïssé apparatus

The proof above is B&C's hand-rolled Fraïssé argument. The same conclusion follows
from the project's *general* finite-rank EF engine
(`Core.Logic.FirstOrder.EhrenfeuchtFraisseGame`): build, for each rank `k`, a pair of
`L_UV`-structures that are rank-`k` back-and-forth equivalent yet separated by *more
than half*, then feed `nEquiv_of_backForth` into `not_foDefinable_of_nEquiv`. This
section is a *demonstration* of that apparatus on a known result — the colored-set
back-and-forth of Libkin, *Elements of Finite Model Theory* §3 (Cor 3.10 and the two-
unary-predicate "colored sets" example) — alongside, not in place of, B&C's own proof.

The rank-`k` witnesses are exactly B&C's `struc₁`/`struc₂` instantiated at `m = k + 1`
on the domain `Fin (3·(k+1)+1)`: the colour classes `U∩V`, `V \ U`, and `¬V` then each
have matching size or both have size `≥ k + 1`, which is the "enough room" condition the
`RegionMatch`-extension lemmas (`extend₁₂`/`extend₂₁`) already discharge. -/

/-- Every `L_UV`-term is a variable, restated over `Fin m'` free variables (the file's
`term_eq_var` is `private` and over `Empty`). -/
private theorem term_eq_var_fin {γ : Type} (t : L_UV.Term γ) : ∃ i, t = Term.var i := by
  cases t with
  | var i => exact ⟨i, rfl⟩
  | func f _ => exact f.elim

private theorem sumElim_eq_append {m' n k : ℕ} (v : Fin m' → Fin k) (xs : Fin n → Fin k)
    (i : Fin m' ⊕ Fin n) : Sum.elim v xs i = (Fin.append v xs) (finSumFinEquiv i) := by
  rcases i with i | i <;> simp [Fin.append_left, Fin.append_right]

/-- **Quantifier-free agreement (`BackForth 0` base case).** Region-matched tuples
satisfy the same quantifier-rank-`0` formulas. Generalized over the bound-variable count
`n` (so the `all` case is vacuous: it would force `qr ≥ 1`); the free tuple `v`/`w` and
the bound tuple `xs`/`ys` are matched jointly via `Fin.append`. -/
private theorem realize_iff_of_regionMatch_qf (m k : ℕ) :
    ∀ {m' n : ℕ} (φ : L_UV.BoundedFormula (Fin m') n), φ.qr = 0 →
      ∀ {v w : Fin m' → Fin k} {xs ys : Fin n → Fin k},
        RegionMatch m k (Fin.append v xs) (Fin.append w ys) →
        (@BoundedFormula.Realize L_UV _ (struc₁ m k) (Fin m') n φ v xs ↔
         @BoundedFormula.Realize L_UV _ (struc₂ m k) (Fin m') n φ w ys) := by
  intro m' n φ
  induction φ with
  | falsum => intro _ v w xs ys _; exact Iff.rfl
  | equal t₁ t₂ =>
    intro _ v w xs ys h
    obtain ⟨i, rfl⟩ := term_eq_var_fin t₁
    obtain ⟨j, rfl⟩ := term_eq_var_fin t₂
    simp only [BoundedFormula.Realize, Term.realize_var]
    rw [sumElim_eq_append v xs i, sumElim_eq_append v xs j,
        sumElim_eq_append w ys i, sumElim_eq_append w ys j]
    exact h.inj _ _
  | rel R ts =>
    intro _ v w xs ys h
    cases R with
    | U =>
      obtain ⟨i, hi⟩ := term_eq_var_fin (ts 0)
      simp only [BoundedFormula.Realize]
      show ((fun p => @Term.realize L_UV _ (struc₁ m k) _ (Sum.elim v xs) (ts p)) 0).val < m ↔
        ((fun p => @Term.realize L_UV _ (struc₂ m k) _ (Sum.elim w ys) (ts p)) 0).val < m + 1
      simp only [hi, Term.realize_var]
      rw [sumElim_eq_append v xs i, sumElim_eq_append w ys i]
      exact h.inU _
    | V =>
      obtain ⟨i, hi⟩ := term_eq_var_fin (ts 0)
      simp only [BoundedFormula.Realize]
      show ((fun p => @Term.realize L_UV _ (struc₁ m k) _ (Sum.elim v xs) (ts p)) 0).val < 2 * m ↔
        ((fun p => @Term.realize L_UV _ (struc₂ m k) _ (Sum.elim w ys) (ts p)) 0).val < 2 * m
      simp only [hi, Term.realize_var]
      rw [sumElim_eq_append v xs i, sumElim_eq_append w ys i]
      exact h.inV _
  | imp f₁ f₂ ih₁ ih₂ =>
    intro hφ v w xs ys h
    rw [BoundedFormula.qr_imp] at hφ
    simp only [BoundedFormula.realize_imp]
    exact imp_congr (ih₁ (by omega) h) (ih₂ (by omega) h)
  | all f ih =>
    intro hφ v w xs ys h
    rw [BoundedFormula.qr_all] at hφ
    omega

/-- **The colored-set back-and-forth between `struc₁` and `struc₂`.** A region match of
two `ℓ`-tuples lifts to the rank-`r` EF back-and-forth as long as `ℓ + r < m` (so each of
the `r` remaining rounds still has "enough room" to extend the correspondence). The base
case is `realize_iff_of_regionMatch_qf`; the forth/back steps reuse the file's
`extend₁₂`/`extend₂₁`. -/
private theorem backForth_of_regionMatch (m k : ℕ) (hk : 3 * m ≤ k) :
    ∀ (r : ℕ) {ℓ : ℕ}, ℓ + r < m → ∀ {v w : Fin ℓ → Fin k}, RegionMatch m k v w →
      @BackForth L_UV (Fin k) (Fin k) (struc₁ m k) (struc₂ m k) r ℓ v w := by
  intro r
  induction r with
  | zero =>
    intro ℓ _ v w h φ hφ
    have hv : Fin.append v (default : Fin 0 → Fin k) = v := by
      rw [Subsingleton.elim (default : Fin 0 → Fin k) Fin.elim0, Fin.append_elim0]; rfl
    have hw : Fin.append w (default : Fin 0 → Fin k) = w := by
      rw [Subsingleton.elim (default : Fin 0 → Fin k) Fin.elim0, Fin.append_elim0]; rfl
    exact realize_iff_of_regionMatch_qf m k φ hφ (v := v) (w := w)
      (xs := default) (ys := default) (by rw [hv, hw]; exact h)
  | succ r ih =>
    intro ℓ hℓ v w h
    refine ⟨fun a => ?_, fun b => ?_⟩
    · obtain ⟨b, hb⟩ := extend₁₂ m k hk (by omega) h a
      exact ⟨b, ih (by omega) hb⟩
    · obtain ⟨a, ha⟩ := extend₂₁ m k hk (by omega) h b
      exact ⟨a, ih (by omega) ha⟩

/-- `MoreThanHalf` as a property of bundled `L_UV`-structures, for the EF inexpressibility
corollary `not_foDefinable_of_nEquiv`. -/
def MoreThanHalfPred (M : CategoryTheory.Bundled.{0} L_UV.Structure) : Prop :=
  MoreThanHalf M M.str

/-- Rank-`k` witness `A`: `U = [0, k+1)`, `V = [0, 2k+2)` on `Fin (3k+4)` — exactly half
the V's are U's, so `¬ MoreThanHalf`. -/
def efWitnessA (k : ℕ) : CategoryTheory.Bundled.{0} L_UV.Structure :=
  ⟨Fin (3 * (k + 1) + 1), struc₁ (k + 1) (3 * (k + 1) + 1)⟩

/-- Rank-`k` witness `B`: `U = [0, k+2)`, `V = [0, 2k+2)` on `Fin (3k+4)` — more than half
the V's are U's, so `MoreThanHalf`. -/
def efWitnessB (k : ℕ) : CategoryTheory.Bundled.{0} L_UV.Structure :=
  ⟨Fin (3 * (k + 1) + 1), struc₂ (k + 1) (3 * (k + 1) + 1)⟩

private theorem not_moreThanHalf_efWitnessA (k : ℕ) : ¬ MoreThanHalfPred (efWitnessA k) := by
  show ¬ MoreThanHalf (Fin (3 * (k + 1) + 1)) (struc₁ (k + 1) (3 * (k + 1) + 1))
  rw [moreThanHalf_iff (m := k + 1) (c := k + 1) _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (by omega) (by omega)]
  omega

private theorem moreThanHalf_efWitnessB (k : ℕ) : MoreThanHalfPred (efWitnessB k) := by
  show MoreThanHalf (Fin (3 * (k + 1) + 1)) (struc₂ (k + 1) (3 * (k + 1) + 1))
  rw [moreThanHalf_iff (m := k + 1) (c := k + 2) _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (by omega) (by omega)]
  omega

private theorem nEquiv_efWitness (k : ℕ) : NEquiv k (efWitnessA k) (efWitnessB k) := by
  haveI : Nonempty (efWitnessA k : Type) := ⟨(0 : Fin (3 * (k + 1) + 1))⟩
  haveI : Nonempty (efWitnessB k : Type) := ⟨(0 : Fin (3 * (k + 1) + 1))⟩
  refine nEquiv_of_backForth (efWitnessA k) (efWitnessB k) ?_
  rw [Subsingleton.elim (default : Fin 0 → (efWitnessA k : Type))
        (default : Fin 0 → Fin (3 * (k + 1) + 1)),
      Subsingleton.elim (default : Fin 0 → (efWitnessB k : Type))
        (default : Fin 0 → Fin (3 * (k + 1) + 1))]
  exact backForth_of_regionMatch (k + 1) (3 * (k + 1) + 1) (by omega) k (ℓ := 0) (by omega)
    (v := default) (w := default) ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-- **C12 via the general EF apparatus** ([barwise-cooper-1981] Appendix C, reproved
through `Core.Logic.FirstOrder.EhrenfeuchtFraisseGame`). *More than half the V's are U's*
is not first-order definable: for each rank `k` the structures `efWitnessA k` and
`efWitnessB k` are `k`-equivalent (a colored-set back-and-forth) yet disagree on the
property, so `not_foDefinable_of_nEquiv` applies. Cf. `more_than_half_not_definable`, which
proves the same via B&C's own hand-rolled Fraïssé argument; Libkin, *Elements of Finite
Model Theory* §3 (Cor 3.10 + colored sets). -/
theorem more_than_half_not_FODefinable_via_EF : ¬ FODefinable MoreThanHalfPred := by
  refine not_foDefinable_of_nEquiv (fun n => ⟨efWitnessA n, efWitnessB n, nEquiv_efWitness n, ?_⟩)
  intro hiff
  exact not_moreThanHalf_efWitnessA n (hiff.mpr (moreThanHalf_efWitnessB n))

end BarwiseCooper1981

/-! ### Appendix C: C13 — *most* is a determiner, not a quantifier

[barwise-cooper-1981] C13 (pp. 214–215): extend the monadic language with a
quantifier symbol `Q`, where `Qx[φ(x)]` means "more than half of all things
satisfy φ". Even in this language, no sentence is true in exactly the finite
models where more than half the V's are U's: the *relativized* quantifier is
not definable from the *unrelativized* one. So *most* cannot be a unary
sentence operator over the domain — it must be a determiner (a footnote
credits a related unpublished 1965 theorem to David Kaplan).

The proof is B&C's: a translation `star` eliminating `Q` (`Qx θ` becomes
"every `x` outside `V` and the free variables satisfies `θ*`"), correct on
models where the domain swamps `V` (property (P), via "a trivial
automorphism argument"), reducing to C12's models. -/

namespace BarwiseCooper1981

open FirstOrder Language

/-- Formulas of B&C's `L(Q)`: the monadic language of C12 (atoms `U`, `V`,
equality) plus the unrelativized majority quantifier `Qx[·]`. De Bruijn
indices; atoms apply directly to variables (the language has no function
symbols). -/
inductive QFormula : ℕ → Type where
  | falsum {n : ℕ} : QFormula n
  | equal {n : ℕ} (i j : Fin n) : QFormula n
  | isU {n : ℕ} (i : Fin n) : QFormula n
  | isV {n : ℕ} (i : Fin n) : QFormula n
  | imp {n : ℕ} (f₁ f₂ : QFormula n) : QFormula n
  | all {n : ℕ} (f : QFormula (n + 1)) : QFormula n
  | qx {n : ℕ} (f : QFormula (n + 1)) : QFormula n

namespace QFormula

/-- Realization over a finite monadic model `⟨E, U, V⟩`. The `Q` clause is
B&C's: more than half of all things satisfy the body. -/
def Realize {E : Type} [Fintype E] (U V : E → Prop) :
    ∀ {n : ℕ}, QFormula n → (Fin n → E) → Prop
  | _, .falsum, _ => False
  | _, .equal i j, xs => xs i = xs j
  | _, .isU i, xs => U (xs i)
  | _, .isV i, xs => V (xs i)
  | _, .imp f₁ f₂, xs => f₁.Realize U V xs → f₂.Realize U V xs
  | _, .all f, xs => ∀ x, f.Realize U V (Fin.snoc xs x)
  | _, .qx f, xs =>
      2 * Set.ncard {a | f.Realize U V (Fin.snoc xs a)} > Fintype.card E

/-- Quantifier count (`all` and `qx` both count). -/
def numQ : ∀ {n : ℕ}, QFormula n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .isU _ => 0
  | _, .isV _ => 0
  | _, .imp f₁ f₂ => numQ f₁ + numQ f₂
  | _, .all f => numQ f + 1
  | _, .qx f => numQ f + 1

/-- `Q`-freeness: the first-order fragment of `L(Q)`. -/
def QFree : ∀ {n : ℕ}, QFormula n → Prop
  | _, .falsum => True
  | _, .equal _ _ => True
  | _, .isU _ => True
  | _, .isV _ => True
  | _, .imp f₁ f₂ => QFree f₁ ∧ QFree f₂
  | _, .all f => QFree f
  | _, .qx _ => False

/-- Negation. -/
def not {n : ℕ} (f : QFormula n) : QFormula n := f.imp .falsum

/-- Disjunction (classical). -/
def or {n : ℕ} (f g : QFormula n) : QFormula n := f.not.imp g

theorem realize_or {E : Type} [Fintype E] {U V : E → Prop} {n : ℕ}
    {f g : QFormula n} {xs : Fin n → E} :
    (f.or g).Realize U V xs ↔ f.Realize U V xs ∨ g.Realize U V xs := by
  show ((f.Realize U V xs → False) → g.Realize U V xs) ↔ _
  exact or_iff_not_imp_left.symm

/-- Finite disjunction. -/
def orList {n : ℕ} : List (QFormula n) → QFormula n
  | [] => .falsum
  | f :: l => f.or (orList l)

theorem realize_orList {E : Type} [Fintype E] {U V : E → Prop} {n : ℕ}
    {xs : Fin n → E} : ∀ {l : List (QFormula n)},
    (orList l).Realize U V xs ↔ ∃ f ∈ l, f.Realize U V xs
  | [] => by simp [orList, Realize]
  | f :: l => by
      simp only [orList, realize_or, realize_orList, List.mem_cons]
      constructor
      · rintro (h | ⟨g, hg, hr⟩)
        · exact ⟨f, Or.inl rfl, h⟩
        · exact ⟨g, Or.inr hg, hr⟩
      · rintro ⟨g, (rfl | hg), hr⟩
        · exact Or.inl hr
        · exact Or.inr ⟨g, hg, hr⟩

/-- "The last variable equals one of the first `n`." -/
def eqAny (n : ℕ) : QFormula (n + 1) :=
  orList ((List.finRange n).map fun i => .equal (Fin.last n) i.castSucc)

theorem realize_eqAny {E : Type} [Fintype E] {U V : E → Prop} {n : ℕ}
    {ys : Fin (n + 1) → E} :
    (eqAny n).Realize U V ys ↔ ∃ i : Fin n, ys (Fin.last n) = ys i.castSucc := by
  simp only [eqAny, realize_orList, List.mem_map, List.mem_finRange]
  constructor
  · rintro ⟨f, ⟨i, -, rfl⟩, hr⟩
    exact ⟨i, hr⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, ⟨i, trivial, rfl⟩, hi⟩

/-- B&C's `Q`-elimination (`ψ*`, p. 215): `Qx θ` becomes "every `x` that is
outside `V` and distinct from the free variables satisfies `θ*`". -/
def star : ∀ {n : ℕ}, QFormula n → QFormula n
  | _, .falsum => .falsum
  | _, .equal i j => .equal i j
  | _, .isU i => .isU i
  | _, .isV i => .isV i
  | _, .imp f₁ f₂ => .imp (star f₁) (star f₂)
  | _, .all f => .all (star f)
  | n, .qx f => .all ((QFormula.isV (Fin.last n)).or ((eqAny n).or (star f)))

theorem qFree_orList : ∀ {n : ℕ} {l : List (QFormula n)},
    (∀ f ∈ l, QFree f) → QFree (orList l)
  | _, [], _ => trivial
  | _, f :: l, h =>
      ⟨⟨h f (.head _), trivial⟩, qFree_orList fun g hg => h g (.tail _ hg)⟩

theorem qFree_eqAny (n : ℕ) : QFree (eqAny n) :=
  qFree_orList fun f hf => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
    trivial

theorem qFree_star : ∀ {n : ℕ} (f : QFormula n), QFree (star f)
  | _, .falsum => trivial
  | _, .equal _ _ => trivial
  | _, .isU _ => trivial
  | _, .isV _ => trivial
  | _, .imp f₁ f₂ => ⟨qFree_star f₁, qFree_star f₂⟩
  | _, .all f => qFree_star f
  | n, .qx f =>
      ⟨⟨trivial, trivial⟩, ⟨⟨qFree_eqAny n, trivial⟩, qFree_star f⟩⟩

theorem numQ_orList : ∀ {n : ℕ} {l : List (QFormula n)},
    (∀ f ∈ l, numQ f = 0) → numQ (orList l) = 0
  | _, [], _ => rfl
  | _, f :: l, h => by
      show numQ f + 0 + numQ (orList l) = 0
      rw [h f (.head _), numQ_orList fun g hg => h g (.tail _ hg)]

theorem numQ_eqAny (n : ℕ) : numQ (eqAny n) = 0 :=
  numQ_orList fun f hf => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
    rfl

theorem numQ_star : ∀ {n : ℕ} (f : QFormula n), numQ (star f) = numQ f
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .isU _ => rfl
  | _, .isV _ => rfl
  | _, .imp f₁ f₂ => by
      show numQ (star f₁) + numQ (star f₂) = _
      rw [numQ_star f₁, numQ_star f₂]; rfl
  | _, .all f => by
      show numQ (star f) + 1 = _
      rw [numQ_star f]; rfl
  | n, .qx f => by
      show 0 + 0 + (numQ (eqAny n) + 0 + numQ (star f)) + 1 = numQ f + 1
      rw [numQ_eqAny, numQ_star f]
      omega

/-- `L(Q)`-realization is invariant under automorphisms of the monadic model
(B&C's "trivial automorphism argument", p. 215). -/
theorem realize_equivMap {E : Type} [Fintype E] {U V : E → Prop} (σ : E ≃ E)
    (hU : ∀ x, U (σ x) ↔ U x) (hV : ∀ x, V (σ x) ↔ V x) :
    ∀ {n : ℕ} (f : QFormula n) (xs : Fin n → E),
      f.Realize U V (σ ∘ xs) ↔ f.Realize U V xs
  | _, .falsum, _ => Iff.rfl
  | _, .equal i j, xs => σ.apply_eq_iff_eq
  | _, .isU i, xs => hU _
  | _, .isV i, xs => hV _
  | _, .imp f₁ f₂, xs =>
      imp_congr (realize_equivMap σ hU hV f₁ xs) (realize_equivMap σ hU hV f₂ xs)
  | _, .all f, xs => by
      have key : ∀ x, Fin.snoc (σ ∘ xs) (σ x) = σ ∘ Fin.snoc xs x := fun x =>
        (Fin.comp_snoc σ xs x).symm
      constructor
      · intro h x
        have := h (σ x)
        rw [key x] at this
        exact (realize_equivMap σ hU hV f _).mp this
      · intro h x
        have hx : Fin.snoc (σ ∘ xs) x = σ ∘ Fin.snoc xs (σ.symm x) := by
          have := key (σ.symm x)
          simpa using this
        rw [show (x : E) = σ (σ.symm x) by simp] at *
        rw [key (σ.symm x)]
        exact (realize_equivMap σ hU hV f _).mpr (h _)
  | _, .qx f, xs => by
      show 2 * Set.ncard {a | f.Realize U V (Fin.snoc (σ ∘ xs) a)} > _ ↔
        2 * Set.ncard {a | f.Realize U V (Fin.snoc xs a)} > _
      have key : ∀ x, Fin.snoc (σ ∘ xs) (σ x) = σ ∘ Fin.snoc xs x := fun x =>
        (Fin.comp_snoc σ xs x).symm
      have hset : {a | f.Realize U V (Fin.snoc (σ ∘ xs) a)}
          = σ '' {a | f.Realize U V (Fin.snoc xs a)} := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro h
          refine ⟨σ.symm a, ?_, by simp⟩
          rw [show (a : E) = σ (σ.symm a) by simp, key (σ.symm a)] at h
          exact (realize_equivMap σ hU hV f _).mp h
        · rintro ⟨a', ha', rfl⟩
          rw [key a']
          exact (realize_equivMap σ hU hV f _).mpr ha'
      rw [hset, Set.ncard_image_of_injective _ σ.injective]

/-- The `Q`-free condition (6): the C12 argument for the `L(Q)` fragment
over the C12 model pair. -/
theorem realize_iff_of_qFree (m k : ℕ) (hk : 3 * m ≤ k) :
    ∀ {ℓ : ℕ} (ψ : QFormula ℓ), QFree ψ → numQ ψ + ℓ < m →
      ∀ {a b : Fin ℓ → Fin k}, RegionMatch m k a b →
        (ψ.Realize (fun x => x.val < m) (fun x => x.val < 2 * m) a ↔
          ψ.Realize (fun x => x.val < m + 1) (fun x => x.val < 2 * m) b) := by
  intro ℓ ψ
  induction ψ with
  | falsum =>
    intro _ _ a b _
    exact Iff.rfl
  | equal i j =>
    intro _ _ a b h
    show a i = a j ↔ b i = b j
    exact h.inj i j
  | isU i =>
    intro _ _ a b h
    exact h.inU i
  | isV i =>
    intro _ _ a b h
    exact h.inV i
  | imp f₁ f₂ ih₁ ih₂ =>
    intro hq hc a b h
    show (_ → _) ↔ (_ → _)
    have hcc : numQ (f₁.imp f₂) = numQ f₁ + numQ f₂ := rfl
    exact imp_congr (ih₁ hq.1 (by omega) h) (ih₂ hq.2 (by omega) h)
  | @all j f ih =>
    intro hq hc a b h
    have hcc : numQ f.all = numQ f + 1 := rfl
    have hc' : numQ f + (j + 1) < m := by omega
    have hℓ : j + 1 < m := by omega
    show (∀ x, _) ↔ (∀ y, _)
    constructor
    · intro hall y
      obtain ⟨x, hx⟩ := extend₂₁ m k hk hℓ h y
      exact (ih hq hc' hx).mp (hall x)
    · intro hall x
      obtain ⟨y, hy⟩ := extend₁₂ m k hk hℓ h x
      exact (ih hq hc' hy).mpr (hall y)
  | qx f ih =>
    intro hq
    exact hq.elim

/-- Swapping two elements outside `V` fixes any predicate below `V`. -/
private theorem swap_pred_iff {E : Type} [DecidableEq E] {P V : E → Prop}
    (hPV : ∀ x, P x → V x) {b₀ b : E} (h₀ : ¬ V b₀) (h₁ : ¬ V b) :
    ∀ x, P (Equiv.swap b₀ b x) ↔ P x := by
  intro x
  rcases eq_or_ne x b₀ with rfl | hx1
  · rw [Equiv.swap_apply_left]
    exact iff_of_false (fun h => h₁ (hPV _ h)) (fun h => h₀ (hPV _ h))
  rcases eq_or_ne x b with rfl | hx2
  · rw [Equiv.swap_apply_right]
    exact iff_of_false (fun h => h₀ (hPV _ h)) (fun h => h₁ (hPV _ h))
  · rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2]

/-- B&C's property (P) (p. 215): on models with `U ⊆ V` whose domain is at
least twice `|V|` plus the complexity of `ψ`, the `Q`-elimination `star` is
correct — the domain "swamps out" `U` and `V`. -/
theorem realize_star_iff {E : Type} [Fintype E] {U V : E → Prop}
    (hUV : ∀ x, U x → V x) :
    ∀ {n : ℕ} (ψ : QFormula n),
      2 * (Set.ncard {x | V x} + (numQ ψ + n)) ≤ Fintype.card E →
      ∀ xs : Fin n → E, ((star ψ).Realize U V xs ↔ ψ.Realize U V xs)
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal _ _, _, _ => Iff.rfl
  | _, .isU _, _, _ => Iff.rfl
  | _, .isV _, _, _ => Iff.rfl
  | _, .imp f₁ f₂, hb, xs => by
      have hq : numQ (f₁.imp f₂) = numQ f₁ + numQ f₂ := rfl
      rw [hq] at hb
      exact imp_congr (realize_star_iff hUV f₁ (by omega) xs)
        (realize_star_iff hUV f₂ (by omega) xs)
  | _, .all f, hb, xs => by
      have hq : numQ f.all = numQ f + 1 := rfl
      rw [hq] at hb
      exact forall_congr' fun x =>
        realize_star_iff hUV f (by omega) (Fin.snoc xs x)
  | n, .qx f, hb, xs => by
      haveI := Classical.decEq E
      have hq : numQ (qx f) = numQ f + 1 := rfl
      rw [hq] at hb
      have hIH : ∀ b, ((star f).Realize U V (Fin.snoc xs b) ↔
          f.Realize U V (Fin.snoc xs b)) := fun b =>
        realize_star_iff hUV f (by omega) (Fin.snoc xs b)
      have hstar : (star (qx f)).Realize U V xs ↔
          ∀ b, ¬ V b → (∀ i, b ≠ xs i) → f.Realize U V (Fin.snoc xs b) := by
        show (∀ b, ((QFormula.isV (Fin.last n)).or
          ((eqAny n).or (star f))).Realize U V (Fin.snoc xs b)) ↔ _
        refine forall_congr' fun b => ?_
        rw [realize_or, realize_or, realize_eqAny, hIH b]
        simp only [Realize, Fin.snoc_last, Fin.snoc_castSucc]
        constructor
        · rintro (hv | ⟨i, hi⟩ | hf) hnv hne
          · exact absurd hv hnv
          · exact absurd hi (hne i)
          · exact hf
        · intro h
          by_cases hv : V b
          · exact Or.inl hv
          · by_cases hex : ∃ i, b = xs i
            · exact Or.inr (Or.inl hex)
            · push_neg at hex
              exact Or.inr (Or.inr (h hv hex))
      rw [hstar]
      show _ ↔ 2 * Set.ncard {a | f.Realize U V (Fin.snoc xs a)} > Fintype.card E
      have hrange : Set.ncard (Set.range xs) ≤ n := by
        rw [← Set.image_univ]
        refine le_trans (Set.ncard_image_le (Set.toFinite _)) ?_
        simp [Set.ncard_univ]
      have hunion : Set.ncard ({x : E | V x} ∪ Set.range xs)
          ≤ Set.ncard {x : E | V x} + n :=
        le_trans (Set.ncard_union_le _ _) (by omega)
      have hcomplsum : Set.ncard ({x : E | V x} ∪ Set.range xs)
          + Set.ncard (({x : E | V x} ∪ Set.range xs)ᶜ) = Fintype.card E := by
        rw [← Nat.card_eq_fintype_card]
        exact Set.ncard_add_ncard_compl _
      constructor
      · intro hall
        have hsub : ({x : E | V x} ∪ Set.range xs)ᶜ
            ⊆ {a | f.Realize U V (Fin.snoc xs a)} := by
          intro x hx
          simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq,
            Set.mem_range, not_or, not_exists] at hx
          exact hall x hx.1 fun i h => hx.2 i h.symm
        have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
        omega
      · intro hmaj b hnv hne
        have hwit : ∃ b₀, f.Realize U V (Fin.snoc xs b₀) ∧ ¬ V b₀ ∧
            ∀ i, b₀ ≠ xs i := by
          by_contra hno
          push_neg at hno
          have hsub : {a | f.Realize U V (Fin.snoc xs a)}
              ⊆ {x : E | V x} ∪ Set.range xs := by
            intro a ha
            by_cases hv : V a
            · exact Or.inl hv
            · obtain ⟨i, hi⟩ := hno a ha hv
              exact Or.inr ⟨i, hi.symm⟩
          have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
          omega
        obtain ⟨b₀, hf₀, hnv₀, hne₀⟩ := hwit
        have hUσ : ∀ x, U (Equiv.swap b₀ b x) ↔ U x :=
          swap_pred_iff hUV hnv₀ hnv
        have hVσ : ∀ x, V (Equiv.swap b₀ b x) ↔ V x :=
          swap_pred_iff (fun _ h => h) hnv₀ hnv
        have hsnoc : Fin.snoc xs b = Equiv.swap b₀ b ∘ Fin.snoc xs b₀ := by
          funext p
          induction p using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_last, Function.comp_apply,
              Equiv.swap_apply_left]
          | cast p =>
            simp only [Fin.snoc_castSucc, Function.comp_apply]
            rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm (hne₀ p))
              (Ne.symm (hne p))]
        rw [hsnoc]
        exact (realize_equivMap _ hUσ hVσ f _).mpr hf₀

end QFormula

/-- **C13** ([barwise-cooper-1981], Appendix C pp. 214–215): even with the
unrelativized majority quantifier `Qx[·]` ("more than half of all things")
available, no sentence of `L(Q)` is true in exactly the finite models where
more than half the V's are U's. The relativized quantifier is not definable
from the unrelativized one: *most* must be treated as a determiner, not a
quantifier. (B&C credit a related unpublished 1965 theorem to David Kaplan.) -/
theorem more_than_half_not_Q_definable :
    ¬ ∃ φ : QFormula 0, ∀ (E : Type) [Fintype E] (U V : E → Prop),
      (φ.Realize U V default ↔ MostUV U V) := by
  rintro ⟨φ, hφ⟩
  set m := QFormula.numQ φ + 1 with hm
  set k := 2 * (2 * m + QFormula.numQ φ) with hk2
  have hk : 3 * m ≤ k := by omega
  have hcardV : Set.ncard {x : Fin k | x.val < 2 * m} = 2 * m :=
    ncard_val_lt k (2 * m) (by omega)
  have hdef : ∀ v₁ v₂ : Fin 0 → Fin k, v₁ = v₂ := fun v₁ v₂ =>
    funext fun i => i.elim0
  have hcast : ∀ {U V : Fin k → Prop} (v₁ v₂ : Fin 0 → Fin k),
      QFormula.Realize U V φ v₁ → QFormula.Realize U V φ v₂ := by
    intro U V v₁ v₂ h
    rwa [hdef v₁ v₂] at h
  have h₁ := hφ (Fin k) (fun x => x.val < m) (fun x => x.val < 2 * m)
  have hUV₁ : {x : Fin k | x.val < m ∧ x.val < 2 * m}
      = {x : Fin k | x.val < m} := by
    ext x
    simp only [Set.mem_setOf_eq]
    omega
  have hfalse₁ : ¬ QFormula.Realize (fun x : Fin k => x.val < m)
      (fun x => x.val < 2 * m) φ default := fun hr => by
    have hcount := h₁.mp (hcast _ _ hr)
    unfold MostUV at hcount
    rw [hUV₁, ncard_val_lt k m (by omega), hcardV] at hcount
    omega
  have h₂ := hφ (Fin k) (fun x => x.val < m + 1) (fun x => x.val < 2 * m)
  have hUV₂ : {x : Fin k | x.val < m + 1 ∧ x.val < 2 * m}
      = {x : Fin k | x.val < m + 1} := by
    ext x
    simp only [Set.mem_setOf_eq]
    omega
  have htrue₂ : QFormula.Realize (fun x : Fin k => x.val < m + 1)
      (fun x => x.val < 2 * m) φ default := hcast _ _ (h₂.mpr (by
    unfold MostUV
    rw [hUV₂, ncard_val_lt k (m + 1) (by omega), hcardV]
    omega))
  have hP₁ := QFormula.realize_star_iff (E := Fin k)
    (U := fun x => x.val < m) (V := fun x => x.val < 2 * m)
    (fun x hx => by omega) φ
    (by rw [show {x : Fin k | x.val < 2 * m}.ncard = 2 * m from hcardV,
      Fintype.card_fin]; omega) default
  have hP₂ := QFormula.realize_star_iff (E := Fin k)
    (U := fun x => x.val < m + 1) (V := fun x => x.val < 2 * m)
    (fun x hx => by omega) φ
    (by rw [show {x : Fin k | x.val < 2 * m}.ncard = 2 * m from hcardV,
      Fintype.card_fin]; omega) default
  have htrans := QFormula.realize_iff_of_qFree m k hk (QFormula.star φ)
    (QFormula.qFree_star φ) (by rw [QFormula.numQ_star]; omega)
    (a := default) (b := default)
    ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  exact hfalse₁ (hP₁.mp (htrans.mpr (hP₂.mpr htrue₂)))

/-! ### The truth condition is the codebase's ⟦most⟧ -/

private theorem count_eq_ncard {M : Type} [Fintype M] (P : M → Prop)
    [DecidablePred P] :
    Quantification.count P = Set.ncard {x | P x} := by
  rw [Quantification.count, Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

/-- The C12/C13 truth condition is `most_sem` with `V` as restrictor — the
theorems are about the denotation the rest of the codebase attributes to
*most*, not a local re-implementation. -/
theorem mostUV_iff_most_sem {M : Type} [Fintype M] (U V : M → Prop) :
    MostUV U V ↔ Quantification.most_sem V U := by
  classical
  unfold MostUV Quantification.most_sem
  rw [count_eq_ncard, count_eq_ncard]
  have hcomm : {x | U x ∧ V x} = {x | V x ∧ U x} := by
    ext x
    simp [and_comm]
  have hpart : Set.ncard {x | V x ∧ U x} + Set.ncard {x | V x ∧ ¬ U x}
      = Set.ncard {x | V x} := by
    rw [← Set.ncard_union_eq (Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx.2)
      (Set.toFinite _) (Set.toFinite _)]
    congr 1
    ext x
    by_cases hU : U x <;> simp [hU]
  rw [hcomm]
  omega

/-- **C12 restated through `most_sem`**: no first-order sentence expresses
the codebase's ⟦most⟧ over finite models. -/
theorem most_sem_not_definable :
    ¬ ∃ φ : L_UV.Sentence, ∀ (M : Type) [Fintype M] [Nonempty M]
      (S : L_UV.Structure M),
      (@Sentence.Realize L_UV M S φ ↔
        Quantification.most_sem (fun x => S.RelMap vRel ![x])
          (fun x => S.RelMap uRel ![x])) := by
  rintro ⟨φ, hφ⟩
  exact more_than_half_not_definable ⟨φ, fun M _ _ S =>
    (hφ M S).trans (mostUV_iff_most_sem _ _).symm⟩

/-! ### The engine-level corollary: no fragment tree means *most* -/

open Semantics.Composition in
/-- **No tree of the compiled fragment means *most***: for any logical
vocabulary and disjoint naming maps over `L_UV`, no closed tree of the FO
fragment has, across all nonempty finite models, exactly ⟦most⟧'s truth
conditions — C12 stated about `Tree.interp` itself, via the agreement
theorem `holdsAt_iff_realize`. The fragment's partiality at *most* is a
theorem, not a design choice. -/
theorem no_tree_means_most (fw : FOWords) (nm : LexNaming L_UV)
    (hnd : fw.Nodup) (hfr : fw.FreshFor nm) (hdj : nm.Disjoint) :
    ¬ ∃ (t : Syntax.Tree Unit String) (φ : L_UV.Formula ℕ)
        (_ : compileFO fw nm t = some φ) (hcl : φ.freeVarFinset = ∅),
      ∀ (M : Type) [Fintype M] [Nonempty M] (S : L_UV.Structure M)
        (g : Core.Assignment M),
        HoldsAt (Model.ofStructure M S)
          ((Model.ofStructure M S).lexiconFO fw nm ()) g t ↔
          Quantification.most_sem (fun x => S.RelMap vRel ![x])
            (fun x => S.RelMap uRel ![x]) := by
  rintro ⟨t, φ, h, hcl, htree⟩
  refine most_sem_not_definable ⟨φ.toSentence hcl, ?_⟩
  intro M _ _ S
  letI := S
  have h1 := htree M S fun _ => Classical.arbitrary M
  rw [holdsAt_iff_realize (Model.ofStructure M S) fw nm () hnd hfr hdj h
    (fun _ => Classical.arbitrary M)] at h1
  rw [Formula.realize_toSentence φ hcl (fun _ => Classical.arbitrary M)]
  exact h1

end BarwiseCooper1981
