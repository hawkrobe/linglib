import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

/-!
# The update algebra

This file defines dynamic meanings in their two canonical forms and the bridge
between them. A relational update (`Update S`) relates input states to output
states pointwise — [groenendijk-stokhof-1991]'s DPL relations and
[kamp-reyle-1993]'s verifying embeddings, parametrized over the state type
following [muskens-1996]. A context change potential (`CCP S`) transforms
information states — sets of states — as wholes: the file change potentials of
[heim-1982] and [heim-1983] and the updates of [veltman-1996]. `lift` sends a
relation to its image transformer ([muskens-van-benthem-visser-2011]'s
strongest postcondition), `lower` recovers a relation from behaviour on
singletons, and the image of `lift` is exactly the distributive transformers.
`Kleisli.lean` upgrades the pair to the Kleisli and Eilenberg–Moore
presentations of the powerset monad.

Both faces carry the same algebra. Updates form a monoid under sequencing —
indeed a quantale, since sequencing distributes over arbitrary unions — and
tests are its subidentities (`Update.isTest_iff_le_one`), with a normal form
at each face: a relational test is the `test` of its truth condition
(`Update.IsTest.eq_test_closure`), a transformer test is the `guard` of its
acceptance condition (`CCP.IsTest.eq_guard`). The two test notions are one
concept at adjacent carriers, so `lift` does not interchange them: `lift` of
a relational test is an eliminative filter, not a pass-or-`∅` guard. The
static fragment is their common ground: a transformer is a lifted test filter
iff it is eliminative and distributive (`exists_eq_lift_test_iff`).

## Main definitions

* `Update S`, `Condition S`: relations on states and properties of states.
* `Update.test`, `Update.neg`, `Update.seq` (`⨟`), `Update.impl`,
  `Update.disj`, `Update.closure`: the relational connectives; `Update S` is
  a scoped `Monoid` and `IsQuantale`.
* `Update.IsTest`: updates that never change the state.
* `CCP S`: transformers of information states, a scoped `Monoid` under
  `CCP.seq`, with `CCP.neg`, the whole-state tests `CCP.guard`, `might`,
  `must`, `negTest`, and acceptance consequence `CCP.entails`.
* `CCP.IsEliminative`, `CCP.IsTest`, `CCP.IsDistributive`: the classification
  of transformers.
* `lift`, `lower`: the bridge between the two faces.
* `supportOf`, `contentOf`, `updateFromSat`, `dynamicEntailsOf`: the layer a
  satisfaction relation induces; PLA, DRT, and DPL instantiate it.

## Main results

* `Update.isTest_iff_le_one`, `Update.IsTest.eq_test_closure`
  ([groenendijk-stokhof-1991]'s Fact 6), `CCP.IsTest.eq_guard`: tests are the
  subidentities, with a normal form at each face.
* `lower_lift`, `lift_lower`, `lift_isDistributive`: the distributive
  transformers are exactly the relational images.
* `lift_le_lift_iff`: `lift` reflects the pointwise order.
* `exists_eq_lift_test_iff`: a transformer is a lifted test filter iff it is
  eliminative and distributive — [van-benthem-1986]'s additivity, per
  [rothschild-yalcin-2016] and [gillies-2022]. `CCP.might_not_isDistributive`
  witnesses that whole-state tests lie outside this fragment.
* `support_iff_update_eq`, `dynamicEntailsOf_iff_entails`: support is being a
  fixed point of the update, and the satisfaction layer's consequence is
  acceptance consequence.

## Notation

* `D₁ ⨟ D₂` for `Update.seq D₁ D₂`.
* `u ;; v` for `CCP.seq u v`, scoped to `DynamicSemantics.CCP`.

## Implementation notes

The algebraic instances are scoped: `Update S` and `CCP S` abbreviate
function types, so global instances would attach `*` and `1` to bare function
types for every importer. `open scoped DynamicSemantics.Update` also makes mathlib's
`WriterT (Update S) Id` a lawful monad.

`Update.neg` does not validate double-negation elimination: negation collapses
update information to a state predicate. The repairs are framework-specific —
bilateral swap (`UpdateSemantics/Bilateral.lean`), propositional discourse
referents (`Studies/Hofmann2025.lean`), classical metalanguage
(`Studies/Cooper2023/`). Similarly `CCP.negTest` is not `CCP.neg`: the two
coincide only on fixed or crashed inputs (`Studies/Beaver2001/ABLE.lean`).

`updateFromSat` is kept as the literal filter rather than defined as
`lift (test _)` (see `updateFromSat_eq_lift_test`) so that instantiating
frameworks connect to it by `rfl`. [groenendijk-stokhof-1991]'s entailment
notions and Facts 10–12 live with their paper in
`Studies/GroenendijkStokhof1991.lean`.

## References

* [groenendijk-stokhof-1991], [kamp-reyle-1993], [muskens-1996]
* [heim-1982], [heim-1983], [veltman-1996]
* [muskens-van-benthem-visser-2011]
* [van-benthem-1986], [rothschild-yalcin-2016], [gillies-2022]
-/

namespace DynamicSemantics

/-! ## The relational face -/

section Relational

/-- A dynamic meaning as a binary relation between input and output states. -/
abbrev Update (S : Type*) := S → S → Prop

/-- A static property of a single state; `test` embeds conditions into updates. -/
abbrev Condition (S : Type*) := S → Prop

namespace Update

variable {S : Type*} {C : Condition S} {D : Update S} {i j : S}

/-! ### The connectives -/

/-- `test C` checks `C` without changing the state. -/
def test (C : Condition S) : Update S := λ i j => i = j ∧ C j

/-- `neg D` holds at `i` iff no output `k` satisfies `D`. -/
def neg (D : Update S) : Condition S := λ i => ¬∃ k, D i k

/-- `D₁ ⨟ D₂` relates `i` to `k` iff some intermediate `j` has `D₁ i j` and `D₂ j k`. -/
def seq (D₁ D₂ : Update S) : Update S := Relation.Comp D₁ D₂

infixl:65 " ⨟ " => Update.seq

/-- `impl D₁ D₂` holds at `i` iff every `D₁`-output from `i` has a `D₂`-output. -/
def impl (D₁ D₂ : Update S) : Condition S := λ i => ∀ h, D₁ i h → ∃ k, D₂ h k

/-- `disj D₁ D₂` holds at `i` iff some disjunct has an output from `i`. -/
def disj (D₁ D₂ : Update S) : Condition S := λ i => ∃ k, D₁ i k ∨ D₂ i k

/-- `closure D` holds at `i` iff `D` has an output from `i` — [heim-1982]'s truth definition. -/
def closure (D : Update S) : Condition S := λ i => ∃ k, D i k

/-! ### The update quantale -/

/-- `Update S` is a monoid under `⨟` with the trivial test as unit (scoped;
see the implementation notes). -/
scoped instance : Monoid (Update S) where
  mul := seq
  one := test (λ _ => True)
  mul_assoc _ _ _ := Relation.comp_assoc
  one_mul D := funext₂ λ i _ => propext ⟨λ ⟨_, ⟨h, _⟩, d⟩ => h ▸ d, λ d => ⟨i, ⟨rfl, ⟨⟩⟩, d⟩⟩
  mul_one D := funext₂ λ _ j => propext ⟨λ ⟨_, d, h, _⟩ => h ▸ d, λ d => ⟨j, d, rfl, ⟨⟩⟩⟩

/-- `Update S` is a quantale: sequencing distributes over arbitrary unions of
updates, so mathlib's residuation vocabulary applies (scoped). -/
scoped instance : IsQuantale (Update S) where
  mul_sSup_distrib D s := by
    funext i k
    show (D ⨟ sSup s) i k = (⨆ E ∈ s, D ⨟ E) i k
    simp only [seq, Relation.Comp, sSup_apply, iSup_apply, iSup_Prop_eq]
    exact propext ⟨fun ⟨b, hD, ⟨E, hE⟩, hbk⟩ => ⟨E, hE, b, hD, hbk⟩,
      fun ⟨E, hE, b, hD, hbk⟩ => ⟨b, hD, ⟨E, hE⟩, hbk⟩⟩
  sSup_mul_distrib s D := by
    funext i k
    show (sSup s ⨟ D) i k = (⨆ E ∈ s, E ⨟ D) i k
    simp only [seq, Relation.Comp, sSup_apply, iSup_apply, iSup_Prop_eq]
    exact propext ⟨fun ⟨b, ⟨⟨E, hE⟩, hib⟩, hbk⟩ => ⟨E, hE, b, hib, hbk⟩,
      fun ⟨E, hE, b, hib, hbk⟩ => ⟨b, ⟨⟨E, hE⟩, hib⟩, hbk⟩⟩

/-! ### Tests are the subidentities -/

/-- An update is a *test* if it never changes the state
([groenendijk-stokhof-1991], Definition 11). -/
def IsTest (D : Update S) : Prop := ∀ ⦃i j⦄, D i j → i = j

/-- `test C` is a test. -/
theorem isTest_test (C : Condition S) : IsTest (test C) :=
  fun _ _ h => h.1

/-- Tests are the subidentities of the update monoid: the coreflexives `D ≤ 1`. -/
theorem isTest_iff_le_one : D.IsTest ↔ D ≤ 1 :=
  ⟨fun h _ _ hij => ⟨h hij, trivial⟩, fun h _ _ hij => (h _ _ hij).1⟩

/-- A test is the test of its own closure ([groenendijk-stokhof-1991]'s
Fact 6); the transformer-face mirror is `CCP.IsTest.eq_guard`. -/
theorem IsTest.eq_test_closure (h : IsTest D) :
    D = test (closure D) := by
  funext i j
  exact propext (by grind [test, closure, IsTest])

end Update

end Relational

/-! ## The transformer face -/

/-- A context change potential: a transformer of whole information states. -/
abbrev CCP (S : Type*) := Set S → Set S

namespace CCP

variable {S : Type*} {u v φ ψ : CCP S}

/-- The identity CCP. -/
def id : CCP S := λ s => s

/-- The absurd CCP: crash to the empty state. -/
def absurd : CCP S := λ _ => ∅

/-- Sequential composition of CCPs, in diagrammatic order. -/
def seq (u v : CCP S) : CCP S := λ s => v (u s)

scoped infixl:70 " ;; " => seq

/-- `CCP S` is a monoid under `seq` (scoped; see the implementation notes). -/
scoped instance : Monoid (CCP S) where
  mul := seq
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- The absurd CCP absorbs on the right. -/
theorem seq_absurd (u : CCP S) : u ;; absurd = absurd := rfl

/-- Dynamic negation by set difference: the states that do not survive `φ`
([heim-1982]; [veltman-1996]). -/
def neg (φ : CCP S) : CCP S := λ s => s \ φ s

/-! ### Whole-state tests -/

open Classical in
/-- `guard C` passes a state through iff it satisfies `C`, else crashes to `∅`. -/
noncomputable def guard (C : Set S → Prop) : CCP S := λ s => if C s then s else ∅

/-- A guard whose condition holds passes the state through. -/
@[simp] theorem guard_pos {C : Set S → Prop} {s} (h : C s) : guard C s = s :=
  if_pos h

/-- A guard whose condition fails crashes to `∅`. -/
@[simp] theorem guard_neg {C : Set S → Prop} {s} (h : ¬C s) : guard C s = ∅ :=
  if_neg h

/-- `negTest φ` passes iff `φ` crashes — a whole-state consistency test, not
the set-difference `neg` (see the implementation notes). -/
noncomputable def negTest (φ : CCP S) : CCP S := guard (λ s => ¬ (φ s).Nonempty)

/-- `might φ` passes iff `φ` yields a nonempty result ([veltman-1996]). -/
noncomputable def might (φ : CCP S) : CCP S := guard (λ s => (φ s).Nonempty)

/-- `must φ` passes iff `φ` returns its input unchanged ([veltman-1996]). -/
noncomputable def must (φ : CCP S) : CCP S := guard (λ s => φ s = s)

/-- Acceptance consequence: every `φ`-output is a fixed point of `ψ`
([veltman-1996]'s acceptance validity; [beaver-2001]'s D45). -/
def entails (φ ψ : CCP S) : Prop := ∀ s : Set S, ψ (φ s) = φ s

/-! ### Classification -/

/-- A transformer is *eliminative* if it never adds possibilities: `u ≤ id`
pointwise. -/
def IsEliminative (u : CCP S) : Prop := ∀ s, u s ⊆ s

/-- The identity is eliminative. -/
theorem isEliminative_id : IsEliminative (id : CCP S) :=
  λ _ => Set.Subset.rfl

/-- Sequencing preserves eliminativity. -/
theorem IsEliminative.seq (hu : IsEliminative u) (hv : IsEliminative v) :
    IsEliminative (u.seq v) := λ s _ hp =>
  hu s (hv (u s) hp)

/-- A transformer is a *test* if it passes its input through or crashes to
`∅` — [veltman-1996]'s tests, `Update.IsTest` one carrier up. -/
def IsTest (u : CCP S) : Prop := ∀ s, u s = s ∨ u s = ∅

/-- Tests are eliminative. -/
theorem IsTest.isEliminative (h : IsTest u) : IsEliminative u :=
  λ s p hp => (h s).elim (· ▸ hp) (λ hemp => (Set.notMem_empty p (hemp ▸ hp)).elim)

/-- Guards are tests. -/
theorem guard_isTest (C : Set S → Prop) : IsTest (guard C) :=
  λ s => (Classical.em (C s)).elim (λ h => .inl (guard_pos h)) (λ h => .inr (guard_neg h))

/-- A test is the guard of its own acceptance condition — the mirror of
`Update.IsTest.eq_test_closure`. -/
theorem IsTest.eq_guard (h : IsTest u) : u = guard fun s => u s = s := by
  funext s
  by_cases hs : u s = s
  · rw [guard_pos (C := fun t => u t = t) hs, hs]
  · rw [guard_neg (C := fun t => u t = t) hs]
    exact (h s).resolve_left hs

/-- The tests are exactly the guards. -/
theorem isTest_iff_exists_guard : IsTest u ↔ ∃ C, u = guard C :=
  ⟨fun h => ⟨_, h.eq_guard⟩, fun ⟨C, hC⟩ => hC ▸ guard_isTest C⟩

/-- A transformer is *distributive* if it acts per-element:
`φ s = ⋃ i ∈ s, φ {i}` — equivalently, it preserves arbitrary joins
(`Kleisli.lean`'s `isDistributive_iff_map_sSup`). -/
def IsDistributive (φ : CCP S) : Prop :=
  ∀ s, φ s = {p | ∃ i ∈ s, p ∈ φ {i}}

/-- `might` is not distributive: a whole-state test can pass where every
per-singleton test fails. -/
theorem might_not_isDistributive :
    ∃ (S : Type) (φ : CCP S), ¬IsDistributive (might φ) := by
  refine ⟨Bool, (fun s => {p ∈ s | p = true}), fun hD => ?_⟩
  have hfalse :
      false ∈ might (fun s : Set Bool => {p ∈ s | p = true}) {true, false} := by
    rw [might, guard_pos ⟨true, Or.inl rfl, rfl⟩]
    exact Or.inr rfl
  rw [hD] at hfalse
  obtain ⟨i, hi, hmem⟩ := hfalse
  rcases hi with rfl | rfl
  · rw [might, guard_pos ⟨true, rfl, rfl⟩] at hmem
    exact Bool.false_ne_true hmem
  · rw [might, guard_neg (fun ⟨x, hx, hx'⟩ => Bool.false_ne_true (hx ▸ hx'))]
      at hmem
    exact hmem

end CCP

/-! ## The bridge -/

section RelationalBridge

variable {S : Type*} {R R' : Update S} {C : Condition S} {σ : Set S} {i j : S}

open Update

/-- The relational image: `lift R σ` collects the `R`-outputs of the elements
of `σ` — the strongest postcondition of [muskens-van-benthem-visser-2011]. -/
def lift (R : Update S) : CCP S := λ σ => { j | ∃ i ∈ σ, R i j }

/-- `lower φ i j` holds iff `j` is an output of `φ` on the singleton `{i}`. -/
def lower (φ : CCP S) : Update S := λ i j => j ∈ φ {i}

theorem mem_lift : j ∈ lift R σ ↔ ∃ i ∈ σ, R i j := Iff.rfl

/-- `lift` sends sequencing to composition. -/
theorem lift_seq (R₁ R₂ : Update S) :
    lift (R₁ ⨟ R₂) = CCP.seq (lift R₁) (lift R₂) :=
  funext λ _ => Set.ext λ _ => ⟨λ ⟨i, m, j, a, b⟩ => ⟨j, ⟨i, m, a⟩, b⟩,
    λ ⟨j, ⟨i, m, a⟩, b⟩ => ⟨i, m, j, a, b⟩⟩

/-- `lift (test C)` is the filter by `C`. -/
theorem lift_test (C : Condition S) :
    lift (test C) = λ σ => { i ∈ σ | C i } :=
  funext λ _ => Set.ext λ j => ⟨λ ⟨_, m, e, c⟩ => ⟨e ▸ m, c⟩, λ ⟨m, c⟩ => ⟨j, m, rfl, c⟩⟩

/-- Lifted transformers are distributive. -/
theorem lift_isDistributive (R : Update S) : CCP.IsDistributive (lift R) :=
  λ _ => Set.ext λ _ => ⟨λ ⟨i, m, r⟩ => ⟨i, m, i, rfl, r⟩, λ ⟨i, m, _, e, r⟩ => ⟨i, m, e ▸ r⟩⟩

/-- `lower` is a left inverse of `lift`: the relational face loses nothing. -/
theorem lower_lift (R : Update S) : lower (lift R) = R :=
  funext₂ λ i _ => propext ⟨λ ⟨_, e, r⟩ => e ▸ r, λ r => ⟨i, rfl, r⟩⟩

/-- `lift` is a right inverse of `lower` on distributive transformers. -/
theorem lift_lower (φ : CCP S) (hd : CCP.IsDistributive φ) :
    lift (lower φ) = φ :=
  funext λ σ => (hd σ).symm

/-- `lift` reflects (and preserves) the pointwise order. -/
theorem lift_le_lift_iff : lift R ≤ lift R' ↔ R ≤ R' :=
  ⟨λ h i _ r => match h {i} ⟨i, rfl, r⟩ with | ⟨_, e, r'⟩ => e ▸ r',
   λ h _ j ⟨i, m, r⟩ => ⟨i, m, h i j r⟩⟩

/-! ### Test filters -/

@[simp] theorem mem_lift_test : i ∈ lift (test C) σ ↔ i ∈ σ ∧ C i := by
  rw [lift_test]; exact Iff.rfl

/-- `lift (test C)` is eliminative: it only removes elements. -/
theorem lift_test_isEliminative (C : Condition S) :
    CCP.IsEliminative (lift (test C)) := by
  rw [lift_test]; intro σ j ⟨hj, _⟩; exact hj

/-- Composing test filters conjoins the conditions. -/
theorem lift_test_lift_test (C₁ C₂ : Condition S) (σ : Set S) :
    lift (test C₂) (lift (test C₁) σ) = lift (test fun i => C₁ i ∧ C₂ i) σ :=
  Set.ext fun i => by
    simp only [mem_lift_test]
    exact and_assoc

/-- Test filters are idempotent. -/
theorem lift_test_idem (C : Condition S) (σ : Set S) :
    lift (test C) (lift (test C) σ) = lift (test C) σ := by
  rw [lift_test_lift_test]
  exact Set.ext fun i => by simp only [mem_lift_test, and_self]

/-- Contradictory test filters compose to the empty state. -/
theorem lift_test_disjoint (C₁ C₂ : Condition S)
    (h : ∀ i, C₁ i → C₂ i → False) (σ : Set S) :
    lift (test C₂) (lift (test C₁) σ) = ∅ := by
  rw [lift_test_lift_test]
  exact Set.eq_empty_of_forall_notMem fun i hi =>
    h i (mem_lift_test.mp hi).2.1 (mem_lift_test.mp hi).2.2

/-- Covering test filters partition the state. -/
theorem lift_test_cover₃ (C₁ C₂ C₃ : Condition S)
    (h : ∀ i, C₁ i ∨ C₂ i ∨ C₃ i) (σ : Set S) :
    lift (test C₁) σ ∪ lift (test C₂) σ ∪ lift (test C₃) σ = σ :=
  Set.ext fun i => by
    simp only [Set.mem_union, mem_lift_test]
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · rcases hi with (⟨h', -⟩ | ⟨h', -⟩) | ⟨h', -⟩ <;> exact h'
    · rcases h i with h' | h' | h'
      · exact Or.inl (Or.inl ⟨hi, h'⟩)
      · exact Or.inl (Or.inr ⟨hi, h'⟩)
      · exact Or.inr ⟨hi, h'⟩

/-! ### The static fragment -/

/-- A transformer is a lifted test filter iff it is eliminative and
distributive — [van-benthem-1986]'s additivity ([rothschild-yalcin-2016];
[gillies-2022]). Update semantics keeps eliminativity but its whole-state
tests break distributivity; DPL's random reassignment keeps distributivity
but breaks eliminativity. -/
theorem exists_eq_lift_test_iff {φ : CCP S} :
    (∃ C : Condition S, φ = lift (test C)) ↔
      CCP.IsEliminative φ ∧ CCP.IsDistributive φ := by
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨lift_test_isEliminative C, lift_isDistributive _⟩
  · rintro ⟨he, hd⟩
    refine ⟨fun i => i ∈ φ {i}, ?_⟩
    funext s
    rw [hd s, lift_test]
    ext p
    exact ⟨fun ⟨i, hi, hpi⟩ => by obtain rfl : p = i := he {i} hpi; exact ⟨hi, hpi⟩,
      fun ⟨hp, hC⟩ => ⟨p, hp, hC⟩⟩

end RelationalBridge

/-! ## The satisfaction layer

A satisfaction relation `sat : S → φ → Prop` induces the standard eliminative
fragment, and the layer reduces to mathlib's intersection–subset API: the
induced update intersects with content (definitionally), support is inclusion
in content, and dynamic entailment is content inclusion
(`dynamicEntailsOf_iff_content_subset`). PLA, DRT, and DPL instantiate
`sat`. -/

section Satisfaction

variable {S φ : Type*}

open Update (test)

/-- The content of a formula: all possibilities satisfying it. -/
def contentOf (sat : S → φ → Prop) (ψ : φ) : Set S := { p | sat p ψ }

/-- `s` supports `ψ` when every possibility in `s` satisfies `ψ`: inclusion
in content. -/
def supportOf (sat : S → φ → Prop) (s : Set S) (ψ : φ) : Prop :=
  s ⊆ contentOf sat ψ

/-- Support is downward closed: smaller states support more. -/
theorem support_mono (sat : S → φ → Prop) (s t : Set S) (ψ : φ)
    (h : t ⊆ s) (hs : supportOf sat s ψ) : supportOf sat t ψ :=
  h.trans hs

/-- The empty state supports everything (vacuously). -/
theorem empty_supports (sat : S → φ → Prop) (ψ : φ) :
    supportOf sat ∅ ψ :=
  Set.empty_subset _

/-- Content is monotone in pointwise entailment. -/
theorem content_mono (sat : S → φ → Prop) (ψ₁ ψ₂ : φ)
    (h : ∀ p, sat p ψ₁ → sat p ψ₂) :
    contentOf sat ψ₁ ⊆ contentOf sat ψ₂ :=
  Set.setOf_subset_setOf.mpr h

/-- Filtering a set by a predicate is monotone. -/
theorem sep_monotone (pred : S → Prop) :
    Monotone (λ s : Set S => { p ∈ s | pred p }) :=
  λ _ _ h => Set.inter_subset_inter_left _ h

/-- Filtering a set by a predicate is eliminative. -/
theorem sep_eliminative (pred : S → Prop) :
    CCP.IsEliminative (λ s : Set S => { p ∈ s | pred p }) :=
  λ s => Set.sep_subset s pred

/-- The update a satisfaction relation induces: filter to the satisfying
possibilities (see the implementation notes on the choice of body). -/
def updateFromSat (sat : S → φ → Prop) (ψ : φ) : CCP S :=
  λ s => { p ∈ s | sat p ψ }

@[simp] theorem mem_updateFromSat {sat : S → φ → Prop} {ψ : φ}
    {s : Set S} {p : S} :
    p ∈ updateFromSat sat ψ s ↔ p ∈ s ∧ sat p ψ := Iff.rfl

/-- Induced updates are eliminative. -/
theorem updateFromSat_eliminative (sat : S → φ → Prop) (ψ : φ) :
    CCP.IsEliminative (updateFromSat sat ψ) :=
  λ _ => Set.inter_subset_left

/-- `updateFromSat` is monotone in the state argument. -/
theorem updateFromSat_monotone (sat : S → φ → Prop) (ψ : φ) :
    Monotone (updateFromSat sat ψ) :=
  λ _ _ h => Set.inter_subset_inter_left _ h

/-- Updating is intersecting with the content. -/
theorem updateFromSat_eq_inter_content (sat : S → φ → Prop)
    (ψ : φ) (s : Set S) :
    updateFromSat sat ψ s = s ∩ contentOf sat ψ :=
  rfl

/-- The induced update is the lift of the satisfaction test. -/
theorem updateFromSat_eq_lift_test (sat : S → φ → Prop) (ψ : φ) :
    updateFromSat sat ψ = lift (test (λ p => sat p ψ)) :=
  funext λ _ => Set.ext λ p =>
    ⟨λ ⟨hp, hs⟩ => ⟨p, hp, rfl, hs⟩, λ ⟨_, hi, hip, hs⟩ => ⟨hip ▸ hi, hs⟩⟩

/-- Induced updates are distributive. -/
theorem updateFromSat_isDistributive (sat : S → φ → Prop) (ψ : φ) :
    CCP.IsDistributive (updateFromSat sat ψ) :=
  updateFromSat_eq_lift_test sat ψ ▸ lift_isDistributive _

/-- Support is being a fixed point of the update ([dekker-2012]'s Proper
Support). -/
theorem support_iff_update_eq (sat : S → φ → Prop)
    (ψ : φ) (s : Set S) :
    supportOf sat s ψ ↔ updateFromSat sat ψ s = s :=
  Set.inter_eq_left.symm

/-- Dynamic entailment: updating with `ψ₁` always yields a state supporting
`ψ₂`. -/
def dynamicEntailsOf (sat : S → φ → Prop) (ψ₁ ψ₂ : φ) : Prop :=
  ∀ s : Set S, supportOf sat (updateFromSat sat ψ₁ s) ψ₂

/-- Dynamic entailment is content inclusion — the layer's consequence
relation is classical entailment on contents. -/
theorem dynamicEntailsOf_iff_content_subset (sat : S → φ → Prop) (ψ₁ ψ₂ : φ) :
    dynamicEntailsOf sat ψ₁ ψ₂ ↔ contentOf sat ψ₁ ⊆ contentOf sat ψ₂ :=
  ⟨λ h _ hp => h Set.univ ⟨trivial, hp⟩, λ h _ => Set.inter_subset_right.trans h⟩

/-- Dynamic entailment is acceptance consequence of the induced updates. -/
theorem dynamicEntailsOf_iff_entails (sat : S → φ → Prop) (ψ₁ ψ₂ : φ) :
    dynamicEntailsOf sat ψ₁ ψ₂ ↔
      CCP.entails (updateFromSat sat ψ₁) (updateFromSat sat ψ₂) :=
  forall_congr' fun s => support_iff_update_eq sat ψ₂ (updateFromSat sat ψ₁ s)

/-- Dynamic entailment is reflexive. -/
theorem dynamicEntails_refl (sat : S → φ → Prop) (ψ : φ) :
    dynamicEntailsOf sat ψ ψ :=
  λ _ => Set.inter_subset_right

/-- Dynamic entailment is transitive. -/
theorem dynamicEntails_trans (sat : S → φ → Prop) (ψ₁ ψ₂ ψ₃ : φ)
    (h1 : dynamicEntailsOf sat ψ₁ ψ₂) (h2 : dynamicEntailsOf sat ψ₂ ψ₃) :
    dynamicEntailsOf sat ψ₁ ψ₃ :=
  λ s => Set.Subset.trans (h1 s) ((dynamicEntailsOf_iff_content_subset sat ψ₂ ψ₃).mp h2)

end Satisfaction

end DynamicSemantics
