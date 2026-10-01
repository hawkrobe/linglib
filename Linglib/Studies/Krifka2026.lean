module

public import Linglib.Semantics.Reference.Kind
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Dynamic.Update
public import Linglib.Logic.Assignment
public import Linglib.Semantics.Plurality.MassCount

/-!
# Krifka (2026): Anaphora for Concepts, Kinds, and Parts in Dynamic Interpretation

This file formalizes [krifka-2026]'s account of anaphora to concepts, kinds and parts. The head
noun of a DP introduces a discourse referent anchored to a concept, a property carrying a
morphosyntactic count feature, and the kind pronouns pick it up: *it* takes a mass concept to
its kind by the down operator of [chierchia-1998], *they* takes a count concept to the kind of
its plural closure (`they`), which is why *a spider* is resumed by *them* and *mold* by *it*; on
a cumulative concept the closure is absorbed, so the two coincide (`they_eq_it_of_supClosed`),
and on a singular count concept with several instances only the closed kind is defined
(`spider_no_kind`, `spiders_kind`). Concept discourse referents are presupposed in the input
assignment, like the referents of names, so they escape anaphoric islands: negation is a test,
and a test returns its input assignment, so a concept referent survives it while an entity
referent introduced under the negation does not (`concept_entity_asymmetry`). The anaphors
differ in what they presuppose: the empty NP and the kind pronoun a concept referent, the
partitive PP an entity referent, so after *John doesn't own a dog* the kind pronoun *them* is
interpretable and a partitive is not (`anaphora_after_negation`). The paper's derivation of
*John doesn't own a dog* is run on a two-entity model (`doesntOwnADog`).

## Implementation notes

* Assignments are total functions into a heterogeneous value type with a value marking
  indices outside the domain; an anaphor's presupposition is a conjunct of its update, so a
  failed presupposition makes the update empty rather than undefined.
* Negation is the paper's VP negation, the substrate's `test (neg φ)`; the sentential negation
  with its condition that the negated existential extend the input differs only in ways
  irrelevant to projection. The concept referent's presupposition is a hypothesis of the
  projection theorems; the paper derives it from the head noun's partial lexical entry.
* Which concepts sponsor kinds (*dogs from the animal shelter* does not) is left to the
  lexicon, as in the paper.
* Individuals form any join semilattice, as in the paper (§3); the models are Link's nonempty
  sets of atoms, `Plurality.Algebra.Individual`. The sufficient condition for σ is stated for
  finite extensions, where the paper has closure under arbitrary sums.

## References

* [krifka-2026]
* [chierchia-1998] — the down operator
* [link-1983] — the maximal element and the plural closure
* [hofmann-2025] — entity referents under negation, the neighbouring account
-/

@[expose] public section

namespace Krifka2026

open Reference Plurality.Algebra
open DynamicSemantics (Update Condition)
open DynamicSemantics.Update (test neg)
open SetRel

variable {World E : Type*}

/-! ### Kinds from concepts -/

section Kinds

variable [SemilatticeSup E]

/-- *it* (17a): the kind of a concept, ∩ of (13b). -/
noncomputable def it (P : World → Set E) : Kind World E := Kind.down P

/-- *they* (17b): the kind of the plural closure (14) of a concept. -/
noncomputable def they (P : World → Set E) : Kind World E := Kind.down fun w ↦ supClosure (P w)

/-- The kind pronoun the count feature selects. -/
noncomputable def pronoun : MassCount → (World → Set E) → Kind World E
  | .mass => it
  | .count => they

/-- Absorption: on a cumulative concept the closure changes nothing, so *they* and *it* would
denote the same kind ((16), (18d)); only the feature keeps *it* off a count concept. -/
theorem they_eq_it_of_supClosed {P : World → Set E} (h : ∀ w, SupClosed (P w)) :
    they P = it P := by
  unfold they it
  simp only [fun w ↦ (h w).supClosure_eq]

end Kinds

/-- Two spiders, as a property of individuals over two atoms. -/
def spider : Unit → Set (Individual Bool) :=
  fun _ ↦ {Individual.atom true, Individual.atom false}

/-- The kind of the singular count concept is undefined with two instances (15c). -/
theorem spider_no_kind : ¬ (it spider ()).Dom := by
  rintro ⟨x, hx, hmax⟩
  have h₁ := hmax (Set.mem_insert _ _)
  have h₂ := hmax (Set.mem_insert_of_mem _ rfl)
  rcases hx with rfl | rfl
  · exact Bool.noConfusion (Set.mem_singleton_iff.1 (h₂ (Set.mem_singleton false)))
  · exact Bool.noConfusion (Set.mem_singleton_iff.1 (h₁ (Set.mem_singleton true)))

/-- The kind of its plural closure is the sum of the two spiders (15b). -/
theorem spiders_kind : Individual.atom true ⊔ Individual.atom false ∈ they spider () := by
  rw [they, Kind.mem_down]
  refine ⟨supClosed_supClosure (subset_supClosure (Set.mem_insert _ _))
    (subset_supClosure (Set.mem_insert_of_mem _ rfl)), ?_⟩
  refine supClosure_min (t := Set.Iic (Individual.atom true ⊔ Individual.atom false)) ?_
    fun _ hx _ hy ↦ Set.mem_Iic.2 (sup_le (Set.mem_Iic.1 hx) (Set.mem_Iic.1 hy))
  rintro x (rfl | rfl)
  · exact (le_sup_left : Individual.atom true ≤ _)
  · exact (le_sup_right : Individual.atom false ≤ _)

/-! ### Concept discourse referents and anaphoric islands -/

/-- The values a discourse referent can be anchored to (§4): an entity, a concept with its
count feature, a kind, or an index; `undef` marks an index outside the assignment's domain. -/
inductive DRefVal (World E : Type*)
  | entity (x : E)
  | concept (P : World → Set E) (f : MassCount)
  | kind (k : Kind World E)
  | index (w : World)
  | undef

/-- Heterogeneous assignments. -/
abbrev HAssign (World E : Type*) := Assignment (DRefVal World E)

/-- Existential introduction of an entity referent at `n`, as by an indexed determiner (40c);
what falls under what is left to the body. -/
def entityIntro (n : ℕ) (body : Update (HAssign World E)) : Update (HAssign World E) :=
  {(g, h) | ∃ x : E, Function.update g n (.entity x) ~[body] h}

/-- A test returns its input assignment, so it preserves every referent: negation,
implication and disjunction all re-enter the update algebra through `test`. -/
theorem test_apply_eq {C : Condition (HAssign World E)} {g h : HAssign World E}
    (hTest : g ~[test C] h) (n : ℕ) : h n = g n :=
  congrFun hTest.1.symm n

/-- A concept referent presupposed in the input survives an island ((5a), (25), (45)). -/
theorem concept_survives_test {n : ℕ} {P : World → Set E} {f : MassCount}
    {C : Condition (HAssign World E)} {g h : HAssign World E}
    (hPresup : g n = .concept P f) (hTest : g ~[test C] h) : h n = .concept P f :=
  (test_apply_eq hTest n).trans hPresup

/-- An entity referent novel in the input, introduced only inside the island, is still undefined
after it (5c). -/
theorem entity_trapped_by_test {n : ℕ} {C : Condition (HAssign World E)}
    {g h : HAssign World E} (hNovel : g n = .undef) (hTest : g ~[test C] h) : h n = .undef :=
  (test_apply_eq hTest n).trans hNovel

/-- The asymmetry under negation (45): the concept referent persists, the entity referent does
not; both are the one fact about tests, the asymmetry lying in where the two conditions sit. -/
theorem concept_entity_asymmetry {nC nE : ℕ} {P : World → Set E} {f : MassCount}
    {φ : Update (HAssign World E)} {g h : HAssign World E}
    (hPresup : g nC = .concept P f) (hNovel : g nE = .undef) (hNeg : g ~[test (neg φ)] h) :
    h nC = .concept P f ∧ h nE = .undef :=
  ⟨concept_survives_test hPresup hNeg, entity_trapped_by_test hNovel hNeg⟩

/-! ### Concept, kind and partitive anaphors -/

section Anaphors

variable [SemilatticeSup E]

/-- The empty NP (46d) presupposes a concept referent at `n` and hands its property on. -/
def emptyNP (n : ℕ) (K : (World → Set E) → Update (HAssign World E)) :
    Update (HAssign World E) :=
  {(g, h) | ∃ P f, g n = .concept P f ∧ g ~[K P] h}

/-- The kind pronoun (48c) presupposes a concept referent at `n` bearing the feature it agrees
with and introduces the kind at `m`. -/
def kindPronoun (f : MassCount) (n m : ℕ) : Update (HAssign World E) :=
  {(g, h) | ∃ P, g n = .concept P f ∧ h = Function.update g m (.kind (pronoun f P))}

/-- The partitive PP presupposes an entity referent at `n` and introduces a part of it at `m`.
-/
def partitive (n m : ℕ) : Update (HAssign World E) :=
  {(g, h) | ∃ x y, g n = .entity x ∧ y ≤ x ∧ h = Function.update g m (.entity y)}

/-- After a negated sentence the kind pronoun and the empty NP are interpretable on the
concept referent, and a partitive on the trapped entity referent is not ((5a)–(5c)). -/
theorem anaphora_after_negation {nC nE m : ℕ} {P : World → Set E} {f : MassCount}
    {φ : Update (HAssign World E)} {g h : HAssign World E}
    (hPresup : g nC = .concept P f) (hNovel : g nE = .undef) (hNeg : g ~[test (neg φ)] h) :
    (∃ h', h ~[kindPronoun f nC m] h') ∧ (∀ K, h ~[K P] h → h ~[emptyNP nC K] h) ∧
      ¬ ∃ h', h ~[partitive nE m] h' :=
  ⟨⟨_, P, concept_survives_test hPresup hNeg, rfl⟩,
    fun _ hK ↦ ⟨P, f, concept_survives_test hPresup hNeg, hK⟩,
    fun ⟨_, _, _, hx, _⟩ ↦ by rw [entity_trapped_by_test hNovel hNeg] at hx; cases hx⟩

end Anaphors

/-! ### *John doesn't own a dog* -/

/-- The entities of the model. -/
inductive Ent
  | john
  | mary
  deriving DecidableEq

/-- The concept *dog*, with no instances. -/
def dog : Unit → Set (Individual Ent) := fun _ ↦ ∅

/-- The input assignment of (44e): John at 1, the count concept *dog* at 2. -/
def g₀ : HAssign Unit (Individual Ent)
  | 1 => .entity (Individual.atom .john)
  | 2 => .concept dog .count
  | _ => .undef

/-- *own [a₃ [dog]₂]* (44c): a referent at 3 falling under the concept at 2. -/
def ownADog : Update (HAssign Unit (Individual Ent)) :=
  entityIntro 3 (test {g | ∃ P f x, g 2 = .concept P f ∧ g 3 = .entity x ∧ x ∈ P ()})

/-- *John₁ doesn't own [a₃ [dog]₂]* (44e): the VP negation is the test of the negated update. -/
def doesntOwnADog : Update (HAssign Unit (Individual Ent)) := test (neg ownADog)

/-- The negated sentence holds in the model, there being no dogs, and returns the input. -/
theorem doesntOwnADog_g₀ : g₀ ~[doesntOwnADog] g₀ :=
  ⟨rfl, fun ⟨_, _, rfl, _, _, _, h₂, _, hy⟩ ↦ by
    rw [Function.update_of_ne (by decide : (2 : ℕ) ≠ 3)] at h₂
    cases h₂; exact Set.notMem_empty _ hy⟩

/-- After it, *them₂,₄* introduces the kind of dogs at 4 (48), while *it₃* has no referent
(5c). -/
theorem them_after_doesntOwnADog {h : HAssign Unit (Individual Ent)}
    (hNeg : g₀ ~[doesntOwnADog] h) :
    h ~[kindPronoun .count 2 4] Function.update h 4 (.kind (they dog)) ∧ h 3 = .undef :=
  ⟨⟨dog, concept_survives_test rfl hNeg, rfl⟩, entity_trapped_by_test rfl hNeg⟩

end Krifka2026
