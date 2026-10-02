module

public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Dynamic.Update
public import Linglib.Logic.Assignment
public import Linglib.Semantics.Plurality.MassCount

/-!
# Krifka (2026): Anaphora for Concepts, Kinds, and Parts in Dynamic Interpretation

Krifka treats the head noun of a DP as introducing a discourse referent for a concept, a
property with a count feature. The kind pronouns take that concept to a kind: *it* takes a mass
concept to its kind, and *they* takes a count concept to the kind of its plural closure, so *a
spider* is resumed by *them* and *mold* by *it*. Concept referents are presupposed by the input
assignment, as the referents of names are, so they survive negation, which is a test, while an
entity referent introduced under negation does not. After *John doesn't own a dog*, the kind
pronoun *them* is therefore interpretable and a partitive is not.

## Main results

* `Krifka2026.they_eq_it_of_supClosed`: on a cumulative concept the two pronouns coincide.
* `Krifka2026.spider_no_kind`, `Krifka2026.spiders_kind`: a singular count concept with two
  instances has only the closed kind.
* `Krifka2026.concept_entity_asymmetry`: a concept referent survives negation and an entity
  referent does not.
* `Krifka2026.anaphora_after_negation`: after negation the kind pronoun and the empty NP are
  interpretable and the partitive is not.
* `Krifka2026.doesntOwnADog_g₀`, `Krifka2026.them_after_doesntOwnADog`: the paper's derivation
  of *John doesn't own a dog* on a two-entity model.

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
  sets of atoms, `Plurality.Algebra.Individual`. A kind is a function from worlds to partial
  individuals, and σ is `Reference.iota?`. The sufficient condition for σ is stated for finite
  extensions (`it_isSome_of_supClosed`), where the paper has closure under arbitrary sums.

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

/-- *it* (17a) denotes the kind of a concept, ∩ as in (13b). -/
noncomputable def it (P : World → Set E) : World → Option E := fun w ↦ iota? (P w)

/-- *they* (17b) denotes the kind of the plural closure (14) of a concept. -/
noncomputable def they (P : World → Set E) : World → Option E :=
  fun w ↦ iota? (supClosure (P w))

/-- `pronoun f` is the kind pronoun that the count feature `f` selects. -/
noncomputable def pronoun : MassCount → (World → Set E) → World → Option E
  | .mass => it
  | .count => they

/-- On a cumulative concept the plural closure changes nothing, so *they* and *it* denote the
same kind ((16), (18d)). -/
theorem they_eq_it_of_supClosed {P : World → Set E} (h : ∀ w, SupClosed (P w)) :
    they P = it P := by
  unfold they it
  simp only [fun w ↦ (h w).supClosure_eq]

/-- The kind of a finite, nonempty, cumulative concept is defined, the finite case of the
sufficient condition for σ stated after (13). -/
theorem it_isSome_of_supClosed {P : World → Set E} {w : World} (hfin : (P w).Finite)
    (hne : (P w).Nonempty) (hcum : SupClosed (P w)) : (it P w).isSome :=
  have ht : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.2 hne
  iota?_isSome_iff.2 ⟨hfin.toFinset.sup' ht id,
    hcum.finsetSup'_mem ht fun _ hx ↦ hfin.mem_toFinset.1 hx,
    fun _ hx ↦ Finset.le_sup' id (hfin.mem_toFinset.2 hx)⟩

end Kinds

/-- The concept *spider* holds of the two atoms of a two-atom model. -/
def spider : Unit → Set (Individual Bool) :=
  fun _ ↦ {Individual.atom true, Individual.atom false}

/-- The kind of the singular count concept is undefined with two instances (15c). -/
theorem spider_no_kind : it spider () = none := by
  refine iota?_eq_none_iff.2 ?_
  rintro ⟨x, hx, hmax⟩
  have h₁ := hmax (Set.mem_insert _ _)
  have h₂ := hmax (Set.mem_insert_of_mem _ rfl)
  rcases hx with rfl | rfl
  · exact Bool.noConfusion (Set.mem_singleton_iff.1 (h₂ (Set.mem_singleton false)))
  · exact Bool.noConfusion (Set.mem_singleton_iff.1 (h₁ (Set.mem_singleton true)))

/-- The kind of the plural closure of *spider* is the sum of the two spiders (15b). -/
theorem spiders_kind : they spider () = some (Individual.atom true ⊔ Individual.atom false) := by
  refine iota?_eq_some_iff.2 ⟨supClosed_supClosure (subset_supClosure (Set.mem_insert _ _))
    (subset_supClosure (Set.mem_insert_of_mem _ rfl)), ?_⟩
  refine supClosure_min (t := Set.Iic (Individual.atom true ⊔ Individual.atom false)) ?_
    fun _ hx _ hy ↦ Set.mem_Iic.2 (sup_le (Set.mem_Iic.1 hx) (Set.mem_Iic.1 hy))
  rintro x (rfl | rfl)
  · exact (le_sup_left : Individual.atom true ≤ _)
  · exact (le_sup_right : Individual.atom false ≤ _)

/-! ### Concept discourse referents and anaphoric islands -/

/-- A discourse referent is anchored to an entity, a concept with its count feature, a kind, or
an index (§4); `undef` marks an index outside the assignment's domain. -/
inductive DRefVal (World E : Type*)
  | entity (x : E)
  | concept (P : World → Set E) (f : MassCount)
  | kind (k : World → Option E)
  | index (w : World)
  | undef

/-- A heterogeneous assignment sends each index to a discourse-referent value. -/
abbrev HAssign (World E : Type*) := Assignment (DRefVal World E)

/-- `entityIntro n body` introduces an entity referent at `n` existentially, as an indexed
determiner does (40c), and leaves its restriction to `body`. -/
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

/-- Under negation the concept referent persists and the entity referent does not (45); the
asymmetry lies only in where the two referents are introduced. -/
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

/-- The model has two entities, John and Mary. -/
inductive Ent
  | john
  | mary
  deriving DecidableEq

/-- The concept *dog* has no instances. -/
def dog : Unit → Set (Individual Ent) := fun _ ↦ ∅

/-- The input assignment of (44e) sends 1 to John and 2 to the count concept *dog*. -/
def g₀ : HAssign Unit (Individual Ent)
  | 1 => .entity (Individual.atom .john)
  | 2 => .concept dog .count
  | _ => .undef

/-- *own [a₃ [dog]₂]* (44c) introduces a referent at 3 that falls under the concept at 2. -/
def ownADog : Update (HAssign Unit (Individual Ent)) :=
  entityIntro 3 (test {g | ∃ P f x, g 2 = .concept P f ∧ g 3 = .entity x ∧ x ∈ P ()})

/-- *John₁ doesn't own [a₃ [dog]₂]* (44e) is the VP negation, the test of the negated update. -/
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
