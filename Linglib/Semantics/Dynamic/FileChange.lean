import Linglib.Semantics.Dynamic.Partial
import Linglib.Semantics.Dynamic.State

/-!
# File change semantics

This file defines file change potentials, the meanings of sentences in Heim's file change
semantics. A file records what a discourse has established so far: it keeps a card for each
individual that has been mentioned, and a sequence of individuals satisfies the file when,
read card by card, it fits every entry. Uttering a sentence changes the file. It filters out
the sequences the sentence rules out and opens a card for each individual the sentence
introduces, and the meaning of the sentence is the function from files to files that its
utterance brings about.

A file is an information state (`State`) whose points are the sequences and whose
established cards are the referents every point defines. The dissertation's files, which
distinguish only finitely many cards, are the states uniform at a set of cards. A file change
potential is a partial function on states. It is undefined at a file that fails the
sentence's felicity conditions, so presupposition is definedness: the Novelty Condition on an
indefinite requires its card to be new to the file, and the Familiarity Condition on a
definite requires the card to be present. Sequencing is composition of partial functions.

The assertive update by an atomic sentence merges the file with the sentence's proposition
state. At the cards the file already has the merge filters the sequences, and at new cards it
extends each sequence by every value, which is Heim's atomic rule read point by point. Every
update only adds information, so it is inflationary in the informativeness order, and a card,
once established, is never lost. Negation keeps the sequences that no extension carries into
the scope's update, which traps the referents introduced inside the scope. On a uniform file
negation is set difference, as in the later propositional presentation of the theory.

## Main definitions

* `FCP`: file change potentials, partial functions on the states of possibilities.
* `FCP.ofState`: the assertive update by a state, merging the file with it.
* `FCP.atomVar`: the update by an atomic predicate at a card.
* `FCP.atomW`: the update by an atomic predicate on the world alone.
* `FCP.neg`, `FCP.cond`: negation as non-subsistence, and the conditional as `¬(φ ∧ ¬ψ)`.
* `FCP.indef`: the indefinite, guarded by the Novelty Condition.
* `FCP.def_`: the definite, guarded by the Familiarity Condition and its descriptive content.
* `FCP.IsInflationary`: the updates that only add information.
* `FCP.trueIn`: truth of a sentence with respect to a file, as consistency of the updated file.

## Main results

* `FCP.ofState_mul`: updating by two states in sequence is updating by their merge.
* `FCP.atomVar_eq`: the atom extends the file along its card and filters by its predicate.
* `FCP.atomVar_eq_of_familiar`, `FCP.atomVar_eq_of_novel`: at an established card the atom
  filters, and at a new card it is random assignment followed by filtering.
* `FCP.admits_indef`, `FCP.admits_def_`: the felicity conditions are definedness.
* `FCP.IsInflationary.seq`, `FCP.isInflationary_neg`, `FCP.IsInflationary.indef`: inflation
  is closed under the clauses.
* `FCP.IsInflationary.familiar`: an established card stays established.
* `FCP.neg_eq_partial_neg`: on a uniform file, negation is set difference.

## References

* [heim-1982], [heim-1983], [heim-1991]
* [kamp-vangenabith-reyle-2011]
-/

namespace DynamicSemantics

/-- A file change potential ([heim-1982]): a partial update of referential
information states, `CCP.Partial` at the possibility type. Partiality is
presupposition (`CCP.Partial.admits`); Heim numbers her cards, `V := ℕ`. -/
abbrev FCP (W V M : Type*) := CCP.Partial (Possibility W V (Part M))

namespace FCP

variable {W V M : Type*} {A B F F' : State W V M} {φ ψ : FCP W V M} {x : V}

/-! ### Assertive update -/

/-- Assertive update by a state: the file merges with it. Each point of the
file pairs with every compatible point of `A`, filtering where their domains
overlap and extending where `A` defines more. The update is total;
appropriateness lives on `indef` and `def_`. -/
def ofState (A : State W V M) : FCP W V M := fun F : State W V M ↦ Part.some (F * A)

@[simp] theorem ofState_apply : ofState A F = Part.some (F * A) := rfl

theorem mem_ofState : F' ∈ ofState A F ↔ F' = F * A := Part.mem_some_iff

/-- Updating by the initial state changes nothing. -/
theorem ofState_one : ofState (1 : State W V M) = PFun.id _ := funext fun _ ↦ by simp

/-- Assertive update is the regular action of the merge monoid: updating by
`A` and then by `B` is updating by `A * B`. -/
theorem ofState_mul : ofState (A * B) = (ofState A).seq (ofState B) :=
  funext fun _ ↦ by simp [CCP.Partial.seq, PFun.comp_apply, mul_assoc]

/-- Principle (A) at an assertive update: merging ascends in informativeness. -/
theorem le_ofState (h : F' ∈ ofState A F) : F ≤ F' := mem_ofState.mp h ▸ State.left_le_mul

/-! ### Atoms -/

/-- An atomic predicate on the world: merge with its proposition at the empty
stratum. -/
def atomW (pred : W → Prop) : FCP W V M :=
  ofState {q ∈ (State.stratum ∅ : State W V M) | pred q.world}

/-- An atomic predicate at card `x`: merge with its proposition state at the
stratum `{x}`. -/
def atomVar (pred : M → Prop) (x : V) : FCP W V M := ofState (State.atomAt x fun _ ↦ pred)

/-- The world atom filters the file by its predicate. -/
theorem atomW_eq (pred : W → Prop) : atomW pred F = Part.some {p ∈ F | pred p.world} := by
  rw [atomW, ofState_apply, State.mul_eq_sep_of_uniformAt fun _ h ↦ h.1, State.mul_stratum_empty]
  congr 1
  ext r
  refine and_congr_right fun _ ↦ ?_
  show (∅ ∩ r.domain = ∅ ∧ pred r.world) ↔ pred r.world
  exact and_iff_right (Set.empty_inter _)

/-- The card atom extends the file along its card, then filters by its
predicate: the satisfaction clause and the domain clause of [heim-1982]'s
atomic rule, per point. -/
theorem atomVar_eq (pred : M → Prop) (x : V) :
    atomVar pred x F =
      Part.some {p ∈ F * State.stratum {x} | ∃ m ∈ p.assignment x, pred m} := by
  rw [atomVar, ofState_apply, State.mul_atomAt]

/-- At an established card the atom filters. -/
theorem atomVar_eq_of_familiar (pred : M → Prop) (hfam : State.Familiar F x) :
    atomVar pred x F = Part.some {p ∈ F | ∃ m ∈ p.assignment x, pred m} := by
  rw [atomVar_eq, hfam.mul_stratum_singleton]

/-- At a novel card the atom is random assignment followed by filtering, so
the indefinite adds only the Novelty guard. -/
theorem atomVar_eq_of_novel [DecidableEq V] (pred : M → Prop) (hnov : State.Novel F x) :
    atomVar pred x F =
      Part.some {p ∈ F.randomAssign x | ∃ m ∈ p.assignment x, pred m} := by
  rw [atomVar_eq, hnov.mul_stratum_singleton]

/-! ### Connectives and felicity conditions -/

/-- Negation keeps the points of `F` that do not subsist in the scope's
update: no extension of the point verifies the scope, so referents
introduced inside it are trapped. Undefined when the scope is. -/
def neg (φ : FCP W V M) : FCP W V M :=
  fun F : State W V M ↦ (φ F).map fun F' ↦ {p ∈ F | p ∉ lowerClosure F'}

/-- The conditional is the negated conjunction `¬(φ ∧ ¬ψ)`. -/
def cond (φ ψ : FCP W V M) : FCP W V M := neg (φ.seq (neg ψ))

/-- An indefinite at card `x`: defined only if `x` is novel (the Novelty
Condition), then random assignment at `x` followed by the body. Indefinites
do not quantify; they open a card. [heim-1991] later derives novelty from
Maximize Presupposition rather than stipulating it. -/
def indef [DecidableEq V] (x : V) (body : FCP W V M) : FCP W V M :=
  fun F : State W V M ↦ Part.assert (State.Novel F x) fun _ ↦ body (F.randomAssign x)

/-- A definite at card `x` with descriptive content `N`: defined only if `x`
is established and the file supports its content (the Extended
Novelty-Familiarity-Condition), and then changes nothing. -/
def def_ (x : V) (N : FCP W V M) : FCP W V M :=
  fun F : State W V M ↦
    Part.assert (State.Familiar F x ∧ CCP.Partial.supports F N) fun _ ↦ Part.some F

@[simp] theorem admits_neg : (neg φ).admits F ↔ φ.admits F := Iff.rfl

/-- The conditional admits a file iff its antecedent does and its consequent
admits the antecedent's update. -/
theorem admits_cond :
    (cond φ ψ).admits F ↔ ∃ h : φ.admits F, ψ.admits ((φ F).get h) := Iff.rfl

/-- The Novelty Condition is definedness. -/
theorem admits_indef [DecidableEq V] (body : FCP W V M) :
    (indef x body).admits F ↔ ∃ _ : State.Novel F x, (body (F.randomAssign x)).Dom :=
  Iff.rfl

theorem indef_apply [DecidableEq V] (body : FCP W V M) (h : State.Novel F x) :
    indef x body F = body (F.randomAssign x) := Part.assert_pos h

/-- The Extended Familiarity Condition is definedness. -/
theorem admits_def_ (N : FCP W V M) :
    (def_ x N).admits F ↔ State.Familiar F x ∧ CCP.Partial.supports F N :=
  ⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, trivial⟩⟩

theorem def_apply (N : FCP W V M) (h : State.Familiar F x ∧ CCP.Partial.supports F N) :
    def_ x N F = Part.some F := Part.assert_pos h

/-- Negation only discards points. -/
theorem subset_of_mem_neg (h : F' ∈ neg φ F) : F' ⊆ F := by
  obtain ⟨_, -, rfl⟩ := (Part.mem_map_iff _).mp h
  exact fun _ hp ↦ hp.1

theorem isEliminative_neg (φ : FCP W V M) : (neg φ).IsEliminative :=
  fun _ _ ↦ subset_of_mem_neg

/-! ### Principle (A) -/

/-- Principle (A): every defined update ascends in informativeness. On a
uniform stratum this is set shrinking (`State.UniformAt.le_iff_superset`);
at a novel card an update extends rather than shrinks. -/
def IsInflationary (φ : FCP W V M) : Prop := ∀ F : State W V M, ∀ F' ∈ φ F, F ≤ F'

theorem isInflationary_id : IsInflationary (PFun.id _ : FCP W V M) :=
  fun _ _ h ↦ le_of_eq (Part.mem_some_iff.mp h).symm

theorem isInflationary_ofState (A : State W V M) : (ofState A).IsInflationary :=
  fun _ _ ↦ le_ofState

/-- A set-shrinking update is inflationary. -/
theorem _root_.DynamicSemantics.CCP.Partial.IsEliminative.isInflationary
    (h : φ.IsEliminative) : φ.IsInflationary :=
  fun _ _ hF' ↦ State.le_of_superset (h _ _ hF')

theorem IsInflationary.seq (hφ : φ.IsInflationary) (hψ : ψ.IsInflationary) :
    IsInflationary (φ.seq ψ) := fun s s' h ↦
  let ⟨t, ht, hs'⟩ := Part.mem_bind_iff.mp h
  (hφ s t ht).trans (hψ t s' hs')

theorem isInflationary_neg (φ : FCP W V M) : (neg φ).IsInflationary :=
  (isEliminative_neg φ).isInflationary

theorem isInflationary_cond (φ ψ : FCP W V M) : (cond φ ψ).IsInflationary :=
  isInflationary_neg _

theorem IsInflationary.indef [DecidableEq V] {body : FCP W V M} (h : body.IsInflationary)
    (x : V) : (indef x body).IsInflationary := fun _ _ hF' ↦
  let ⟨hn, hF'⟩ := Part.mem_assert_iff.mp hF'
  (State.le_randomAssign hn).trans (h _ _ hF')

theorem isInflationary_def_ (x : V) (N : FCP W V M) : (def_ x N).IsInflationary :=
  fun _ _ hF' ↦ let ⟨_, hF'⟩ := Part.mem_assert_iff.mp hF'; le_of_eq (Part.mem_some_iff.mp hF').symm

/-- Once false, always false: an inflationary update of the absurd file is
absurd. -/
theorem IsInflationary.eq_empty_of_mem (h : φ.IsInflationary) (hF' : F' ∈ φ ∅) : F' = ∅ :=
  State.eq_empty_of_top_le (h ∅ F' hF')

/-- A card, once established, stays established. -/
theorem IsInflationary.familiar (h : φ.IsInflationary) (hx : State.Familiar F x)
    (hF' : F' ∈ φ F) : State.Familiar F' x :=
  hx.of_le (h F F' hF')

/-! ### Truth -/

/-- The truth criterion (C): `φ` is true with respect to `F` iff `F + φ` is
defined and consistent. Existential quantification is built into truth, so
indefinites need no existential closure. -/
def trueIn (F : State W V M) (φ : FCP W V M) : Prop := ∃ F' ∈ φ F, F'.Nonempty

/-- Truth implies definedness. -/
theorem trueIn_admits (h : trueIn F φ) : φ.admits F :=
  let ⟨F', hF', _⟩ := h
  Part.dom_iff_mem.mpr ⟨F', hF'⟩

/-- A consistent file is true at what it supports. -/
theorem trueIn_of_supports (hsup : CCP.Partial.supports F φ) (hcons : F.Nonempty) :
    trueIn F φ :=
  ⟨F, CCP.Partial.supports_iff_mem.mp hsup, hcons⟩

/-! ### The uniform shadow -/

/-- On a uniform stratum, non-subsistence negation is [heim-1983]'s
set-difference negation (`CCP.Partial.neg`): with every referent shared, a
point subsists in the update exactly when it survives into it. -/
theorem neg_eq_partial_neg [DecidableEq V] {X : Finset V} (hF : State.UniformAt X F)
    (hφ : ∀ F' ∈ φ F, State.UniformAt X F') :
    neg φ F = CCP.Partial.neg φ F := by
  refine Part.ext' Iff.rfl fun h₁ h₂ ↦ ?_
  show ({p ∈ (F : Set (Possibility W V (Part M))) | p ∉ lowerClosure ((φ F).get h₁)} : Set _) =
    (F : Set (Possibility W V (Part M))) \ (φ F).get h₁
  ext p
  exact and_congr_right fun hp ↦ not_congr
    ((hφ _ (Part.get_mem _)).mem_lowerClosure (hF p hp))

end FCP

end DynamicSemantics
