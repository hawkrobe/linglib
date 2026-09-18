import Linglib.Semantics.Dynamic.Partial
import Linglib.Semantics.Dynamic.State

/-!
# File change semantics

This file defines [heim-1982]'s file change potentials as partial updates of
referential information states: `FCP W V M` is `CCP.Partial` at the
possibility type, the partiality effect of `Dynamic/Partial.lean` over the
states of `Dynamic/State.lean`. A file is a state whose points are its
sequences and whose cards are the established referents; a file in the
dissertation's sense, a satisfaction set of total sequences closed under
revaluing the cards outside its domain, is a state uniform at that domain
(`State.uniformEquiv`). Presupposition is `Part`-definedness
(`CCP.Partial.admits`), so the Novelty and Familiarity Conditions are
definedness conditions, and sequencing is `PFun.comp`.

Assertive update is consistent merge with a state, the regular action of the
merge monoid (`ofState_mul`). [heim-1982]'s atomic rule, whose satisfaction
clause filters the file and whose domain clause adds the atom's cards, is
this action at a state uniform at those cards, and its filtering and
extending regimes are `State.mul_eq_sep_of_uniformAt` read at an established
and at a novel card. Principle (A), that an update only adds information, is
inflation in the informativeness order (`IsInflationary`), closed under every
clause. Negation keeps the points that do not subsist in the scope's update,
which on a uniform stratum is [heim-1983]'s set difference
(`neg_eq_partial_neg`): the 1983 clauses over sequence–world pairs are the
uniform shadow of the 1982 ones.

## Main definitions

- `FCP`: file change potentials, `CCP.Partial (Possibility W V (Part M))`.
- `FCP.ofState`: assertive update by a state, with `FCP.atomW` and
  `FCP.atomVar` its instances at a world predicate and at a card.
- `FCP.neg`, `FCP.cond`: negation as non-subsistence, and *if* as
  `¬(φ ∧ ¬ψ)`.
- `FCP.indef`, `FCP.def_`: the Novelty Condition and the Extended
  Familiarity Condition as `Part.assert` guards.
- `FCP.IsInflationary`: Principle (A).
- `FCP.trueIn`: the truth criterion (C).

## Main results

- `ofState_one`, `ofState_mul`: assertive update is the regular action of
  the merge monoid.
- `atomVar_eq`, `atomVar_eq_of_familiar`, `atomVar_eq_of_novel`, `atomW_eq`:
  the card atom extends the file along its card and filters; at an
  established card it filters, at a novel card it is random assignment
  followed by filtering.
- `admits_indef`, `admits_def_`: the felicity conditions are definedness.
- `IsInflationary.seq`, `isInflationary_neg`, `IsInflationary.indef`,
  `isInflationary_def_`: Principle (A) is closed under the clauses, and
  `IsInflationary.familiar` is its consequence that a card, once
  established, stays established.
- `neg_eq_partial_neg`: on a uniform stratum, negation is set difference.

## References

- [heim-1982], [heim-1983], [heim-1991]
- [kamp-vangenabith-reyle-2011]
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

/-- An atomic predicate at card `x`: merge with its proposition at the
stratum `{x}`. -/
def atomVar (pred : M → Prop) (x : V) : FCP W V M :=
  ofState {q ∈ (State.stratum {x} : State W V M) | ∃ m ∈ q.assignment x, pred m}

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
  rw [atomVar, ofState_apply, State.mul_eq_sep_of_uniformAt fun _ h ↦ h.1]
  congr 1
  ext r
  refine and_congr_right fun hr ↦ ?_
  have hx : x ∈ r.domain := State.familiar_mul_stratum (Set.mem_singleton x) r hr
  show ((r.restrict {x}).domain = {x} ∧ ∃ m ∈ (r.restrict {x}).assignment x, pred m) ↔ _
  rw [Possibility.restrict_assignment_of_mem (Set.mem_singleton x), Possibility.domain_restrict,
    Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hx)]
  exact and_iff_right rfl

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
