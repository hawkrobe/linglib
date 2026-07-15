import Linglib.Semantics.Dynamic.DRS.Basic
import Linglib.Semantics.Dynamic.Transition

/-!
# Based relational semantics of DRSs
[kamp-vangenabith-reyle-2011] (Defs. 19, 22, 24), [kamp-reyle-1993]

The base-threaded verification semantics: `toRelAt X K f g` holds when the
output `g` agrees with the input `f` *on the context base* `X` and verifies
`K`'s conditions, sub-boxes entered at the grown base. This is the
total-assignment rendering of K&R's partial-embedding semantics
(Def. 19): values at established referents *persist* — contrast the flat
`DRS.toRel` (`DRS/Dynamics.lean`), whose agree-off-universe clause freely
reassigns re-declared referents (Muskens's fn. 4 divergence).

Persistence is what makes the based semantics well-typed: `toRelAt X K` is
read only at `X` (`toRelAt_congr_left` — one line, no witness surgery) and
written only at `X ∪ U` (`toRelAt_congr_right`, given the *referential
presupposition* `K.fv ⊆ X`), so a well-formed DRS denotes a spine
`Transition X (X ∪ U)` (`DRS.transition`), and a proper DRS expresses an
information state by acting on `⊥` (`DRS.state`, Def. 22).

The Merging Lemma and the action equation for this semantics
(`toRelAt_merge`, `state_merge`) are stated with the familiar freshness
hypothesis; the based setting needs strictly less — only *capture* by
sub-box universes is fatal, re-declaration is harmless — and the TODOs
record the sharp side condition.

## Main declarations

* `DRS.toRelAt` / `Condition.holdsAt` — the base-threaded semantics.
* `DRS.toRelAt_congr_left` / `toRelAt_congr_right` — read/write support.
* `DRS.transition` — a DRS as a spine transition `X ⟶ X ∪ U`.
* `DRS.state` — the information state a proper DRS expresses.
-/

open FirstOrder FirstOrder.Language
open Semantics.Dynamic (Possibility State Transition baseSupported_of_iff)

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]
variable [DecidableEq V]

/-! ### The base-threaded semantics -/

mutual
/-- Base-threaded relational semantics ([kamp-vangenabith-reyle-2011],
Def. 19 in total-assignment form): the output agrees with the input *on the
base* — established referents persist — and verifies the conditions, with
sub-boxes entered at the grown base. -/
def DRS.toRelAt (X : Finset V) : DRS L V → (V → M) → (V → M) → Prop
  | .mk U conds => fun f g => Set.EqOn g f ↑X ∧ Condition.holdsAllAt (X ∪ U) conds g
/-- A condition holds at a base under an assignment; sub-DRSs are entered as
context extensions of the current base. -/
def Condition.holdsAt (X : Finset V) : Condition L V → (V → M) → Prop
  | .rel R args => fun g => Structure.RelMap R (fun i => g (args i))
  | .eq u v => fun g => g u = g v
  | .neg K => fun g => ¬ ∃ g', DRS.toRelAt X K g g'
  | .imp a c => fun g => ∀ g', DRS.toRelAt X a g g' →
      ∃ g'', DRS.toRelAt (X ∪ a.referents) c g' g''
  | .dis l r => fun g => ∃ g', DRS.toRelAt X l g g' ∨ DRS.toRelAt X r g g'
/-- Every condition in the list holds at the base. A `List` helper — the
higher-order form fails the nested-inductive structural-recursion checker. -/
def Condition.holdsAllAt (X : Finset V) : List (Condition L V) → (V → M) → Prop
  | [] => fun _ => True
  | c :: cs => fun g => Condition.holdsAt X c g ∧ Condition.holdsAllAt X cs g
end

/-! ### Structural simp API -/

@[simp] theorem DRS.toRelAt_mk (X U : Finset V) (conds : List (Condition L V))
    (f g : V → M) :
    DRS.toRelAt X (.mk U conds) f g ↔
      Set.EqOn g f ↑X ∧ Condition.holdsAllAt (X ∪ U) conds g := Iff.rfl

@[simp] theorem Condition.holdsAt_rel (X : Finset V) {n : ℕ} (R : L.Relations n)
    (args : Fin n → V) (g : V → M) :
    (Condition.rel R args).holdsAt X g ↔
      Structure.RelMap R (fun i => g (args i)) := Iff.rfl

@[simp] theorem Condition.holdsAt_eq (X : Finset V) (u v : V) (g : V → M) :
    (Condition.eq u v : Condition L V).holdsAt X g ↔ g u = g v := Iff.rfl

@[simp] theorem Condition.holdsAt_neg (X : Finset V) (K : DRS L V) (g : V → M) :
    (Condition.neg K).holdsAt X g ↔ ¬ ∃ g', DRS.toRelAt X K g g' := Iff.rfl

@[simp] theorem Condition.holdsAt_imp (X : Finset V) (a c : DRS L V) (g : V → M) :
    (Condition.imp a c).holdsAt X g ↔
      ∀ g', DRS.toRelAt X a g g' →
        ∃ g'', DRS.toRelAt (X ∪ a.referents) c g' g'' := Iff.rfl

@[simp] theorem Condition.holdsAt_dis (X : Finset V) (l r : DRS L V) (g : V → M) :
    (Condition.dis l r).holdsAt X g ↔
      ∃ g', DRS.toRelAt X l g g' ∨ DRS.toRelAt X r g g' := Iff.rfl

@[simp] theorem Condition.holdsAllAt_nil (X : Finset V) (g : V → M) :
    Condition.holdsAllAt X ([] : List (Condition L V)) g := trivial

@[simp] theorem Condition.holdsAllAt_cons (X : Finset V) (c : Condition L V)
    (cs : List (Condition L V)) (g : V → M) :
    Condition.holdsAllAt X (c :: cs) g ↔
      Condition.holdsAt X c g ∧ Condition.holdsAllAt X cs g := Iff.rfl

/-! ### Read and write support

The based clauses only mention the input through the agreement conjunct, so
read-support is one line — the flat semantics' piecewise witness surgery
disappears. Write-support needs the referential presupposition `fv ⊆ X`
only at the atomic clauses. -/

/-- `toRelAt X K` reads its input only at `X`. -/
theorem DRS.toRelAt_congr_left (X : Finset V) (K : DRS L V) {f f' g : V → M}
    (h : Set.EqOn f f' ↑X) : DRS.toRelAt X K f g ↔ DRS.toRelAt X K f' g := by
  obtain ⟨U, conds⟩ := K
  simp only [DRS.toRelAt_mk]
  exact and_congr_left fun _ => ⟨fun he => he.trans h, fun he => he.trans h.symm⟩

/-- A condition with free referents in `X` depends on the assignment only at
`X`. -/
theorem Condition.holdsAt_congr {X : Finset V} (c : Condition L V)
    (hfv : c.fv ⊆ X) {g g' : V → M} (hgg' : Set.EqOn g g' ↑X) :
    Condition.holdsAt X c g ↔ Condition.holdsAt X c g' := by
  match c with
  | .rel R args =>
    simp only [Condition.holdsAt_rel]
    have : (fun i => g (args i)) = fun i => g' (args i) := by
      funext i
      exact hgg' (Finset.mem_coe.mpr (hfv (by simp)))
    rw [this]
  | .eq u v =>
    simp only [Condition.holdsAt_eq]
    rw [hgg' (Finset.mem_coe.mpr (hfv (by simp [Condition.fv_eq]))),
      hgg' (Finset.mem_coe.mpr (hfv (by simp [Condition.fv_eq])))]
  | .neg K =>
    simp only [Condition.holdsAt_neg]
    exact not_congr (exists_congr fun k => DRS.toRelAt_congr_left X K hgg')
  | .imp a c =>
    simp only [Condition.holdsAt_imp]
    exact forall_congr' fun g₁ =>
      imp_congr (DRS.toRelAt_congr_left X a hgg') Iff.rfl
  | .dis l r =>
    simp only [Condition.holdsAt_dis]
    exact exists_congr fun k =>
      or_congr (DRS.toRelAt_congr_left X l hgg') (DRS.toRelAt_congr_left X r hgg')

/-- The list analogue of `Condition.holdsAt_congr`. -/
theorem Condition.holdsAllAt_congr {X : Finset V} (cs : List (Condition L V))
    (hfv : Condition.fvL cs ⊆ X) {g g' : V → M} (hgg' : Set.EqOn g g' ↑X) :
    Condition.holdsAllAt X cs g ↔ Condition.holdsAllAt X cs g' := by
  induction cs with
  | nil => exact Iff.rfl
  | cons c cs ih =>
    rw [Condition.fvL_cons, Finset.union_subset_iff] at hfv
    simp only [Condition.holdsAllAt_cons]
    exact and_congr (Condition.holdsAt_congr c hfv.1 hgg') (ih hfv.2)

/-- `toRelAt X K` writes its output only at `X ∪ U`, given the referential
presupposition `K.fv ⊆ X`. -/
theorem DRS.toRelAt_congr_right {X : Finset V} (K : DRS L V) (hfv : K.fv ⊆ X)
    {f g g' : V → M} (hgg' : Set.EqOn g g' ↑(X ∪ K.referents)) :
    DRS.toRelAt X K f g ↔ DRS.toRelAt X K f g' := by
  obtain ⟨U, conds⟩ := K
  rw [DRS.fv_mk, sdiff_le_iff] at hfv
  rw [DRS.referents_mk] at hgg'
  have hX : Set.EqOn g g' ↑X := hgg'.mono (by simp)
  simp only [DRS.toRelAt_mk]
  exact and_congr
    ⟨fun he => hX.symm.trans he, fun he => hX.trans he⟩
    (Condition.holdsAllAt_congr conds
      (by rwa [sup_comm, Finset.sup_eq_union] at hfv) hgg')

/-! ### A DRS as a spine transition -/

/-- A well-formed DRS denotes a transition from its context base to the
base grown by its universe — `K.fv ⊆ X` is the *referential presupposition*
([kamp-vangenabith-reyle-2011], Def. 27(i)). -/
def DRS.transition (W : Type*) (K : DRS L V) (X : Finset V) (hK : K.fv ⊆ X) :
    Transition W M X (X ∪ K.referents) where
  rel _ f g := DRS.toRelAt X K f g
  grow := Finset.subset_union_left
  supported_left _ _ _ _ h := DRS.toRelAt_congr_left X K h
  supported_right _ _ _ _ h := DRS.toRelAt_congr_right K hK h

/-- Established referents persist along a DRS transition. -/
theorem DRS.transition_isExtension (W : Type*) (K : DRS L V) (X : Finset V)
    (hK : K.fv ⊆ X) : (K.transition (M := M) W X hK).IsExtension := by
  intro w f g h
  obtain ⟨U, conds⟩ := K
  exact h.1

/-- The information state a proper DRS expresses
([kamp-vangenabith-reyle-2011], Def. 22): act on the minimal state. -/
def DRS.state (W : Type*) (K : DRS L V) (hK : K.IsProper) : State W V M :=
  (K.transition W ∅ (Finset.subset_empty.mpr hK)).apply ⊥

end DRT
