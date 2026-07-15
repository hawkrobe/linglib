import Linglib.Semantics.Dynamic.DRS.Basic
import Linglib.Semantics.Dynamic.DRS.Dynamics
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

The Merging Lemma for this semantics (`toRelAt_merge`) needs strictly less
than the flat freshness hypothesis — only *capture* by sub-box universes is
fatal, re-declaration is harmless — and lifts to the spine
(`transition_merge`), where the action equation (`state_merge`) becomes an
instance of functoriality (`Transition.apply_comp`).

## Main declarations

* `DRS.toRelAt` / `Condition.holdsAt` — the base-threaded semantics.
* `DRS.toRelAt_congr_left` / `toRelAt_congr_right` — read/write support.
* `DRS.transition` — a DRS as a spine transition `X ⟶ X ∪ U`.
* `DRS.state` — the information state a proper DRS expresses.
* `DRS.transition_merge` / `DRS.state_merge` — the Merging Lemma on the
  spine and the action equation.
* `DRS.trueRel_iff_toRelAt` — on reuse-free DRSs the flat and based
  semantics have the same truth conditions.
-/

open FirstOrder FirstOrder.Language
open DynamicSemantics (Possibility State Transition baseSupported_of_iff)

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
  rw [DRS.referents_mk] at hgg'
  have hX : Set.EqOn g g' ↑X := hgg'.mono (by simp)
  simp only [DRS.toRelAt_mk]
  exact and_congr
    ⟨fun he => hX.symm.trans he, fun he => hX.trans he⟩
    (Condition.holdsAllAt_congr conds (DRS.fv_subset_iff.mp hfv) hgg')

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

/-- The empty DRS denotes the identity transition. -/
theorem DRS.transition_empty (W : Type*) (X : Finset V)
    (h : (DRS.empty : DRS L V).fv ⊆ X) :
    DRS.empty.transition (M := M) W X h =
      (Transition.id X).copy rfl (Finset.union_empty X).symm := by
  apply Transition.ext
  funext w f g
  rw [Transition.rel_copy]
  show (Set.EqOn g f ↑X ∧ _) = _
  simp [Transition.id, Set.eqOn_comm]

/-- Established referents persist along a DRS transition. -/
theorem DRS.transition_isExtension (W : Type*) (K : DRS L V) (X : Finset V)
    (hK : K.fv ⊆ X) : (K.transition (M := M) W X hK).IsExtension := by
  intro w f g h
  obtain ⟨U, conds⟩ := K
  exact h.1

/-- Repackaging a DRS transition along an equality of context bases is the
transition at the new base. -/
theorem DRS.transition_copy (W : Type*) {X X' : Finset V} (K : DRS L V)
    (hX : X = X') (hK : K.fv ⊆ X) (hK' : K.fv ⊆ X') :
    (K.transition (M := M) W X hK).copy hX (by rw [hX]) = K.transition W X' hK' := by
  subst hX; rfl

/-- The information state a proper DRS expresses
([kamp-vangenabith-reyle-2011], Def. 22): act on the minimal state. -/
def DRS.state (W : Type*) (K : DRS L V) (hK : K.IsProper) : State W V M :=
  (K.transition W ∅ (Finset.subset_empty.mpr hK)).apply ⊥

@[simp] theorem DRS.state_base (W : Type*) (K : DRS L V) (hK : K.IsProper) :
    (K.state (M := M) W hK).base = K.referents := by
  simp [DRS.state]

/-- The characteristic membership form: a possibility survives in `⟦K⟧ˢ` iff
some input reaches its assignment. -/
@[simp] theorem DRS.mem_state {W : Type*} {K : DRS L V} {hK : K.IsProper}
    {w : W} {g : V → M} :
    (⟨w, g⟩ : Possibility W V M) ∈ K.state W hK ↔ ∃ e, DRS.toRelAt ∅ K e g := by
  simp only [DRS.state, Transition.mem_apply]
  exact ⟨fun ⟨e, _, he⟩ => ⟨e, he⟩, fun ⟨e, he⟩ => ⟨e, Set.mem_univ _, he⟩⟩

/-! ### Base invariance

A fresh extension of the base is invisible to a well-formed condition. The
only fatal interference is *capture* — a fresh referent colliding with a
sub-box universe would freeze a previously local existential — so the
hypothesis is disjointness from the occurring referents. Re-declaration of
base referents needs no exclusion: persistence makes it inert. -/

@[simp] theorem Condition.holdsAllAt_append (X : Finset V)
    (cs ds : List (Condition L V)) (g : V → M) :
    Condition.holdsAllAt X (cs ++ ds) g ↔
      Condition.holdsAllAt X cs g ∧ Condition.holdsAllAt X ds g := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, and_assoc]

/-- Surgery: overriding a `toRelAt`-output with the input's values on a
fresh `Δ` yields an output at the grown base, agreeing with the original on
the working base. -/
private theorem DRS.toRelAt_adjust {X Δ U : Finset V} {conds : List (Condition L V)}
    (hΔU : Disjoint Δ U) (hfvc : Condition.fvL conds ⊆ X ∪ U)
    (hIH : ∀ k : V → M, Condition.holdsAllAt ((X ∪ U) ∪ Δ) conds k ↔
      Condition.holdsAllAt (X ∪ U) conds k)
    {g k : V → M} (hk : DRS.toRelAt X (.mk U conds) g k) :
    DRS.toRelAt (X ∪ Δ) (.mk U conds) g (fun x => if x ∈ Δ then g x else k x) ∧
      Set.EqOn (fun x => if x ∈ Δ then g x else k x) k ↑(X ∪ U) := by
  obtain ⟨hag, hh⟩ := hk
  have hkk' : Set.EqOn (fun x => if x ∈ Δ then g x else k x) k ↑(X ∪ U) := by
    intro x hx
    by_cases hxΔ : x ∈ Δ
    · have hxU : x ∉ U := Finset.disjoint_left.mp hΔU hxΔ
      have hxX : x ∈ X := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
        · exact h
        · exact absurd h hxU
      simp only [if_pos hxΔ]
      exact (hag (Finset.mem_coe.mpr hxX)).symm
    · simp only [if_neg hxΔ]
  refine ⟨⟨?_, ?_⟩, hkk'⟩
  · intro x hx
    by_cases hxΔ : x ∈ Δ
    · simp only [if_pos hxΔ]
    · have hxX : x ∈ X := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
        · exact h
        · exact absurd h hxΔ
      simp only [if_neg hxΔ]
      exact hag (Finset.mem_coe.mpr hxX)
  · rw [Finset.union_right_comm]
    exact (hIH _).mpr ((Condition.holdsAllAt_congr conds hfvc hkk'.symm).mp hh)

/-- Fresh base extensions discard: an output at the grown base is an output
at the working base. -/
private theorem DRS.toRelAt_down {X Δ U : Finset V} {conds : List (Condition L V)}
    (hIH : ∀ k : V → M, Condition.holdsAllAt ((X ∪ U) ∪ Δ) conds k ↔
      Condition.holdsAllAt (X ∪ U) conds k)
    {g k : V → M} (hk : DRS.toRelAt (X ∪ Δ) (.mk U conds) g k) :
    DRS.toRelAt X (.mk U conds) g k := by
  obtain ⟨hag, hh⟩ := hk
  refine ⟨hag.mono (Finset.coe_subset.mpr Finset.subset_union_left), ?_⟩
  rw [Finset.union_right_comm] at hh
  exact (hIH k).mp hh

mutual
/-- **Base invariance**: a fresh base extension is invisible to a well-formed
condition. -/
theorem Condition.holdsAt_union_fresh {X Δ : Finset V} (c : Condition L V)
    (hocc : Disjoint Δ c.occ) (hfv : c.fv ⊆ X) (g : V → M) :
    Condition.holdsAt (X ∪ Δ) c g ↔ Condition.holdsAt X c g := by
  match c with
  | .rel R args => exact Iff.rfl
  | .eq u v => exact Iff.rfl
  | .neg K =>
    obtain ⟨U, conds⟩ := K
    simp only [Condition.occ, DRS.occ] at hocc
    rw [Condition.fv_neg] at hfv
    obtain ⟨hΔU, hΔc⟩ := Finset.disjoint_union_right.mp hocc
    have hfvc : Condition.fvL conds ⊆ X ∪ U := DRS.fv_subset_iff.mp hfv
    have hIH : ∀ k : V → M, Condition.holdsAllAt ((X ∪ U) ∪ Δ) conds k ↔
        Condition.holdsAllAt (X ∪ U) conds k :=
      fun k => Condition.holdsAllAt_union_fresh conds hΔc hfvc k
    simp only [Condition.holdsAt_neg]
    exact not_congr ⟨fun ⟨k, hk⟩ => ⟨k, DRS.toRelAt_down hIH hk⟩,
      fun ⟨k, hk⟩ => ⟨_, (DRS.toRelAt_adjust hΔU hfvc hIH hk).1⟩⟩
  | .imp a c' =>
    obtain ⟨Ua, ca⟩ := a
    obtain ⟨Uc, cc⟩ := c'
    simp only [Condition.occ, DRS.occ] at hocc
    obtain ⟨ha, hc⟩ := Finset.disjoint_union_right.mp hocc
    obtain ⟨hΔUa, hΔca⟩ := Finset.disjoint_union_right.mp ha
    obtain ⟨hΔUc, hΔcc⟩ := Finset.disjoint_union_right.mp hc
    rw [Condition.fv_imp, Finset.union_subset_iff] at hfv
    obtain ⟨hfva, hfvc'⟩ := hfv
    have hfvca : Condition.fvL ca ⊆ X ∪ Ua := DRS.fv_subset_iff.mp hfva
    have hfvcc : Condition.fvL cc ⊆ (X ∪ Ua) ∪ Uc := by
      intro x hx
      by_cases hxUc : x ∈ Uc
      · exact Finset.mem_union_right _ hxUc
      · by_cases hxUa : x ∈ Ua
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxUa)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (hfvc' ?_))
          rw [DRS.fv_mk, DRS.referents_mk, Finset.mem_sdiff, Finset.mem_sdiff]
          exact ⟨⟨hx, hxUc⟩, hxUa⟩
    have hIHa : ∀ k : V → M, Condition.holdsAllAt ((X ∪ Ua) ∪ Δ) ca k ↔
        Condition.holdsAllAt (X ∪ Ua) ca k :=
      fun k => Condition.holdsAllAt_union_fresh ca hΔca hfvca k
    have hIHc : ∀ k : V → M, Condition.holdsAllAt (((X ∪ Ua) ∪ Uc) ∪ Δ) cc k ↔
        Condition.holdsAllAt ((X ∪ Ua) ∪ Uc) cc k :=
      fun k => Condition.holdsAllAt_union_fresh cc hΔcc hfvcc k
    simp only [Condition.holdsAt_imp, DRS.referents_mk]
    constructor
    · intro hL g₁ hg₁
      obtain ⟨hadj, heq⟩ := DRS.toRelAt_adjust hΔUa hfvca hIHa hg₁
      obtain ⟨g₂, hg₂⟩ := hL _ hadj
      rw [Finset.union_right_comm] at hg₂
      refine ⟨g₂, (DRS.toRelAt_congr_left (X ∪ Ua) _ heq).mp ?_⟩
      exact DRS.toRelAt_down hIHc hg₂
    · intro hR g₁ hg₁
      obtain ⟨g₂, hg₂⟩ := hR g₁ (DRS.toRelAt_down hIHa hg₁)
      have hadj := (DRS.toRelAt_adjust hΔUc hfvcc hIHc hg₂).1
      rw [Finset.union_right_comm] at hadj
      exact ⟨_, hadj⟩
  | .dis l r =>
    obtain ⟨Ul, cl⟩ := l
    obtain ⟨Ur, cr⟩ := r
    simp only [Condition.occ, DRS.occ] at hocc
    obtain ⟨hl, hr⟩ := Finset.disjoint_union_right.mp hocc
    obtain ⟨hΔUl, hΔcl⟩ := Finset.disjoint_union_right.mp hl
    obtain ⟨hΔUr, hΔcr⟩ := Finset.disjoint_union_right.mp hr
    rw [Condition.fv_dis, Finset.union_subset_iff] at hfv
    obtain ⟨hfvl, hfvr⟩ := hfv
    have hfvcl : Condition.fvL cl ⊆ X ∪ Ul := DRS.fv_subset_iff.mp hfvl
    have hfvcr : Condition.fvL cr ⊆ X ∪ Ur := DRS.fv_subset_iff.mp hfvr
    have hIHl : ∀ k : V → M, Condition.holdsAllAt ((X ∪ Ul) ∪ Δ) cl k ↔
        Condition.holdsAllAt (X ∪ Ul) cl k :=
      fun k => Condition.holdsAllAt_union_fresh cl hΔcl hfvcl k
    have hIHr : ∀ k : V → M, Condition.holdsAllAt ((X ∪ Ur) ∪ Δ) cr k ↔
        Condition.holdsAllAt (X ∪ Ur) cr k :=
      fun k => Condition.holdsAllAt_union_fresh cr hΔcr hfvcr k
    simp only [Condition.holdsAt_dis]
    constructor
    · rintro ⟨k, hk | hk⟩
      · exact ⟨k, Or.inl (DRS.toRelAt_down hIHl hk)⟩
      · exact ⟨k, Or.inr (DRS.toRelAt_down hIHr hk)⟩
    · rintro ⟨k, hk | hk⟩
      · exact ⟨_, Or.inl (DRS.toRelAt_adjust hΔUl hfvcl hIHl hk).1⟩
      · exact ⟨_, Or.inr (DRS.toRelAt_adjust hΔUr hfvcr hIHr hk).1⟩
/-- The list analogue of `Condition.holdsAt_union_fresh`. -/
theorem Condition.holdsAllAt_union_fresh {X Δ : Finset V}
    (cs : List (Condition L V)) (hocc : Disjoint Δ (Condition.occL cs))
    (hfv : Condition.fvL cs ⊆ X) (g : V → M) :
    Condition.holdsAllAt (X ∪ Δ) cs g ↔ Condition.holdsAllAt X cs g := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    simp only [Condition.occL] at hocc
    obtain ⟨hc, hcs⟩ := Finset.disjoint_union_right.mp hocc
    rw [Condition.fvL_cons, Finset.union_subset_iff] at hfv
    simp only [Condition.holdsAllAt_cons]
    exact and_congr (Condition.holdsAt_union_fresh c hc hfv.1 g)
      (Condition.holdsAllAt_union_fresh cs hcs hfv.2 g)
end

/-! ### The Merging Lemma and the action equation -/

/-- **Based Merging Lemma**: merge is sequencing. The side condition asks
only that `K₂`'s universe not occur in `K₁`'s conditions (no *capture*);
re-declaration of context or `K₁`-universe referents is allowed — persistence
makes it inert. Contrast the flat lemma (`DRS.toRel_merge`), whose freshness
hypothesis also had to forbid re-declaration. -/
theorem DRS.toRelAt_merge {X : Finset V} (K₁ K₂ : DRS L V) (h₁ : K₁.fv ⊆ X)
    (hfresh : Disjoint K₂.referents (Condition.occL K₁.conditions)) :
    (DRS.toRelAt X (K₁.merge K₂) : (V → M) → (V → M) → Prop) =
      DRS.toRelAt X K₁ ⨟ DRS.toRelAt (X ∪ K₁.referents) K₂ := by
  obtain ⟨U₁, c₁⟩ := K₁
  obtain ⟨U₂, c₂⟩ := K₂
  have hfvc₁ := DRS.fv_subset_iff.mp h₁
  simp only [DRS.referents_mk, DRS.conditions_mk] at hfresh
  funext f g
  apply propext
  simp only [DRS.merge, DRS.referents_mk, DRS.conditions_mk, DRS.toRelAt_mk,
    Condition.holdsAllAt_append, DynamicSemantics.DynProp.dseq, Relation.Comp]
  rw [← Finset.union_assoc]
  constructor
  · rintro ⟨hag, hh₁, hh₂⟩
    exact ⟨g, ⟨hag, (Condition.holdsAllAt_union_fresh c₁ hfresh hfvc₁ g).mp hh₁⟩,
      Set.eqOn_refl g _, hh₂⟩
  · rintro ⟨h, ⟨hhf, hh₁⟩, hgh, hh₂⟩
    exact ⟨(hgh.mono (Finset.coe_subset.mpr Finset.subset_union_left)).trans hhf,
      (Condition.holdsAllAt_union_fresh c₁ hfresh hfvc₁ g).mpr
        ((Condition.holdsAllAt_congr c₁ hfvc₁ hgh).mpr hh₁), hh₂⟩

/-- **Transition-level Merging Lemma**: sequencing the transitions is the
merge's transition, repackaged along associativity of the grown bases. -/
theorem DRS.transition_merge (W : Type*) {X : Finset V} (K₁ K₂ : DRS L V)
    (h₁ : K₁.fv ⊆ X) (h₂ : K₂.fv ⊆ X ∪ K₁.referents)
    (hfresh : Disjoint K₂.referents (Condition.occL K₁.conditions)) :
    (K₁.transition (M := M) W X h₁).comp (K₂.transition W (X ∪ K₁.referents) h₂) =
      ((K₁.merge K₂).transition W X (DRS.fv_merge_subset h₁ h₂)).copy rfl
        (by rw [DRS.merge_referents, ← Finset.union_assoc]) := by
  ext w f g
  simp only [Transition.rel_copy, Transition.comp, DRS.transition,
    DRS.toRelAt_merge K₁ K₂ h₁ hfresh, DynamicSemantics.DynProp.dseq]

/-- **Action equation** ([kamp-vangenabith-reyle-2011], p. 159): applying a
DRS's transition to the state a proper context DRS expresses yields the
state of the merge — an instance of `Transition.apply_comp` through the
transition-level Merging Lemma. -/
theorem DRS.state_merge (W : Type*) (K₁ K₂ : DRS L V) (h₁ : K₁.IsProper)
    (h₂ : K₂.fv ⊆ K₁.referents)
    (hfresh : Disjoint K₂.referents (Condition.occL K₁.conditions)) :
    (K₂.transition (M := M) W K₁.referents h₂).apply (K₁.state W h₁) =
      (K₁.merge K₂).state W (DRS.isProper_merge h₁ h₂) := by
  simp only [DRS.state]
  rw [← DRS.transition_copy (M := M) W K₂ (Finset.empty_union _)
      (h₂.trans Finset.subset_union_right) h₂,
    Transition.apply_copy, ← Transition.apply_comp,
    DRS.transition_merge (M := M) W K₁ K₂ (Finset.subset_empty.mpr h₁)
      (h₂.trans Finset.subset_union_right) hfresh,
    Transition.apply_copy]

/-! ### Reconciliation with the flat semantics

On reuse-free DRSs (`DRS.ReuseFreeAt`, `DRS/Basic.lean`) the flat
agree-off-universe semantics (`DRS.toRel`, `DRS/Dynamics.lean`) and the based
persistence semantics coincide at truth level: every flat output is a based
output, and a based output repairs, off the grown base, into a flat one.
Reuse-freeness is needed — on a DRS that re-declares a referent the two
diverge ([muskens-1996], fn. 4; witness in `Studies/Muskens1996.lean`). -/

/-- Flat-to-based on a reuse-free box: agreement off the universe restricts
to agreement on a disjoint base. -/
private theorem DRS.toRelAt_of_toRel' {X U : Finset V} {conds : List (Condition L V)}
    (hXU : Disjoint X U)
    (hIH : ∀ k : V → M, Condition.holdsAll conds k ↔ Condition.holdsAllAt (X ∪ U) conds k)
    {g g' : V → M} (h : DRS.toRel (.mk U conds) g g') :
    DRS.toRelAt X (.mk U conds) g g' := by
  obtain ⟨hag, hh⟩ := h
  exact ⟨fun x hx => hag x (Finset.disjoint_left.mp hXU (Finset.mem_coe.mp hx)),
    (hIH g').mp hh⟩

/-- Based-to-flat on a bounded box: repair the output off the grown base with
the input's values. -/
private theorem DRS.toRel_of_toRelAt' {X U : Finset V} {conds : List (Condition L V)}
    (hfvc : Condition.fvL conds ⊆ X ∪ U)
    (hIH : ∀ k : V → M, Condition.holdsAll conds k ↔ Condition.holdsAllAt (X ∪ U) conds k)
    {g g' : V → M} (h : DRS.toRelAt X (.mk U conds) g g') :
    DRS.toRel (.mk U conds) g (fun x => if x ∈ U then g' x else g x) ∧
      Set.EqOn (fun x => if x ∈ U then g' x else g x) g' ↑(X ∪ U) := by
  obtain ⟨hag, hh⟩ := h
  have heq : Set.EqOn (fun x => if x ∈ U then g' x else g x) g' ↑(X ∪ U) := by
    intro x hx
    by_cases hxU : x ∈ U
    · simp only [if_pos hxU]
    · have hxX : x ∈ X := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
        · exact h
        · exact absurd h hxU
      simp only [if_neg hxU]
      exact (hag (Finset.mem_coe.mpr hxX)).symm
  exact ⟨⟨fun x hxU => if_neg hxU,
    (hIH _).mpr ((Condition.holdsAllAt_congr conds hfvc heq).mpr hh)⟩, heq⟩

mutual
/-- On a reuse-free condition with free referents in the base, the flat set
denotation and the based one coincide. -/
theorem Condition.holds_iff_holdsAt {X : Finset V} (c : Condition L V)
    (hrf : Condition.ReuseFreeAt X c) (hfv : c.fv ⊆ X) (g : V → M) :
    Condition.holds c g ↔ Condition.holdsAt X c g := by
  match c with
  | .rel R args => exact Iff.rfl
  | .eq u v => exact Iff.rfl
  | .neg K =>
    obtain ⟨U, conds⟩ := K
    simp only [Condition.reuseFreeAt_neg, DRS.reuseFreeAt_mk] at hrf
    rw [Condition.fv_neg] at hfv
    have hfvc := DRS.fv_subset_iff.mp hfv
    have hIH : ∀ k : V → M, Condition.holdsAll conds k ↔
        Condition.holdsAllAt (X ∪ U) conds k :=
      fun k => Condition.holdsAll_iff_holdsAllAt conds hrf.2 hfvc k
    simp only [Condition.holds_neg, Condition.holdsAt_neg]
    exact not_congr ⟨fun ⟨k, hk⟩ => ⟨k, DRS.toRelAt_of_toRel' hrf.1 hIH hk⟩,
      fun ⟨k, hk⟩ => ⟨_, (DRS.toRel_of_toRelAt' hfvc hIH hk).1⟩⟩
  | .imp a c' =>
    obtain ⟨Ua, ca⟩ := a
    obtain ⟨Uc, cc⟩ := c'
    simp only [Condition.reuseFreeAt_imp, DRS.reuseFreeAt_mk, DRS.referents_mk] at hrf
    obtain ⟨⟨hXUa, hrfa⟩, hXUc, hrfc⟩ := hrf
    rw [Condition.fv_imp, Finset.union_subset_iff] at hfv
    obtain ⟨hfva, hfvc'⟩ := hfv
    have hfvca : Condition.fvL ca ⊆ X ∪ Ua := DRS.fv_subset_iff.mp hfva
    have hfvcc : Condition.fvL cc ⊆ (X ∪ Ua) ∪ Uc := by
      intro x hx
      by_cases hxUc : x ∈ Uc
      · exact Finset.mem_union_right _ hxUc
      · by_cases hxUa : x ∈ Ua
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxUa)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (hfvc' ?_))
          rw [DRS.fv_mk, DRS.referents_mk, Finset.mem_sdiff, Finset.mem_sdiff]
          exact ⟨⟨hx, hxUc⟩, hxUa⟩
    have hIHa : ∀ k : V → M, Condition.holdsAll ca k ↔
        Condition.holdsAllAt (X ∪ Ua) ca k :=
      fun k => Condition.holdsAll_iff_holdsAllAt ca hrfa hfvca k
    have hIHc : ∀ k : V → M, Condition.holdsAll cc k ↔
        Condition.holdsAllAt ((X ∪ Ua) ∪ Uc) cc k :=
      fun k => Condition.holdsAll_iff_holdsAllAt cc hrfc hfvcc k
    simp only [Condition.holds_imp, Condition.holdsAt_imp, DRS.referents_mk]
    constructor
    · intro hL g₁ hg₁
      obtain ⟨hflat, heq⟩ := DRS.toRel_of_toRelAt' hfvca hIHa hg₁
      obtain ⟨g₂, hg₂⟩ := hL _ hflat
      exact ⟨g₂, (DRS.toRelAt_congr_left (X ∪ Ua) _ heq).mp
        (DRS.toRelAt_of_toRel' hXUc hIHc hg₂)⟩
    · intro hR g₁ hg₁
      obtain ⟨g₂, hg₂⟩ := hR g₁ (DRS.toRelAt_of_toRel' hXUa hIHa hg₁)
      exact ⟨_, (DRS.toRel_of_toRelAt' hfvcc hIHc hg₂).1⟩
  | .dis l r =>
    obtain ⟨Ul, cl⟩ := l
    obtain ⟨Ur, cr⟩ := r
    simp only [Condition.reuseFreeAt_dis, DRS.reuseFreeAt_mk] at hrf
    obtain ⟨⟨hXUl, hrfl⟩, hXUr, hrfr⟩ := hrf
    rw [Condition.fv_dis, Finset.union_subset_iff] at hfv
    have hfvcl : Condition.fvL cl ⊆ X ∪ Ul := DRS.fv_subset_iff.mp hfv.1
    have hfvcr : Condition.fvL cr ⊆ X ∪ Ur := DRS.fv_subset_iff.mp hfv.2
    have hIHl : ∀ k : V → M, Condition.holdsAll cl k ↔
        Condition.holdsAllAt (X ∪ Ul) cl k :=
      fun k => Condition.holdsAll_iff_holdsAllAt cl hrfl hfvcl k
    have hIHr : ∀ k : V → M, Condition.holdsAll cr k ↔
        Condition.holdsAllAt (X ∪ Ur) cr k :=
      fun k => Condition.holdsAll_iff_holdsAllAt cr hrfr hfvcr k
    simp only [Condition.holds_dis, Condition.holdsAt_dis]
    constructor
    · rintro ⟨k, hk | hk⟩
      · exact ⟨k, Or.inl (DRS.toRelAt_of_toRel' hXUl hIHl hk)⟩
      · exact ⟨k, Or.inr (DRS.toRelAt_of_toRel' hXUr hIHr hk)⟩
    · rintro ⟨k, hk | hk⟩
      · exact ⟨_, Or.inl (DRS.toRel_of_toRelAt' hfvcl hIHl hk).1⟩
      · exact ⟨_, Or.inr (DRS.toRel_of_toRelAt' hfvcr hIHr hk).1⟩
/-- The list analogue of `Condition.holds_iff_holdsAt`. -/
theorem Condition.holdsAll_iff_holdsAllAt {X : Finset V} (cs : List (Condition L V))
    (hrf : Condition.ReuseFreeAtL X cs) (hfv : Condition.fvL cs ⊆ X) (g : V → M) :
    Condition.holdsAll cs g ↔ Condition.holdsAllAt X cs g := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    simp only [Condition.reuseFreeAtL_cons] at hrf
    rw [Condition.fvL_cons, Finset.union_subset_iff] at hfv
    exact and_congr (Condition.holds_iff_holdsAt c hrf.1 hfv.1 g)
      (Condition.holdsAll_iff_holdsAllAt cs hrf.2 hfv.2 g)
end

/-- Flat-to-based: on a reuse-free DRS every flat output is a based output. -/
theorem DRS.toRelAt_of_toRel {X : Finset V} {K : DRS L V} (hrf : DRS.ReuseFreeAt X K)
    (hfv : K.fv ⊆ X) {g g' : V → M} (h : DRS.toRel K g g') : DRS.toRelAt X K g g' := by
  obtain ⟨U, conds⟩ := K
  simp only [DRS.reuseFreeAt_mk] at hrf
  exact DRS.toRelAt_of_toRel' hrf.1
    (fun k => Condition.holdsAll_iff_holdsAllAt conds hrf.2 (DRS.fv_subset_iff.mp hfv) k) h

/-- Based-to-flat: on a reuse-free DRS a based output repairs, off the grown
base, into a flat output. -/
theorem DRS.toRel_of_toRelAt {X : Finset V} {K : DRS L V} (hrf : DRS.ReuseFreeAt X K)
    (hfv : K.fv ⊆ X) {g g' : V → M} (h : DRS.toRelAt X K g g') :
    ∃ g'', DRS.toRel K g g'' ∧ Set.EqOn g'' g' ↑(X ∪ K.referents) := by
  obtain ⟨U, conds⟩ := K
  simp only [DRS.reuseFreeAt_mk] at hrf
  exact ⟨_, DRS.toRel_of_toRelAt' (DRS.fv_subset_iff.mp hfv)
    (fun k => Condition.holdsAll_iff_holdsAllAt conds hrf.2 (DRS.fv_subset_iff.mp hfv) k) h⟩

/-- **Truth-level reconciliation** ([muskens-1996], fn. 4): on a reuse-free
DRS the flat total-assignment semantics and the based persistence semantics
have the same truth conditions. Reuse-freeness is needed — a re-declaring
witness separates the two (`Studies/Muskens1996.lean`). -/
theorem DRS.trueRel_iff_toRelAt {X : Finset V} {K : DRS L V} (hrf : DRS.ReuseFreeAt X K)
    (hfv : K.fv ⊆ X) (g : V → M) :
    DRS.trueRel K g ↔ ∃ g', DRS.toRelAt X K g g' := by
  rw [DRS.trueRel_iff]
  exact ⟨fun ⟨g', h⟩ => ⟨g', DRS.toRelAt_of_toRel hrf hfv h⟩,
    fun ⟨g', h⟩ => (DRS.toRel_of_toRelAt hrf hfv h).imp fun _ hg => hg.1⟩

end DRT
