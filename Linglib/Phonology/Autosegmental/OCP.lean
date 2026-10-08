/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.FreeMonoid.Destutter
public import Linglib.Phonology.OCP
public import Linglib.Phonology.Autosegmental.Realization
public import Linglib.Phonology.Autosegmental.TwoTier

/-!
# OCP-merging collapse of autosegmental representations

A merging realization ([jardine-2019]; the melody merge of [jardine-heinz-2015]) fuses adjacent
identical melody nodes, so that a melody `Hⁿ` realizes as one `H` linked to `n` timing slots.
`AR.collapse m` performs the merge on melody tier `m`: the tier word is destuttered
(`OCP.collapse`), each link is repointed through the run index `runIdx`, and the other tiers are
untouched, so a merged node keeps every slot its run was linked to. `realizeMerged` is the
realization followed by the collapse.

## Main definitions

* `AR.collapse`: the OCP merge of melody tier `m`.
* `realizeMerged`: the merging realization of a string.
* `AR.IsCleanAt`: no adjacent repeats on melody tier `m`.
* `MergedLinks`: the lines of the merged realization of a string of two-tier presentations.

## Main results

* `AR.link_collapse`: the links of a collapse are the repointed links.
* `AR.cls_collapse_tensor`: collapsing a concatenation equals collapsing the concatenation of
  the collapses, up to isomorphism.
* `AR.isCleanAt_collapse`, `AR.noCrossing_collapse`: the collapse is OCP-clean and preserves
  the NCC.
* `AR.isCleanAt_iff_isOCPClean`: tier-word cleanliness is Axiom 6 on the normal form.
* `AR.free_realizeMerged_ofWords_iff`: the merged realization of a string of presentations
  reads as one presentation.
-/

@[expose] public section

namespace Autosegmental

open OCP

variable {α β : Type*} [DecidableEq α]

/-! ### The collapse in coordinates

The OCP merge on the graph foundation: destutter melody tier `m`'s word and
repoint its links through `runIdx`. Like `normalize` the result is a
`AR` on a sigma-`Fin` carrier, but the merge is not a pullback —
`runIdx` is monotone, not bijective — so the structural axioms are proved
directly on the merged carrier. -/

section CoordinateCollapse
open CategoryTheory
open scoped MonoidalCategory

variable {ι : Type*} [DecidableEq ι] {τ : ι → Type*}
variable (X : TieredAR ι τ)
variable (m : ι) [DecidableEq (τ m)]

/-- The tier words after collapsing melody tier `m` are destuttered at `m` and untouched
elsewhere. -/
noncomputable def AR.collapsedWord [Finite X.obj.V] : ∀ i, List (τ i) :=
  Function.update (fun i => X.tierWord i) m (OCP.collapse (X.tierWord m))

@[simp] theorem AR.collapsedWord_self [Finite X.obj.V] :
    X.collapsedWord m m = OCP.collapse (X.tierWord m) :=
  Function.update_self ..

@[simp] theorem AR.collapsedWord_of_ne [Finite X.obj.V] {i : ι} (h : i ≠ m) :
    X.collapsedWord m i = X.tierWord i :=
  Function.update_of_ne h ..

theorem AR.collapsedWord_length_le [Finite X.obj.V] (i : ι) :
    (X.collapsedWord m i).length ≤ X.tierLength i := by
  rcases eq_or_ne i m with rfl | h
  · simpa using OCP.collapse_length_le (X.tierWord i)
  · simp [h]

/-- Positions are repointed by `runIdx` on the melody tier and fixed elsewhere. -/
noncomputable def AR.collapseIdx [Finite X.obj.V] (i : ι) (p : ℕ) : ℕ :=
  if i = m then runIdx (X.tierWord m) p else p

@[simp] theorem AR.collapseIdx_self [Finite X.obj.V] (p : ℕ) :
    X.collapseIdx m m p = runIdx (X.tierWord m) p :=
  ite_eq_left rfl

@[simp] theorem AR.collapseIdx_of_ne [Finite X.obj.V] {i : ι} (h : i ≠ m) (p : ℕ) :
    X.collapseIdx m i p = p :=
  ite_eq_right h

/-- The OCP-merging collapse destutters melody tier `m`, repoints links through `runIdx`, and
leaves the other tiers untouched. -/
noncomputable def AR.collapse [Finite X.obj.V] :
    TieredAR ι τ where
  obj :=
    { V := (i : ι) × Fin (X.collapsedWord m i).length
      edges :=
        { Adj := fun v w => v ≠ w ∧ ∃ p q, X.link v.1 w.1 p q ∧
            X.collapseIdx m v.1 p = v.2 ∧ X.collapseIdx m w.1 q = w.2
          symm := ⟨fun v w h => ⟨h.1.symm, by
            obtain ⟨p, q, hl, hp, hq⟩ := h.2
            exact ⟨q, p, X.link_symm hl, hq, hp⟩⟩⟩
          loopless := ⟨fun v h => h.1 rfl⟩ }
      arcs := ⟨fun v w => v.1 = w.1 ∧ (v.2 : ℕ) < (w.2 : ℕ)⟩
      label := fun v => ⟨v.1, (X.collapsedWord m v.1)[v.2]⟩ }
  property := by
    refine ⟨{ irrefl := fun v h => lt_irrefl _ h.2,
              trans := fun u v w huv hvw => ⟨huv.1.trans hvw.1, huv.2.trans hvw.2⟩,
              tier_eq := fun v w h => h.1,
              total := fun v w hne htier => ?_ },
      fun v w hadj harc => ?_⟩
    · obtain ⟨i, p⟩ := v
      obtain ⟨j, q⟩ := w
      obtain rfl : i = j := htier
      rcases Nat.lt_trichotomy (p : ℕ) (q : ℕ) with h | h | h
      · exact Or.inl ⟨rfl, h⟩
      · exact absurd (by rw [Fin.ext h]) hne
      · exact Or.inr ⟨rfl, h⟩
    · obtain ⟨hne, p, q, ⟨hp, hq, hl⟩, -, -⟩ := hadj
      obtain ⟨i, pv⟩ := v
      obtain ⟨j, qw⟩ := w
      obtain rfl : i = j := harc.1
      have hlab : X.obj.tier Sigma.fst (X.vertexEquiv ⟨i, ⟨p, hp⟩⟩)
          = X.obj.tier Sigma.fst (X.vertexEquiv ⟨i, ⟨q, hq⟩⟩) := by
        show (X.obj.label _).1 = (X.obj.label _).1
        rw [X.label_vertexEquiv, X.label_vertexEquiv]
      exact (X.property.1.total hl.ne hlab).elim (X.property.2 hl) (X.property.2 hl.symm)

instance [Finite X.obj.V] : Finite (X.collapse m).obj.V :=
  haveI : Finite ((i : ι) × Fin (X.tierLength i)) := Finite.of_equiv _ X.vertexEquiv.symm
  Finite.of_injective
    (fun v : (i : ι) × Fin (X.collapsedWord m i).length =>
      (⟨v.1, v.2.castLE (X.collapsedWord_length_le m v.1)⟩ : (i : ι) × Fin (X.tierLength i)))
    fun v w h => by
      obtain ⟨i, p⟩ := v
      obtain ⟨j, q⟩ := w
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
      exact congrArg _ (Fin.castLE_injective _ (eq_of_heq h2))

/-- The collapsed fiber at `i` is enumerated by its position range. -/
noncomputable def AR.collapseFiberEnum [Finite X.obj.V] (i : ι) :
    Fin ((X.collapsedWord m i).length) ≃o (X.collapse m).fiber i := by
  refine StrictMono.orderIsoOfSurjective (fun p => ⟨⟨i, p⟩, rfl⟩) (fun p q h => ⟨rfl, h⟩)
    fun v => ?_
  obtain ⟨⟨j, q⟩, hp⟩ := v
  obtain rfl : j = i := hp
  exact ⟨q, rfl⟩

/-- The tier words of the collapse are the collapsed words. -/
@[simp] theorem AR.tierWord_collapse [Finite X.obj.V] (i : ι) :
    (X.collapse m).tierWord i = X.collapsedWord m i := by
  rw [AR.tierWord_eq_ofFn (X.collapseFiberEnum m i)]
  exact List.ofFn_getElem

/-- Collapsing a tensor computes the same tier words as collapsing the tensor of the
collapsed factors, the word half of the OCP congruence. -/
theorem AR.collapsedWord_tensor
    {Y : TieredAR ι τ}
    [Finite X.obj.V] [Finite Y.obj.V] (i : ι) :
    (X ⊗ Y).collapsedWord m i = (X.collapse m ⊗ Y.collapse m).collapsedWord m i := by
  rcases eq_or_ne i m with rfl | h
  · simp only [AR.collapsedWord, Function.update_self,
      AR.tierWord_tensor, AR.tierWord_collapse]
    exact OCP.collapse_append _ _
  · simp [AR.collapsedWord, Function.update_of_ne h]

theorem AR.fiberEnum_collapse [Finite X.obj.V] (i : ι) :
    (X.collapse m).fiberEnum i =
      (Fin.castOrderIso (by rw [← AR.length_tierWord,
        AR.tierWord_collapse])).trans (X.collapseFiberEnum m i) :=
  Subsingleton.elim _ _

theorem AR.vertexEquiv_collapse [Finite X.obj.V] {i : ι}
    (r : Fin ((X.collapse m).tierLength i)) :
    (X.collapse m).vertexEquiv ⟨i, r⟩
      = ⟨i, Fin.cast (by rw [← AR.length_tierWord,
          AR.tierWord_collapse]) r⟩ := by
  show ((X.collapse m).fiberEnum i r).val = _
  rw [AR.fiberEnum_collapse]
  rfl

/-- The collapse's links are the image of the original links under the
    repointing — `edges_normalize`'s analogue for the merge. -/
theorem AR.link_collapse [Finite X.obj.V] (i j : ι) (r s : ℕ) :
    (X.collapse m).link i j r s ↔
      ∃ p q, X.link i j p q ∧ X.collapseIdx m i p = r ∧ X.collapseIdx m j q = s := by
  constructor
  · rintro ⟨hr, hs, hl⟩
    rw [AR.linkRel_def, AR.vertexEquiv_collapse,
      AR.vertexEquiv_collapse] at hl
    obtain ⟨-, p, q, hpq, hp, hq⟩ := hl
    exact ⟨p, q, hpq, hp, hq⟩
  · rintro ⟨p, q, hpq, hp, hq⟩
    have hbr : r < (X.collapse m).tierLength i := by
      rw [← AR.length_tierWord, AR.tierWord_collapse]
      subst hp
      unfold AR.collapseIdx
      split_ifs with h
      · subst h
        simpa [AR.collapsedWord] using
          runIdx_lt_collapse_length _ (by simpa using hpq.1)
      · simpa [AR.collapsedWord, Function.update_of_ne h] using hpq.1
    have hbs : s < (X.collapse m).tierLength j := by
      rw [← AR.length_tierWord, AR.tierWord_collapse]
      subst hq
      unfold AR.collapseIdx
      split_ifs with h
      · subst h
        simpa [AR.collapsedWord] using
          runIdx_lt_collapse_length _ (by simpa using hpq.2.1)
      · simpa [AR.collapsedWord, Function.update_of_ne h] using hpq.2.1
    refine ⟨hbr, hbs, ?_⟩
    rw [AR.linkRel_def, AR.vertexEquiv_collapse,
      AR.vertexEquiv_collapse]
    refine ⟨?_, p, q, hpq, hp, hq⟩
    intro heq
    obtain ⟨hij, -⟩ := Sigma.mk.inj_iff.mp heq
    subst hij
    exact X.not_link_self_tier i p q hpq

@[simp] theorem AR.tierLength_collapse [Finite X.obj.V] (i : ι) :
    (X.collapse m).tierLength i = (X.collapsedWord m i).length := by
  rw [← AR.length_tierWord, AR.tierWord_collapse]

section Congruence
variable {Y : TieredAR ι τ}
variable [Finite X.obj.V] [Finite Y.obj.V]

/-- Left-block positions commute with the collapse-collapse seam. -/
theorem AR.collapseIdx_left (i : ι) {p : ℕ} (hp : p < X.tierLength i) :
    (X.collapse m ⊗ Y.collapse m).collapseIdx m i (X.collapseIdx m i p)
      = (X ⊗ Y).collapseIdx m i p := by
  unfold AR.collapseIdx
  split_ifs with h
  · subst h
    simp only [AR.tierWord_tensor, AR.tierWord_collapse,
      AR.collapsedWord, Function.update_self]
    exact (runIdx_append_collapse_left (xs := X.tierWord i) (ys := Y.tierWord i)
      (by simpa using hp)).symm
  · rfl

/-- Right-block positions commute with the collapse-collapse seam. -/
theorem AR.collapseIdx_right (i : ι) {p : ℕ} (hp : p < Y.tierLength i) :
    (X.collapse m ⊗ Y.collapse m).collapseIdx m i
        ((X.collapse m).tierLength i + Y.collapseIdx m i p)
      = (X ⊗ Y).collapseIdx m i (X.tierLength i + p) := by
  unfold AR.collapseIdx
  split_ifs with h
  · subst h
    simp only [AR.tierWord_tensor, AR.tierWord_collapse,
      AR.collapsedWord, Function.update_self,
      ← AR.length_tierWord]
    exact (runIdx_append_collapse_right (xs := X.tierWord i) (ys := Y.tierWord i)
      (by simpa using hp)).symm
  · simp [AR.tierLength_collapse, AR.collapsedWord,
      Function.update_of_ne h]

/-- The link half of the OCP congruence, in ℕ coordinates. -/
theorem AR.link_collapse_tensor (i j : ι) (r s : ℕ) :
    ((X ⊗ Y).collapse m).link i j r s ↔
      ((X.collapse m ⊗ Y.collapse m).collapse m).link i j r s := by
  rw [AR.link_collapse, AR.link_collapse]
  constructor
  · rintro ⟨p, q, hpq, hr, hs⟩
    rcases (AR.link_tensor i j p q).mp hpq with hX | ⟨hpi, hqj, hY⟩
    · refine ⟨X.collapseIdx m i p, X.collapseIdx m j q,
        (AR.link_tensor i j _ _).mpr
          (Or.inl ((X.link_collapse m i j _ _).mpr ⟨p, q, hX, rfl, rfl⟩)), ?_, ?_⟩
      · rw [X.collapseIdx_left m i hX.1, hr]
      · rw [X.collapseIdx_left m j hX.2.1, hs]
    · refine ⟨(X.collapse m).tierLength i + Y.collapseIdx m i (p - X.tierLength i),
        (X.collapse m).tierLength j + Y.collapseIdx m j (q - X.tierLength j),
        (AR.link_tensor i j _ _).mpr (Or.inr ⟨by omega, by omega, ?_⟩), ?_, ?_⟩
      · rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
        exact (Y.link_collapse m i j _ _).mpr ⟨_, _, hY, rfl, rfl⟩
      · rw [X.collapseIdx_right m i hY.1, Nat.add_sub_cancel' hpi, hr]
      · rw [X.collapseIdx_right m j hY.2.1, Nat.add_sub_cancel' hqj, hs]
  · rintro ⟨p', q', hpq', hr, hs⟩
    rcases (AR.link_tensor i j p' q').mp hpq' with hX | ⟨hpi', hqj', hY'⟩
    · obtain ⟨p, q, hX₀, hcp, hcq⟩ := (X.link_collapse m i j p' q').mp hX
      refine ⟨p, q, (AR.link_tensor i j p q).mpr (Or.inl hX₀), ?_, ?_⟩
      · rw [← X.collapseIdx_left m i hX₀.1, hcp, hr]
      · rw [← X.collapseIdx_left m j hX₀.2.1, hcq, hs]
    · obtain ⟨a, b, hY₀, hca, hcb⟩ :=
        (Y.link_collapse m i j (p' - (X.collapse m).tierLength i)
          (q' - (X.collapse m).tierLength j)).mp hY'
      refine ⟨X.tierLength i + a, X.tierLength j + b,
        (AR.link_tensor i j _ _).mpr (Or.inr ⟨by omega, by omega, ?_⟩), ?_, ?_⟩
      · rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
        exact hY₀
      · rw [← X.collapseIdx_right m i hY₀.1, hca, Nat.add_sub_cancel' hpi', hr]
      · rw [← X.collapseIdx_right m j hY₀.2.1, hcb, Nat.add_sub_cancel' hqj', hs]

/-- Collapsing a concatenation is isomorphic to collapsing the concatenation of the
collapses, the melody-merge law of [jardine-heinz-2015]. -/
noncomputable def AR.collapseTensorFullIso :
    Graph.Iso ((X ⊗ Y).collapse m).obj
      ((X.collapse m ⊗ Y.collapse m).collapse m).obj :=
  AR.fullIsoOfReaderEq
    (fun i => ((X ⊗ Y).tierWord_collapse m i).trans ((X.collapsedWord_tensor m i).trans
      ((X.collapse m ⊗ Y.collapse m).tierWord_collapse m i).symm))
    (fun i j r s => AR.link_collapse_tensor X m i j r s)

/-- The OCP congruence holds in the class monoid, so `collapse` descends to it. -/
theorem AR.cls_collapse_tensor :
    AR.cls ((X ⊗ Y).collapse m)
      = AR.cls ((X.collapse m ⊗ Y.collapse m).collapse m) :=
  Quotient.sound ⟨AR.fullIsoToWideIso (AR.collapseTensorFullIso X m)⟩

end Congruence

/-- OCP-cleanliness at melody tier `m`: the tier word has no adjacent
    repeats. -/
def AR.IsCleanAt [Finite X.obj.V] : Prop := IsClean (X.tierWord m)

/-- The collapse is OCP-clean at the collapsed tier. -/
theorem AR.isCleanAt_collapse [Finite X.obj.V] :
    (X.collapse m).IsCleanAt m := by
  unfold AR.IsCleanAt
  rw [AR.tierWord_collapse]
  simpa [AR.collapsedWord] using collapse_clean (X.tierWord m)

/-- The collapse preserves the NCC, since it repoints links monotonically. -/
theorem AR.noCrossing_collapse [Finite X.obj.V] (h : NoCrossing X.obj.edges X.obj.arcs) :
    NoCrossing (X.collapse m).obj.edges (X.collapse m).obj.arcs := by
  have hmono (i : ι) : Monotone (X.collapseIdx m i) := fun p q hpq => by
    rcases eq_or_ne i m with rfl | hi
    · rw [AR.collapseIdx_self, AR.collapseIdx_self]
      exact runIdx_monotone _ hpq
    · rwa [AR.collapseIdx_of_ne X m hi, AR.collapseIdx_of_ne X m hi]
  rw [AR.noCrossing_iff] at h ⊢
  intro i j ⟨r, s⟩ hl ⟨r', s'⟩ hl' hrr'
  obtain ⟨p, q, hpq, rfl, rfl⟩ := (AR.link_collapse X m i j r s).mp hl
  obtain ⟨p', q', hpq', rfl, rfl⟩ := (AR.link_collapse X m i j r' s').mp hl'
  exact hmono j (h i j (show (p, q) ∈ _ from hpq) (show (p', q') ∈ _ from hpq')
    ((hmono i).reflect_lt hrr'))

section RealizeMerged
variable {S : Type*}

/-- The OCP-merging realization at melody tier `m` — [jardine-2019]'s merging
    `g_T`: AR.realize, then merge the melody runs. -/
noncomputable def realizeMerged (g₀ : S → TieredAR ι τ)
    [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    TieredAR ι τ :=
  (AR.realize g₀ w).collapse m

instance (g₀ : S → TieredAR ι τ) [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    Finite (realizeMerged m g₀ w).obj.V :=
  inferInstanceAs (Finite ((AR.realize g₀ w).collapse m).obj.V)

end RealizeMerged

/-! ### The merged realization of word primitives

In the two-tier case, with the melody over `true`, the merged realization of a string of
presentations reads as one presentation whose melody is destuttered and whose lines are
repointed through the run index of the melody. -/

section MergedOfWords

universe u
variable {α β : Type u} [DecidableEq α] {S : Type*}

/-- A line of an OCP-merged realization is a line of the realization with its melody position
repointed through the run index of the melody. -/
def MergedLinks (melody : List α) (Lk : ℕ → ℕ → Prop) (r s : ℕ) : Prop :=
  ∃ p < melody.length, Lk p s ∧ runIdx melody p = r

instance (melody : List α) (Lk : ℕ → ℕ → Prop) [DecidableRel Lk] :
    DecidableRel (MergedLinks melody Lk) :=
  fun _ _ => by unfold MergedLinks; infer_instance

/-- Melody-to-timing lines of a two-tier collapse at the melody tier. -/
theorem AR.link_collapse_true_false (X : TieredAR Bool (TwoTier α β)) [Finite X.obj.V]
    (r s : ℕ) :
    (X.collapse true).link true false r s ↔
      ∃ p < X.tierLength true, X.link true false p s ∧ runIdx (X.tierWord true) p = r := by
  rw [AR.link_collapse]
  simp only [AR.collapseIdx_self, AR.collapseIdx_of_ne _ true (by decide : false ≠ true)]
  constructor
  · rintro ⟨p, q, hl, rfl, rfl⟩
    obtain ⟨hp, -, -⟩ := id hl
    exact ⟨p, hp, hl, rfl⟩
  · rintro ⟨p, hp, hl, rfl⟩
    exact ⟨p, s, hl, rfl, rfl⟩

variable (as : S → List α) (bs : S → List β) (L : S → ℕ → ℕ → Prop)

theorem AR.tierWord_realizeMerged_ofWords_true (w : List S) :
    (realizeMerged true (fun s => AR.ofWords (as s) (bs s) (L s)) w).tierWord true =
      OCP.collapse (w.map as).flatten := by
  simp [realizeMerged, AR.tierWord_realize_ofWords_true]

theorem AR.tierWord_realizeMerged_ofWords_false (w : List S) :
    (realizeMerged true (fun s => AR.ofWords (as s) (bs s) (L s)) w).tierWord false =
      (w.map bs).flatten := by
  simp [realizeMerged, AR.tierWord_realize_ofWords_false]

theorem AR.link_realizeMerged_ofWords (w : List S) (r s : ℕ) :
    (realizeMerged true (fun s => AR.ofWords (as s) (bs s) (L s)) w).link true false r s ↔
      MergedLinks (w.map as).flatten (BlockLinks as bs L w) r s := by
  show ((AR.realize _ w).collapse true).link true false r s ↔ _
  rw [AR.link_collapse_true_false]
  simp only [AR.link_realize_ofWords, AR.tierWord_realize_ofWords_true, MergedLinks,
    AR.tierLength_realize, AR.tierLength_ofWords_true, List.length_flatten, List.map_map,
    Function.comp_def]

/-- The tier words of the merged realization are those of its presentation. -/
theorem AR.tierWord_realizeMerged_eq_tierWord_ofWords (w : List S) (i : Bool) :
    (realizeMerged true (fun s => AR.ofWords (as s) (bs s) (L s)) w).tierWord i =
      (AR.ofWords (OCP.collapse (w.map as).flatten) (w.map bs).flatten
        (MergedLinks (w.map as).flatten (BlockLinks as bs L w))).tierWord i := by
  cases i
  · exact (AR.tierWord_realizeMerged_ofWords_false as bs L w).trans AR.tierWord_ofWords_false.symm
  · exact (AR.tierWord_realizeMerged_ofWords_true as bs L w).trans AR.tierWord_ofWords_true.symm

/-- The lines of the merged realization are those of its presentation. -/
theorem AR.link_realizeMerged_iff_link_ofWords (w : List S) (i j : Bool) (p q : ℕ) :
    (realizeMerged true (fun s => AR.ofWords (as s) (bs s) (L s)) w).link i j p q ↔
      (AR.ofWords (OCP.collapse (w.map as).flatten) (w.map bs).flatten
        (MergedLinks (w.map as).flatten (BlockLinks as bs L w))).link i j p q :=
  AR.link_iff_of_true_false (fun r s => by
    rw [AR.link_realizeMerged_ofWords, AR.link_ofWords]
    constructor
    · rintro ⟨p, hp, hl, rfl⟩
      exact ⟨runIdx_lt_collapse_length _ hp, (hl.lt as bs L).2, p, hp, hl, rfl⟩
    · exact fun h => h.2.2) i j p q

theorem AR.free_realizeMerged_ofWords_iff
    (B : List {F : TieredAR Bool (TwoTier α β) // Finite F.obj.V}) (w : List S) :
    (realizeMerged true (fun s => AR.ofWords (as s) (bs s) (L s)) w).Free B ↔
      (AR.ofWords (OCP.collapse (w.map as).flatten) (w.map bs).flatten
        (MergedLinks (w.map as).flatten (BlockLinks as bs L w))).Free B :=
  AR.free_congr (AR.tierWord_realizeMerged_eq_tierWord_ofWords as bs L w)
    (AR.link_realizeMerged_iff_link_ofWords as bs L w) B

end MergedOfWords

section Axiom6Bridge

omit [DecidableEq ι] [DecidableEq (τ m)]

/-- On a normal form, one position covers another in the arc order iff it is
    its immediate successor. -/
theorem AR.covering_normalize [Finite X.obj.V] {i : ι}
    {p q : Fin (X.tierLength i)} :
    ((X.normalize).obj.arcs.Adj ⟨i, p⟩ ⟨i, q⟩ ∧
        ∀ u, ¬ ((X.normalize).obj.arcs.Adj ⟨i, p⟩ u ∧
          (X.normalize).obj.arcs.Adj u ⟨i, q⟩)) ↔
      (q : ℕ) = p + 1 := by
  constructor
  · rintro ⟨hpq, hcov⟩
    rw [AR.arcs_normalize] at hpq
    by_contra hne
    have hmid : (p : ℕ) + 1 < q := by
      have := Fin.lt_def.mp hpq; omega
    have hq := q.isLt
    refine hcov ⟨i, ⟨(p : ℕ) + 1, by omega⟩⟩ ⟨?_, ?_⟩
    · exact (AR.arcs_normalize _ _ _).mpr
        (show (p : ℕ) < (p : ℕ) + 1 by omega)
    · exact (AR.arcs_normalize _ _ _).mpr
        (show (p : ℕ) + 1 < (q : ℕ) from hmid)
  · intro hsucc
    refine ⟨(AR.arcs_normalize _ _ _).mpr
      (show (p : ℕ) < (q : ℕ) by omega), ?_⟩
    rintro ⟨j, u⟩ ⟨h1, h2⟩
    rcases eq_or_ne i j with rfl | hij
    · rw [AR.arcs_normalize] at h1 h2
      have := Fin.lt_def.mp h1
      have := Fin.lt_def.mp h2
      omega
    · exact AR.arcs_normalize_ne hij p u h1

/-- Cleanliness fails at a successor pair exactly when its labels repeat. -/
private theorem AR.label_normalize_succ [Finite X.obj.V]
    {p : ℕ} (hp1 : p + 1 < X.tierLength m) (hp : p < X.tierLength m) :
    (X.normalize).obj.label ⟨m, ⟨p, hp⟩⟩ = (X.normalize).obj.label ⟨m, ⟨p + 1, hp1⟩⟩ ↔
      (X.tierWord m)[p]'(by simp; omega) = (X.tierWord m)[p + 1]'(by simp; omega) := by
  rw [AR.label_normalize, AR.label_normalize,
    ← AR.tierWord_getElem (p := ⟨p, hp⟩),
    ← AR.tierWord_getElem (p := ⟨p + 1, hp1⟩)]
  exact ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.mp h).2, fun h => congrArg (Sigma.mk m) h⟩

/-- Tier-word cleanliness is Axiom 6 of [jardine-2016b] on the normal form. -/
theorem AR.isCleanAt_iff_isOCPClean [Finite X.obj.V] :
    X.IsCleanAt m ↔
      IsOCPClean (X.normalize).obj.arcs (X.normalize).obj.label Sigma.fst m := by
  constructor
  · rintro h ⟨i, p⟩ ⟨j, q⟩ hpq hcov htier heq
    rcases eq_or_ne i j with rfl | hij
    · obtain rfl : m = i := by
        symm; simpa [AR.label_normalize] using htier
      have hsucc : (q : ℕ) = (p : ℕ) + 1 := (X.covering_normalize).mp ⟨hpq, hcov⟩
      have hq1 : (p : ℕ) + 1 < X.tierLength m := hsucc ▸ q.isLt
      rw [show q = ⟨(p : ℕ) + 1, hq1⟩ from Fin.ext hsucc] at heq
      have hp' : (p : ℕ) + 1 < (X.tierWord m).length := by
        simp only [AR.length_tierWord]
        omega
      exact List.isChain_iff_getElem.mp h p hp'
        ((X.label_normalize_succ m hq1 p.isLt).mp heq)
    · exact AR.arcs_normalize_ne hij p q hpq
  · intro h
    refine List.isChain_iff_getElem.mpr fun p hp heq => ?_
    have hlen : p + 1 < X.tierLength m := by
      simpa only [AR.length_tierWord] using hp
    have hplt : p < X.tierLength m := by omega
    have hcover := (X.covering_normalize
      (p := ⟨p, hplt⟩) (q := ⟨p + 1, hlen⟩) (i := m)).mpr rfl
    exact h hcover.1 hcover.2 (by simp [AR.label_normalize])
      ((X.label_normalize_succ m hlen hplt).mpr heq)

end Axiom6Bridge

end CoordinateCollapse

end Autosegmental
