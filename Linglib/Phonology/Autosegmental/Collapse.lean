/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.FreeMonoid.Destutter
import Linglib.Phonology.OCP
import Linglib.Phonology.Autosegmental.NormalForm

/-!
# OCP-merging collapse of autosegmental representations

A merging tone realization ([jardine-2019]; the melody-merging naming function of
[jardine-heinz-2015], Mende example) is **OCP-merging**: a tonal melody `Hⁿ` realizes as a
*single* H node multiply associated to the `n` morae, not `n` separate H nodes. The
project's `Autosegmental.realize` (`Realization.lean`) instead uses the bridge-only
`concat` (the categorical coproduct), which keeps the `n` H nodes apart. This file
supplies the missing merge as a post-processing retraction on the upper tier:

* `collapseGraph` / `collapseAR` — fuse each maximal run of identical adjacent
  *upper*-tier labels into one node, **carrying the association lines along**: a link
  `(k, j)` is repointed to `(ρ k, j)`, where `ρ` (`runIdx`) sends an upper position to
  the index of its run in the collapsed tier. The lower tier is untouched, so a merged
  node keeps *all* the morae its run was associated with (multiple association).
* `AR.realizeMerged := collapseAR ∘ AR.realize` — the OCP-merging realization.

The upper-tier collapse is exactly `OCP.collapse` (= `List.destutter (· ≠ ·)`); the
link pushforward is the `SimpleGraph.map`/`Quiver.Push` idiom
(`Finset.image (Prod.map ρ id)`); planarity survives because `ρ` is monotone
(`IsNonCrossing.image_monotone`, `NonCrossing.lean`).

## The AR-level OCP quotient monoid

`collapseAR` is the AR-level lift of `FreeMonoid.destutterHom`: a retraction onto the OCP-clean
ARs that descends to a quotient of the concat monoid `AR α β`. The key congruence is
`collapseAR_concat` — the AR shadow of `OCP.collapse_append`, whose links half reduces to
`runIdx` commuting with the collapse-collapse seam (`runIdx_append_collapse_left/right`,
in turn the boundary-length lemma `List.destutter_append_length_clean`). It bundles as
`collapseARHom : AR α β →* {A // IsCleanAR A}`, whose mathlib quotient
(`ocpARQuotientEquiv`) is the concrete OCP-clean model.

## Main results

* `collapseGraph_concat` / `collapseAR_concat` — the collapse congruence (in-bounds free
  at AR level), the AR lift of `OCP.collapse_append`.
* `collapseAR_id_on_clean` — `collapseAR` retracts onto its OCP-clean fixed points.
* `instMonoidCleanAR` / `collapseARHom` / `ocpARQuotientEquiv` — the AR-level OCP quotient
  monoid, its bundled hom, and the first-isomorphism equivalence.
* `upperHom` / `upperHomClean_comp_collapseARHom` — the upper-tier projection and the
  decategorification square: the AR-level OCP quotient maps onto the tier-level one.
* `autosegment_mul_self` / `ocpPresentation` — the tier-level OCP-clean monoid is presented
  by idempotent autosegments `⟨α | a · a = a⟩`; the OCP is a monoidal **quotient**, the
  counterpart to the No-Crossing Constraint's monoidal **subcategory** (`ncc_isMonoidal`).
* `collapse_not_reflective` — that quotient does *not* categorify: `collapse` is not a
  reflector (a morphism can split a geminate), so the OCP quotient lives on the object monoid,
  not the category — the precise sense in which OCP and NCC differ.
-/

namespace Autosegmental

open OCP

variable {α β : Type*} [DecidableEq α]

/-! ### The run-index map -/

/-- **Run index** of upper position `k` in `xs`: the index (0-based) of the
    OCP-run containing `k`, i.e. one less than the number of runs in the prefix
    `xs[0..k]`. Concretely `(OCP.collapse (xs.take (k+1))).length - 1`. -/
def runIdx (xs : List α) (k : ℕ) : ℕ := (collapse (xs.take (k + 1))).length - 1

/-- `runIdx` is monotone: later positions sit in later (or the same) runs. -/
theorem runIdx_monotone (xs : List α) : Monotone (runIdx xs) := by
  intro a b hab
  unfold runIdx
  have hsub : (collapse (xs.take (a + 1))).Sublist (xs.take (b + 1)) :=
    (collapse_sublist _).trans (List.take_sublist_take_left (by omega))
  have hlen := List.IsChain.length_le_length_destutter_ne hsub (collapse_clean _)
  simp only [collapse_eq_destutter] at hlen ⊢
  omega

/-- `runIdx` lands inside the collapsed tier: an in-bounds position maps to an
    in-bounds run index. The upper half of `collapseAR`'s in-bounds proof. -/
theorem runIdx_lt_collapse_length (xs : List α) {k : ℕ} (hk : k < xs.length) :
    runIdx xs k < (collapse xs).length := by
  unfold runIdx
  have hne : xs.take (k + 1) ≠ [] := by
    intro h
    have hlen : (xs.take (k + 1)).length = k + 1 := List.length_take_of_le (by omega)
    rw [h] at hlen; simp at hlen
  have hsub : (collapse (xs.take (k + 1))).Sublist xs :=
    (collapse_sublist _).trans (List.take_sublist _ _)
  have hlen := List.IsChain.length_le_length_destutter_ne hsub (collapse_clean _)
  simp only [collapse_eq_destutter] at hlen ⊢
  have hpos : 0 < ((xs.take (k + 1)).destutter (· ≠ ·)).length := by
    rw [List.length_pos_iff]
    intro h
    rw [← collapse_eq_destutter, collapse_eq_nil] at h
    exact hne h
  omega

/-- On a constant tier every position lies in the single run: `runIdx` is `0`. -/
@[simp] theorem runIdx_replicate (n : ℕ) (a : α) (k : ℕ) :
    runIdx (List.replicate n a) k = 0 := by
  unfold runIdx
  rw [List.take_replicate]
  cases hm : min (k + 1) n with
  | zero => simp
  | succ m => rw [collapse_replicate, List.length_singleton]

/-! ### Run-index and concatenation

The defining property of `concat` for the OCP quotient: `runIdx` commutes with the
collapse-collapse seam (`runIdx_append_collapse_left/right`). On the A-block the prefix
run-index is untouched (`runIdx_append_left`, plus `runIdx_clean` re-reading a clean tier
as the identity); on the B-block the seam merges exactly when `collapse xs` ends in the
element heading `ys` (`runIdx_append_right`, the AR shadow of
`List.destutter_append_length_clean`). -/

/-- The prefix run-index is unaffected by a right append. -/
theorem runIdx_append_left {xs ys : List α} {k : ℕ} (h : k < xs.length) :
    runIdx (xs ++ ys) k = runIdx xs k := by
  unfold runIdx; rw [List.take_append_of_le_length (by omega)]

/-- On a clean tier `runIdx` is the identity (no runs to merge). -/
theorem runIdx_clean {xs : List α} (hc : IsClean xs) {k : ℕ} (h : k < xs.length) :
    runIdx xs k = k := by
  unfold runIdx
  rw [collapse_idempotent_on_clean (hc.take (k + 1)), List.length_take_of_le (by omega)]
  omega

/-- The length of the collapse of a nonempty prefix is its top run-index plus one. -/
theorem collapse_take_succ_length {xs : List α} {m : ℕ} (hm : m < xs.length) :
    (collapse (xs.take (m + 1))).length = runIdx xs m + 1 := by
  unfold runIdx
  have hpos : 0 < (collapse (xs.take (m + 1))).length := by
    rw [List.length_pos_iff]
    refine fun h => ?_
    have hne : xs.take (m + 1) ≠ [] := by
      intro h'
      have : (xs.take (m + 1)).length = m + 1 := List.length_take_of_le (by omega)
      rw [h'] at this; simp at this
    exact hne (collapse_eq_nil.mp h)
  omega

/-- The collapse of a prefix has the same head as the whole tier. -/
theorem collapse_take_head? {xs : List α} {m : ℕ} :
    (collapse (xs.take (m + 1))).head? = xs.head? := by
  rw [collapse, List.destutter_head?]
  cases xs <;> simp

/-- **The B-part seam identity.** Reading a suffix position through the collapse of an
append: the run-index is the left collapse's length plus the suffix's own run-index, minus
one exactly when the seam merges (`List.destutter_append_length_clean`). -/
theorem runIdx_append_right {xs ys : List α} {a : ℕ} (ha : a < ys.length) :
    runIdx (xs ++ ys) (xs.length + a) =
      (collapse xs).length + runIdx ys a -
        (if (collapse xs).getLast? = ys.head? then 1 else 0) := by
  unfold runIdx
  rw [show xs.length + a + 1 = xs.length + (a + 1) by omega, List.take_length_add_append,
    collapse_append, collapse_eq_destutter,
    List.destutter_append_length_clean (collapse_clean _) (collapse_clean _),
    collapse_take_succ_length ha, collapse_take_head?]
  split_ifs with h
  · have : 0 < (collapse ys).length := Nat.zero_lt_of_lt (runIdx_lt_collapse_length ys ha)
    omega
  · omega

/-- A-block: a prefix index commutes with the collapse-collapse seam. -/
theorem runIdx_append_collapse_left {xs ys : List α} {k : ℕ} (h : k < xs.length) :
    runIdx (xs ++ ys) k = runIdx (collapse xs ++ collapse ys) (runIdx xs k) := by
  rw [runIdx_append_left h, runIdx_append_left (runIdx_lt_collapse_length xs h),
    runIdx_clean (collapse_clean _) (runIdx_lt_collapse_length xs h)]

/-- B-block: a suffix index commutes with the collapse-collapse seam. -/
theorem runIdx_append_collapse_right {xs ys : List α} {a : ℕ} (ha : a < ys.length) :
    runIdx (xs ++ ys) (xs.length + a) =
      runIdx (collapse xs ++ collapse ys) ((collapse xs).length + runIdx ys a) := by
  rw [runIdx_append_right ha, runIdx_append_right (runIdx_lt_collapse_length ys ha),
    collapse_idempotent, runIdx_clean (collapse_clean _) (runIdx_lt_collapse_length ys ha),
    collapse_eq_destutter ys, List.destutter_head?]

/-! ### The collapse in coordinates

The OCP merge on the graph foundation: destutter melody tier `m`'s word and
repoint its links through `runIdx`. Like `normalize` the result is a
`Representation` on a sigma-`Fin` carrier, but the merge is not a pullback —
`runIdx` is monotone, not bijective — so the structural axioms are proved
directly on the merged carrier. -/

section CoordinateCollapse
open CategoryTheory
open scoped MonoidalCategory

variable {ι : Type*} [DecidableEq ι] {τ : ι → Type*}
variable (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι))
variable (m : ι) [DecidableEq (τ m)]

/-- Tier words after collapsing melody tier `m`: destuttered at `m`, untouched
    elsewhere. -/
noncomputable def Representation.collapsedWord [Finite X.obj.V] : ∀ i, List (τ i) :=
  Function.update (fun i => X.tierWord i) m (OCP.collapse (X.tierWord m))

theorem Representation.collapsedWord_length_le [Finite X.obj.V] (i : ι) :
    (X.collapsedWord m i).length ≤ X.tierLength i := by
  rcases eq_or_ne i m with rfl | h
  · simpa [Representation.collapsedWord] using OCP.collapse_length_le (X.tierWord i)
  · simp [Representation.collapsedWord, Function.update_of_ne h]

/-- Position repointing: `runIdx` on the melody tier, identity elsewhere. -/
noncomputable def Representation.collapseIdx [Finite X.obj.V] (i : ι) (p : ℕ) : ℕ :=
  if i = m then runIdx (X.tierWord m) p else p

/-- **The OCP-merging collapse**: melody tier `m` destuttered, links repointed
    through `runIdx`, other tiers untouched. -/
noncomputable def Representation.collapse [Finite X.obj.V] :
    Representation (Sigma.fst : ((i : ι) × τ i) → ι) where
  obj :=
    { V := (i : ι) × Fin (X.collapsedWord m i).length
      graph :=
        { edges :=
            { Adj := fun v w => v ≠ w ∧ ∃ p q, X.link v.1 w.1 p q ∧
                X.collapseIdx m v.1 p = v.2 ∧ X.collapseIdx m w.1 q = w.2
              symm := ⟨fun v w h => ⟨h.1.symm, by
                obtain ⟨p, q, hl, hp, hq⟩ := h.2
                exact ⟨q, p, X.link_symm hl, hq, hp⟩⟩⟩
              loopless := ⟨fun v h => h.1 rfl⟩ }
          arcs := ⟨fun v w => v.1 = w.1 ∧ (v.2 : ℕ) < (w.2 : ℕ)⟩ }
      label := fun v => ⟨v.1, (X.collapsedWord m v.1)[v.2]⟩ }
  property := by
    refine ⟨⟨fun v w h => h.1, fun v w hne htier => ?_, fun v h => lt_irrefl _ h.2,
      fun u v w huv hvw => ⟨huv.1.trans hvw.1, huv.2.trans hvw.2⟩⟩, fun v w hadj harc => ?_⟩
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
noncomputable def Representation.collapseFiberEnum [Finite X.obj.V] (i : ι) :
    Fin ((X.collapsedWord m i).length) ≃o (X.collapse m).fiber i := by
  refine StrictMono.orderIsoOfSurjective (fun p => ⟨⟨i, p⟩, rfl⟩) (fun p q h => ⟨rfl, h⟩)
    fun v => ?_
  obtain ⟨⟨j, q⟩, hp⟩ := v
  obtain rfl : j = i := hp
  exact ⟨q, rfl⟩

/-- **The collapse does what it says**: its tier words are the collapsed
    words — destuttered at `m` (`Function.update_self`), untouched elsewhere. -/
@[simp] theorem Representation.tierWord_collapse [Finite X.obj.V] (i : ι) :
    (X.collapse m).tierWord i = X.collapsedWord m i := by
  rw [Representation.tierWord_eq_ofFn (X.collapseFiberEnum m i)]
  exact List.ofFn_getElem

/-- The word half of the OCP congruence: collapsing a tensor computes the same
    tier words as collapsing the tensor of the collapsed factors —
    `OCP.collapse_append` lifted through the readers. -/
theorem Representation.collapsedWord_tensor
    {Y : Representation (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite X.obj.V] [Finite Y.obj.V] (i : ι) :
    (X ⊗ Y).collapsedWord m i = (X.collapse m ⊗ Y.collapse m).collapsedWord m i := by
  rcases eq_or_ne i m with rfl | h
  · simp only [Representation.collapsedWord, Function.update_self,
      Representation.tierWord_tensor, Representation.tierWord_collapse]
    exact OCP.collapse_append _ _
  · simp [Representation.collapsedWord, Function.update_of_ne h]

theorem Representation.fiberEnum_collapse [Finite X.obj.V] (i : ι) :
    (X.collapse m).fiberEnum i =
      (Fin.castOrderIso (by rw [← Representation.length_tierWord,
        Representation.tierWord_collapse])).trans (X.collapseFiberEnum m i) :=
  Subsingleton.elim _ _

theorem Representation.vertexEquiv_collapse [Finite X.obj.V] {i : ι}
    (r : Fin ((X.collapse m).tierLength i)) :
    (X.collapse m).vertexEquiv ⟨i, r⟩
      = ⟨i, Fin.cast (by rw [← Representation.length_tierWord,
          Representation.tierWord_collapse]) r⟩ := by
  show ((X.collapse m).fiberEnum i r).val = _
  rw [Representation.fiberEnum_collapse]
  rfl

/-- The collapse's links are the image of the original links under the
    repointing — `edges_normalize`'s analogue for the merge. -/
theorem Representation.link_collapse [Finite X.obj.V] (i j : ι) (r s : ℕ) :
    (X.collapse m).link i j r s ↔
      ∃ p q, X.link i j p q ∧ X.collapseIdx m i p = r ∧ X.collapseIdx m j q = s := by
  constructor
  · rintro ⟨hr, hs, hl⟩
    rw [Representation.linkRel_def, Representation.vertexEquiv_collapse,
      Representation.vertexEquiv_collapse] at hl
    obtain ⟨-, p, q, hpq, hp, hq⟩ := hl
    exact ⟨p, q, hpq, hp, hq⟩
  · rintro ⟨p, q, hpq, hp, hq⟩
    have hbr : r < (X.collapse m).tierLength i := by
      rw [← Representation.length_tierWord, Representation.tierWord_collapse]
      subst hp
      unfold Representation.collapseIdx
      split_ifs with h
      · subst h
        simpa [Representation.collapsedWord] using
          runIdx_lt_collapse_length _ (by simpa using hpq.1)
      · simpa [Representation.collapsedWord, Function.update_of_ne h] using hpq.1
    have hbs : s < (X.collapse m).tierLength j := by
      rw [← Representation.length_tierWord, Representation.tierWord_collapse]
      subst hq
      unfold Representation.collapseIdx
      split_ifs with h
      · subst h
        simpa [Representation.collapsedWord] using
          runIdx_lt_collapse_length _ (by simpa using hpq.2.1)
      · simpa [Representation.collapsedWord, Function.update_of_ne h] using hpq.2.1
    refine ⟨hbr, hbs, ?_⟩
    rw [Representation.linkRel_def, Representation.vertexEquiv_collapse,
      Representation.vertexEquiv_collapse]
    refine ⟨?_, p, q, hpq, hp, hq⟩
    intro heq
    obtain ⟨hij, -⟩ := Sigma.mk.inj_iff.mp heq
    subst hij
    exact X.not_link_self_tier i p q hpq

theorem Representation.tierLength_collapse [Finite X.obj.V] (i : ι) :
    (X.collapse m).tierLength i = (X.collapsedWord m i).length := by
  rw [← Representation.length_tierWord, Representation.tierWord_collapse]

section Congruence
variable {Y : Representation (Sigma.fst : ((i : ι) × τ i) → ι)}
variable [Finite X.obj.V] [Finite Y.obj.V]

/-- Left-block positions commute with the collapse-collapse seam. -/
theorem Representation.collapseIdx_left (i : ι) {p : ℕ} (hp : p < X.tierLength i) :
    (X.collapse m ⊗ Y.collapse m).collapseIdx m i (X.collapseIdx m i p)
      = (X ⊗ Y).collapseIdx m i p := by
  unfold Representation.collapseIdx
  split_ifs with h
  · subst h
    simp only [Representation.tierWord_tensor, Representation.tierWord_collapse,
      Representation.collapsedWord, Function.update_self]
    exact (runIdx_append_collapse_left (xs := X.tierWord i) (ys := Y.tierWord i)
      (by simpa using hp)).symm
  · rfl

/-- Right-block positions commute with the collapse-collapse seam. -/
theorem Representation.collapseIdx_right (i : ι) {p : ℕ} (hp : p < Y.tierLength i) :
    (X.collapse m ⊗ Y.collapse m).collapseIdx m i
        ((X.collapse m).tierLength i + Y.collapseIdx m i p)
      = (X ⊗ Y).collapseIdx m i (X.tierLength i + p) := by
  unfold Representation.collapseIdx
  split_ifs with h
  · subst h
    simp only [Representation.tierWord_tensor, Representation.tierWord_collapse,
      Representation.collapsedWord, Function.update_self,
      ← Representation.length_tierWord]
    exact (runIdx_append_collapse_right (xs := X.tierWord i) (ys := Y.tierWord i)
      (by simpa using hp)).symm
  · simp [Representation.tierLength_collapse, Representation.collapsedWord,
      Function.update_of_ne h]

/-- The link half of the OCP congruence, in ℕ coordinates. -/
theorem Representation.link_collapse_tensor (i j : ι) (r s : ℕ) :
    ((X ⊗ Y).collapse m).link i j r s ↔
      ((X.collapse m ⊗ Y.collapse m).collapse m).link i j r s := by
  rw [Representation.link_collapse, Representation.link_collapse]
  constructor
  · rintro ⟨p, q, hpq, hr, hs⟩
    rcases (Representation.link_tensor i j p q).mp hpq with hX | ⟨hpi, hqj, hY⟩
    · refine ⟨X.collapseIdx m i p, X.collapseIdx m j q,
        (Representation.link_tensor i j _ _).mpr
          (Or.inl ((X.link_collapse m i j _ _).mpr ⟨p, q, hX, rfl, rfl⟩)), ?_, ?_⟩
      · rw [X.collapseIdx_left m i hX.1, hr]
      · rw [X.collapseIdx_left m j hX.2.1, hs]
    · refine ⟨(X.collapse m).tierLength i + Y.collapseIdx m i (p - X.tierLength i),
        (X.collapse m).tierLength j + Y.collapseIdx m j (q - X.tierLength j),
        (Representation.link_tensor i j _ _).mpr (Or.inr ⟨by omega, by omega, ?_⟩), ?_, ?_⟩
      · rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
        exact (Y.link_collapse m i j _ _).mpr ⟨_, _, hY, rfl, rfl⟩
      · rw [X.collapseIdx_right m i hY.1, Nat.add_sub_cancel' hpi, hr]
      · rw [X.collapseIdx_right m j hY.2.1, Nat.add_sub_cancel' hqj, hs]
  · rintro ⟨p', q', hpq', hr, hs⟩
    rcases (Representation.link_tensor i j p' q').mp hpq' with hX | ⟨hpi', hqj', hY'⟩
    · obtain ⟨p, q, hX₀, hcp, hcq⟩ := (X.link_collapse m i j p' q').mp hX
      refine ⟨p, q, (Representation.link_tensor i j p q).mpr (Or.inl hX₀), ?_, ?_⟩
      · rw [← X.collapseIdx_left m i hX₀.1, hcp, hr]
      · rw [← X.collapseIdx_left m j hX₀.2.1, hcq, hs]
    · obtain ⟨a, b, hY₀, hca, hcb⟩ :=
        (Y.link_collapse m i j (p' - (X.collapse m).tierLength i)
          (q' - (X.collapse m).tierLength j)).mp hY'
      refine ⟨X.tierLength i + a, X.tierLength j + b,
        (Representation.link_tensor i j _ _).mpr (Or.inr ⟨by omega, by omega, ?_⟩), ?_, ?_⟩
      · rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
        exact hY₀
      · rw [← X.collapseIdx_right m i hY₀.1, hca, Nat.add_sub_cancel' hpi', hr]
      · rw [← X.collapseIdx_right m j hY₀.2.1, hcb, Nat.add_sub_cancel' hqj', hs]

/-- **The OCP congruence**: collapsing a concatenation is isomorphic to
    collapsing the concatenation of the collapses — [jardine-heinz-2015]'s
    melody-merge law, by the classification theorem. -/
noncomputable def Representation.collapseTensorFullIso :
    MixedGraphCat.Iso ((X ⊗ Y).collapse m).obj
      ((X.collapse m ⊗ Y.collapse m).collapse m).obj :=
  Representation.fullIsoOfReaderEq
    (fun i => by
      rw [Representation.tierWord_collapse, Representation.tierWord_collapse,
        Representation.collapsedWord_tensor])
    (fun i j r s => Representation.link_collapse_tensor X m i j r s)

/-- The OCP congruence as an equality of isomorphism classes: `collapse`
    descends to the class monoid. -/
theorem Representation.cls_collapse_tensor :
    Representation.cls ((X ⊗ Y).collapse m)
      = Representation.cls ((X.collapse m ⊗ Y.collapse m).collapse m) :=
  Quotient.sound ⟨Representation.fullIsoToWideIso (Representation.collapseTensorFullIso X m)⟩

end Congruence

/-- OCP-cleanliness at melody tier `m`: the tier word has no adjacent
    repeats. -/
def Representation.IsCleanAt [Finite X.obj.V] : Prop := IsClean (X.tierWord m)

/-- The collapse is OCP-clean at the collapsed tier. -/
theorem Representation.isCleanAt_collapse [Finite X.obj.V] :
    (X.collapse m).IsCleanAt m := by
  unfold Representation.IsCleanAt
  rw [Representation.tierWord_collapse]
  simpa [Representation.collapsedWord] using collapse_clean (X.tierWord m)

section RealizeMerged
variable {S : Type*}

/-- The OCP-merging realization at melody tier `m` — [jardine-2019]'s merging
    `g_T`: realize, then merge the melody runs. -/
noncomputable def realizeMerged (g₀ : S → Representation (Sigma.fst : ((i : ι) × τ i) → ι))
    [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    Representation (Sigma.fst : ((i : ι) × τ i) → ι) :=
  (realize g₀ w).collapse m

end RealizeMerged

section Axiom6Bridge

omit [DecidableEq ι] [DecidableEq (τ m)]

/-- On a normal form, one position covers another in the arc order iff it is
    its immediate successor. -/
theorem Representation.covering_normalize [Finite X.obj.V] {i : ι}
    {p q : Fin (X.tierLength i)} :
    ((X.normalize).obj.graph.arcs.Adj ⟨i, p⟩ ⟨i, q⟩ ∧
        ∀ u, ¬ ((X.normalize).obj.graph.arcs.Adj ⟨i, p⟩ u ∧
          (X.normalize).obj.graph.arcs.Adj u ⟨i, q⟩)) ↔
      (q : ℕ) = p + 1 := by
  constructor
  · rintro ⟨hpq, hcov⟩
    rw [Representation.arcs_normalize] at hpq
    by_contra hne
    have hmid : (p : ℕ) + 1 < q := by
      have := Fin.lt_def.mp hpq; omega
    have hq := q.isLt
    refine hcov ⟨i, ⟨(p : ℕ) + 1, by omega⟩⟩ ⟨?_, ?_⟩
    · exact (Representation.arcs_normalize _ _ _).mpr
        (show (p : ℕ) < (p : ℕ) + 1 by omega)
    · exact (Representation.arcs_normalize _ _ _).mpr
        (show (p : ℕ) + 1 < (q : ℕ) from hmid)
  · intro hsucc
    refine ⟨(Representation.arcs_normalize _ _ _).mpr
      (show (p : ℕ) < (q : ℕ) by omega), ?_⟩
    rintro ⟨j, u⟩ ⟨h1, h2⟩
    rcases eq_or_ne i j with rfl | hij
    · rw [Representation.arcs_normalize] at h1 h2
      have := Fin.lt_def.mp h1
      have := Fin.lt_def.mp h2
      omega
    · exact Representation.arcs_normalize_ne hij p u h1

/-- Cleanliness fails at a successor pair exactly when its labels repeat. -/
private theorem Representation.label_normalize_succ [Finite X.obj.V]
    {p : ℕ} (hp1 : p + 1 < X.tierLength m) (hp : p < X.tierLength m) :
    (X.normalize).obj.label ⟨m, ⟨p, hp⟩⟩ = (X.normalize).obj.label ⟨m, ⟨p + 1, hp1⟩⟩ ↔
      (X.tierWord m)[p]'(by simp; omega) = (X.tierWord m)[p + 1]'(by simp; omega) := by
  rw [Representation.label_normalize, Representation.label_normalize,
    ← Representation.tierWord_getElem (p := ⟨p, hp⟩),
    ← Representation.tierWord_getElem (p := ⟨p + 1, hp1⟩)]
  exact ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.mp h).2, fun h => congrArg (Sigma.mk m) h⟩

/-- **The OCP bridge**: tier-word cleanliness is Axiom 6 on the normal form —
    the coordinate OCP and [jardine-2016-diss]'s §4.2 axiom agree. -/
theorem Representation.isCleanAt_iff_isOCPClean [Finite X.obj.V] :
    X.IsCleanAt m ↔
      IsOCPClean (X.normalize).obj.graph (X.normalize).obj.label Sigma.fst m := by
  constructor
  · rintro h ⟨i, p⟩ ⟨j, q⟩ hpq hcov htier heq
    rcases eq_or_ne i j with rfl | hij
    · obtain rfl : m = i := by
        symm; simpa [Representation.label_normalize] using htier
      have hsucc : (q : ℕ) = (p : ℕ) + 1 := (X.covering_normalize).mp ⟨hpq, hcov⟩
      have hq1 : (p : ℕ) + 1 < X.tierLength m := hsucc ▸ q.isLt
      rw [show q = ⟨(p : ℕ) + 1, hq1⟩ from Fin.ext hsucc] at heq
      have hp' : (p : ℕ) + 1 < (X.tierWord m).length := by
        simp only [Representation.length_tierWord]
        omega
      exact List.isChain_iff_getElem.mp h p hp'
        ((X.label_normalize_succ m hq1 p.isLt).mp heq)
    · exact Representation.arcs_normalize_ne hij p q hpq
  · intro h
    refine List.isChain_iff_getElem.mpr fun p hp heq => ?_
    have hlen : p + 1 < X.tierLength m := by
      simpa only [Representation.length_tierWord] using hp
    have hplt : p < X.tierLength m := by omega
    have hcover := (X.covering_normalize
      (p := ⟨p, hplt⟩) (q := ⟨p + 1, hlen⟩) (i := m)).mpr rfl
    exact h hcover.1 hcover.2 (by simp [Representation.label_normalize])
      ((X.label_normalize_succ m hlen hplt).mpr heq)

end Axiom6Bridge

end CoordinateCollapse

end Autosegmental
