/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.OCP
import Linglib.Phonology.Autosegmental.Realization

/-!
# OCP-merging collapse of autosegmental representations

[jardine-2019]'s tone realization `g_T` is **OCP-merging**: `g_T(Hⁿ)` is a *single*
H node multiply associated to the `n` morae, not `n` separate H nodes. The
project's `Autosegmental.realize` (`Realization.lean`) instead uses the bridge-only
`concat` (the categorical coproduct), which keeps the `n` H nodes apart. This file
supplies the missing merge as a post-processing retraction on the upper tier:

* `collapseGraph` / `collapseAR` — fuse each maximal run of identical adjacent
  *upper*-tier labels into one node, **carrying the association lines along**: a link
  `(k, j)` is repointed to `(ρ k, j)`, where `ρ` (`runIdx`) sends an upper position to
  the index of its run in the collapsed tier. The lower tier is untouched, so a merged
  node keeps *all* the morae its run was associated with (multiple association).
* `realizeMerged := collapseAR ∘ realize` — the OCP-merging realization `g_T`.

The upper-tier collapse is exactly `OCP.collapse` (= `List.destutter (· ≠ ·)`); the
link pushforward is the `SimpleGraph.map`/`Quiver.Push` idiom
(`Finset.image (Prod.map ρ id)`); planarity survives because `ρ` is monotone
(`IsNonCrossing.image_monotone`, `NonCrossing.lean`).

## The AR-level OCP quotient monoid

`collapseAR` is the AR-level lift of `OCP.collapseHom`: a retraction onto the OCP-clean
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

/-! ### Collapse on graphs -/

/-- **OCP-merging collapse** on graphs: fuse each maximal run of identical adjacent
    *upper* labels into one node (`OCP.collapse`), repointing every association line
    `(k, j)` to `(runIdx k, j)` (the `SimpleGraph.map`/push idiom). The lower tier is
    unchanged, so a merged node inherits *all* the lines of its run. -/
def collapseGraph (A : Graph α β) : Graph α β where
  upper := LabeledTuple.ofList (collapse A.upper.toList)
  lower := A.lower
  links := A.links.image (Prod.map (runIdx A.upper.toList) id)

@[simp] theorem collapseGraph_upper (A : Graph α β) :
    (collapseGraph A).upper = LabeledTuple.ofList (collapse A.upper.toList) := rfl

@[simp] theorem collapseGraph_lower (A : Graph α β) :
    (collapseGraph A).lower = A.lower := rfl

@[simp] theorem collapseGraph_links (A : Graph α β) :
    (collapseGraph A).links = A.links.image (Prod.map (runIdx A.upper.toList) id) := rfl

/-- `collapseGraph` preserves in-bounds: upper indices land in the collapsed tier
    (`runIdx_lt_collapse_length`), lower indices are unchanged. -/
theorem inBounds_collapseGraph {A : Graph α β} (hA : A.InBounds) :
    (collapseGraph A).InBounds := by
  intro p hp
  simp only [collapseGraph_links, Finset.mem_image, Prod.exists, Prod.map_apply,
    id_eq] at hp
  obtain ⟨k, j, hkj, rfl⟩ := hp
  obtain ⟨hku, hjl⟩ := hA (k, j) hkj
  refine ⟨?_, hjl⟩
  simpa [collapseGraph_upper, LabeledTuple.ofList_len] using
    runIdx_lt_collapse_length A.upper.toList (by simpa using hku)

/-- `collapseGraph` preserves planarity: the run-collapse `runIdx` is monotone, so
    pushing the links forward stays non-crossing (`IsNonCrossing.image_monotone`). -/
theorem isPlanar_collapseGraph {A : Graph α β} (hA : A.IsPlanar) :
    (collapseGraph A).IsPlanar :=
  IsNonCrossing.image_monotone (runIdx_monotone _) hA

/-! ### The collapse congruence

`collapseGraph` is a congruence for `concat`: collapsing the operands first is harmless.
This is the AR-level lift of `OCP.collapse_append`, and the algebraic content powering the
OCP quotient monoid (`collapseARHom`). The upper tier follows from `collapse_append`; the
links follow because `runIdx` commutes with the collapse-collapse seam
(`runIdx_append_collapse_left/right`), on link sets kept in-bounds by hypothesis. -/

open Graph in
/-- **The collapse congruence** on graphs (in-bounds operands). -/
theorem collapseGraph_concat {A B : Graph α β}
    (hA : A.InBounds) (hB : B.InBounds) :
    collapseGraph (A.concat B) =
      collapseGraph ((collapseGraph A).concat (collapseGraph B)) := by
  apply Graph.ext
  · simp only [collapseGraph_upper, upper_concat, LabeledTuple.toList_concat,
      LabeledTuple.toList_ofList]
    rw [collapse_append]
  · rfl
  · simp only [collapseGraph_links, links_concat, collapseGraph_upper, collapseGraph_lower,
      LabeledTuple.ofList_len, LabeledTuple.toList_concat, LabeledTuple.toList_ofList,
      Finset.image_union, Finset.image_image, upper_concat]
    congr 1
    · refine Finset.image_congr fun p hp => ?_
      obtain ⟨k, j⟩ := p
      have hk : k < A.upper.toList.length := by
        simpa [LabeledTuple.toList_length] using (hA (k, j) hp).1
      simp only [Function.comp_apply, Prod.map_apply, id_eq, Prod.mk.injEq, and_true]
      exact runIdx_append_collapse_left hk
    · refine Finset.image_congr fun p hp => ?_
      obtain ⟨a, b⟩ := p
      have ha : a < B.upper.toList.length := by
        simpa [LabeledTuple.toList_length] using (hB (a, b) hp).1
      simp only [Function.comp_apply, Prod.map_apply, id_eq, shiftLink_apply, Prod.mk.injEq,
        and_true]
      rw [Nat.add_comm a A.upper.len, ← LabeledTuple.toList_length A.upper,
        Nat.add_comm (runIdx B.upper.toList a)]
      exact runIdx_append_collapse_right ha

/-! ### Collapse on ARs -/

/-- **OCP-merging collapse** on ARs: `collapseGraph` repackaged with its in-bounds
    proof. The AR-level lift of `OCP.collapseHom` — the run-collapse carrying the
    association lines the flat tier-string discards. -/
def collapseAR (A : AR α β) : AR α β where
  toGraph := collapseGraph A.toGraph
  inBounds := inBounds_collapseGraph A.inBounds

@[simp] theorem collapseAR_toGraph (A : AR α β) :
    (collapseAR A).toGraph = collapseGraph A.toGraph := rfl

/-- `collapseAR` preserves planarity ([goldsmith-1976]'s NCC survives OCP merging):
    the consumer-facing form of `isPlanar_collapseGraph`. -/
theorem collapseAR_isPlanar {A : AR α β} (hA : A.toGraph.IsPlanar) :
    (collapseAR A).toGraph.IsPlanar :=
  isPlanar_collapseGraph hA

/-- **The collapse congruence** on ARs (`collapseGraph_concat` repackaged; `inBounds` is
    free): `collapseAR` descends to a homomorphism of the concat monoid. -/
theorem collapseAR_concat (A B : AR α β) :
    collapseAR (A.concat B) =
      collapseAR ((collapseAR A).concat (collapseAR B)) :=
  AR.ext_toGraph (collapseGraph_concat A.inBounds B.inBounds)

/-! ### The AR-level OCP quotient monoid

The base object `AR α β` carries the concatenation monoid (`AR.instMonoid`); `collapseAR`
is the OCP retraction onto its OCP-clean fixed points. `collapseAR_concat` is the
homomorphism law, so `collapseAR` bundles as `collapseARHom : AR α β →* {A // IsCleanAR A}`
— the AR-level lift of `OCP.collapseHom`, carrying the association lines the flat
tier-string discards. As a mathlib quotient, `{A // IsCleanAR A}` is
`AR α β ⧸ Con.ker collapseARHom` (`ocpARQuotientEquiv`). -/

/-- An AR is **OCP-clean** when its upper tier is (no adjacent identical autosegments). -/
def IsCleanAR (A : AR α β) : Prop := IsClean A.upper.toList

instance decidableIsCleanAR : DecidablePred (IsCleanAR (α := α) (β := β)) :=
  fun A => inferInstanceAs (Decidable (IsClean A.upper.toList))

@[simp] theorem isCleanAR_collapseAR (A : AR α β) : IsCleanAR (collapseAR A) := by
  simpa [IsCleanAR, collapseAR, collapseGraph_upper, LabeledTuple.toList_ofList] using
    collapse_clean A.upper.toList

/-- `collapseAR` fixes OCP-clean ARs: a clean upper tier is its own collapse and `runIdx`
    is then the identity, so the links are unchanged. -/
theorem collapseAR_id_on_clean {A : AR α β} (hA : IsCleanAR A) : collapseAR A = A := by
  apply AR.ext_toGraph
  apply Graph.ext
  · simp only [collapseAR_toGraph, collapseGraph_upper]
    rw [collapse_idempotent_on_clean hA, LabeledTuple.ofList_toList]
  · rfl
  · simp only [collapseAR_toGraph, collapseGraph_links]
    refine (Finset.image_congr fun p hp => ?_).trans (Finset.image_id)
    obtain ⟨k, j⟩ := p
    have hk : k < A.upper.toList.length := by
      simpa [LabeledTuple.toList_length] using (A.inBounds (k, j) hp).1
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq, and_true]
    exact runIdx_clean hA hk

omit [DecidableEq α] in
@[simp] theorem isCleanAR_one : IsCleanAR (1 : AR α β) := by
  simp [IsCleanAR, AR.one_eq_empty, AR.empty, Graph.empty, LabeledTuple.toList,
    LabeledTuple.empty]

@[simp] theorem collapseAR_one : collapseAR (1 : AR α β) = 1 :=
  collapseAR_id_on_clean isCleanAR_one

@[simp] theorem collapseAR_idempotent (A : AR α β) :
    collapseAR (collapseAR A) = collapseAR A :=
  collapseAR_id_on_clean (isCleanAR_collapseAR A)

/-- Collapsing the left operand before concatenating is absorbed by the outer collapse. -/
theorem collapseAR_concat_left (A B : AR α β) :
    collapseAR ((collapseAR A).concat B) = collapseAR (A.concat B) := by
  rw [collapseAR_concat (collapseAR A) B, collapseAR_idempotent, ← collapseAR_concat]

/-- Collapsing the right operand before concatenating is absorbed by the outer collapse. -/
theorem collapseAR_concat_right (A B : AR α β) :
    collapseAR (A.concat (collapseAR B)) = collapseAR (A.concat B) := by
  rw [collapseAR_concat A (collapseAR B), collapseAR_idempotent, ← collapseAR_concat]

/-! ### The bundled AR quotient monoid -/

/-- **OCP-gluing concatenation** on ARs: concatenate, then merge the new boundary run. The
    multiplication of the AR-level OCP quotient monoid. -/
def gconcatAR (A B : AR α β) : AR α β := collapseAR (A.concat B)

instance : Mul {A : AR α β // IsCleanAR A} :=
  ⟨fun A B => ⟨gconcatAR A B, isCleanAR_collapseAR _⟩⟩

instance : One {A : AR α β // IsCleanAR A} := ⟨⟨1, isCleanAR_one⟩⟩

@[simp] theorem coe_mul_AR (A B : {A : AR α β // IsCleanAR A}) :
    ((A * B : {A : AR α β // IsCleanAR A}) : AR α β) = gconcatAR A B := rfl

omit [DecidableEq α] in
@[simp] theorem coe_one_AR : ((1 : {A : AR α β // IsCleanAR A}) : AR α β) = 1 := rfl

/-- The AR-level OCP quotient monoid on the OCP-clean subtype: `gconcatAR` multiplication,
    `1` unit. Associativity is `collapseAR_concat`; units use `collapseAR_id_on_clean`. -/
instance instMonoidCleanAR : Monoid {A : AR α β // IsCleanAR A} where
  mul_assoc A B C := Subtype.ext <| by
    show collapseAR ((collapseAR (A.1.concat B.1)).concat C.1) =
      collapseAR (A.1.concat (collapseAR (B.1.concat C.1)))
    rw [collapseAR_concat_left, collapseAR_concat_right,
      ← AR.mul_eq_concat, ← AR.mul_eq_concat, ← AR.mul_eq_concat, ← AR.mul_eq_concat,
      mul_assoc]
  one_mul A := Subtype.ext <| by
    show collapseAR ((1 : AR α β).concat A.1) = A.1
    rw [← AR.mul_eq_concat, one_mul, collapseAR_id_on_clean A.2]
  mul_one A := Subtype.ext <| by
    show collapseAR (A.1.concat (1 : AR α β)) = A.1
    rw [← AR.mul_eq_concat, mul_one, collapseAR_id_on_clean A.2]

/-- The bundled AR-level OCP quotient map. `collapseAR_concat` is its `map_mul`; the AR-level
    lift of `OCP.collapseHom`. -/
def collapseARHom : AR α β →* {A : AR α β // IsCleanAR A} where
  toFun A := ⟨collapseAR A, isCleanAR_collapseAR _⟩
  map_one' := Subtype.ext collapseAR_one
  map_mul' A B := Subtype.ext <| by
    show collapseAR (A * B) = collapseAR (collapseAR A |>.concat (collapseAR B))
    rw [AR.mul_eq_concat, collapseAR_concat]

/-! ### As a mathlib quotient monoid -/

/-- The **OCP congruence** on the AR concat monoid: the kernel of `collapseARHom`. The
    AR-level OCP quotient monoid is `ocpConAR.Quotient`. -/
def ocpConAR : Con (AR α β) := Con.ker collapseARHom

/-- `collapseARHom` is surjective: every OCP-clean AR is its own collapse. -/
theorem collapseARHom_surjective :
    Function.Surjective (collapseARHom : AR α β →* {A : AR α β // IsCleanAR A}) := fun C =>
  ⟨C.1, Subtype.ext (collapseAR_id_on_clean C.2)⟩

/-- **First isomorphism theorem for the AR-level OCP quotient.** The abstract quotient
    `AR α β ⧸ OCP` is the concrete OCP-clean model `{A // IsCleanAR A}` ([jardine-2019]'s
    OCP-merging realization, now carrying the association lines). -/
noncomputable def ocpARQuotientEquiv :
    (ocpConAR (α := α) (β := β)).Quotient ≃* {A : AR α β // IsCleanAR A} :=
  Con.quotientKerEquivOfSurjective collapseARHom collapseARHom_surjective

/-! ### The OCP-merging realization -/

variable {S : Type*}

/-- **The OCP-merging realization** `g_T` ([jardine-2019]): realize the string via the
    bridge-only `concat`, then fuse adjacent identical upper nodes
    (`collapseAR ∘ realize`). Unlike `realize`, `realizeMerged gT (Hⁿ)` is a single H
    node multiply associated — the merge that renders unbounded tone plateauing a
    *local* AR pattern. -/
def realizeMerged (g₀ : S → AR α β) (w : List S) : AR α β := collapseAR (realize g₀ w)

@[simp] theorem realizeMerged_def (g₀ : S → AR α β) (w : List S) :
    realizeMerged g₀ w = collapseAR (realize g₀ w) := rfl

end Autosegmental
