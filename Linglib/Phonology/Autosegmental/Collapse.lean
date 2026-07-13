/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.FreeMonoid.Destutter
import Linglib.Phonology.OCP
import Linglib.Phonology.Autosegmental.NormalForm
import Linglib.Phonology.Autosegmental.Realization

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
* `realizeMerged := collapseAR ∘ AR.realize` — the OCP-merging realization.

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
    proof. The AR-level lift of `FreeMonoid.destutterHom` — the run-collapse carrying the
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
— the AR-level lift of `FreeMonoid.destutterHom`, carrying the association lines the flat
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
    lift of `FreeMonoid.destutterHom`. -/
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
    OCP-merging realization, now carrying the association lines). Computable: an OCP-clean AR
    is its own collapse, the right inverse. -/
def ocpARQuotientEquiv :
    (ocpConAR (α := α) (β := β)).Quotient ≃* {A : AR α β // IsCleanAR A} :=
  Con.quotientKerEquivOfRightInverse collapseARHom (·.1)
    (fun C => Subtype.ext (collapseAR_id_on_clean C.2))

/-! ### The decategorification square: the OCP as a monoidal quotient

Forgetting morphisms and the lower tier, the upper-tier projection `upperHom : AR α β →*
FreeMonoid α` (concatenation appends upper tiers) carries the AR-level OCP quotient down to
the *tier-level* one, and the square

```
        (AR α β, concat)  ──collapseARHom──►  {A // IsCleanAR A}
              │                                      │
        upperHom │                                   │ upperHomClean
              ▼                                       ▼
        FreeMonoid α ──destutterHom──►  {l // IsClean l}  ≃  PresentedMonoid ⟨α | a · a = a⟩
```

commutes (`upperHomClean_comp_collapseARHom`). The bottom-right model is the monoid
**presented by idempotent autosegments** `⟨α | a · a = a⟩` (`ocpPresentation`, via
`FreeMonoid.presentedMonoidEquiv`): each autosegment is idempotent (`autosegment_mul_self`),
which *is* the OCP. This is the precise sense in which the OCP is "monoidal" — a monoidal
**quotient**, in contrast to the No-Crossing Constraint, which is a monoidal **subcategory**
(`ncc_isMonoidal`); the OCP-clean objects are *not* closed under the monoidal product
(`ocp_not_isMonoidal`), so no sub-object will do. The square is a `MonoidHom` identity in the
decategorified monoid `(AR α β, concat)`; the `IsMonoidal` facts live one level up, in the
monoidal category `(AR α β, ⊗ = coproduct)`. -/

/-- The upper tier of a collapse is the tier-level collapse of the upper tier: the engine of
the decategorification square. -/
@[simp] theorem upper_collapseAR (A : AR α β) :
    (collapseAR A).upper.toList = collapse A.upper.toList := by
  simp [collapseAR, collapseGraph_upper, LabeledTuple.toList_ofList]

/-- **Upper-tier projection** as a monoid hom `AR α β →* FreeMonoid α`: morpheme
concatenation appends upper tiers (`AR.upper_concat`, `LabeledTuple.toList_concat`). The
decategorification of an autosegmental representation to its melodic tier string. -/
def upperHom : AR α β →* FreeMonoid α where
  toFun A := FreeMonoid.ofList A.upper.toList
  map_one' := rfl
  map_mul' A B := by
    simp only [AR.mul_eq_concat, AR.upper_concat, LabeledTuple.toList_concat,
      FreeMonoid.ofList_append]

omit [DecidableEq α] in
@[simp] theorem upperHom_apply (A : AR α β) :
    upperHom A = FreeMonoid.ofList A.upper.toList := rfl

/-- The projection restricts to OCP-clean representations onto OCP-clean tiers: `IsCleanAR`
is by definition cleanness of the upper tier. -/
def upperHomClean : {A : AR α β // IsCleanAR A} →* {l : List α // IsClean l} where
  toFun A := ⟨A.1.upper.toList, A.2⟩
  map_one' := rfl
  map_mul' A B := Subtype.ext <| by
    show (collapseAR (A.1.concat B.1)).upper.toList =
      List.destutterConcat A.1.upper.toList B.1.upper.toList
    rw [upper_collapseAR, AR.upper_concat, LabeledTuple.toList_concat]
    rfl

/-- **The decategorification square commutes.** Projecting to the upper tier intertwines the
AR-level OCP quotient map with the tier-level one (`FreeMonoid.destutterHom`): collapse then
project equals project then collapse. -/
theorem upperHomClean_comp_collapseARHom :
    upperHomClean.comp (collapseARHom (α := α) (β := β))
      = FreeMonoid.destutterHom.comp upperHom := by
  refine MonoidHom.ext fun A => Subtype.ext ?_
  show (collapseAR A).upper.toList = (FreeMonoid.ofList A.upper.toList).toList.destutter (· ≠ ·)
  rw [upper_collapseAR, FreeMonoid.toList_ofList]
  rfl

/-! #### The OCP-clean tier monoid is presented by idempotent autosegments -/

/-- A single autosegment as a (trivially) OCP-clean tier. -/
def autosegment (a : α) : {l : List α // IsClean l} := ⟨[a], isClean_singleton a⟩

/-- **The OCP, as a monoid equation.** Fusion-gluing an autosegment to a copy of itself
returns the one autosegment: each generator is idempotent, `a · a = a`. This is the
*tier-string* shadow of OCP-driven fusion ([mccarthy-1986]'s gemination); the multiple
association it creates — one melody node linked to several timing slots — lives at the AR
level (`collapseARHom`), which the tier-string projection discards. -/
@[simp] theorem autosegment_mul_self (a : α) :
    autosegment a * autosegment a = autosegment a :=
  Subtype.ext (by simp [autosegment, List.coe_mul, List.destutterConcat, List.destutter_pair])

/-- **The OCP-clean tier monoid is the presented monoid `⟨α | a · a = a⟩`**
(`FreeMonoid.presentedMonoidEquiv`), with `collapse` computing its normal forms — the
bottom-right corner of the decategorification square. With `ocp_not_isMonoidal`, this is the
precise content of "the OCP is monoidal": a monoidal *quotient*, the counterpart to the
No-Crossing Constraint's monoidal *subcategory* (`ncc_isMonoidal`). -/
def ocpPresentation :
    {l : List α // IsClean l} ≃* PresentedMonoid (FreeMonoid.destutterRel α) :=
  FreeMonoid.presentedMonoidEquiv.symm

/-! #### The OCP quotient does not categorify: `collapse` is not a reflector

`collapseAR` is an idempotent retraction on *objects* (`collapseAR_idempotent`,
`collapseAR_id_on_clean`), so one might hope OCP-clean were a *reflective subcategory* of `AR`
with `collapseAR` the reflector — the exact categorical dual of `ncc_isMonoidal`. It is
**not**. An autosegmental morphism is an arbitrary label-preserving position map, so it can
send a morpheme-internal geminate to two *distinct* like nodes of a clean target; the
collapse, having already merged the geminate into one node, cannot separate them, so no
universal factorization exists. The OCP quotient is therefore irreducibly decategorified: it
lives on the object monoid `(AR, concat)`, not on the category. -/

/-- Source with an upper-tier geminate `[true, true]` (not OCP-clean). -/
private abbrev gemSrc : AR Bool Unit := ⟨⟨.ofList [true, true], .empty, ∅⟩, by decide⟩

/-- Clean target `[true, false, true]`: the two `true`s are non-adjacent. -/
private abbrev cleanTgt : AR Bool Unit := ⟨⟨.ofList [true, false, true], .empty, ∅⟩, by decide⟩

/-- The **geminate-splitting morphism** `[true, true] ⟶ [true, false, true]`, sending the two
`true` nodes to the *distinct* clean positions 0 and 2 — a valid label-preserving morphism. -/
private abbrev splitHom : gemSrc ⟶ cleanTgt :=
  { fU := { toFun := fun i => if i.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
            label_comp := by decide }
    fL := { toFun := id, label_comp := rfl }
    links_preserve := by intro i j _ _ h; simp at h }

/-- **`collapse` is not a reflector.** OCP-clean is not a reflective subcategory of `AR`:
there is a clean target `B` and a morphism `g : A ⟶ B` injective on the upper tier (it keeps
a geminate apart) out of a source `A` whose collapse strictly merges that tier. Such a `g`
cannot factor through the collapse — the dual of `ncc_isMonoidal` fails, and the OCP quotient
exists only after decategorification. -/
theorem collapse_not_reflective :
    ∃ (A B : AR Bool Unit) (g : A ⟶ B),
      IsCleanAR B ∧ Function.Injective g.fU.toFun ∧
        (collapseAR A).upper.len < A.upper.len :=
  ⟨gemSrc, cleanTgt, splitHom, by decide, by decide, by decide⟩

/-! #### J&H Theorem 5 and the tier asymmetry

[jardine-heinz-2015] build the OCP merge *into* their concatenation `◦`, and their **Theorem
5** is that `◦` preserves the OCP. Here `◦` is `gconcatAR` (collapse after the bare coproduct
`concat`), and Theorem 5 is `isCleanAR_gconcatAR`: OCP-clean ARs are closed under
fusion-concatenation, where they are *not* closed under the bare coproduct
(`ocp_not_isMonoidal`). That is the genuine sub-vs-quotient asymmetry — the NCC survives the
coproduct (`ncc_isMonoidal`), the OCP needs the merge.

The merge acts on the *upper* (melody) tier only: `collapseAR` leaves the lower (timing) tier
untouched (`collapseAR_lower`). So the two tier projections carry different algebra — the
upper is destuttered (`upper_collapseAR`, the OCP quotient), the lower is **free**, invariant
under collapse (`lowerHom_collapseAR`). This is [jardine-heinz-2015]'s §7 prediction in
algebraic form: the melody tier fuses, so contour tones are *bounded*; the timing tier does
not, so spreading is *unbounded*. -/

/-- **[jardine-heinz-2015] Theorem 5.** OCP-clean ARs are closed under fusion-concatenation
`◦` (`gconcatAR`): the merge built into `◦` preserves the OCP, where the bare coproduct
`concat` does not (`ocp_not_isMonoidal`). The positive half of the sub-vs-quotient dichotomy. -/
theorem isCleanAR_gconcatAR (A B : AR α β) : IsCleanAR (gconcatAR A B) :=
  isCleanAR_collapseAR _

/-- `collapseAR` leaves the lower (timing) tier untouched: the merge is upper-tier only. -/
@[simp] theorem collapseAR_lower (A : AR α β) : (collapseAR A).lower = A.lower := rfl

@[simp] theorem collapseAR_links (A : AR α β) :
    (collapseAR A).links = A.links.image (Prod.map (runIdx A.upper.toList) id) := rfl

/-- OCP-merging a constant melody funnels every association line to the single surviving
node: a link survives at `(0, j)` exactly when slot `j` was linked at all. -/
theorem mem_links_collapseAR_of_upper_replicate {A : AR α β} {n : ℕ} {a : α}
    (hA : A.upper.toList = List.replicate n a) {p : ℕ × ℕ} :
    p ∈ (collapseAR A).links ↔ p.1 = 0 ∧ A.toGraph.IsLinkedLower p.2 := by
  obtain ⟨k, j⟩ := p
  rw [collapseAR_links, hA, Graph.isLinkedLower_iff]
  simp only [Finset.mem_image, Prod.exists, Prod.map_apply, id_eq, runIdx_replicate,
    Prod.mk.injEq]
  constructor
  · rintro ⟨q₁, q₂, hq, rfl, rfl⟩
    exact ⟨rfl, q₁, hq⟩
  · rintro ⟨rfl, q₁, hq⟩
    exact ⟨q₁, j, hq, rfl, rfl⟩

/-- **Lower-tier projection** as a monoid hom `AR α β →* FreeMonoid β`: concatenation appends
lower tiers. The timing-tier decategorification, dual to `upperHom`. -/
def lowerHom : AR α β →* FreeMonoid β where
  toFun A := FreeMonoid.ofList A.lower.toList
  map_one' := rfl
  map_mul' A B := by
    simp only [AR.mul_eq_concat, AR.lower_concat, LabeledTuple.toList_concat,
      FreeMonoid.ofList_append]

omit [DecidableEq α] in
@[simp] theorem lowerHom_apply (A : AR α β) :
    lowerHom A = FreeMonoid.ofList A.lower.toList := rfl

/-- **The timing tier is free.** Unlike the melody tier — which `collapse` destutters
(`upper_collapseAR`) — the lower tier is *invariant* under collapse: it is not quotiented.
The algebraic form of the spreading/contour asymmetry ([jardine-heinz-2015] §7). -/
@[simp] theorem lowerHom_collapseAR (A : AR α β) : lowerHom (collapseAR A) = lowerHom A := by
  simp [lowerHom]

/-! ### The OCP-merging realization -/

variable {S : Type*}

/-- **The OCP-merging realization** ([jardine-2019]): AR.realize the string via the
    bridge-only `concat`, then fuse adjacent identical upper nodes
    (`collapseAR ∘ AR.realize`). Unlike `AR.realize`, `realizeMerged g₀ (Hⁿ)` is a single H
    node multiply associated — the merge that renders unbounded tone plateauing a
    *local* AR pattern. -/
def realizeMerged (g₀ : S → AR α β) (w : List S) : AR α β := collapseAR (AR.realize g₀ w)

@[simp] theorem realizeMerged_def (g₀ : S → AR α β) (w : List S) :
    realizeMerged g₀ w = collapseAR (AR.realize g₀ w) := rfl

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

omit [DecidableEq ι] in
/-- The label of a canonical vertex sits on its own tier. -/
theorem Representation.label_vertexEquiv [Finite X.obj.V] (i : ι)
    (p : Fin (X.tierLength i)) : (X.obj.label (X.vertexEquiv ⟨i, p⟩)).1 = i :=
  (X.fiberEnum i p).property

omit [DecidableEq ι] in
/-- Links are symmetric in coordinates. -/
theorem Representation.link_symm [Finite X.obj.V] {i j : ι} {p q : ℕ}
    (h : X.link i j p q) : X.link j i q p := by
  obtain ⟨hp, hq, hl⟩ := h
  exact ⟨hq, hp, hl.symm⟩

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

omit [DecidableEq ι] in
/-- Same-tier vertices are never linked: they are arc-comparable (Axioms 1–2),
    and association never follows arcs (Axiom 3). -/
theorem Representation.not_link_self_tier [Finite X.obj.V] (i : ι) (p q : ℕ) :
    ¬ X.link i i p q := by
  rintro ⟨hp, hq, hl⟩
  rw [Representation.linkRel_def] at hl
  have hlab : X.obj.tier Sigma.fst (X.vertexEquiv ⟨i, ⟨p, hp⟩⟩)
      = X.obj.tier Sigma.fst (X.vertexEquiv ⟨i, ⟨q, hq⟩⟩) := by
    show (X.obj.label _).1 = (X.obj.label _).1
    rw [Representation.label_vertexEquiv, Representation.label_vertexEquiv]
  exact (X.property.1.total hl.ne hlab).elim (X.property.2 hl) (X.property.2 hl.symm)

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

end CoordinateCollapse

end Autosegmental
