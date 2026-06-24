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
(`IsNonCrossing.image_monotone`, `NonCrossing.lean`). The result is the AR-level lift
of `OCP.collapseHom`: the same run-collapse, now carrying the autosegmental links the
flat tier-string discards.
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
