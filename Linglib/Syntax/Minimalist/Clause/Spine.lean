import Linglib.Syntax.Minimalist.Clause.Size
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Chain
import Mathlib.Data.List.DropRight

/-!
# Clause spines

This file defines the clause spine and its bilateral label. A clause spine is the nonempty list of
heads a clause projects, from the lexical head upward, so a bare VP is `[V]`, a finite clause
`[V, v, T, C]`, and a nominalized complement the finite clause with the nominal shell `[N, D]`
appended. A spine is an extended projection in Grimshaw's sense when each head extends the one
below it. Keine observes that category features project bilaterally within an extended
projection, so a clause is labeled by the set of every head it projects. The label of a spine is
that finset, and spines are preordered by inclusion of labels, the extension order, in which the
clause sizes of one extended projection form a chain and a nominalized clause and a finite clause
are incomparable.

## Main definitions

* `Minimalist.ClauseSpine`: the nonempty list of heads a clause projects, bottom-up.
* `Minimalist.ClauseSpine.label`: the bilateral label, the finset of heads a spine projects.
* `Minimalist.ClauseSpine.IsExtendedProjection`: a spine each of whose heads extends the one
  below it.
* `Minimalist.ClauseSpine.size`: the complement size of a spine, that of its highest head.
* `Minimalist.ClauseSpine.append`: the spine with a nominal or adpositional shell over it.
* `Minimalist.ClauseSpine.above`: the heads projected above the last occurrence of a category,
  the shell over a clause's CP.
* `Minimalist.ClauseSpine.vP`, `Minimalist.ClauseSpine.tP`, `Minimalist.ClauseSpine.cP`: the
  clause sizes of the verbal extended projection.

## Main results

* `Minimalist.ClauseSpine.le_def`: the extension order is inclusion of labels.
* `Minimalist.ClauseSpine.IsExtendedProjection.anchor_extendsTo`: every head of an extended
  projection extends its lexical anchor.
* `Minimalist.ClauseSpine.above_append`: appending a shell that does not contain a category
  appends it to the heads above that category.

## References

* [grimshaw-2005]
* [keine-2019]
* [keine-2020]
* [deal-2026]
-/

namespace Minimalist

/-- A clause spine is the nonempty list of heads a clause projects, from the lexical head
upward. -/
structure ClauseSpine where
  /-- The projected heads, bottom-up. -/
  heads : List Cat
  heads_ne_nil : heads ≠ []
  deriving Repr, DecidableEq

namespace ClauseSpine

variable {s t : ClauseSpine} {c : Cat} {l : List Cat}

instance : Membership Cat ClauseSpine := ⟨fun s c ↦ c ∈ s.heads⟩

@[simp] theorem mem_def : c ∈ s ↔ c ∈ s.heads := Iff.rfl

instance (c : Cat) (s : ClauseSpine) : Decidable (c ∈ s) :=
  inferInstanceAs (Decidable (c ∈ s.heads))

instance (P : Cat → Prop) [DecidablePred P] (s : ClauseSpine) : Decidable (∀ c ∈ s, P c) :=
  inferInstanceAs (Decidable (∀ c ∈ s.heads, P c))

instance (P : Cat → Prop) [DecidablePred P] (s : ClauseSpine) : Decidable (∃ c ∈ s, P c) :=
  inferInstanceAs (Decidable (∃ c ∈ s.heads, P c))

/-- The lexical anchor of a spine, its lowest head. -/
def anchor (s : ClauseSpine) : Cat := s.heads.head s.heads_ne_nil

/-- The highest head of a spine. -/
def top (s : ClauseSpine) : Cat := s.heads.getLast s.heads_ne_nil

/-- The size of a spine is the complement size of its highest head. -/
def size (s : ClauseSpine) : ComplementSize := ⟨s.top⟩

/-! ### Extended projections -/

/-- A spine is an extended projection when each head extends the one below it, so that its heads
are of one family and their F-values do not decrease. -/
def IsExtendedProjection (s : ClauseSpine) : Prop := s.heads.IsChain Cat.ExtendsTo

instance (s : ClauseSpine) : Decidable s.IsExtendedProjection :=
  inferInstanceAs (Decidable (List.IsChain _ _))

/-- Every head of an extended projection extends its lexical anchor. -/
theorem IsExtendedProjection.anchor_extendsTo (h : s.IsExtendedProjection) (hc : c ∈ s) :
    s.anchor.ExtendsTo c := by
  obtain ⟨x, l, hl⟩ := List.exists_cons_of_ne_nil s.heads_ne_nil
  have hx : s.anchor = x := by simp [anchor, hl]
  rw [IsExtendedProjection, List.isChain_iff_pairwise, hl, List.pairwise_cons] at h
  rw [mem_def, hl, List.mem_cons] at hc
  rw [hx]
  rcases hc with rfl | hc
  · exact ⟨rfl, le_rfl⟩
  · exact h.1 c hc

/-! ### Labels and the extension order -/

/-- The bilateral label of a spine is the set of heads it projects. -/
def label (s : ClauseSpine) : Finset Cat := s.heads.toFinset

@[simp] theorem mem_label : c ∈ s.label ↔ c ∈ s := List.mem_toFinset

/-- The extension order. A spine lies below another when the other projects every head it does,
as the clause sizes of one extended projection do. -/
instance : Preorder ClauseSpine := Preorder.lift label

theorem le_def : s ≤ t ↔ s.label ⊆ t.label := Iff.rfl

theorem le_iff_forall_mem : s ≤ t ↔ ∀ c ∈ s, c ∈ t := by simp [le_def, Finset.subset_iff]

instance : DecidableLE ClauseSpine := fun s t ↦ inferInstanceAs (Decidable (s.label ⊆ t.label))

instance : DecidableLT ClauseSpine := fun s t ↦ inferInstanceAs (Decidable (s.label ⊂ t.label))

/-! ### Shells -/

/-- Appending heads to a spine projects a nominal or adpositional shell over the clause. -/
def append (s : ClauseSpine) (l : List Cat) : ClauseSpine :=
  ⟨s.heads ++ l, by simp [s.heads_ne_nil]⟩

@[simp] theorem heads_append (s : ClauseSpine) (l : List Cat) :
    (s.append l).heads = s.heads ++ l :=
  rfl

@[simp] theorem mem_append : c ∈ s.append l ↔ c ∈ s ∨ c ∈ l := List.mem_append

theorem le_append (s : ClauseSpine) (l : List Cat) : s ≤ s.append l :=
  le_iff_forall_mem.2 fun _ hc ↦ mem_append.2 (Or.inl hc)

/-- The heads projected strictly above the last occurrence of `c`, so that `s.above .C` is the
shell over the CP of `s` and `[]` for a bare CP. -/
def above (s : ClauseSpine) (c : Cat) : List Cat := s.heads.rtakeWhile (· != c)

theorem above_append (s : ClauseSpine) (h : c ∉ l) : (s.append l).above c = s.above c ++ l := by
  induction l using List.reverseRecOn with
  | nil => simp [above]
  | append_singleton l x ih =>
    simp only [List.mem_append, List.mem_singleton, not_or] at h
    rw [above, heads_append, ← List.append_assoc,
      List.rtakeWhile_concat_pos (· != c) _ x (bne_iff_ne.2 (Ne.symm h.2)), ← List.append_assoc]
    exact congrArg (· ++ [x]) (ih h.1)

/-! ### Clause sizes -/

/-- The vP-sized clause `[V, v]`, the small nonfinite clause. -/
def vP : ClauseSpine := ⟨[.V, .v], by simp⟩

/-- The TP-sized clause `[V, v, T]`, the large nonfinite clause. -/
def tP : ClauseSpine := ⟨[.V, .v, .T], by simp⟩

/-- The CP-sized clause `[V, v, T, C]`, the finite clause. -/
def cP : ClauseSpine := ⟨[.V, .v, .T, .C], by simp⟩

theorem vP_le_tP : vP ≤ tP := by decide

theorem tP_le_cP : tP ≤ cP := by decide

theorem cP_isExtendedProjection : cP.IsExtendedProjection := by decide

end ClauseSpine

end Minimalist
