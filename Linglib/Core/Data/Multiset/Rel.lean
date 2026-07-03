/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.ZeroCons

/-!
# Deciding `Multiset.Rel` for a partial equivalence

`Multiset.Rel r s t` holds when the elements of `s` and `t` can be matched one-to-one
along `r`. For a general decidable `r` this is a bipartite-matching problem, but when `r`
is symmetric and transitive on the elements involved, the greedy strategy — match each
element of `s` to the first `r`-related element of `t` and discard the pair — is complete.
This file implements the greedy matcher as a Boolean function on lists, proves it decides
`Multiset.Rel`, and packages the result as a `Decidable` instance. The matcher recurses
structurally, so the instance reduces in the kernel and concrete goals close by `decide`.

## Main definitions

- `List.isPermBy p l₁ l₂`: greedy matching of `l₁` against `l₂` along the Boolean
  relation `p` — the algorithm of `List.isPerm`, with `p` in place of `==`.

## Main results

- `Multiset.rel_coe_iff_exists`: `Rel r ↑l₁ ↑l₂` iff some reordering of `l₂` is
  componentwise `r`-related to `l₁`.
- `List.isPermBy_iff_rel`: `isPermBy p` decides `Multiset.Rel (p · ·)`, given symmetry
  and transitivity of `p` on a predicate covering both lists.
- `Multiset.rel_symm_on`, `Multiset.rel_trans_on`: symmetry and transitivity of `Rel r`
  from the corresponding properties of `r` on the members alone.
- `Multiset.Rel.decidable`: `Decidable (Rel r s t)` for decidable symmetric transitive
  `r`.

## Implementation notes

Core's `List.isPerm_iff` proves the greedy matcher correct only under `LawfulBEq`, which
forces `p` to coincide with equality. The lemmas here assume instead that `p` is
symmetric and transitive *on a predicate `P` covering the lists' members* — the form a
consumer needs when `p` is defined by recursion and its equivalence properties are only
available beneath a termination bound (see `RootedTree/DecEq.lean`). The unconditional
`Std.Symm`/`IsTrans` version is a corollary.

`[UPSTREAM]` candidate.
-/

namespace List

variable {α : Type*} {p : α → α → Bool}

/-- Greedy matching of `l₁` against `l₂` along `p`: pair each element of `l₁` with the
    first `p`-related element of `l₂`, removing it. The algorithm of `List.isPerm`, with
    `p` in place of `==`. Complete for `Multiset.Rel (p · ·)` when `p` is symmetric and
    transitive on the members (`isPermBy_iff_rel`). -/
def isPermBy (p : α → α → Bool) : List α → List α → Bool
  | [], l₂ => l₂.isEmpty
  | a :: l₁, l₂ =>
    match l₂.findIdx? (p a) with
    | some i => isPermBy p l₁ (l₂.eraseIdx i)
    | none => false

/-- `l₁` and `l₂` match as multisets under `p`: some reordering of `l₂` is componentwise
    `p`-related to `l₁`. -/
private def PermMatch (p : α → α → Bool) (l₁ l₂ : List α) : Prop :=
  ∃ l', List.Forall₂ (fun a b => p a b = true) l₁ l' ∧ l'.Perm l₂

/-- Soundness of the greedy matcher: `isPermBy p l₁ l₂ = true → PermMatch p l₁ l₂`. -/
private theorem permMatch_of_isPermBy :
    ∀ (l₁ l₂ : List α), isPermBy p l₁ l₂ = true → PermMatch p l₁ l₂
  | [], [], _ => ⟨[], .nil, .refl _⟩
  | [], _ :: _, h => by rw [isPermBy] at h; exact absurd h (by simp)
  | _ :: _, [], h => by rw [isPermBy] at h; exact absurd h (by simp)
  | a :: l₁, b :: l₂, h => by
    rw [isPermBy] at h
    cases hfind : (b :: l₂).findIdx? (p a) with
    | none => rw [hfind] at h; exact absurd h (by simp)
    | some i =>
      rw [hfind] at h
      rw [List.findIdx?_eq_some_iff_getElem] at hfind
      obtain ⟨hi, hpi, _⟩ := hfind
      obtain ⟨es', hf', hperm'⟩ := permMatch_of_isPermBy l₁ ((b :: l₂).eraseIdx i) h
      refine ⟨(b :: l₂)[i] :: es', List.Forall₂.cons hpi hf', ?_⟩
      exact (hperm'.cons _).trans (List.getElem_cons_eraseIdx_perm hi)

section
-- `DecidableEq` is proof bookkeeping only (the `List.erase`-based match rebuilding);
-- the public lemmas below discharge it with `classical`.
variable [DecidableEq α]

/-- Swap step for completeness: matching `a` to the greedily-found `d` and rebuilding the
    leftover match for `l₁` against `(e :: es).erase d`. Reattaching the floating `e` to
    `d`'s old partner uses symmetry and transitivity of `p` on the members (supplied
    through the bound predicate `P`). -/
private theorem forall₂_cons_erase_match {P : α → Prop}
    (Ssymm : ∀ x y, P x → P y → p x y = true → p y x = true)
    (Strans : ∀ x y z, P x → P y → P z → p x y = true → p y z = true → p x z = true)
    {a e : α} (hPa : P a) (hPe : P e) (hae : p a e = true)
    {l₁ es : List α} (hPl₁ : ∀ x ∈ l₁, P x) (hPes : ∀ x ∈ es, P x)
    (hl₁ : List.Forall₂ (fun a b => p a b = true) l₁ es) :
    ∀ {d : α}, P d → p a d = true → d ∈ e :: es →
      ∃ X, List.Forall₂ (fun a b => p a b = true) l₁ X ∧ X.Perm ((e :: es).erase d) := by
  induction hl₁ with
  | nil =>
    intro d _ _ hd
    rw [List.mem_singleton] at hd
    exact ⟨[], List.Forall₂.nil, by rw [hd, List.erase_cons_head]⟩
  | @cons x y l₁₀ es₀ hxy hl₁₀ ih =>
    intro d hPd had hd
    have hPx : P x := hPl₁ x List.mem_cons_self
    have hPy : P y := hPes y List.mem_cons_self
    have hPl₁₀ : ∀ z ∈ l₁₀, P z := fun z hz => hPl₁ z (List.mem_cons_of_mem _ hz)
    have hPes₀ : ∀ z ∈ es₀, P z := fun z hz => hPes z (List.mem_cons_of_mem _ hz)
    by_cases hde : d = e
    · exact ⟨y :: es₀, List.Forall₂.cons hxy hl₁₀, by rw [hde, List.erase_cons_head]⟩
    · have hdes : d ∈ y :: es₀ := (List.mem_cons.mp hd).resolve_left hde
      have hne : ¬ (e == d) = true := by simpa using (fun h => hde h.symm)
      rw [List.erase_cons_tail hne]
      by_cases hdy : d = y
      · have hay : p a y = true := hdy ▸ had
        have hax : p a x = true := Strans a y x hPa hPy hPx hay (Ssymm x y hPx hPy hxy)
        have hxe : p x e = true := Strans x a e hPx hPa hPe (Ssymm a x hPa hPx hax) hae
        exact ⟨e :: es₀, List.Forall₂.cons hxe hl₁₀, by rw [← hdy, List.erase_cons_head]⟩
      · have hd₀ : d ∈ es₀ := (List.mem_cons.mp hdes).resolve_left hdy
        have hyd : ¬ (y == d) = true := by simpa using (fun h => hdy h.symm)
        obtain ⟨X₀, hX₀f, hX₀p⟩ := ih hPl₁₀ hPes₀ hPd had (List.mem_cons_of_mem _ hd₀)
        rw [List.erase_cons_tail hyd]
        refine ⟨y :: X₀, List.Forall₂.cons hxy hX₀f, ?_⟩
        rw [List.erase_cons_tail hne] at hX₀p
        exact (hX₀p.cons y).trans (List.Perm.swap e y _)

/-- Completeness of the greedy matcher: `PermMatch p l₁ l₂ → isPermBy p l₁ l₂ = true`,
    given symmetry and transitivity of `p` on the members (via the bound predicate
    `P`). -/
private theorem isPermBy_of_permMatch {P : α → Prop}
    (Ssymm : ∀ x y, P x → P y → p x y = true → p y x = true)
    (Strans : ∀ x y z, P x → P y → P z → p x y = true → p y z = true → p x z = true) :
    ∀ (l₁ l₂ : List α), (∀ x ∈ l₁, P x) → (∀ x ∈ l₂, P x) →
      PermMatch p l₁ l₂ → isPermBy p l₁ l₂ = true
  | [], l₂, _, _, ⟨l', hf, hperm⟩ => by
    rw [List.forall₂_nil_left_iff.mp hf] at hperm
    rw [hperm.symm.eq_nil, isPermBy]; rfl
  | a :: l₁, l₂, hPl₁, hPl₂, ⟨l', hf, hperm⟩ => by
    obtain ⟨e, es, hae, hf', rfl⟩ := List.forall₂_cons_left_iff.mp hf
    have hPa : P a := hPl₁ a List.mem_cons_self
    have hPl₁' : ∀ x ∈ l₁, P x := fun x hx => hPl₁ x (List.mem_cons_of_mem _ hx)
    have hPe : P e := hPl₂ e (hperm.subset List.mem_cons_self)
    have hPes : ∀ x ∈ es, P x := fun x hx => hPl₂ x (hperm.subset (List.mem_cons_of_mem _ hx))
    have hel₂ : e ∈ l₂ := hperm.subset List.mem_cons_self
    have hfi : l₂.findIdx? (p a) = some (l₂.findIdx (p a)) :=
      List.findIdx?_eq_some_of_exists ⟨e, hel₂, hae⟩
    rw [isPermBy, hfi]
    set i := l₂.findIdx (p a)
    rw [List.findIdx?_eq_some_iff_getElem] at hfi
    obtain ⟨hi, hpi, _⟩ := hfi
    set d := l₂[i] with hd
    have hPd : P d := hPl₂ d (List.getElem_mem hi)
    obtain ⟨X, hXf, hXp⟩ :=
      forall₂_cons_erase_match Ssymm Strans hPa hPe hae hPl₁' hPes hf' hPd hpi
        (hperm.symm.subset (List.getElem_mem hi))
    apply isPermBy_of_permMatch Ssymm Strans l₁ (l₂.eraseIdx i) hPl₁'
      (fun x hx => hPl₂ x ((List.eraseIdx_sublist l₂ i).subset hx))
    exact ⟨X, hXf, (hXp.trans (hperm.erase d)).trans (List.erase_getElem hi)⟩

end

/-- `isPermBy p` is reflexive when `p` is reflexive on the members. -/
theorem isPermBy_refl : ∀ (l : List α), (∀ x ∈ l, p x x = true) → isPermBy p l l = true
  | [], _ => rfl
  | a :: l, h => by
    rw [isPermBy]
    have h0 : (a :: l).findIdx? (p a) = some 0 := by
      rw [List.findIdx?_cons]; simp [h a List.mem_cons_self]
    rw [h0]
    simp only [List.eraseIdx_cons_zero]
    exact isPermBy_refl l fun x hx => h x (List.mem_cons_of_mem _ hx)

end List

namespace Multiset

variable {α : Type*} {β : Type*}

/-- `Rel r` on coerced lists: some reordering of `l₂` is componentwise `r`-related to
    `l₁`. The list-level reading of `Multiset.Rel`. -/
theorem rel_coe_iff_exists {r : α → β → Prop} {l₁ : List α} {l₂ : List β} :
    Rel r ↑l₁ ↑l₂ ↔ ∃ l', List.Forall₂ r l₁ l' ∧ l'.Perm l₂ := by
  constructor
  · induction l₁ generalizing l₂ with
    | nil =>
      intro h
      rw [Multiset.coe_nil, rel_zero_left, ← Multiset.coe_nil, Multiset.coe_eq_coe] at h
      exact ⟨[], List.Forall₂.nil, h.symm⟩
    | cons a l₁ ih =>
      intro h
      rw [← Multiset.cons_coe, rel_cons_left] at h
      obtain ⟨b, bs, hab, hrel, hbs⟩ := h
      obtain ⟨l₂', rfl⟩ := Quotient.exists_rep bs
      obtain ⟨l', hf, hperm⟩ := ih hrel
      refine ⟨b :: l', List.Forall₂.cons hab hf, ?_⟩
      have : l₂.Perm (b :: l₂') := Multiset.coe_eq_coe.mp (by simpa using hbs)
      exact (hperm.cons b).trans this.symm
  · rintro ⟨l', hf, hperm⟩
    rw [← Multiset.coe_eq_coe.mpr hperm]
    clear hperm
    induction hf with
    | nil => exact Rel.zero
    | cons hab _ ih => exact Rel.cons hab ih

/-- `Rel r` is symmetric when `r` is symmetric on the members. -/
theorem rel_symm_on {r : α → α → Prop} {s t : Multiset α}
    (hs : ∀ x ∈ s, ∀ y ∈ t, r x y → r y x) (h : Rel r s t) : Rel r t s :=
  rel_flip.mp (h.mono hs)

/-- `Rel r` is transitive when `r` is transitive on the members. -/
theorem rel_trans_on {r : α → α → Prop} {s t u : Multiset α}
    (ht : ∀ x ∈ s, ∀ y ∈ t, ∀ z ∈ u, r x y → r y z → r x z)
    (h₁ : Rel r s t) (h₂ : Rel r t u) : Rel r s u := by
  induction t using Multiset.induction_on generalizing s u with
  | empty => rw [rel_zero_right.mp h₁, rel_zero_left.mp h₂, rel_zero_left]
  | cons y t ih =>
    obtain ⟨x, s', hxy, hrel₁, rfl⟩ := rel_cons_right.mp h₁
    obtain ⟨z, u', hyz, hrel₂, rfl⟩ := rel_cons_left.mp h₂
    refine Rel.cons
      (ht x (mem_cons_self _ _) y (mem_cons_self _ _) z (mem_cons_self _ _) hxy hyz)
      (ih (fun a ha b hb c hc => ht a (mem_cons_of_mem ha) b (mem_cons_of_mem hb) c
        (mem_cons_of_mem hc)) hrel₁ hrel₂)

end Multiset

namespace List

variable {α : Type*} {p : α → α → Bool}

/-- Soundness of the greedy matcher against `Multiset.Rel`, hypothesis-free. -/
theorem rel_of_isPermBy {l₁ l₂ : List α} (h : isPermBy p l₁ l₂ = true) :
    Multiset.Rel (fun a b => p a b = true) ↑l₁ ↑l₂ := by
  obtain ⟨l', hf, hperm⟩ := permMatch_of_isPermBy l₁ l₂ h
  exact Multiset.rel_coe_iff_exists.mpr ⟨l', hf, hperm⟩

/-- Completeness of the greedy matcher against `Multiset.Rel`, given symmetry and
    transitivity of `p` on a predicate `P` covering both lists. -/
theorem isPermBy_of_rel {P : α → Prop}
    (Ssymm : ∀ x y, P x → P y → p x y = true → p y x = true)
    (Strans : ∀ x y z, P x → P y → P z → p x y = true → p y z = true → p x z = true)
    {l₁ l₂ : List α} (hP₁ : ∀ x ∈ l₁, P x) (hP₂ : ∀ x ∈ l₂, P x)
    (h : Multiset.Rel (fun a b => p a b = true) ↑l₁ ↑l₂) : isPermBy p l₁ l₂ = true := by
  classical
  exact isPermBy_of_permMatch Ssymm Strans l₁ l₂ hP₁ hP₂ (Multiset.rel_coe_iff_exists.mp h)

/-- The greedy matcher decides `Multiset.Rel`, given symmetry and transitivity of `p` on
    a predicate `P` covering both lists. -/
theorem isPermBy_iff_rel {P : α → Prop}
    (Ssymm : ∀ x y, P x → P y → p x y = true → p y x = true)
    (Strans : ∀ x y z, P x → P y → P z → p x y = true → p y z = true → p x z = true)
    {l₁ l₂ : List α} (hP₁ : ∀ x ∈ l₁, P x) (hP₂ : ∀ x ∈ l₂, P x) :
    isPermBy p l₁ l₂ = true ↔ Multiset.Rel (fun a b => p a b = true) ↑l₁ ↑l₂ :=
  ⟨rel_of_isPermBy, isPermBy_of_rel Ssymm Strans hP₁ hP₂⟩

end List

namespace Multiset

variable {α : Type*}

/-- `Multiset.Rel r` is decidable, and computably so, for a decidable symmetric
    transitive `r`: decided by the greedy matcher on representatives, which reduces in
    the kernel. -/
instance Rel.decidable {r : α → α → Prop} [DecidableRel r] [Std.Symm r] [IsTrans α r]
    (s t : Multiset α) : Decidable (Rel r s t) :=
  Quotient.recOnSubsingleton₂ s t fun l₁ l₂ =>
    decidable_of_iff (List.isPermBy (fun a b => decide (r a b)) l₁ l₂ = true) <| by
      rw [List.isPermBy_iff_rel (p := fun a b => decide (r a b)) (P := fun _ => True)
        (fun x y _ _ h => decide_eq_true (Std.Symm.symm x y (of_decide_eq_true h)))
        (fun x y z _ _ _ h₁ h₂ => decide_eq_true
          (IsTrans.trans x y z (of_decide_eq_true h₁) (of_decide_eq_true h₂)))
        (fun _ _ => trivial) (fun _ _ => trivial)]
      exact ⟨fun h => h.mono (by simp), fun h => h.mono (by simp)⟩

end Multiset
