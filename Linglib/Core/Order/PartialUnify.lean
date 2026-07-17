import Mathlib.Order.Bounds.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.UpperLower.Closure
import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Partial unification: computable pairwise least upper bounds

`PartialUnify α` equips a partial order with a computable partial join:
`unify a b` returns the least upper bound of `{a, b}` when the pair is
bounded above, and `none` otherwise. This is the pairwise face of
bounded completeness — [carpenter-1992]'s setting for unification
domains (Definition 2.1: an inheritance hierarchy is a finite bounded
complete partial order), with the join taken as primitive because
"joins correspond to unifications" (p. 13). Carpenter notes the
equivalence this file exploits: "a finite BCPO is nothing more nor less
than a finite meet semilattice", presented through its joins.

The laws of unification — idempotence, commutativity,
associativity-with-failure, `⊥` as identity, guarded monotonicity —
are proved here once, from least-upper-bound uniqueness; carriers
(feature slots, bundles, attribute-value records) supply only `unify`
and the two axioms.

Adjoining a top element to make the join total is a *derived*
presentation ([carpenter-1992] p. 16 attributes it to Aït-Kaci and
Smolka), not the primitive; this file deliberately does not take it.

## Main declarations

* `PartialUnify` — the class
* `PartialUnify.unify_eq_some_iff_isLUB`,
  `PartialUnify.isSome_unify_iff_bddAbove` — characterizations
* `PartialUnify.unify_comm`, `unify_assoc`, `unify_self`, `bot_unify`,
  `unify_mono` — the unification laws
* the Pi instance: pointwise unification over a `Fintype` index
-/

/-- A computable partial join on a partial order: `unify a b` is `some`
of the least upper bound of `{a, b}` when the pair is bounded above,
and `none` otherwise — the pairwise face of [carpenter-1992]'s bounded
completeness, with the join as the primitive operation. -/
class PartialUnify (α : Type*) [PartialOrder α] where
  /-- The partial join. -/
  unify : α → α → Option α
  /-- A successful unification is a least upper bound. -/
  isLUB_of_unify_eq_some : ∀ {a b c : α}, unify a b = some c → IsLUB {a, b} c
  /-- Unification succeeds on bounded-above pairs. -/
  isSome_unify_of_bddAbove :
    ∀ {a b : α}, BddAbove ({a, b} : Set α) → (unify a b).isSome

namespace PartialUnify

theorem mem_upperBounds_pair {α : Type*} [Preorder α] {u a b : α} :
    u ∈ upperBounds ({a, b} : Set α) ↔ a ≤ u ∧ b ≤ u := by
  simp [upperBounds_insert, upperBounds_singleton]

variable {α : Type*} [PartialOrder α] [PartialUnify α] {a b c u : α}

theorem isSome_unify_iff_bddAbove :
    (unify a b).isSome ↔ BddAbove ({a, b} : Set α) := by
  refine ⟨λ h => ?_, isSome_unify_of_bddAbove⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  exact ⟨c, (isLUB_of_unify_eq_some hc).1⟩

theorem unify_eq_some_iff_isLUB :
    unify a b = some c ↔ IsLUB {a, b} c := by
  refine ⟨isLUB_of_unify_eq_some, λ h => ?_⟩
  obtain ⟨d, hd⟩ :=
    Option.isSome_iff_exists.mp (isSome_unify_of_bddAbove ⟨c, h.1⟩)
  rw [hd, Option.some_inj]
  exact (isLUB_of_unify_eq_some hd).unique h

theorem unify_eq_none_iff :
    unify a b = none ↔ ¬ BddAbove ({a, b} : Set α) := by
  rw [← isSome_unify_iff_bddAbove]
  cases unify a b <;> simp

theorem unify_comm (a b : α) : unify a b = unify b a := by
  have hpair : ({b, a} : Set α) = {a, b} := Set.pair_comm b a
  cases hab : unify a b with
  | some c =>
    symm
    rw [unify_eq_some_iff_isLUB, hpair]
    exact isLUB_of_unify_eq_some hab
  | none =>
    symm
    rw [unify_eq_none_iff, hpair]
    exact unify_eq_none_iff.mp hab

@[simp]
theorem unify_self (a : α) : unify a a = some a := by
  rw [unify_eq_some_iff_isLUB, Set.pair_eq_singleton]
  exact isLUB_singleton

@[simp]
theorem bot_unify [OrderBot α] (a : α) : unify (⊥ : α) a = some a := by
  rw [unify_eq_some_iff_isLUB]
  exact ⟨mem_upperBounds_pair.mpr ⟨bot_le, le_rfl⟩,
    λ u hu => (mem_upperBounds_pair.mp hu).2⟩

@[simp]
theorem unify_bot [OrderBot α] (a : α) : unify a (⊥ : α) = some a := by
  rw [unify_comm]; exact bot_unify a

omit [PartialUnify α] in
/-- Glueing pairwise LUBs: if `v` is the LUB of `{a, b}`, then LUBs of
`{v, c}` are exactly LUBs of `{a, b, c}`. -/
theorem isLUB_pair_step {a b c v u : α} (hv : IsLUB {a, b} v) :
    IsLUB {v, c} u ↔ IsLUB ({a, b, c} : Set α) u := by
  have hub : upperBounds ({v, c} : Set α) = upperBounds {a, b, c} := by
    ext w
    constructor
    · intro hw x hx
      rcases hx with rfl | rfl | rfl
      · exact (hv.1 (Set.mem_insert _ _)).trans (hw (Set.mem_insert _ _))
      · exact (hv.1 (Set.mem_insert_of_mem _ rfl)).trans (hw (Set.mem_insert _ _))
      · exact hw (Set.mem_insert_of_mem _ rfl)
    · intro hw x hx
      rcases hx with rfl | rfl
      · exact hv.2 λ y hy => by
          rcases hy with rfl | rfl
          · exact hw (Set.mem_insert _ _)
          · exact hw (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact hw (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  unfold IsLUB
  rw [hub]

theorem bind_unify_left_eq_some_iff {u : α} :
    (unify a b).bind (unify · c) = some u ↔ IsLUB ({a, b, c} : Set α) u := by
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨v, hv, hu⟩
    exact (isLUB_pair_step (isLUB_of_unify_eq_some hv)).mp
      (isLUB_of_unify_eq_some hu)
  · intro h
    have hab : BddAbove ({a, b} : Set α) := by
      refine ⟨u, mem_upperBounds_pair.mpr ⟨?_, ?_⟩⟩
      · exact h.1 (Set.mem_insert _ _)
      · exact h.1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (isSome_unify_of_bddAbove hab)
    refine ⟨v, hv, ?_⟩
    rw [unify_eq_some_iff_isLUB]
    exact (isLUB_pair_step (isLUB_of_unify_eq_some hv)).mpr h

/-- Unification is associative, with failure propagating: both
associations compute the least upper bound of all three elements. -/
theorem unify_assoc (a b c : α) :
    (unify a b).bind (unify · c) = (unify b c).bind (unify a ·) := by
  have hset : ({b, c, a} : Set α) = {a, b, c} := by
    ext x; simp [Set.mem_insert_iff]; tauto
  have hcomm : (unify b c).bind (unify a ·) = (unify b c).bind (unify · a) := by
    apply congrArg
    funext v
    exact unify_comm a v
  apply Option.ext
  intro u
  rw [hcomm, bind_unify_left_eq_some_iff, bind_unify_left_eq_some_iff, hset]

/-- Unification is monotone where defined: shrinking both inputs
preserves success and shrinks the output. -/
theorem unify_mono {a₁ a₂ b₁ b₂ u₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (h₂ : unify a₂ b₂ = some u₂) : ∃ u₁, unify a₁ b₁ = some u₁ ∧ u₁ ≤ u₂ := by
  have hlub := isLUB_of_unify_eq_some h₂
  have hub : u₂ ∈ upperBounds ({a₁, b₁} : Set α) :=
    mem_upperBounds_pair.mpr
      ⟨ha.trans (hlub.1 (Set.mem_insert _ _)),
       hb.trans (hlub.1 (Set.mem_insert_of_mem _ rfl))⟩
  obtain ⟨u₁, hu₁⟩ :=
    Option.isSome_iff_exists.mp (isSome_unify_of_bddAbove ⟨u₂, hub⟩)
  exact ⟨u₁, hu₁, (isLUB_of_unify_eq_some hu₁).2 hub⟩

/-! ### Pointwise unification on Pi types -/

section Pi

variable {F : Type*} {S : F → Type*} [∀ t, PartialOrder (S t)]
  [∀ t, PartialUnify (S t)] [Fintype F]

instance : PartialUnify ((t : F) → S t) where
  unify f g :=
    if h : ∀ t, (unify (f t) (g t)).isSome then
      some (λ t => (unify (f t) (g t)).get (h t))
    else none
  isLUB_of_unify_eq_some := by
    intro f g u hu
    by_cases h : ∀ t, (unify (f t) (g t)).isSome
    · rw [dif_pos h, Option.some_inj] at hu
      rw [isLUB_pi]
      intro t
      rw [Set.image_pair]
      have : unify (f t) (g t) = some (u t) := by
        rw [← hu]; exact (Option.some_get (h t)).symm
      exact isLUB_of_unify_eq_some this
    · rw [dif_neg h] at hu
      exact absurd hu (by simp)
  isSome_unify_of_bddAbove := by
    intro f g hbdd
    obtain ⟨w, hw⟩ := hbdd
    have hfw : f ≤ w := hw (Set.mem_insert _ _)
    have hgw : g ≤ w := hw (Set.mem_insert_of_mem _ rfl)
    have h : ∀ t, (unify (f t) (g t)).isSome := λ t =>
      isSome_unify_of_bddAbove ⟨w t, mem_upperBounds_pair.mpr ⟨hfw t, hgw t⟩⟩
    rw [dif_pos h]
    rfl

end Pi

end PartialUnify

/-! ### Compatibility

The consistency relation of unification: two elements are compatible when
they have a common upper bound — equivalently (`compat_iff_isSome_unify`),
when they unify. On feature carriers this is the agreement relation
([carpenter-1992]; [shieber-1986]'s "compatible"). -/

section Compat

variable {α β : Type*}

/-- Two elements are compatible: bounded above — the consistency relation
    of unification. An `abbrev` so the `BddAbove` API applies directly. -/
abbrev Compat [Preorder α] (a b : α) : Prop :=
  BddAbove ({a, b} : Set α)

/-- A common upper bound witnesses compatibility. -/
theorem Compat.of_le [Preorder α] {a b u : α} (ha : a ≤ u) (hb : b ≤ u) :
    Compat a b :=
  ⟨u, PartialUnify.mem_upperBounds_pair.mpr ⟨ha, hb⟩⟩

theorem Compat.symm [Preorder α] {a b : α} (h : Compat a b) : Compat b a := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨ha, hb⟩ := PartialUnify.mem_upperBounds_pair.mp hu
  exact Compat.of_le hb ha

/-- Compatibility persists downward. -/
theorem Compat.mono [Preorder α] {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d)
    (h : Compat b d) : Compat a c := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨hb, hd⟩ := PartialUnify.mem_upperBounds_pair.mp hu
  exact Compat.of_le (h₁.trans hb) (h₂.trans hd)

theorem compat_self [Preorder α] (a : α) : Compat a a :=
  Compat.of_le le_rfl le_rfl

/-- `⊥` is a wildcard: compatible with everything. -/
theorem bot_compat [Preorder α] [OrderBot α] (a : α) : Compat (⊥ : α) a :=
  Compat.of_le bot_le le_rfl

theorem compat_bot [Preorder α] [OrderBot α] (a : α) : Compat a (⊥ : α) :=
  Compat.of_le le_rfl bot_le

/-- Monotone maps preserve compatibility. -/
theorem Monotone.compat [Preorder α] [Preorder β] {f : α → β}
    (hf : Monotone f) {a b : α} (h : Compat a b) : Compat (f a) (f b) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨ha, hb⟩ := PartialUnify.mem_upperBounds_pair.mp hu
  exact Compat.of_le (hf ha) (hf hb)

/-- Compatibility is decided by unification. -/
theorem compat_iff_isSome_unify [PartialOrder α] [PartialUnify α] {a b : α} :
    Compat a b ↔ (PartialUnify.unify a b).isSome :=
  PartialUnify.isSome_unify_iff_bddAbove.symm

instance [PartialOrder α] [PartialUnify α] (a b : α) : Decidable (Compat a b) :=
  decidable_of_iff _ PartialUnify.isSome_unify_iff_bddAbove

end Compat

/-! ### Joining point sets -/

namespace Set

variable {α : Type*} [PartialOrder α] {s t : Set α} {c : α}

/-- The least upper bounds of pairs drawn from two sets — the
partial-join analogue of `Set.sups`, keeping exactly the bounded pairs:
unification of description sets in [carpenter-1992]'s setting. -/
def lubs (s t : Set α) : Set α :=
  {c | ∃ a ∈ s, ∃ b ∈ t, IsLUB {a, b} c}

@[simp] theorem mem_lubs : c ∈ s.lubs t ↔ ∃ a ∈ s, ∃ b ∈ t, IsLUB {a, b} c :=
  Iff.rfl

theorem lubs_comm (s t : Set α) : s.lubs t = t.lubs s := by
  ext c
  constructor <;> rintro ⟨a, ha, b, hb, h⟩ <;>
    exact ⟨b, hb, a, ha, pair_comm a b ▸ h⟩

/-- A set of local units is a right identity for `lubs`: every element
dominates a member of `t`, and members of `t` sit below anything they
are compatible with — the set-level face of `⊥` as identity. -/
theorem lubs_eq_left (h₁ : ∀ a : α, ∃ b ∈ t, b ≤ a)
    (h₂ : ∀ a : α, ∀ b ∈ t, Compat a b → b ≤ a) : s.lubs t = s := by
  ext c
  constructor
  · rintro ⟨a, ha, b, hb, hub, hleast⟩
    have hca : c = a := le_antisymm
      (hleast (PartialUnify.mem_upperBounds_pair.mpr ⟨le_rfl, h₂ a b hb ⟨c, hub⟩⟩))
      (hub (mem_insert _ _))
    exact hca ▸ ha
  · intro hc
    obtain ⟨b, hb, hbc⟩ := h₁ c
    exact ⟨c, hc, b, hb, PartialUnify.mem_upperBounds_pair.mpr ⟨le_rfl, hbc⟩,
      fun _ hu => hu (mem_insert _ _)⟩

/-- Under pairwise bounded completeness, upper closure sends `lubs` to
the join: a point bounds a pairwise join iff it bounds a point of each
set. -/
theorem upperClosure_lubs
    (H : ∀ a b : α, Compat a b → ∃ c, IsLUB ({a, b} : Set α) c) (s t : Set α) :
    upperClosure (s.lubs t) = upperClosure s ⊔ upperClosure t := by
  ext x
  simp only [SetLike.mem_coe, UpperSet.mem_sup_iff, mem_upperClosure, mem_lubs]
  constructor
  · rintro ⟨c, ⟨a, ha, b, hb, hab⟩, hcx⟩
    obtain ⟨hac, hbc⟩ := PartialUnify.mem_upperBounds_pair.mp hab.1
    exact ⟨⟨a, ha, hac.trans hcx⟩, b, hb, hbc.trans hcx⟩
  · rintro ⟨⟨a, ha, hax⟩, b, hb, hbx⟩
    obtain ⟨c, hc⟩ := H a b ⟨x, PartialUnify.mem_upperBounds_pair.mpr ⟨hax, hbx⟩⟩
    exact ⟨c, ⟨a, ha, b, hb, hc⟩,
      hc.2 (PartialUnify.mem_upperBounds_pair.mpr ⟨hax, hbx⟩)⟩

private theorem mem_lubs_left_iff
    (H : ∀ a b : α, Compat a b → ∃ c, IsLUB ({a, b} : Set α) c) :
    ∀ (s t u : Set α) (c : α),
      c ∈ (s.lubs t).lubs u ↔ ∃ a ∈ s, ∃ b ∈ t, ∃ w ∈ u, IsLUB {a, b, w} c := by
  intro s t u c
  constructor
  · rintro ⟨v, ⟨a, ha, b, hb, hab⟩, w, hw, hvw⟩
    exact ⟨a, ha, b, hb, w, hw, (PartialUnify.isLUB_pair_step hab).mp hvw⟩
  · rintro ⟨a, ha, b, hb, w, hw, h⟩
    obtain ⟨v, hv⟩ := H a b (Compat.of_le (h.1 (mem_insert _ _))
      (h.1 (mem_insert_of_mem _ (mem_insert _ _))))
    exact ⟨v, ⟨a, ha, b, hb, hv⟩, w, hw, (PartialUnify.isLUB_pair_step hv).mpr h⟩

/-- Under pairwise bounded completeness — every bounded pair has a join —
joining point sets is associative. -/
theorem lubs_assoc (H : ∀ a b : α, Compat a b → ∃ c, IsLUB ({a, b} : Set α) c)
    (s t u : Set α) : (s.lubs t).lubs u = s.lubs (t.lubs u) := by
  have hset : ∀ b w a : α, ({b, w, a} : Set α) = {a, b, w} := by
    intro b w a; ext x; simp [mem_insert_iff]; tauto
  ext c
  rw [mem_lubs_left_iff H, lubs_comm s (t.lubs u), mem_lubs_left_iff H]
  constructor
  · rintro ⟨a, ha, b, hb, w, hw, h⟩
    exact ⟨b, hb, w, hw, a, ha, (hset b w a).symm ▸ h⟩
  · rintro ⟨b, hb, w, hw, a, ha, h⟩
    exact ⟨a, ha, b, hb, w, hw, hset b w a ▸ h⟩

end Set
