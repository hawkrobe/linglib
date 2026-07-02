import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Defs.Unbundled

/-!
# Bundled decidable total preorders

A `TotalPreorder α` bundles a relation with mathlib's unbundled relation-class
laws (`IsPreorder`, `Std.Total`) and decidability. Bundled — unlike a
`Preorder` instance — because consumers quantify over orderings of a fixed
carrier: plausibility frames rank worlds ([lewis-1973] comparative
similarity), and metalinguistic common grounds are *sets* of ordering-world
pairs ranking semantic interpretations ([rudolph-kocurek-2024]), so orderings
must be first-class data.

## Main declarations

* `TotalPreorder` — the bundle, with `lt`, `equiv`, and `ofBool` (construction
  from a Boolean table, for finite models).
* `IsMaximal`, `AcceptedAt` — top-ranked points, and truth of a predicate
  throughout them (Stalnaker-style acceptance on a plausibility frame).

## Implementation notes

The canonical form of an ordering-as-data is the model-theoretic one: a
`Language.order.Structure` modeling the total-preorder theory
(`Core/Logic/FirstOrder/TotalPreorder.lean`, where `toStructure`/`ofModel`
exchange the two presentations). This bundle is that object's decidable,
proof-transparent working presentation. Mathlib has no bundled
order-on-a-carrier object (its `Preord` bundles a *type* with one order);
among term-level presentations, a raw relation with unbundled relation
classes — the founding used here — beats `extends Preorder α`, which would
transport the `Preorder` API but makes `lt` an opaque field where consumers
need the transparent `le a b ∧ ¬ le b a` for `decide` and destructuring.
Same-rank equivalence is mathlib's `AntisymmRel` rather than a new
definition. -/

namespace Core.Order

/-- A bundled total preorder. Laws are carried as mathlib's unbundled relation
classes, registered as instances; decidability is not part of the frame — it
enters locally where finite models compute (`decidableLE_ofBool`). -/
structure TotalPreorder (α : Type*) where
  /-- The preorder relation: `le a b` means a is ranked no higher than b. -/
  le : α → α → Prop
  /-- Reflexivity and transitivity, as mathlib's unbundled relation class. -/
  isPreorder : IsPreorder α le
  /-- Totality, as mathlib's unbundled relation class. -/
  total : Std.Total le

attribute [instance] TotalPreorder.isPreorder TotalPreorder.total

namespace TotalPreorder

variable {α : Type*} (ord : TotalPreorder α)

/-- Reflexivity (mathlib's `Std.Refl`, field-style). -/
theorem le_refl (a : α) : ord.le a a := Std.Refl.refl a

/-- Transitivity (mathlib's `IsTrans`, field-style). -/
theorem le_trans (a b c : α) : ord.le a b → ord.le b c → ord.le a c :=
  IsTrans.trans a b c

/-- Totality (mathlib's `Std.Total`, field-style). -/
theorem le_total (a b : α) : ord.le a b ∨ ord.le b a := Std.Total.total a b

/-- Strict ordering: a is ranked strictly below b. -/
def lt (a b : α) : Prop := ord.le a b ∧ ¬ ord.le b a

instance decRelLt [DecidableRel ord.le] : DecidableRel ord.lt := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

theorem lt_of_le_of_lt {a b c : α} (h : ord.le a b) (h' : ord.lt b c) :
    ord.lt a c :=
  ⟨ord.le_trans a b c h h'.1, fun hca => h'.2 (ord.le_trans c a b hca h)⟩

theorem lt_of_lt_of_le {a b c : α} (h : ord.lt a b) (h' : ord.le b c) :
    ord.lt a c :=
  ⟨ord.le_trans a b c h.1 h', fun hca => h.2 (ord.le_trans b c a h' hca)⟩

theorem lt_irrefl (a : α) : ¬ ord.lt a a := fun h => h.2 (ord.le_refl a)

/-- Every nonempty finset has a greatest element under a total preorder. -/
theorem exists_le_max (S : Finset α) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ s ∈ S, ord.le s m := by
  induction S using Finset.cons_induction with
  | empty => exact absurd hS (by simp)
  | cons x S' hx ih =>
    by_cases hS' : S'.Nonempty
    · obtain ⟨m, hm, hle⟩ := ih hS'
      rcases ord.le_total x m with h | h
      · exact ⟨m, Finset.mem_cons.mpr (Or.inr hm), fun s hs => by
          rcases Finset.mem_cons.mp hs with rfl | hs'
          · exact h
          · exact hle s hs'⟩
      · exact ⟨x, Finset.mem_cons_self x S', fun s hs => by
          rcases Finset.mem_cons.mp hs with rfl | hs'
          · exact ord.le_refl _
          · exact ord.le_trans s m x (hle s hs') h⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hS'
      exact ⟨x, Finset.mem_cons_self x S', fun s hs => by
        simp [hS'] at hs; exact hs ▸ ord.le_refl _⟩

/-- Equivalence: a and b are ranked at the same level — mathlib's
`AntisymmRel` (whose `AntisymmRel.setoid` is the level-quotient). -/
abbrev equiv (a b : α) : Prop := AntisymmRel ord.le a b

instance decRelEquiv [DecidableRel ord.le] : DecidableRel ord.equiv := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- ¬(a < b) → b ≤ a (by totality). -/
theorem le_of_not_lt {a b : α} (h : ¬ ord.lt a b) : ord.le b a :=
  Classical.byContradiction fun hba => h ⟨(ord.le_total a b).resolve_right hba, hba⟩

/-- Construct a `TotalPreorder` from a Bool-valued table — the convenient
form for concrete finite models defined by pattern matching. -/
def ofBool {α : Type*} (f : α → α → Bool)
    (h_refl : ∀ a, f a a = true)
    (h_trans : ∀ a b c, f a b = true → f b c = true → f a c = true)
    (h_total : ∀ a b, f a b = true ∨ f b a = true) :
    TotalPreorder α where
  le a b := f a b = true
  isPreorder := { refl := h_refl, trans := h_trans }
  total := ⟨h_total⟩

/-- Table-built orderings are decidable — the local decidability finite
models recover in one instance. -/
instance decidableLE_ofBool {α : Type*} (f : α → α → Bool) (h₁ h₂ h₃) :
    DecidableRel (ofBool f h₁ h₂ h₃).le := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))

/-- A top-ranked point: no point is ranked strictly above it. -/
def IsMaximal (x : α) : Prop := ∀ y, ¬ ord.lt x y

instance [Fintype α] [DecidableRel ord.le] (x : α) :
    Decidable (ord.IsMaximal x) := by
  unfold IsMaximal; infer_instance

/-- Acceptance: a predicate holds throughout the top-ranked points. -/
def AcceptedAt (A : α → Prop) : Prop := ∀ x, ord.IsMaximal x → A x

instance [Fintype α] [DecidableRel ord.le] (A : α → Prop) [DecidablePred A] :
    Decidable (ord.AcceptedAt A) := by
  unfold AcceptedAt; infer_instance

end TotalPreorder

end Core.Order
