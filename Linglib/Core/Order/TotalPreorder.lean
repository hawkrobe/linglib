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

/-- A bundled total preorder with decidability. Laws are carried as mathlib's
unbundled relation classes, registered as instances. -/
structure TotalPreorder (α : Type*) where
  /-- The preorder relation: `le a b` means a is ranked no higher than b. -/
  le : α → α → Prop
  /-- Reflexivity and transitivity, as mathlib's unbundled relation class. -/
  isPreorder : IsPreorder α le
  /-- Totality, as mathlib's unbundled relation class. -/
  total : Std.Total le
  /-- Decidability of the ordering. -/
  decRel : DecidableRel le

attribute [instance] TotalPreorder.isPreorder TotalPreorder.total
  TotalPreorder.decRel

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

instance decRelLt : DecidableRel ord.lt := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Equivalence: a and b are ranked at the same level — mathlib's
`AntisymmRel` (whose `AntisymmRel.setoid` is the level-quotient). -/
abbrev equiv (a b : α) : Prop := AntisymmRel ord.le a b

instance decRelEquiv : DecidableRel ord.equiv := fun _ _ =>
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
  decRel _ _ := inferInstance

/-- A top-ranked point: no point is ranked strictly above it. -/
def IsMaximal (x : α) : Prop := ∀ y, ¬ ord.lt x y

instance [Fintype α] (x : α) : Decidable (ord.IsMaximal x) := by
  unfold IsMaximal; infer_instance

/-- Acceptance: a predicate holds throughout the top-ranked points. -/
def AcceptedAt (A : α → Prop) : Prop := ∀ x, ord.IsMaximal x → A x

instance [Fintype α] (A : α → Prop) [DecidablePred A] :
    Decidable (ord.AcceptedAt A) := by
  unfold AcceptedAt; infer_instance

end TotalPreorder

end Core.Order
