/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence.Basic
import Linglib.Core.Data.List.Destutter

/-!
# The Obligatory Contour Principle

The categorical, strict-identity, single-tier OCP: the ban on two *identical* adjacent
autosegments on one tier ([mccarthy-1986]), on a projected tier for `IsCleanOn`
([chandlee-jardine-2019]). As a stringset the constraint is tier-based strictly local
(TSL₂, [heinz-rawal-tanner-2011]), characterised in `OCP`. The
fusion repair `collapse` is mathlib's
`List.destutter (· ≠ ·)` ([goldsmith-1976], [mccarthy-prince-1995]) — a retraction onto
cleanness, input-strictly-local ([chandlee-heinz-2018]); the blocking repair `block` is
antigemination, a guard rather than a retraction ([mccarthy-1986]).

Gradient, similarity-scaled OCP ([frisch-pierrehumbert-broe-2004]) is a different object
and lives in the thresholded-TSL substrate, not here.

## Main definitions

* `OCP.IsClean` / `OCP.IsCleanOn` — OCP-cleanness, flat and on a projected tier.
* `OCP.collapse` — the fusion repair (OCP-merger normal form).
* `OCP.gconcat` — OCP-gluing concatenation `∘`, the OCP quotient monoid's multiplication.
* `OCP.instMonoidSubtypeIsClean` — the OCP quotient monoid on `{l // IsClean l}`.
* `OCP.collapseHom` — the bundled quotient map `FreeMonoid α →* {l // IsClean l}`.
* `OCP.ocpQuotientEquiv` — the OCP quotient `FreeMonoid α ⧸ Con.ker collapseHom ≃* {l // IsClean l}`.
* `OCP.block` — the blocking repair (antigemination guard).

## Main results

* `collapse_eq_destutter` — the fusion repair is `List.destutter`.
* `collapse_clean` / `collapse_eq_self_iff` — `collapse` is the retraction onto `IsClean`.
* `collapse_sublist` — fusion never adds material.
* `collapse_append` / `gconcat_assoc` — `collapse` is the quotient hom and `gconcat` the
  quotient multiplication: `(OCP-clean, gconcat, [])` is the quotient `(List α, ++)/OCP`,
  bundled as `collapseHom` over the `Monoid {l // IsClean l}` instance.
* `block_eq_self` — antigemination: a rule is blocked when it would violate the OCP.
-/

namespace OCP

variable {α β : Type*}

/-! ### The constraint -/

/-- A tier is **OCP-clean** when no adjacent pair is identical. Adjacency-only, so
weaker than `List.Nodup` (`[1, 2, 1]` is clean). -/
def IsClean (xs : List α) : Prop :=
  List.IsChain (· ≠ ·) xs

@[simp] theorem isClean_nil : IsClean ([] : List α) := List.isChain_nil

@[simp] theorem isClean_singleton (x : α) : IsClean [x] := List.isChain_singleton x

@[simp] theorem isClean_cons_cons_iff (x y : α) (rs : List α) :
    IsClean (x :: y :: rs) ↔ x ≠ y ∧ IsClean (y :: rs) := by
  simp only [IsClean, List.isChain_cons_cons]

/-- OCP on the tier projected from `xs` by keeping `p`-elements and reading `proj`
(tier-relativity, [chandlee-jardine-2019]); flat `IsClean` is the `p = ⊤`, `proj = id` case. -/
def IsCleanOn (p : α → Prop) [DecidablePred p] (proj : α → β) (xs : List α) : Prop :=
  IsClean ((xs.filter (fun a => decide (p a))).map proj)

instance decidableIsClean [DecidableEq α] : DecidablePred (IsClean (α := α)) :=
  fun xs => inferInstanceAs (Decidable (List.IsChain (· ≠ ·) xs))

instance decidableIsCleanOn [DecidableEq β] (p : α → Prop)
    [DecidablePred p] (proj : α → β) : DecidablePred (IsCleanOn p proj) :=
  fun _ => inferInstanceAs (Decidable (IsClean _))

section
variable [DecidableEq α]

/-! ### The fusion repair -/

/-- **OCP-merger normal form** (the fusion repair): collapse each maximal run of
identical adjacent elements into one. Fusing identical autosegments returns that same
autosegment, so the payload is unchanged. -/
def collapse (xs : List α) : List α := xs.destutter (· ≠ ·)

theorem collapse_eq_destutter (xs : List α) : collapse xs = xs.destutter (· ≠ ·) := rfl

@[simp] theorem collapse_nil : collapse ([] : List α) = [] := by simp [collapse]

@[simp] theorem collapse_singleton (x : α) : collapse [x] = [x] := by simp [collapse]

/-- `collapse` lands in the OCP-clean set. -/
theorem collapse_clean (xs : List α) : IsClean (collapse xs) :=
  List.isChain_destutter _ xs

/-- `collapse` fixes OCP-clean lists. -/
theorem collapse_idempotent_on_clean {xs : List α} (h : IsClean xs) : collapse xs = xs :=
  List.destutter_of_isChain _ xs h

/-- `collapse` fixes a tier iff it is OCP-clean; with `collapse_clean`, the retraction
onto `IsClean`. -/
@[simp] theorem collapse_eq_self_iff (xs : List α) : collapse xs = xs ↔ IsClean xs :=
  List.destutter_eq_self_iff _ xs

/-- The fusion repair is a retraction onto the OCP-clean set. -/
theorem collapse_idempotent (xs : List α) : collapse (collapse xs) = collapse xs :=
  List.destutter_idem _ _

/-! ### Normal-form lemmas -/

@[simp] theorem collapse_eq_nil {xs : List α} : collapse xs = [] ↔ xs = [] :=
  List.destutter_eq_nil _

/-- Fusion never adds material: the repair output is a sublist of the input. -/
theorem collapse_sublist (xs : List α) : (collapse xs).Sublist xs :=
  List.destutter_sublist _ xs

theorem collapse_length_le (xs : List α) : (collapse xs).length ≤ xs.length :=
  (collapse_sublist xs).length_le

theorem mem_collapse {a : α} {xs : List α} (ha : a ∈ collapse xs) : a ∈ xs :=
  (collapse_sublist xs).mem ha

/-! ### The OCP quotient monoid

The autosegmental free concatenation `⊙` (list `++`, the categorical coproduct) and the
OCP-gluing concatenation `∘` (`gconcat`) are a **free monoid and its quotient**: `collapse`
is the quotient homomorphism and `(OCP-clean, gconcat, [])` is `(List α, ++)/OCP`. This is
the algebraic content of `ocp_not_isMonoidal`: OCP-cleanness is not a `++`-submonoid but is
the `gconcat`-quotient monoid. It is bundled below as `collapseHom : FreeMonoid α →* {l //
IsClean l}`, the quotient map; concretely `{l // IsClean l}` with this `Monoid` is
`FreeMonoid α ⧸ Con.ker collapseHom`. The AR-level lift (links pushed forward along the
run-collapse map) is future work. -/

/-- Collapsing the left operand before appending does not change the result. -/
theorem collapse_append_left (x y : List α) :
    collapse (collapse x ++ y) = collapse (x ++ y) :=
  List.destutter_append_left x y

/-- Collapsing the right operand before appending does not change the result. -/
theorem collapse_append_right (x y : List α) :
    collapse (x ++ collapse y) = collapse (x ++ y) :=
  List.destutter_append_right x y

/-- **The OCP congruence.** `collapse` is a `++`→quotient homomorphism: collapsing each
operand first is harmless. Thus `collapse` descends to the OCP quotient of `(List α, ++)`. -/
theorem collapse_append (x y : List α) :
    collapse (x ++ y) = collapse (collapse x ++ collapse y) :=
  List.destutter_append_destutter x y

/-- **OCP-gluing concatenation** `∘`: concatenate, then merge the new boundary geminate. The
multiplication of the OCP quotient monoid. -/
def gconcat (x y : List α) : List α := collapse (x ++ y)

/-- `gconcat` is associative — the quotient inherits `++`'s associativity through `collapse`. -/
theorem gconcat_assoc (x y z : List α) :
    gconcat (gconcat x y) z = gconcat x (gconcat y z) := by
  simp only [gconcat, collapse_append_left, collapse_append_right, List.append_assoc]

/-- `[]` is a left unit up to `collapse`; on OCP-clean lists a genuine left unit. -/
theorem nil_gconcat (x : List α) : gconcat [] x = collapse x := by simp [gconcat]

/-- `[]` is a right unit up to `collapse`; on OCP-clean lists a genuine right unit. -/
theorem gconcat_nil (x : List α) : gconcat x [] = collapse x := by simp [gconcat]

/-- `gconcat` lands in the OCP-clean set: the quotient is closed under its multiplication. -/
theorem gconcat_clean (x y : List α) : IsClean (gconcat x y) := collapse_clean _

/-- `collapse` carries `(List α, ++)` onto `(OCP-clean, gconcat)`: the quotient-hom equation. -/
theorem collapse_gconcat (x y : List α) :
    collapse (x ++ y) = gconcat (collapse x) (collapse y) := by
  rw [gconcat, ← collapse_append]

/-- `gconcat` outputs are OCP-clean fixed points of `collapse`. -/
theorem collapse_collapse_gconcat (x y : List α) : collapse (gconcat x y) = gconcat x y := by
  rw [gconcat, collapse_idempotent]

/-! ### The bundled quotient monoid -/

instance : Mul {l : List α // IsClean l} := ⟨fun a b => ⟨gconcat a b, gconcat_clean _ _⟩⟩

instance : One {l : List α // IsClean l} := ⟨⟨[], isClean_nil⟩⟩

@[simp] theorem coe_mul (a b : {l : List α // IsClean l}) :
    ((a * b : {l : List α // IsClean l}) : List α) = gconcat a b := rfl

omit [DecidableEq α] in
@[simp] theorem coe_one : ((1 : {l : List α // IsClean l}) : List α) = [] := rfl

/-- The OCP quotient monoid on the OCP-clean subtype: `gconcat` multiplication, `[]` unit. -/
instance : Monoid {l : List α // IsClean l} where
  mul_assoc a b c := Subtype.ext <| by simp [gconcat_assoc]
  one_mul a := Subtype.ext <| by simp [nil_gconcat, collapse_idempotent_on_clean a.2]
  mul_one a := Subtype.ext <| by simp [gconcat_nil, collapse_idempotent_on_clean a.2]

/-- The bundled OCP quotient map. `collapse_append` is morally its `map_mul`: `{l // IsClean
l}` with the `Monoid` instance above is `FreeMonoid α ⧸ Con.ker collapseHom`. -/
def collapseHom : FreeMonoid α →* {l : List α // IsClean l} where
  toFun l := ⟨collapse l.toList, collapse_clean _⟩
  map_one' := Subtype.ext collapse_nil
  map_mul' x y := Subtype.ext <| by simp [FreeMonoid.toList_mul, collapse_gconcat]

/-! ### As a mathlib quotient monoid -/

/-- The **OCP congruence** on the free monoid: the kernel of `collapseHom`. The OCP quotient
monoid is `ocpCon.Quotient` — mathlib's `Con.Quotient`, a `Monoid` for free. -/
def ocpCon : Con (FreeMonoid α) := Con.ker collapseHom

/-- `collapseHom` is surjective: every OCP-clean list is its own collapse. -/
theorem collapseHom_surjective :
    Function.Surjective (collapseHom : FreeMonoid α →* {l : List α // IsClean l}) := fun c =>
  ⟨FreeMonoid.ofList c.1, Subtype.ext (by
    simp only [collapseHom, MonoidHom.coe_mk, OneHom.coe_mk, FreeMonoid.toList_ofList]
    exact collapse_idempotent_on_clean c.2)⟩

/-- **First isomorphism theorem for the OCP quotient.** The abstract quotient monoid
`FreeMonoid α ⧸ OCP` is the concrete OCP-clean model `{l // IsClean l}` ([mccarthy-1986]). -/
noncomputable def ocpQuotientEquiv :
    (ocpCon (α := α)).Quotient ≃* {l : List α // IsClean l} :=
  Con.quotientKerEquivOfSurjective collapseHom collapseHom_surjective

/-! ### The blocking repair -/

variable (rule : List α → List α)

/-- **Blocking** ([mccarthy-1986]'s antigemination): apply `rule` only when it would not
create an OCP violation, else leave the input untouched — a guard preventing a process,
not a retraction repairing its output. -/
def block (xs : List α) : List α :=
  if IsClean (rule xs) then rule xs else xs

theorem block_eq_rule {xs : List α} (hc : IsClean (rule xs)) : block rule xs = rule xs := if_pos hc

/-- Antigemination: the rule fails to apply exactly when it would create an OCP
violation, leaving the input unrepaired (contrast `collapse`). -/
theorem block_eq_self {xs : List α} (hc : ¬ IsClean (rule xs)) : block rule xs = xs := if_neg hc

/-- Blocking never worsens a clean tier. -/
theorem block_isClean {xs : List α} (hx : IsClean xs) : IsClean (block rule xs) := by
  unfold block; split <;> assumption

end

end OCP
