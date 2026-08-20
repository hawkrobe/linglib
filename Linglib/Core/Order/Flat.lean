import Mathlib.Order.OmegaCompletePartialOrder
import Linglib.Core.Order.PartialUnify

/-!
# The flat order

`Flat α` is `Option α` with the flat order: `⊥` below everything, distinct
values incomparable. It is the lift of the discrete order on `α` — the order
of partial values under extension — and is mathlib's order on `Part α`
carried on its decidable twin `Option` (`le_iff_ofOption_le`), where it
supports `DecidableEq`, `DecidableLE`, `#eval`, and constructor
pattern-matching. "Flat domain" is the domain-theory name for this poset
([winskel-1993]; the `flat` class of Isabelle/HOLCF).

The flat order is bounded-complete but not a lattice: meets are total
(`SemilatticeInf`), joins partial (`PartialUnify`). It is ω-complete
(`OmegaCompletePartialOrder`), every chain being eventually constant.
Linguistically it is one atomic feature slot, ordered by [shieber-1986]'s and
[carpenter-1992]'s subsumption; `Flat Bool` is the knowledge order of Kleene
three-valued logic. Feature bundles arise via the `Pi` `PartialUnify`
instance, with `Compat` as consistency.

The order skeleton follows the `WithBot` mold (`Mathlib/Order/TypeTags.lean`,
`Mathlib/Order/WithBot.lean`) and is an `[UPSTREAM]` candidate for
`Mathlib/Order/Flat.lean`, coexisting with the namespaced `Module.Flat` and
`ConvexCone.Flat`. The `PartialUnify` instance and `compat_iff` stay here.

## Main declarations

* `Flat` — the order-carrying alias, with coercion `↑ : α → Flat α`, and
  `PartialOrder`, `OrderBot`, `SemilatticeInf`, `OmegaCompletePartialOrder`,
  and `PartialUnify` instances
* `Flat.coe_le_coe`, `Flat.not_coe_le_bot` — the order, characterized
* `Flat.or` — left-biased total merge, with `le_or_left`/`or_le`
* `Flat.ωSup_mem_range` — chains attain their supremum (the domain has height ≤ 2)
* `Flat.ωScottContinuous_of_monotone` — monotone maps out of `Flat` are continuous
* `Flat.liftEquiv` — the free-domain universal property: functions `α → D` are
  exactly strict continuous maps `Flat α →𝒄 D`
* `Flat.compat_iff` — slot compatibility (`Compat`), characterized
* `Flat.unify_distinct_eq_none` — distinct atoms do not unify (the
  non-distributivity witness)

## TODO

The free-domain universal property is now `liftEquiv` (with its enabling lemma
`ωScottContinuous_of_monotone`). The remaining domain-theoretic program:

* **Categorical freeness.** Package `liftEquiv` as a free–forgetful adjunction
  between `Type` and the pointed `ωCPO` category — `Flat ⊣ U` (template:
  mathlib's `latToBddLatForgetAdjunction`, the free bounded lattice via
  `WithBot`).
* **Lifting monad.** Give `Flat` (= `Option`) its ω-CPO monad structure — the
  partiality/lifting monad — whose Kleisli arrows `α → Flat β` are partial
  continuous functions; `PartialUnify.unify` is one, which is why it composes
  through `Option.bind` (`unify_assoc`). (mathlib has this for `Part`.)
* **Algebraicity / bounded-completeness.** Every element of `Flat α` is compact,
  making it an algebraic (finite-height) bounded-complete domain — the
  Scott-domain packaging of the partial join `PartialUnify` provides.
* **Three-valued logic.** `Flat Bool` is the knowledge order of Kleene
  three-valued logic; the strong-Kleene connectives are exactly its continuous
  maps. Connects this substrate to the trivalence/presupposition layer.
* An inductive `Flat.LT` in the `WithBot.LT` mold, for upstreaming.
-/

/-- `Flat α` is `Option α` carrying the flat information order: `⊥` below
everything, distinct values incomparable. A `def`, not an `abbrev`, so the
order instances do not leak onto bare `Option`. -/
def Flat (α : Type*) := Option α

namespace Flat

variable {α : Type*} {a b : α} {x y z : Flat α}

/-- The canonical map from `α` into `Flat α`. -/
@[coe, match_pattern] def some : α → Flat α :=
  Option.some

instance coe : Coe α (Flat α) :=
  ⟨some⟩

instance bot : Bot (Flat α) :=
  ⟨none⟩

instance inhabited : Inhabited (Flat α) :=
  ⟨⊥⟩

instance [DecidableEq α] : DecidableEq (Flat α) :=
  inferInstanceAs (DecidableEq (Option α))

instance [BEq α] : BEq (Flat α) :=
  inferInstanceAs (BEq (Option α))

instance [BEq α] [LawfulBEq α] : LawfulBEq (Flat α) :=
  inferInstanceAs (LawfulBEq (Option α))

instance [Repr α] : Repr (Flat α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | Option.some a => "↑" ++ repr a⟩

theorem coe_injective : Function.Injective ((↑) : α → Flat α) :=
  Option.some_injective _

@[simp, norm_cast] theorem coe_inj : (a : Flat α) = b ↔ a = b :=
  Option.some_inj

theorem none_eq_bot : (none : Flat α) = (⊥ : Flat α) := rfl

theorem some_eq_coe (a : α) : (Option.some a : Flat α) = (↑a : Flat α) := rfl

@[simp] theorem bot_ne_coe : ⊥ ≠ (a : Flat α) := nofun

@[simp] theorem coe_ne_bot : (a : Flat α) ≠ ⊥ := nofun

/-- Recursor for `Flat` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recBotCoe {C : Flat α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ x : Flat α, C x
  | ⊥ => bot
  | (a : α) => coe a

@[simp] theorem recBotCoe_bot {C : Flat α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d := rfl

@[simp] theorem recBotCoe_coe {C : Flat α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x := rfl

theorem ne_bot_iff_exists : x ≠ ⊥ ↔ ∃ a : α, x = ↑a := by
  cases x <;> simp

/-! ### The flat order -/

/-- Auxiliary definition for the order on `Flat`. -/
@[mk_iff le_def_aux]
protected inductive LE : Flat α → Flat α → Prop
  | protected bot_le (x : Flat α) : Flat.LE ⊥ x
  | protected refl (a : α) : Flat.LE ↑a ↑a

/-- The flat order on `Flat α`, defined by `⊥ ≤ x` and `↑a ≤ ↑a`. The
definition as an inductive predicate follows `WithBot.LE`; it cannot be
accidentally unfolded too far. -/
instance (priority := 10) instLE : LE (Flat α) where le := Flat.LE

lemma le_def : x ≤ y ↔ x = ⊥ ∨ ∃ a : α, x = ↑a ∧ y = ↑a := by
  rw [show (x ≤ y) = Flat.LE x y from rfl, le_def_aux]

@[simp, norm_cast] theorem coe_le_coe : (a : Flat α) ≤ b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .refl a⟩

@[simp] theorem not_coe_le_bot (a : α) : ¬(a : Flat α) ≤ ⊥ :=
  fun h => by cases h

instance : OrderBot (Flat α) where
  bot_le := Flat.LE.bot_le

instance : PartialOrder (Flat α) where
  le_refl x := by cases x with
    | bot => exact .bot_le _
    | coe a => exact .refl a
  le_trans x y z hxy hyz := by
    cases hxy with
    | bot_le => exact .bot_le _
    | refl => exact hyz
  le_antisymm x y hxy hyx := by
    cases hxy with
    | bot_le => cases hyx with | bot_le => rfl
    | refl => rfl

@[simp] theorem le_bot_iff : x ≤ ⊥ ↔ x = ⊥ := by
  cases x <;> simp

theorem coe_le_iff : (a : Flat α) ≤ y ↔ y = ↑a :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .refl a⟩

theorem le_coe_iff : x ≤ (b : Flat α) ↔ x = ⊥ ∨ x = ↑b := by
  cases x <;> simp

instance [DecidableEq α] : DecidableLE (Flat α)
  | ⊥, _ => isTrue (.bot_le _)
  | (a : α), ⊥ => isFalse (not_coe_le_bot a)
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe

/-- Definedness persists up the flat order. -/
theorem ne_bot_of_le (h : x ≤ y) (hx : x ≠ ⊥) : y ≠ ⊥ :=
  fun hy => hx (le_bot_iff.mp (hy ▸ h))

/-- A flat inequality with no definedness gain is an equality. -/
theorem eq_of_le (h : x ≤ y) (hyx : y ≠ ⊥ → x ≠ ⊥) : x = y := by
  cases h with
  | bot_le y =>
    cases y with
    | bot => rfl
    | coe a => exact absurd (hyx coe_ne_bot) (by simp)
  | refl => rfl

/-- The flat order is `Part`'s order, along `Part.ofOption`. -/
theorem le_iff_ofOption_le :
    x ≤ y ↔ Part.ofOption (x : Option α) ≤ Part.ofOption (y : Option α) := by
  constructor
  · rintro (_ | _)
    · exact fun i hi => absurd (Part.mem_ofOption.mp hi) nofun
    · exact le_rfl
  · intro h
    cases x with
    | bot => exact bot_le
    | coe a =>
      obtain rfl : y = ↑a :=
        Part.mem_ofOption.mp (h a (Part.mem_ofOption.mpr rfl))
      exact le_rfl

/-! ### Left-biased merge -/

/-- The left-biased total merge of two slots, keeping the first committed
value; the total companion of the partial join `Flat.unify`. -/
protected def or (x y : Flat α) : Flat α :=
  Option.or x y

@[simp] theorem bot_or (y : Flat α) : (⊥ : Flat α).or y = y := rfl

@[simp] theorem coe_or (a : α) (y : Flat α) : (↑a : Flat α).or y = ↑a := rfl

@[simp] theorem or_bot (x : Flat α) : x.or ⊥ = x := by cases x <;> rfl

theorem or_assoc (x y z : Flat α) : (x.or y).or z = x.or (y.or z) :=
  Option.or_assoc ..

theorem le_or_left (x y : Flat α) : x ≤ x.or y := by
  cases x <;> simp

theorem or_le (hx : x ≤ z) (hy : y ≤ z) : x.or y ≤ z := by
  cases x with
  | bot => exact hy
  | coe a => exact hx

/-! ### Meets -/

/-- The meet of two slots is their agreement, or `⊥` — the *generalization*
(anti-unification) of the two, order-dual to the partial join `PartialUnify`. -/
protected def inf [DecidableEq α] (x y : Flat α) : Flat α :=
  if x = y then x else ⊥

instance [DecidableEq α] : SemilatticeInf (Flat α) where
  inf := Flat.inf
  inf_le_left x y := by unfold Flat.inf; split <;> simp
  inf_le_right x y := by unfold Flat.inf; split <;> simp_all
  le_inf x y z hxy hxz := by
    cases hxy with
    | bot_le => exact bot_le
    | refl a =>
      obtain rfl : z = ↑a := by cases hxz; rfl
      simp [Flat.inf]

/-! ### The flat domain is ω-complete

A monotone chain in the flat order is eventually constant — `⊥` until it
(optionally) commits to a single value, then constant — so it has a
supremum. This is the *flat domain*, the canonical nontrivial example of an
`OmegaCompletePartialOrder`. -/

section OmegaCPO
open OmegaCompletePartialOrder
  (Chain ωScottContinuous ContinuousHom ωSup le_ωSup isLUB_range_ωSup)
open Classical

/-- The supremum of a chain in the flat order: the committed value if the chain
ever leaves `⊥`, and `⊥` otherwise. The implementation behind the `ωSup`
projection (cf. `Prod.ωSupImpl`); state results about `ωSup`. -/
private noncomputable def ωSupImpl (c : Chain (Flat α)) : Flat α :=
  if h : ∃ i, c i ≠ ⊥ then c (Nat.find h) else ⊥

private theorem ωSupImpl_isLUB (c : Chain (Flat α)) :
    IsLUB (Set.range c) (ωSupImpl c) := by
  constructor
  · rintro _ ⟨j, rfl⟩
    unfold ωSupImpl
    split
    · next h =>
      cases hj : c j with
      | bot => exact bot_le
      | coe a =>
        obtain ⟨b, hb⟩ := ne_bot_iff_exists.mp (Nat.find_spec h)
        have hmono : c (Nat.find h) ≤ c j :=
          (OrderHomClass.mono c) (Nat.find_min' h (by simp [hj]))
        rw [hj, hb, coe_le_coe] at hmono
        rw [hb, hmono]
    · next h =>
      push Not at h
      exact (h j).le
  · intro u hu
    unfold ωSupImpl
    split
    · next h => exact hu (Set.mem_range_self (Nat.find h))
    · exact bot_le

/-- The flat domain is an `OmegaCompletePartialOrder`: chains are eventually
constant, so their suprema are the eventual value (or `⊥`). -/
noncomputable instance : OmegaCompletePartialOrder (Flat α) where
  ωSup := ωSupImpl
  le_ωSup c i := (ωSupImpl_isLUB c).1 (Set.mem_range_self i)
  ωSup_le c x hub := (ωSupImpl_isLUB c).2 (by rintro _ ⟨i, rfl⟩; exact hub i)

/-- Chains in the flat domain attain their supremum — `ωSup c` is some `c i`:
the domain has height ≤ 2. -/
theorem ωSup_mem_range (c : Chain (Flat α)) : ωSup c ∈ Set.range c := by
  show ωSupImpl c ∈ Set.range c
  unfold ωSupImpl
  split
  · next h => exact ⟨Nat.find h, rfl⟩
  · next h =>
    push Not at h
    exact ⟨0, h 0⟩

/-- Every monotone map out of the flat domain is `ωScottContinuous`: chains
attain their suprema (`ωSup_mem_range`), so continuity is automatic. This is
the key fact behind the universal property `liftEquiv`. -/
theorem ωScottContinuous_of_monotone {D : Type*} [OmegaCompletePartialOrder D]
    {f : Flat α → D} (hf : Monotone f) : ωScottContinuous f := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨hf, fun c => ?_⟩
  refine IsLUB.unique ?_ (isLUB_range_ωSup _)
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hf (le_ωSup c i)
  · obtain ⟨k, hk⟩ := ωSup_mem_range c
    rw [← hk]
    exact hu ⟨k, rfl⟩

/-- The extension of `g : α → D` to the flat domain by `⊥ ↦ ⊥`. -/
private def liftFun {D : Type*} [Bot D] (g : α → D) : Flat α → D :=
  recBotCoe ⊥ g

private theorem liftFun_monotone {D : Type*} [Preorder D] [OrderBot D]
    (g : α → D) : Monotone (liftFun g) := by
  intro x y hxy
  cases hxy with
  | bot_le => exact bot_le
  | refl => exact le_rfl

/-- The flat domain is free: functions `α → D` into a pointed domain are
exactly the strict continuous maps `Flat α →𝒄 D`. The forward map extends by
`⊥ ↦ ⊥`, continuous by `ωScottContinuous_of_monotone`; the inverse
precomposes with `↑`. -/
noncomputable def liftEquiv {D : Type*} [OmegaCompletePartialOrder D] [OrderBot D] :
    (α → D) ≃ {f : Flat α →𝒄 D // f ⊥ = ⊥} where
  toFun g := ⟨ContinuousHom.ofFun (liftFun g)
    (ωScottContinuous_of_monotone (liftFun_monotone g)), rfl⟩
  invFun f a := f.1 ↑a
  left_inv g := by funext a; rfl
  right_inv := by
    rintro ⟨f, hf⟩
    refine Subtype.ext (DFunLike.ext _ _ ?_)
    intro x
    cases x with
    | bot => exact hf.symm
    | coe a => rfl

end OmegaCPO

/-! ### Unification -/

/-- Unification of two slots merges equal commitments, treats `⊥` as
identity, and fails on distinct commitments. -/
protected def unify [DecidableEq α] (x y : Flat α) : Option (Flat α) :=
  match x, y with
  | ⊥, y => Option.some y
  | (a : α), ⊥ => Option.some ↑a
  | (a : α), (b : α) => if a = b then Option.some ↑a else Option.none

private theorem unify_coe_coe [DecidableEq α] (a b : α) :
    Flat.unify (↑a : Flat α) ↑b = if a = b then Option.some ↑a else Option.none :=
  rfl

instance [DecidableEq α] : PartialUnify (Flat α) where
  unify := Flat.unify
  isLUB_of_unify_eq_some := by
    intro x y z h
    match x, y with
    | ⊥, y =>
      obtain rfl : y = z := Option.some.inj h
      exact ⟨PartialUnify.mem_upperBounds_pair.mpr ⟨bot_le, le_rfl⟩,
        fun u hu => (PartialUnify.mem_upperBounds_pair.mp hu).2⟩
    | (a : α), ⊥ =>
      obtain rfl : (↑a : Flat α) = z := Option.some.inj h
      exact ⟨PartialUnify.mem_upperBounds_pair.mpr ⟨le_rfl, bot_le⟩,
        fun u hu => (PartialUnify.mem_upperBounds_pair.mp hu).1⟩
    | (a : α), (b : α) =>
      rw [unify_coe_coe] at h
      split at h
      · next hab =>
        subst hab
        obtain rfl : (↑a : Flat α) = z := Option.some.inj h
        rw [Set.pair_eq_singleton]
        exact isLUB_singleton
      · exact absurd h.symm (Option.some_ne_none z)
  isSome_unify_of_bddAbove := by
    intro x y hbdd
    obtain ⟨u, hu⟩ := hbdd
    obtain ⟨hxu, hyu⟩ := PartialUnify.mem_upperBounds_pair.mp hu
    match x, y with
    | ⊥, y => exact rfl
    | (a : α), ⊥ => exact rfl
    | (a : α), (b : α) =>
      obtain rfl : u = ↑a := coe_le_iff.mp hxu
      obtain rfl : a = b := coe_inj.mp (coe_le_iff.mp hyu)
      show (Flat.unify (↑a : Flat α) ↑a).isSome
      rw [unify_coe_coe, if_pos rfl]
      rfl

/-- Two slots are compatible exactly when their committed values coincide;
an uncommitted slot is a wildcard. -/
theorem compat_iff [DecidableEq α] :
    Compat x y ↔ ∀ a : α, x = ↑a → ∀ b : α, y = ↑b → a = b := by
  rw [compat_iff_isSome_unify]
  show (Flat.unify x y).isSome = true ↔ _
  match x, y with
  | ⊥, y => exact iff_of_true rfl (fun a ha => absurd ha bot_ne_coe)
  | (a : α), ⊥ => exact iff_of_true rfl (fun _ _ b hb => absurd hb bot_ne_coe)
  | (a : α), (b : α) =>
    rw [unify_coe_coe]
    by_cases hab : a = b
    · subst hab
      exact iff_of_true (by rw [if_pos rfl]; rfl)
        (fun a' ha' b' hb' => (coe_inj.mp ha').symm.trans (coe_inj.mp hb'))
    · rw [if_neg hab]
      exact iff_of_false nofun (fun h => hab (h a rfl b rfl))

/-- On compatible slots, unification is the priority union: agreeing
commitments collapse and `⊥` defers, so the biased and unbiased merges
coincide. -/
theorem unify_eq_some_or_of_compat [DecidableEq α] {x y : Flat α}
    (h : Compat x y) : PartialUnify.unify x y = Option.some (x.or y) := by
  match x, y with
  | ⊥, y => rfl
  | (a : α), ⊥ => rfl
  | (a : α), (b : α) =>
    obtain rfl : a = b := compat_iff.mp h a rfl b rfl
    show Flat.unify (↑a : Flat α) ↑a = _
    rw [unify_coe_coe, if_pos rfl]
    rfl

/-! ### Non-distributivity

The flat order is not distributive: three distinct atoms (with a top
adjoined) form the diamond M₃ — [carpenter-1992] takes subsumption orders
to be neither distributive nor modular in general. `Flat` carries only the
partial join (`PartialUnify`), so the distributive law cannot even be
*stated* on it directly; `unify_distinct_eq_none` is the witness — distinct
atoms have no upper bound, so the join the law would require is undefined. -/

theorem unify_distinct_eq_none [DecidableEq α] (h : a ≠ b) :
    Flat.unify (↑a : Flat α) ↑b = Option.none := by
  rw [unify_coe_coe]
  exact if_neg h

end Flat
