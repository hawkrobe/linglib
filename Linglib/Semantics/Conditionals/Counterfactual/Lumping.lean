import Mathlib.Data.Set.Lattice
import Mathlib.Order.Max

/-!
# Lumping

[kratzer-1989], [kratzer-2012]

Kratzer's situation-semantic notion of *lumping*: a proposition `p` lumps
a proposition `q` in a world `w` when truth of `p` at every part of `w`
forces truth of `q` there. Lumping is the technical glue Kratzer uses to
repair the premise-semantic account of counterfactuals — when an
antecedent is added to a Base Set, every proposition lumped by the
antecedent in the evaluation world comes along, blocking the spurious
counterfactuals that arise when independent true propositions are added
freely (the Paula-paints-a-still-life and zebra-escapes examples in
[kratzer-2012], §5.4.1).

Situations are the elements of a type `S` carrying a preorder, parthood; propositions are
`Set S`, the worlds are the maximal situations (`worlds S`), and persistence is mathlib's
`Monotone`. Possible-worlds semantics is the case of the discrete order (`discreteOrder`),
in which every situation is a world.

## Scope

This file covers [kratzer-2012] §5.3.3 (p. 118): the worlds-only
logical relations (validity, consistency, compatibility, logical
consequence, logical equivalence) and the official lumping definition
that closes the section. The counterfactual machinery of §5.4 — base
sets, the truth conditions for would/might-counterfactuals, and the
formal definitions in §5.4.4 — is out of scope here.

## Architectural notes

- **Lumping is order-theoretic.** `Lumps` uses only the parthood preorder; the logical
  relations additionally quantify over `worlds S`.
- **Logical relations follow Kratzer's set notation literally.** Each
  definition unfolds to the same set-theoretic formula on p. 118
  (`worlds S ⊆ p`, `worlds S ∩ ⋂₀ A ⊆ q`, etc.), so the mathlib `Set`
  and `sInter` APIs apply unchanged.
- **Worlds vs. arbitrary situations.** Kratzer's official definition
  restricts `Lumps p q w` to `w ∈ W`. We define the relation for any
  situation; combine with `IsMax w` for the standard restriction. The
  `Lumps.follows_singleton` bridge below shows how to recover Kratzer's
  worlds-only reading.
-/

namespace Conditionals.Counterfactual

open Set

/-! ## Lumping ([kratzer-2012] §5.3.3, p. 118)

The official text of [kratzer-2012], p. 118:
> For all propositions `p, q ∈ P(S)` and all `w ∈ W`:
> `p` lumps `q` in `w` iff (i) `w ∈ p`. (ii) For all `s ∈ S`,
> if `s ≤ w` and `s ∈ p`, then `s ∈ q`.

The same definition appears informally on p. 114, where footnote 4
credits condition (ii) to Yablo's "local implication". -/

section LumpingCore

variable {S : Type*} [Preorder S]

/-- **Lumps**: `p` lumps `q` at `w` iff
    (i) `p` is true at `w`, and
    (ii) every part of `w` at which `p` is true is also a part at which
    `q` is true.

    Generalized from [kratzer-2012]'s situation-frame setting to
    any preordered carrier `S`; the parthood preorder is the only piece
    of structure the definition uses. -/
structure Lumps (p q : Set S) (w : S) : Prop where
  /-- `p` is true at `w` ([kratzer-2012], p. 118, condition (i)). -/
  holds : w ∈ p
  /-- Every part of `w` at which `p` is true also has `q` true
      ([kratzer-2012], p. 118, condition (ii); = Yablo's "local
      implication", noted in footnote 4 of [kratzer-2012], p. 114). -/
  localImpl : ∀ ⦃s⦄, s ≤ w → s ∈ p → s ∈ q

namespace Lumps

variable {p q r : Set S} {w : S}

/-- Setting `s = w` in the local-implication conjunct: `q` is true at
    `w` whenever `p` lumps `q` there. -/
theorem holds_target (h : Lumps p q w) : w ∈ q :=
  h.localImpl le_rfl h.holds

/-- A true proposition lumps itself (reflexivity, conditional on truth). -/
theorem refl_of_holds (hp : w ∈ p) : Lumps p p w :=
  ⟨hp, fun _ _ h => h⟩

/-- Lumping composes. -/
theorem trans (hpq : Lumps p q w) (hqr : Lumps q r w) : Lumps p r w :=
  ⟨hpq.holds, fun _ hs hps => hqr.localImpl hs (hpq.localImpl hs hps)⟩

/-- If `p` lumps both `q` and `r` at `w`, it lumps their intersection. -/
theorem inter (hq : Lumps p q w) (hr : Lumps p r w) : Lumps p (q ∩ r) w :=
  ⟨hq.holds, fun _ hs hps => ⟨hq.localImpl hs hps, hr.localImpl hs hps⟩⟩

/-- **Strengthening the lumping proposition**: a pointwise stronger
    `p'` (true at `w`) inherits everything `p` lumps. -/
theorem mono_left {p' : Set S} (hp' : p' ⊆ p) (hp'w : w ∈ p')
    (h : Lumps p q w) : Lumps p' q w :=
  ⟨hp'w, fun _ hs hps => h.localImpl hs (hp' hps)⟩

/-- **Weakening the lumped proposition**: pointwise entailment lifts. -/
theorem mono_right {q' : Set S} (hq' : q ⊆ q') (h : Lumps p q w) :
    Lumps p q' w :=
  ⟨h.holds, fun _ hs hps => hq' (h.localImpl hs hps)⟩

/-- A proposition true at every part of `w` is lumped by every
    proposition true at `w`. (Strictly weaker hypothesis than "true
    everywhere": only the parts of `w` matter.) -/
theorem of_local_universal (hp : w ∈ p) (hq : ∀ ⦃s⦄, s ≤ w → s ∈ q) :
    Lumps p q w :=
  ⟨hp, fun _ hs _ => hq hs⟩

end Lumps

end LumpingCore

/-! ## Logical relations ([kratzer-2012] §5.3.3, p. 118)

These quantify only over the worlds — the maximal situations — and so remain
"classical": equivalent to their possible-worlds counterparts on the worlds
of `S`. We follow Kratzer's set-theoretic notation verbatim. -/

section LogicalRelations

variable (S : Type*) [Preorder S]

/-- The worlds of a situation structure: its maximal situations ([kratzer-1989]). -/
def worlds : Set S := {s | IsMax s}

variable {S}

@[simp] theorem mem_worlds {s : S} : s ∈ worlds S ↔ IsMax s := Iff.rfl

/-- **Validity** ([kratzer-2012], p. 118): every world satisfies `p`.
    Kratzer writes this as `p ∩ W = W`; equivalently `worlds S ⊆ p`. -/
def IsValid (p : Set S) : Prop := worlds S ⊆ p

/-- **Logical consequence** ([kratzer-2012], p. 118): every world
    that satisfies all of `A` also satisfies `q`. Kratzer's text: "for
    all `w ∈ W`: if `w ∈ ⋂A`, then `w ∈ q`." -/
def Follows (A : Set (Set S)) (q : Set S) : Prop :=
  worlds S ∩ ⋂₀ A ⊆ q

/-- **Consistency** ([kratzer-2012], p. 118): some world satisfies
    every member of `A`. -/
def IsConsistent (A : Set (Set S)) : Prop :=
  (worlds S ∩ ⋂₀ A).Nonempty

/-- **Compatibility** ([kratzer-2012], p. 118): `p` is compatible
    with `A` iff `A ∪ {p}` is consistent. -/
def IsCompatible (p : Set S) (A : Set (Set S)) : Prop :=
  IsConsistent (insert p A)

/-- **Logical equivalence** ([kratzer-2012], p. 118): `p` and `q`
    agree on the worlds part. Kratzer writes `p ∩ W = q ∩ W`.

    Renamed from Kratzer's "logical equivalence" to `LogEquiv` to avoid
    collision with mathlib's `Equiv` (type equivalences). -/
def LogEquiv (p q : Set S) : Prop := p ∩ worlds S = q ∩ worlds S

/-! ### Characterizations -/

/-- A premise in a set is a logical consequence of the set. -/
theorem Follows.of_mem {A : Set (Set S)} {p : Set S}
    (hp : p ∈ A) : Follows A p :=
  Set.inter_subset_right.trans (Set.sInter_subset_of_mem hp)

/-- Validity is logical consequence from no premises. -/
theorem isValid_iff_follows_empty {p : Set S} :
    IsValid p ↔ Follows (∅ : Set (Set S)) p := by
  simp only [IsValid, Follows, Set.sInter_empty, Set.inter_univ]

/-- Consistency of `A` is the negation of "false follows from `A`". -/
theorem isConsistent_iff_not_follows_empty_set {A : Set (Set S)} :
    IsConsistent A ↔ ¬ Follows A (∅ : Set S) := by
  simp only [IsConsistent, Follows, Set.subset_empty_iff,
    ← Set.nonempty_iff_ne_empty]

/-- Compatibility unfolds to consistency of the augmented set
    (definitional; this lemma exists for `simp`-style rewriting). -/
@[simp] theorem isCompatible_iff_isConsistent_insert
    {p : Set S} {A : Set (Set S)} :
    IsCompatible p A ↔ IsConsistent (insert p A) := Iff.rfl

end LogicalRelations

/-! ## Bridge: lumping and logical consequence

If `p` lumps `q` at every world satisfying `p`, then `q` follows
logically from `p`. This is the cleanest connection between the
order-theoretic core (`Lumps`) and the worlds-restricted relations
(`Follows`). -/

section LumpingBridge

variable {S : Type*} [Preorder S]

/-- Worlds-restricted lumping entails logical consequence from the
    singleton premise set. The hypothesis is `Kratzer 2012`'s standard
    "for all `w ∈ W`" pattern: at every world where `p` holds, `p` lumps
    `q` there, so `q` holds at that world. -/
theorem Lumps.follows_singleton {p q : Set S}
    (h : ∀ w ∈ worlds S, w ∈ p → Lumps p q w) :
    Follows {p} q := by
  intro w hw
  have hwW : w ∈ worlds S := hw.1
  have hwp : w ∈ p := (Set.mem_sInter.mp hw.2) p (Set.mem_singleton p)
  exact (h w hwW hwp).holds_target

end LumpingBridge

/-! ## Possible-worlds reduction

Under the discrete order, parthood is equality: every situation is a world, every
proposition is persistent, and the local-implication conjunct of lumping collapses, so
lumping at `w` becomes joint truth at `w`. This is the formal sense in which possible-worlds
semantics flattens the distinctions Kratzer's lumping is designed to capture. -/

section DiscreteCorollary

/-- The discrete partial order on `X`: `s ≤ s' ↔ s = s'`. Reducible, so `≤` unfolds to `=`
in downstream proofs. -/
@[reducible] def discreteOrder (X : Type*) : PartialOrder X where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h

variable (G : Type)

local instance : PartialOrder G := discreteOrder G

/-- Under the discrete order every situation is a world. -/
theorem discrete_isMax (s : G) : IsMax s := fun _ h => h.symm.le

/-- Under the discrete order every proposition is persistent. -/
theorem discrete_monotone (p : G → Prop) : Monotone p := fun _ _ h hp => h ▸ hp

/-- Lumping in a discrete frame collapses to joint truth at the index. -/
theorem Lumps.discrete_iff (p q : Set G) (w : G) :
    Lumps p q w ↔ (w ∈ p ∧ w ∈ q) := by
  refine ⟨fun h => ⟨h.holds, h.holds_target⟩, fun ⟨hp, hq⟩ => ⟨hp, ?_⟩⟩
  intro s hs _
  -- `s ≤ w` in `discreteOrder` reduces by definition to `s = w`.
  obtain rfl : s = w := hs
  exact hq

end DiscreteCorollary

end Conditionals.Counterfactual
