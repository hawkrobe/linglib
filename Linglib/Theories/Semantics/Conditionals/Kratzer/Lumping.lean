import Mathlib.Data.Set.Lattice
import Linglib.Core.IntensionalLogic.Situations

/-!
# Lumping

@cite{kratzer-1989}, @cite{kratzer-2012}

Kratzer's situation-semantic notion of *lumping*: a proposition `p` lumps
a proposition `q` in a world `w` when truth of `p` at every part of `w`
forces truth of `q` there. Lumping is the technical glue Kratzer uses to
repair the premise-semantic account of counterfactuals — when an
antecedent is added to a Base Set, every proposition lumped by the
antecedent in the evaluation world comes along, blocking the spurious
counterfactuals that arise when independent true propositions are added
freely (the Paula-paints-a-still-life and zebra-escapes examples in
@cite{kratzer-2012}, §5.4.1).

This module sits on top of `Core.IntensionalLogic.Situations`, which
provides the `SituationFrame` carrier — a `Frame` whose `Index` carries
a partial order representing parthood. Propositions are `Set F.Index`;
the order grounds both lumping and persistence (= mathlib's `Monotone`,
aliased as `Persistent` in `Situations.lean`).

## Scope

This file covers @cite{kratzer-2012} §5.3.3 (p. 118): the worlds-only
logical relations (validity, consistency, compatibility, logical
consequence, logical equivalence) and the official lumping definition
that closes the section. The counterfactual machinery of §5.4 — base
sets, the truth conditions for would/might-counterfactuals, and the
formal definitions in §5.4.4 — is out of scope here.

## Architectural notes

- **Lumping is order-theoretic.** `Lumps` is parametric in any
  `[Preorder S]`; only the worlds-restricted relations are bundled
  through `SituationFrame`. Mirrors how `Persistent` is generalized in
  `Situations.lean`.
- **Logical relations follow Kratzer's set notation literally.** Each
  definition unfolds to the same set-theoretic formula on p. 118
  (`F.Worlds ⊆ p`, `F.Worlds ∩ ⋂₀ A ⊆ q`, etc.), so the mathlib `Set`
  and `sInter` APIs apply unchanged.
- **Worlds vs. arbitrary situations.** Kratzer's official definition
  restricts `Lumps p q w` to `w ∈ W`. We define the relation for any
  situation; combine with `IsWorld w` (from `Situations.lean`) for the
  standard restriction. The `Lumps.follows_singleton` bridge below
  shows how to recover Kratzer's worlds-only reading.
-/

namespace Semantics.Conditionals.Kratzer.Lumping

open Core.IntensionalLogic Set

/-! ## Lumping (@cite{kratzer-2012} §5.3.3, p. 118)

The official text of @cite{kratzer-2012}, p. 118:
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

    Generalized from @cite{kratzer-2012}'s situation-frame setting to
    any preordered carrier `S`; the parthood preorder is the only piece
    of structure the definition uses. -/
structure Lumps (p q : Set S) (w : S) : Prop where
  /-- `p` is true at `w` (@cite{kratzer-2012}, p. 118, condition (i)). -/
  holds : w ∈ p
  /-- Every part of `w` at which `p` is true also has `q` true
      (@cite{kratzer-2012}, p. 118, condition (ii); = Yablo's "local
      implication", noted in footnote 4 of @cite{kratzer-2012}, p. 114). -/
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

/-! ## Logical relations (@cite{kratzer-2012} §5.3.3, p. 118)

These quantify only over `F.Worlds` (maximal situations) and so remain
"classical" — equivalent to their possible-worlds counterparts on the
worlds part of `F.Index`. We follow Kratzer's set-theoretic notation
verbatim. -/

section LogicalRelations

variable {F : SituationFrame}

/-- **Validity** (@cite{kratzer-2012}, p. 118): every world satisfies `p`.
    Kratzer writes this as `p ∩ W = W`; equivalently `F.Worlds ⊆ p`. -/
def IsValid (p : Set F.Index) : Prop := F.Worlds ⊆ p

/-- **Logical consequence** (@cite{kratzer-2012}, p. 118): every world
    that satisfies all of `A` also satisfies `q`. Kratzer's text: "for
    all `w ∈ W`: if `w ∈ ⋂A`, then `w ∈ q`." -/
def Follows (A : Set (Set F.Index)) (q : Set F.Index) : Prop :=
  F.Worlds ∩ ⋂₀ A ⊆ q

/-- **Consistency** (@cite{kratzer-2012}, p. 118): some world satisfies
    every member of `A`. -/
def IsConsistent (A : Set (Set F.Index)) : Prop :=
  (F.Worlds ∩ ⋂₀ A).Nonempty

/-- **Compatibility** (@cite{kratzer-2012}, p. 118): `p` is compatible
    with `A` iff `A ∪ {p}` is consistent. -/
def IsCompatible (p : Set F.Index) (A : Set (Set F.Index)) : Prop :=
  IsConsistent (insert p A)

/-- **Logical equivalence** (@cite{kratzer-2012}, p. 118): `p` and `q`
    agree on the worlds part. Kratzer writes `p ∩ W = q ∩ W`.

    Renamed from Kratzer's "logical equivalence" to `LogEquiv` to avoid
    collision with mathlib's `Equiv` (type equivalences). -/
def LogEquiv (p q : Set F.Index) : Prop := p ∩ F.Worlds = q ∩ F.Worlds

/-! ### Characterizations -/

/-- A premise in a set is a logical consequence of the set. -/
theorem Follows.of_mem {A : Set (Set F.Index)} {p : Set F.Index}
    (hp : p ∈ A) : Follows A p :=
  Set.inter_subset_right.trans (Set.sInter_subset_of_mem hp)

/-- Validity is logical consequence from no premises. -/
theorem isValid_iff_follows_empty {p : Set F.Index} :
    IsValid p ↔ Follows (∅ : Set (Set F.Index)) p := by
  simp only [IsValid, Follows, Set.sInter_empty, Set.inter_univ]

/-- Consistency of `A` is the negation of "false follows from `A`". -/
theorem isConsistent_iff_not_follows_empty_set {A : Set (Set F.Index)} :
    IsConsistent A ↔ ¬ Follows A (∅ : Set F.Index) := by
  simp only [IsConsistent, Follows, Set.subset_empty_iff,
    ← Set.nonempty_iff_ne_empty]

/-- Compatibility unfolds to consistency of the augmented set
    (definitional; this lemma exists for `simp`-style rewriting). -/
@[simp] theorem isCompatible_iff_isConsistent_insert
    {p : Set F.Index} {A : Set (Set F.Index)} :
    IsCompatible p A ↔ IsConsistent (insert p A) := Iff.rfl

end LogicalRelations

/-! ## Bridge: lumping and logical consequence

If `p` lumps `q` at every world satisfying `p`, then `q` follows
logically from `p`. This is the cleanest connection between the
order-theoretic core (`Lumps`) and the worlds-restricted relations
(`Follows`). -/

section LumpingBridge

variable {F : SituationFrame}

/-- Worlds-restricted lumping entails logical consequence from the
    singleton premise set. The hypothesis is `Kratzer 2012`'s standard
    "for all `w ∈ W`" pattern: at every world where `p` holds, `p` lumps
    `q` there, so `q` holds at that world. -/
theorem Lumps.follows_singleton {p q : Set F.Index}
    (h : ∀ w ∈ F.Worlds, w ∈ p → Lumps p q w) :
    Follows {p} q := by
  intro w hw
  have hwW : w ∈ F.Worlds := hw.1
  have hwp : w ∈ p := (Set.mem_sInter.mp hw.2) p (Set.mem_singleton p)
  exact (h w hwW hwp).holds_target

end LumpingBridge

/-! ## Possible-worlds reduction

In a discrete situation frame (a `Frame` promoted via
`Frame.toDiscreteSituationFrame`), parthood reduces to equality. The
local-implication conjunct then collapses, and lumping at any index `w`
becomes joint truth at `w` — a degenerate notion. This is the formal
sense in which possible-worlds semantics flattens the distinctions
Kratzer's lumping is designed to capture. -/

section DiscreteCorollary

variable (G : Frame)

/-- Bring the discrete partial order on `G.Index` into scope so the
    corollary below can quote `Lumps` without explicit `@`-application. -/
local instance : PartialOrder G.Index := discreteOrder G.Index

/-- Lumping in a discrete frame collapses to joint truth at the index. -/
theorem Lumps.discrete_iff (p q : Set G.Index) (w : G.Index) :
    Lumps p q w ↔ (w ∈ p ∧ w ∈ q) := by
  refine ⟨fun h => ⟨h.holds, h.holds_target⟩, fun ⟨hp, hq⟩ => ⟨hp, ?_⟩⟩
  intro s hs _
  -- `s ≤ w` in `discreteOrder` reduces by definition to `s = w`.
  obtain rfl : s = w := hs
  exact hq

end DiscreteCorollary

end Semantics.Conditionals.Kratzer.Lumping
