import Mathlib.Data.Set.Basic
import Linglib.Core.IntensionalLogic.Situations

/-!
# Lumping

@cite{kratzer-1989} @cite{kratzer-2012}

Kratzer's situation-semantic notion of *lumping*: a proposition `p` lumps
a proposition `q` in a world `w` when truth of `p` at every part of `w`
forces truth of `q` there. Lumping is the technical glue Kratzer uses to
repair the premise-semantic account of counterfactuals — when an
antecedent is added to a Base Set, every proposition lumped by the
antecedent in the evaluation world comes along, blocking the spurious
counterfactuals that arise when independent true propositions are added
freely (cf. the Paula-paints-a-still-life and zebra-escapes examples in
Kratzer 2012, §5.4).

This module sits on top of `Core.IntensionalLogic.Situations`, which
provides the `SituationFrame` carrier — a `Frame` whose `Index` carries
a partial order representing parthood. Propositions are `Prop' Index`
(= `Index → Prop`) from `Core.Semantics.Proposition`; the order grounds
both lumping and persistence (= mathlib's `Monotone`, aliased as
`Persistent` in `Situations.lean`).

## Scope

This file covers Kratzer 2012 §5.3.3 and §5.3.5: the base situation-
semantic logical relations (truth, validity, consistency, compatibility,
logical consequence, logical equivalence) and the lumping relation
itself. The counterfactual machinery of §5.4.4 — admissible Base Sets,
the Crucial Set construction, and the would/might-counterfactual truth
conditions — is deferred to a forthcoming `Counterfactual.lean` next
door.

## Worlds vs. arbitrary situations

Kratzer's official definition (p. 118) restricts `Lumps p q w` to worlds
`w ∈ W`. We define the relation for any situation; the world case is the
standard application but the more general form is harmless and lets us
reason about lumping at intermediate situations. Combine with `IsWorld w`
(from `Situations.lean`) to express the standard restriction.
-/

namespace Semantics.Conditionals.Kratzer.Lumping

open Core.IntensionalLogic

variable {F : SituationFrame}

/-! ## Logical relations (Kratzer 2012 §5.3.3)

These are the situation-semantics analogues of the standard PWS
relations. They quantify only over worlds (maximal situations), so
they remain "classical" — equivalent to their PWS counterparts on the
worlds part of `F.Index`. -/

/-- Truth at a situation: `p` is true at `s` iff `p s`. Trivial by
    definition; named for parity with Kratzer 2012 §5.3.3. -/
@[simp] def IsTrue (p : Set F.Index) (s : F.Index) : Prop := p s

/-- **Validity**: `p` holds at every world. -/
def IsValid (p : Set F.Index) : Prop := ∀ w, IsWorld w → p w

/-- **Consistency**: a set of propositions is consistent iff some world
    satisfies every member. -/
def IsConsistent (A : Set (Set F.Index)) : Prop :=
  ∃ w, IsWorld w ∧ ∀ p ∈ A, p w

/-- **Compatibility**: `p` is compatible with `A` iff `A ∪ {p}` is
    consistent. -/
def IsCompatible (p : Set F.Index) (A : Set (Set F.Index)) : Prop :=
  IsConsistent (insert p A)

/-- **Logical consequence**: `q` follows from `A` iff every world that
    satisfies all of `A` also satisfies `q`. -/
def Follows (A : Set (Set F.Index)) (q : Set F.Index) : Prop :=
  ∀ w, IsWorld w → (∀ p ∈ A, p w) → q w

/-- **Logical equivalence**: `p` and `q` agree at every world. -/
def Equiv (p q : Set F.Index) : Prop :=
  ∀ w, IsWorld w → (p w ↔ q w)

/-- A premise in a set is a logical consequence of the set. -/
theorem Follows.of_mem {A : Set (Set F.Index)} {p : Set F.Index}
    (hp : p ∈ A) : Follows A p :=
  fun _ _ h => h p hp

/-! ## Lumping (Kratzer 2012 §5.3.3 / §5.3.5)

The official definition (p. 118):
> For all propositions `p, q ∈ P(S)` and all `w ∈ W`:
> `p` lumps `q` in `w` iff (i) `w ∈ p`. (ii) For all `s ∈ S`,
> if `s ≤ w` and `s ∈ p`, then `s ∈ q`.

Yablo's "local implication" (footnote 4 in Kratzer 2012) corresponds to
condition (ii). We allow `w` to be any situation; restrict to worlds
with `IsWorld w` for the standard reading. -/

/-- **Lumps**: `p` lumps `q` at `w` iff (i) `p` is true at `w`, and
    (ii) every part of `w` at which `p` is true is also a part at which
    `q` is true. -/
def Lumps (p q : Set F.Index) (w : F.Index) : Prop :=
  p w ∧ ∀ s, s ≤ w → p s → q s

/-! ### Basic lumping properties -/

/-- The "truth" condition extracted: if `p` lumps `q` at `w`, then `p`
    is true at `w`. -/
theorem Lumps.true_left {p q : Set F.Index} {w : F.Index}
    (h : Lumps p q w) : p w := h.1

/-- The "local implication" condition extracted. -/
theorem Lumps.local_impl {p q : Set F.Index} {w : F.Index}
    (h : Lumps p q w) {s : F.Index} (hs : s ≤ w) (hps : p s) : q s :=
  h.2 s hs hps

/-- Setting `s = w` in the local-implication conjunct: `q` is true at `w`
    too. So lumping at `w` is at least as strong as joint truth at `w`. -/
theorem Lumps.true_right {p q : Set F.Index} {w : F.Index}
    (h : Lumps p q w) : q w :=
  h.2 w le_rfl h.1

/-- Lumping is reflexive (when truth holds): a true proposition lumps
    itself. -/
theorem Lumps.self {p : Set F.Index} {w : F.Index} (hp : p w) :
    Lumps p p w :=
  ⟨hp, fun _ _ h => h⟩

/-- **Transitivity (right)**: if `p` lumps `q` and `q` lumps `r` at `w`,
    then `p` lumps `r` at `w`. -/
theorem Lumps.trans {p q r : Set F.Index} {w : F.Index}
    (hpq : Lumps p q w) (hqr : Lumps q r w) : Lumps p r w :=
  ⟨hpq.1, fun s hs hps => hqr.2 s hs (hpq.2 s hs hps)⟩

/-- **Conjunction**: if `p` lumps both `q` and `r` at `w`, then `p` lumps
    their conjunction at `w`. -/
theorem Lumps.and {p q r : Set F.Index} {w : F.Index}
    (hq : Lumps p q w) (hr : Lumps p r w) :
    Lumps p (fun s => q s ∧ r s) w :=
  ⟨hq.1, fun s hs hps => ⟨hq.2 s hs hps, hr.2 s hs hps⟩⟩

/-- **Strengthening the lumping proposition**: if `p'` is pointwise
    stronger than `p` and `p'` is true at `w`, then `p lumps q` lifts to
    `p' lumps q` at `w`. -/
theorem Lumps.of_stronger {p p' q : Set F.Index} {w : F.Index}
    (hpp' : ∀ s, p' s → p s) (hp'w : p' w) (h : Lumps p q w) :
    Lumps p' q w :=
  ⟨hp'w, fun s hs hps => h.2 s hs (hpp' s hps)⟩

/-- **Weakening the lumped proposition**: if `q` pointwise entails `q'`,
    then `p lumps q` upgrades to `p lumps q'`. -/
theorem Lumps.weaken {p q q' : Set F.Index} {w : F.Index}
    (hqq' : ∀ s, q s → q' s) (h : Lumps p q w) : Lumps p q' w :=
  ⟨h.1, fun s hs hps => hqq' s (h.2 s hs hps)⟩

/-- A proposition true at every situation is lumped by every proposition
    true at `w`. -/
theorem Lumps.of_universal {p q : Set F.Index} {w : F.Index}
    (hp : p w) (hq : ∀ s, q s) : Lumps p q w :=
  ⟨hp, fun s _ _ => hq s⟩

/-! ## Possible-worlds reduction

In a discrete situation frame (a `Frame` promoted via
`Frame.toDiscreteSituationFrame`), parthood reduces to equality, so the
local-implication conjunct collapses. Lumping at any index `w` becomes
"both propositions are true at `w`" — a degenerate notion. This is the
formal sense in which possible-worlds semantics flattens the
distinctions Kratzer's lumping is designed to capture. -/

theorem lumps_discrete (F : Frame)
    (p q : Set F.Index) (w : F.Index) :
    @Lumps F.toDiscreteSituationFrame p q w ↔ (p w ∧ q w) := by
  unfold Lumps
  refine ⟨fun ⟨hp, h⟩ => ⟨hp, h w le_rfl hp⟩, fun ⟨hp, hq⟩ => ⟨hp, ?_⟩⟩
  intro s hs _
  -- In discrete order, `s ≤ w` reduces definitionally to `s = w`.
  have heq : s = w := hs
  exact heq ▸ hq

end Semantics.Conditionals.Kratzer.Lumping
