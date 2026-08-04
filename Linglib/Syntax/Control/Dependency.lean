/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Rel
import Mathlib.Order.Basic

/-!
# Control Dependencies

The framework-neutral stratum of control theory. Control is pre-theoretically
an antecedence relation between the understood subject of a clause-like
complement and the matrix argument that supplies its interpretation
([landau-2013] (74)); the one definition in the literature written to be
neutral between the rival mechanisms is [stiebels-2007] (22): the control
predicate requires one of its arguments to be (improperly) included in the
reference of the embedded subject, "open as to how the control reading is
obtained: either structurally or semantically/lexically". A dependency here is
a relation `SetRel Pos Pos` over argument positions, read
`antecedent ~[r] dependent`, with a valuation `val : Pos → Ref` assigning
referents. Identical inclusion is *exhaustive control* ([landau-2000]):
related positions are co-valued (`Control.IsExhaustive`); proper inclusion —
a *partial* reading — is strict growth `val a < val b` along the dependency
(`exists_lt_of_comp_lt` localizes it to a leg of a composite).

Grammatical dependencies share the fixed format of the configurational matrix:
[koster-1987]'s five shared properties, as explained by
[neeleman-vandekoot-2002] — c-command by the antecedent, obligatoriness,
uniqueness of the antecedent, nonuniqueness of the dependent, and locality.
Every clause of the matrix is mathlib vocabulary: c-command and locality are
refinements `r ⊆ s` in the `SetRel` lattice, uniqueness of the antecedent is
`Relator.LeftUnique`, obligatoriness is `dependent ⊆ r.cod`. Movement chains,
bound anaphora, and both control mechanisms instantiate the format, so nothing
here chooses between base-generation and movement.

Which assignment a dependency exhaustively shares distinguishes the
enforcement species — [bresnan-1982]'s functional vs. anaphoric control:
*functional* control shares the occupant assignment itself (structure sharing;
movement chains), *anaphoric* control only the referent valuation. Occupant
sharing is the stronger: it transports along every map of the assignment
(`IsExhaustive.map`), so one observed occupant mismatch refutes it
(`not_isExhaustive_of_mismatch`) — the refutation engine of the overt-copy
diagnostics ([polinsky-potsdam-2006]).

## Main definitions

- `Control.IsExhaustive`: exhaustive control — the dependency refines the
  kernel of the valuation
-/

namespace Control

open SetRel

/-! ### Exhaustive sharing -/

variable {Pos Ref : Type*} {val : Pos → Ref} {ante bind pred : SetRel Pos Pos}
  {a b p c : Pos}

/-- Exhaustive control ([landau-2000]): the dependency shares the valuation
    exhaustively — related positions are co-valued, i.e. the dependency
    refines the kernel of the valuation. -/
def IsExhaustive (val : Pos → Ref) (ante : SetRel Pos Pos) : Prop :=
  ante ⊆ {(a, b) | val a = val b}

/-- Related positions of an exhaustive dependency are co-valued. -/
theorem IsExhaustive.eq (hs : IsExhaustive val ante) (h : a ~[ante] b) :
    val a = val b :=
  hs h

/-- A refinement of an exhaustive dependency is exhaustive. -/
theorem IsExhaustive.mono (h : ante ⊆ bind) (hs : IsExhaustive val bind) :
    IsExhaustive val ante :=
  h.trans hs

/-- Exhaustivity composes through the mediating position. -/
theorem IsExhaustive.comp (hb : IsExhaustive val bind)
    (hp : IsExhaustive val pred) : IsExhaustive val (bind ○ pred) := by
  rintro ⟨a, c⟩ ⟨m, ham, hmc⟩
  exact (hb.eq ham).trans (hp.eq hmc)

/-- Exhaustive control excludes partial readings: no strict growth of the
    referent along the dependency ([landau-2000]). -/
theorem IsExhaustive.not_lt [Preorder Ref] (hs : IsExhaustive val ante)
    (h : a ~[ante] b) : ¬ val a < val b := by
  simp [hs.eq h]

/-- Under exhaustive control, joint antecedents are co-valued — split control
    needs a non-exhaustive leg. -/
theorem IsExhaustive.eq_of_two (hs : IsExhaustive val ante)
    (ha : a ~[ante] p) (hb : b ~[ante] p) : val a = val b :=
  (hs.eq ha).trans (hs.eq hb).symm

/-- A partial reading in a composite localizes to a leg: if referents grow
    monotonely along the first leg and strictly across the composite, one of
    the two legs already grows strictly. -/
theorem exists_lt_of_comp_lt [PartialOrder Ref]
    (hb : ∀ ⦃x m⦄, x ~[bind] m → val x ≤ val m)
    (h : a ~[bind ○ pred] c) (hlt : val a < val c) :
    (∃ x m, x ~[bind] m ∧ val x < val m) ∨
      ∃ m x, m ~[pred] x ∧ val m < val x := by
  obtain ⟨m, ham, hmc⟩ := h
  rcases (hb ham).lt_or_eq with hlt' | heq
  · exact Or.inl ⟨a, m, ham, hlt'⟩
  · exact Or.inr ⟨m, c, hmc, heq ▸ hlt⟩

/-! ### Enforcement

Which assignment a dependency exhaustively shares distinguishes the
enforcement species ([bresnan-1982]): functional control shares the occupant
assignment itself (structure sharing — movement chains, LFG control
equations), anaphoric control only the referent valuation. Occupant sharing
is the stronger: a shared assignment transports along every map of it
(`IsExhaustive.map`), so every occupant property transports across the
dependency (`IsExhaustive.iff_of_rel`) — and one observed mismatch refutes
it (`not_isExhaustive_of_mismatch`), the engine of the overt-copy
diagnostics ([polinsky-potsdam-2006]). -/

variable {Item : Type*} {occ : Pos → Item}

/-- Sharing an assignment transports along any map of it: token identity
    yields referential co-valuation for every referent map. -/
theorem IsExhaustive.map (hs : IsExhaustive occ ante) (f : Item → Ref) :
    IsExhaustive (f ∘ occ) ante := by
  rintro ⟨a, b⟩ h
  exact congrArg f (hs.eq h)

/-- Under a shared assignment, every property of the assigned value transports
    across the dependency: copies are indistinguishable. -/
theorem IsExhaustive.iff_of_rel (hs : IsExhaustive occ ante) (h : a ~[ante] b)
    (P : Item → Prop) : P (occ a) ↔ P (occ b) :=
  iff_of_eq (congrArg P (hs.eq h))

/-- One observed mismatch refutes a shared assignment — the refutation engine
    of the copy-control diagnostics. -/
theorem not_isExhaustive_of_mismatch {P : Item → Prop} (h : a ~[ante] b)
    (hPa : P (occ a)) (hPb : ¬ P (occ b)) : ¬ IsExhaustive occ ante :=
  fun hs => hPb (hs.eq h ▸ hPa)

end Control
