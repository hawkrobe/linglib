/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Focus.Control
import Linglib.Pragmatics.Expressives.Basic

/-!
# Alternative-sensitive particles in Ngamo

Formalises [grubic-2015] Ch. 6–7: the Ngamo particles *yak('i)*
'only', *ke('e)* 'also', and *har('i)* 'even' in a Beaver &
Clark-style QUD account. *yak(p)* presupposes *at least p* and
asserts *at most p* over entailment-ranked alternatives (the Coppock
& Beaver decomposition); *ke(p)* presupposes a given alternative
about a different topic situation; *har(p)* presupposes a contextual
implication of *p* ranked high on a salient scale (kept as prose).

`yak_eq_prejacent_inter_onlyVia` reconciles the scalar and identity
formulations of exclusivity: over the conjunction-closure of the
atomic alternatives, *yak*'s total content (presupposition plus
assertion) coincides with the prejacent exhaustified by the
strong-theory `onlyVia` over the atoms — the Kiss-style
identificational meaning derived from the scalar decomposition.

Distribution (her (10)–(12)): *yak* cannot associate with preverbal
subjects but is fine in any focus construction; *ke/har* associate
with preverbal subjects but are marginal with `=i/ye`-marked focus
under parallel backgrounds — data recorded in `distribution`.
-/

namespace Grubic2015

open Pragmatics.Expressives (TwoDimProp)
open Focus (onlyVia)

variable {W : Type*}

/-! ## The Coppock & Beaver decomposition (Ch. 7) -/

/-- *At least p*: some alternative at least as strong as the prejacent
holds — *yak*'s presupposition. -/
def atLeast (C : Set (Set W)) (p : Set W) : Set W :=
  {w | ∃ q ∈ C, q ⊆ p ∧ w ∈ q}

/-- *At most p*: no alternative strictly stronger than the prejacent
holds — *yak*'s assertion. -/
def atMost (C : Set (Set W)) (p : Set W) : Set W :=
  {w | ∀ q ∈ C, w ∈ q → ¬ q ⊂ p}

/-- *yak('i)* 'only': presupposes at least `p`, asserts at most `p`
(her Ch. 7, following Coppock & Beaver's *only*). -/
def yak (C : Set (Set W)) (p : Set W) : TwoDimProp W :=
  .withCI (· ∈ atMost C p) (· ∈ atLeast C p)

/-- *ke('e)* 'also': presupposes that a distinct alternative is given
(her Ch. 7; the different-topic-situation refinement is prose). -/
def ke (given : Set (Set W)) (p : Set W) : TwoDimProp W :=
  .withCI (· ∈ p) (fun w => ∃ q ∈ given, q ≠ p ∧ w ∈ q)

/-- The total content of a two-dimensional meaning: at-issue plus
presupposed. -/
def total (m : TwoDimProp W) : Set W := {w | m.atIssue w ∧ m.ci w}

/-! ## Reconciling the scalar and identity formulations

On the building scenario (her (10)–(11)): worlds track which of the
house and the granary Kule built. -/

/-- Who-built-what worlds. -/
structure BuildWorld where
  house   : Bool
  granary : Bool
  deriving DecidableEq, Repr

def builtHouse : Set BuildWorld := {w | w.house}
def builtGranary : Set BuildWorld := {w | w.granary}
def builtBoth : Set BuildWorld := builtHouse ∩ builtGranary

/-- The atomic alternatives. -/
def atoms : Set (Set BuildWorld) := {builtHouse, builtGranary}

/-- The QUD's answer space: the atoms and their conjunction. -/
def answers : Set (Set BuildWorld) := {builtHouse, builtGranary, builtBoth}

private theorem builtGranary_ne_builtHouse : builtGranary ≠ builtHouse := by
  intro h
  have hmem : (⟨false, true⟩ : BuildWorld) ∈ builtGranary := rfl
  rw [h] at hmem
  exact absurd hmem Bool.false_ne_true

private theorem builtBoth_ssubset : builtBoth ⊂ builtHouse := by
  constructor
  · exact Set.inter_subset_left
  · intro h
    have hmem : (⟨true, false⟩ : BuildWorld) ∈ builtBoth :=
      h (show (⟨true, false⟩ : BuildWorld) ∈ builtHouse from rfl)
    exact absurd hmem.2 Bool.false_ne_true

/-- The scalar and identity formulations coincide: *yak*'s total
content over the conjunction-closed answer space equals the prejacent
exhaustified by `onlyVia` over the atoms — the Kiss-style
identificational meaning ('built the house and nothing else') derived
from the at-least/at-most decomposition. -/
theorem yak_eq_prejacent_inter_onlyVia :
    total (yak answers builtHouse) =
      builtHouse ∩ onlyVia atoms builtHouse := by
  ext w
  constructor
  · rintro ⟨hmost, q, hq, hsub, hwq⟩
    have hp : w ∈ builtHouse := hsub hwq
    refine ⟨hp, fun r hr hwr => ?_⟩
    rcases hr with rfl | rfl
    · rfl
    · exact absurd builtBoth_ssubset
        (hmost builtBoth (Or.inr (Or.inr rfl)) ⟨hp, hwr⟩)
  · rintro ⟨hp, honly⟩
    refine ⟨fun q hq hwq hlt => ?_, builtHouse, Or.inl rfl, subset_rfl, hp⟩
    rcases hq with rfl | rfl | rfl
    · exact absurd rfl hlt.ne
    · exact absurd (honly builtGranary (Or.inr rfl) hwq)
        builtGranary_ne_builtHouse
    · exact absurd (honly builtGranary (Or.inr rfl) hwq.2)
        builtGranary_ne_builtHouse

/-- *ke*'s additive presupposition needs a distinct given alternative:
with only the prejacent given, the presupposition fails everywhere —
the anaphoricity behind her (12) parallel-background facts. -/
theorem ke_needs_distinct_antecedent :
    ∀ w, ¬ (ke {builtHouse} builtHouse).ci w :=
  fun _ ⟨_, hq, hne, _⟩ => hne hq

/-! ## Distribution (her (10)–(12)) -/

/-- The particles. -/
inductive Particle where
  | yak | ke | har
  deriving DecidableEq, Repr

/-- The association configurations tested. -/
inductive Host where
  | preverbalSubject
  | bmMarkedFocus
  | plainFocus
  deriving DecidableEq, Repr

/-- Her (10)–(11) acceptability table: *yak* cannot associate with
preverbal subjects; *ke/har* are marginal with `=i/ye`-marked focus
(under parallel backgrounds — the (12) exception is prose). -/
def acceptable : Particle → Host → Bool
  | .yak, .preverbalSubject => false
  | .yak, _                 => true
  | _,    .bmMarkedFocus    => false
  | _,    _                 => true

/-- No particle-host uniformity: the two asymmetries cross-cut —
association possibilities do not follow from the particle or the
host alone. -/
theorem association_crosscuts :
    acceptable .yak .bmMarkedFocus ≠ acceptable .ke .bmMarkedFocus ∧
    acceptable .yak .preverbalSubject ≠ acceptable .ke .preverbalSubject := by
  decide

end Grubic2015
