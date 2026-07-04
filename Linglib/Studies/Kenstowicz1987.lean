/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Logic.FactorsThroughOn
import Linglib.Fragments.Tangale.Phonology

/-!
# Tangale sandhi as a probe for syntactic structure

Formalises [kenstowicz-1987]: the blockage of phrasal phonological
rules can reveal surface syntax "that we did not already know".
Tangale elision and tonal delinking apply obligatorily between a verb
and its object (15b, e) but block before a wh-object (15c, f). A
[wh]-sensitive sandhi rule is rejected both on interface-theoretic
grounds and by the minimal pair (16): wh-*possessors* inside NP
trigger elision (*ayab noŋ* 'whose banana'). The solution: wh-subjects
obligatorily postpose to a position with "the force of the English
cleft" (18) — the Focus position — and apparently in-situ wh-objects
occupy it string-vacuously, so a constituent boundary blocks sandhi.
Elision tracks government exactly once the Focus position is admitted;
the [wh] feature does not factor it.
-/

namespace Kenstowicz1987

/-- The junctures at which the sandhi rules are tested
((4)–(5), (15)–(16)). -/
inductive Juncture where
  | headComplementNP
  | verbObject
  | verbAdjunct
  | subjectVP
  | verbWhObject
  | headWhPossessor
  deriving DecidableEq, Repr

/-- Observed: elision (and delinking) applies at the juncture
((4a, b), (5a–c), (15c, f), (16a, b)). -/
def elides : Juncture → Bool
  | .headComplementNP => true
  | .verbObject       => true
  | .verbAdjunct      => false
  | .subjectVP        => false
  | .verbWhObject     => false
  | .headWhPossessor  => true

/-- Whether the juncture's second element is a wh-word. -/
def secondIsWh : Juncture → Bool
  | .verbWhObject | .headWhPossessor => true
  | _ => false

/-- The juncture is a government configuration under the Focus-position
analysis: head–complement and verb–object are; adjuncts and subjects
are not; a wh-object sits in the postverbal Focus position across a
constituent boundary (string-vacuous postposing, as with the
obligatorily postposed wh-subjects of (18)); a wh-possessor has no
NP-internal Focus position and stays in situ. -/
def governed : Juncture → Bool
  | .headComplementNP => true
  | .verbObject       => true
  | .verbAdjunct      => false
  | .subjectVP        => false
  | .verbWhObject     => false
  | .headWhPossessor  => true

/-- The rejected account: elision does not factor through the [wh]
feature of the second word — wh-objects block it while wh-possessors
trigger it ((15c, f) vs (16a, b)). -/
theorem elision_not_factor_through_wh :
    ¬ Function.FactorsThroughOn elides secondIsWh Set.univ := by
  rw [Function.not_factorsThroughOn_iff_exists_witness]
  exact ⟨.verbWhObject, .headWhPossessor, trivial, trivial, rfl, by decide⟩

/-- His solution: elision tracks government exactly, once apparently
in-situ wh-objects are placed in the postverbal Focus position. The
blockage is a syntactic discovery made by phonology. -/
theorem elision_tracks_government : ∀ j, elides j = governed j := by
  intro j; cases j <;> rfl

/-- (15d–f): before a wh-object the verb surfaces in the blocked
(faithful) form (*dobgo noŋ*), before a plain object in the
elided–repaired form (*dobug Malay*) — audibly distinct by
[kidda-1985]'s cascade. -/
theorem wh_object_cell_audible :
    Tangale.blockedForm ≠ Tangale.elidedForm :=
  Tangale.boundary_audible.1

end Kenstowicz1987
