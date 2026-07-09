import Linglib.Morphology.Realization

/-!
# Branan and Erlewine 2023: Anti-pied-piping

[branan-erlewine-2023] documents anti-pied-piping — focus morphosyntax
(particle placement, focus movement) targeting a proper subpart of the
logical focus — in over sixty languages from over forty language
groups, and proposes that focus particles are morphosyntactic flags
for abstract operators, severing the particle's pronounced position
from the position of its semantic contribution. This file formalizes
the introductory paradigm (their (1)–(8)): Japanese *mo* placement and
Hungarian focus movement each attest exact targeting, pied-piping, and
anti-pied-piping, stated over the host–focus containment relations of
`Morphology/Realization.lean`.

## Main declarations

* `BrananErlewine2023.Node`: the clause skeleton of the paradigm.
* `mo_attests_all_relations` / `movement_attests_all_relations`:
  particle placement and focus movement each realize all three
  host–focus relations.
* `msf_tolerates_mismatches`: neither process strictly targets the
  F-marked constituent — the shape of the paper's argument that focus
  morphosyntax targets a particle phrase rather than F itself.

## TODO

* The leftmost-targeting generalization of their §3 (requires linear
  order on constituents).
* The particle-phrase theory of their §4 and the cross-linguistic
  appendix as `Data/Examples` rows.
-/

namespace BrananErlewine2023

open Morphology

/-! ### The clause skeleton -/

/-- Clause skeleton for the introductory paradigm: an attributive
adjective within the object DP; verb and object within VP; subject and
VP within S. -/
inductive Node where
  | s | sbj | vp | v | obj | att
  deriving DecidableEq, Repr, Fintype

/-- Constituent containment. -/
def nle : Node → Node → Bool
  | _, .s => true
  | .v, .vp | .obj, .vp | .att, .vp | .vp, .vp => true
  | .att, .obj | .obj, .obj => true
  | .sbj, .sbj | .v, .v | .att, .att => true
  | _, _ => false

instance : PartialOrder Node where
  le a b := nle a b = true
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Node := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))

instance : DecidableLT Node := fun a b =>
  inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))

/-! ### The introductory paradigm

Their (1)–(8): Japanese additive *mo* and Hungarian focus movement in
all three host–focus configurations. -/

/-- Their (2): Hanako-wa [hon]F*-mo* katta — *mo* on the focused object
itself. -/
def moExact : Realization Node := ⟨.obj, [.morpheme .obj]⟩

/-- Their (4): Hanako-wa [[hon]F-o kai]*-mo* — *mo* on the VP properly
containing the focused object (Kuroda's pied-piping datum). -/
def moPiedPiped : Realization Node := ⟨.obj, [.morpheme .vp]⟩

/-- Their (8): [[Ame]*-mo* furu]F — sentence focus with *mo* on the
subject properly contained in it (Nagano's anti-pied-piping datum). -/
def moAntiPiedPiped : Realization Node := ⟨.s, [.morpheme .sbj]⟩

/-- Their (1): Hungarian movement of exactly the focused argument to
the immediately preverbal focus position. -/
def movementExact : Realization Node := ⟨.obj, [.displacement .obj]⟩

/-- Their (3): [a [használt]F autót] adta el — the whole object DP moves
for a focus on the attributive adjective (Kenesei's pied-piping
datum). -/
def movementPiedPiped : Realization Node := ⟨.att, [.displacement .obj]⟩

/-- Their (7): Péter [a Hamletet] [olvasta fel _ a kertben]F — predicate
focus with movement of the object properly contained in it (Kenesei's
anti-pied-piping datum). -/
def movementAntiPiedPiped : Realization Node := ⟨.vp, [.displacement .obj]⟩

/-! ### All three relations, in both processes -/

/-- Japanese *mo* placement attests all three host–focus relations
(their (2)/(4)/(8)). -/
theorem mo_attests_all_relations :
    moExact.ExactlyTargets ∧ moPiedPiped.PiedPipes ∧
    moAntiPiedPiped.AntiPiedPipes := by decide

/-- Hungarian focus movement attests all three host–focus relations
(their (1)/(3)/(7)). -/
theorem movement_attests_all_relations :
    movementExact.ExactlyTargets ∧ movementPiedPiped.PiedPipes ∧
    movementAntiPiedPiped.AntiPiedPipes := by decide

/-- Neither particle placement nor focus movement strictly targets the
F-marked constituent: each tolerates mismatches in both directions. -/
theorem msf_tolerates_mismatches :
    ¬ moPiedPiped.ExactlyTargets ∧ ¬ moAntiPiedPiped.ExactlyTargets ∧
    ¬ movementPiedPiped.ExactlyTargets ∧
    ¬ movementAntiPiedPiped.ExactlyTargets :=
  ⟨mo_attests_all_relations.2.1.not_exactlyTargets,
   mo_attests_all_relations.2.2.not_exactlyTargets,
   movement_attests_all_relations.2.1.not_exactlyTargets,
   movement_attests_all_relations.2.2.not_exactlyTargets⟩

end BrananErlewine2023
