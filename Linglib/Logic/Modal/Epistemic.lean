import Linglib.Discourse.CommonGround
import Linglib.Logic.Modal.Basic
import Mathlib.Order.CompleteLattice.Basic

/-!
# Multi-agent epistemic logic

This file defines the group knowledge operators of [fagin-halpern-moses-vardi-1995] over
agent-indexed accessibility relations `Rs : E → W → W → Prop`: individual knowledge `Kᵢ` is
`box (Rs i)`, everyone-knows `E_G` is `box` over the union `⨆ i ∈ G, Rs i`, distributed
knowledge `D_G` is `box` over the intersection `⨅ i ∈ G, Rs i`, and common knowledge `C_G` is
`box` over the transitive closure of the union — `φ` holds at every world reachable by a chain
of members' accessibility. The infinite-conjunction form `E_G φ ∧ E_G (E_G φ) ∧ ⋯` is the
theorem `commonKnowledge_iff_forall_iterate`, an instance of `ModalLogic.box_transGen_iff`.
Belief is the same operator over a KD45 frame (`ModalLogic.IsKD45Frame`), with the D, 4, and
5 laws `ModalLogic.box_D`, `ModalLogic.box_four`, and `ModalLogic.box_five`.

## Main definitions

* `knows`, `everyoneKnows`, `distributedKnowledge`, `commonKnowledge`: `Kᵢ`, `E_G`, `D_G`,
  `C_G`.
* `CommonGround.GroundedIn`: a common ground whose context set is exactly what is common
  knowledge ([stalnaker-2002]).

## Main results

* `knows_of_everyoneKnows`, `everyoneKnows_of_commonKnowledge`,
  `distributedKnowledge_of_knows`: the hierarchy `C_G ≤ E_G ≤ Kᵢ ≤ D_G`, each by restricting
  accessibility (`ModalLogic.box_restrict`).
* `commonKnowledge_iff_forall_iterate`: `C_G` as the infinite conjunction of iterated `E_G`.

## References

* [fagin-halpern-moses-vardi-1995] — group knowledge and its reachability semantics
* [halpern-2003] — the same operators in the uncertainty setting
* [fagin-halpern-1994] — the probabilistic extension, `Studies/FaginHalpern1994.lean`
* [hintikka-1962] — knowledge as `box`
* [stalnaker-2002] — common ground as common knowledge
-/

namespace ModalLogic.Epistemic

open ModalLogic Relation

variable {W E : Type*} {Rs : E → W → W → Prop} {i : E} {G : Set E} {φ : W → Prop} {w : W}

/-- Agent `i` knows `φ` at `w`: `φ` holds at every world `i` considers possible. -/
def knows (Rs : E → W → W → Prop) (i : E) (φ : W → Prop) (w : W) : Prop := box (Rs i) φ w

/-- Everyone in `G` knows `φ` at `w`: `box` over the union of the members' accessibility. -/
def everyoneKnows (Rs : E → W → W → Prop) (G : Set E) (φ : W → Prop) (w : W) : Prop :=
  box (⨆ i ∈ G, Rs i) φ w

/-- Distributed knowledge: what `G` would know by pooling its information, `box` over the
intersection of the members' accessibility. -/
def distributedKnowledge (Rs : E → W → W → Prop) (G : Set E) (φ : W → Prop) (w : W) : Prop :=
  box (⨅ i ∈ G, Rs i) φ w

/-- Common knowledge: `φ` holds at every world reachable from `w` by a chain of members'
accessibility. -/
def commonKnowledge (Rs : E → W → W → Prop) (G : Set E) (φ : W → Prop) (w : W) : Prop :=
  box (TransGen (⨆ i ∈ G, Rs i)) φ w

theorem everyoneKnows_iff : everyoneKnows Rs G φ w ↔ ∀ i ∈ G, knows Rs i φ w := by
  simp only [everyoneKnows, knows, box, iSup_apply, iSup_Prop_eq, exists_prop,
    forall_exists_index, and_imp]
  exact ⟨fun h i hi v hv => h v i hi hv, fun h v i hi hv => h i hi v hv⟩

/-! ### The knowledge hierarchy -/

theorem knows_of_everyoneKnows (hi : i ∈ G) (h : everyoneKnows Rs G φ w) : knows Rs i φ w :=
  box_restrict φ (le_iSup₂ (f := fun i (_ : i ∈ G) => Rs i) i hi) w h

theorem everyoneKnows_of_commonKnowledge (h : commonKnowledge Rs G φ w) :
    everyoneKnows Rs G φ w :=
  box_restrict φ (fun _ _ => TransGen.single) w h

theorem distributedKnowledge_of_knows (hi : i ∈ G) (h : knows Rs i φ w) :
    distributedKnowledge Rs G φ w :=
  box_restrict φ (iInf₂_le (f := fun i (_ : i ∈ G) => Rs i) i hi) w h

/-- Common knowledge is veridical once some member's accessibility is reflexive. -/
theorem commonKnowledge_imp (hi : i ∈ G) [hR : Std.Refl (Rs i)]
    (h : commonKnowledge Rs G φ w) : φ w :=
  h w (TransGen.single (le_iSup₂ (f := fun i (_ : i ∈ G) => Rs i) i hi w w (hR.refl w)))

/-- Common knowledge is the infinite conjunction `E_G φ ∧ E_G (E_G φ) ∧ ⋯`. -/
theorem commonKnowledge_iff_forall_iterate :
    commonKnowledge Rs G φ w ↔ ∀ n, (everyoneKnows Rs G)^[n + 1] φ w :=
  box_transGen_iff _

end ModalLogic.Epistemic

namespace CommonGround

variable {W E : Type*}

/-- A common ground is grounded in common knowledge when its context set is exactly the set
of worlds where each of its propositions is common knowledge among `G` ([stalnaker-2002]). -/
def GroundedIn (cg : CommonGround W) (Rs : E → W → W → Prop) (G : Set E) : Prop :=
  ∀ w, w ∈ cg.contextSet ↔
    ∀ p ∈ cg.propositions, ModalLogic.Epistemic.commonKnowledge Rs G (· ∈ p) w

end CommonGround
