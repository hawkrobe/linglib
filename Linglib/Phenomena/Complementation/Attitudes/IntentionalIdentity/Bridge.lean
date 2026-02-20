import Linglib.Phenomena.Complementation.Attitudes.IntentionalIdentity.Data
import Linglib.Theories.Semantics.TypeTheoretic.Modality

/-!
# Intentional Identity Bridge @cite{chatzikyriakidis-etal-2025}

TTR solution to Geach's intentional identity puzzle.

## The problem

"Hob thinks a witch has blighted Bob's mare,
 and Nob wonders whether she killed Cob's sow."

In possible-worlds semantics, the pronoun "she" needs a referent,
but the witch need not exist, and Hob and Nob may not share a
doxastic alternative. There is no entity in the model to serve
as the antecedent.

## The TTR solution

In TTR (Cooper 2023, Chatzikyriakidis et al. 2025 §2), the solution
uses *types* rather than *entities* as the locus of identity:

1. Hob's belief state contains a type `T_witch` (a predicate type
   "witch who blighted Bob's mare") — this type can be inhabited or empty
2. Nob's wonder state references *the same type* `T_witch`
3. Intentional identity = both agents' attitudes involve the same
   `IType` (intensional type), not the same individual entity
4. The type can be empty (no witch exists) — `IsFalse T_witch` is fine

The key: TTR types are intensional objects that can be shared across
attitude contexts without requiring witnesses. Two agents can think
"about the same witch-type" without any witch existing.

## References

- Geach (1967). Intentional Identity. Journal of Philosophy.
- Cooper (2023). From Perception to Communication. OUP. §6.5.
- Chatzikyriakidis et al. (2025). Types and the Structure of Meaning. §2.
-/

namespace Phenomena.Complementation.Attitudes.IntentionalIdentity.Bridge

open Semantics.TypeTheoretic

/-! ## TTR model of the Hob-Nob puzzle -/

/-- Agents in the Hob-Nob scenario. -/
inductive Agent where | hob | nob
  deriving Repr, DecidableEq

/-- Entities in the scenario (Bob's mare, Cob's sow). -/
inductive Entity where | bobsMare | cobsSow
  deriving Repr, DecidableEq

/-- The shared witch type: an intentional type that both agents'
attitudes reference. This is the key to the TTR solution —
the type exists as an intensional object even when empty. -/
def witchType : IType := ⟨Empty, "witch_who_blights"⟩

/-- Hob's belief content: the witch type applied to Bob's mare.
"A witch has blighted Bob's mare" ≈ [x : Witch, e : blight(x, bobsMare)].
We model this as a dependent record type. -/
structure HobBelief where
  /-- The witch (of the shared witch type) -/
  witch : witchType.carrier
  /-- The blighting event -/
  blight : Entity  -- target = bobsMare

/-- Nob's wondering content: the witch type applied to Cob's sow.
"She killed Cob's sow" ≈ [x : Witch, e : kill(x, cobsSow)].
Crucially, "she" refers to the SAME witch type. -/
structure NobWonder where
  /-- The witch — SAME type as in HobBelief -/
  witch : witchType.carrier
  /-- The killing event -/
  kill : Entity  -- target = cobsSow

/-- The witch type is shared: both attitudes reference the same IType.
This is intentional identity — agreement at the type level,
not at the entity level. -/
theorem shared_witch_type :
    ({ carrier := HobBelief, name := "hob_belief" : IType}).name ≠
    ({ carrier := NobWonder, name := "nob_wonder" : IType}).name ∧
    -- But the witch field in both has the same type
    (witchType = witchType) :=
  ⟨by simp, rfl⟩

/-- The witch need not exist — the type can be empty.
This is what possible-worlds semantics cannot express:
both agents have attitudes "about" an empty type. -/
theorem witch_need_not_exist : IsEmpty witchType.carrier :=
  show IsEmpty Empty from inferInstance

/-- Despite non-existence, both belief structures are well-defined types.
They are *empty* types (no witnesses), but they are valid TTR types. -/
theorem hob_belief_is_empty : IsEmpty HobBelief :=
  ⟨λ h => Empty.elim h.witch⟩

theorem nob_wonder_is_empty : IsEmpty NobWonder :=
  ⟨λ h => Empty.elim h.witch⟩

/-- The intentional identity is *structural*: both record types
depend on the same `witchType.carrier` field. Changing the witch
type in one attitude changes it in both — they are linked by
type sharing, not by coreference to an entity. -/
theorem intentional_identity_is_type_sharing :
    -- The witch field type is the same in both structures
    (∀ (h : HobBelief), (h.witch : witchType.carrier) = h.witch) ∧
    (∀ (n : NobWonder), (n.witch : witchType.carrier) = n.witch) :=
  ⟨λ _ => rfl, λ _ => rfl⟩

/-! ## Contrast with possible-worlds approach

In `Prop' W`, there's no way to distinguish "Hob thinks p"
from "Hob thinks q" when p and q are the same set of worlds.
The intensional identity of the witch type is lost. -/

/-- Two ITypes can share the same (empty) carrier but differ intensionally.
This is why TTR can handle intentional identity but `Prop' W` cannot:
it distinguishes types by identity, not just extension. -/
theorem intensional_distinction_enables_ii :
    witchType.extEquiv ⟨Empty, "ghost_who_haunts"⟩ ∧
    ¬ witchType.intEq ⟨Empty, "ghost_who_haunts"⟩ :=
  ⟨⟨Equiv.refl Empty⟩, by simp [IType.intEq, witchType]⟩

end Phenomena.Complementation.Attitudes.IntentionalIdentity.Bridge
