import Linglib.Semantics.Intensional.Rigidity
import Mathlib.Data.Set.Function

/-!
# Acquaintance and Conceptual Covers
[lewis-1979-attitudes] (de se / de re reduction via centered worlds);
[cresswell-vonstechow-1982] (de re belief generalized);
[aloni-2001] (conceptual covers); [abusch-1997] (the temporal
analogue: a "way of identifying a time" is the temporal time-concept
licensing temporal de re).

A polymorphic substrate for acquaintance-relation semantics: a `Cover Idx Res`
is a set of intensions over an evaluation index `Idx` that picks out values
in `Res`; an entity is *acquainted* (at index `p`) when some concept in the
cover identifies it at `p`.

Instantiated at `Idx := Assignment E × WitnessSeq E`, `Res := E` this is the
PLA cover system in `Semantics/Dynamic/PLA/Belief.lean`.
Instantiated at `Idx := KContext W E P T`, `Res := T` this is the Abusch
1997 time-concept (def. 13). The polymorphic substrate makes the
individual ↔ temporal de re parallel that Abusch's prose asserts true by
construction.

## Reuse

Built on `Intensional.Intension W τ` (`Semantics/Intensional/Rigidity.lean`) — no
parallel `Concept` type is introduced. The acquaintance predicate is
`Set.image`-membership; cover exhaustiveness is `Set.SurjOn`. Both are
mathlib idioms — the only genuinely new content here is naming.
-/

namespace Semantics.Reference.Acquaintance

open Intensional (Intension)

/-- A conceptual cover ([aloni-2001] §3.2): a set of intensions over
    an evaluation index `Idx` representing the agent's available "ways of
    identifying" values of type `Res`.

    The Abusch 1997 §3 acquaintance relation `R : eeiwt` is the temporal
    instance with `Idx := KContext W E P T`, `Res := T`. -/
abbrev Cover (Idx Res : Type*) : Type _ := Set (Intension Idx Res)

/-- A cover is exhaustive on a domain when, at every index, every value
    in the domain is picked out by some concept in the cover.

    Mathlib idiom: `Set.SurjOn (· p) C dom`. -/
def Cover.isExhaustiveOn {Idx Res : Type*} (C : Cover Idx Res)
    (dom : Set Res) : Prop :=
  ∀ p : Idx, Set.SurjOn (· p) C dom

/-- [lewis-1979-attitudes]'s acquaintance relation, generalized: `r` is
    acquainted-with at index `p` (relative to `C`) when some concept in
    `C` picks out `r` at `p`.

    Mathlib idiom: `r ∈ ((· p) '' C)` — set-image membership. -/
def isAcquaintedWith {Idx Res : Type*}
    (r : Res) (C : Cover Idx Res) (p : Idx) : Prop :=
  r ∈ ((fun (c : Intension Idx Res) => c p) '' C)

/-- [aloni-2001]'s name cover: rigid concepts (one per entity).
    Each entity is identified by its constant intension `Intension.rigid`.
    This is the "de re" cover — entities thought of as themselves. -/
def nameCover {Idx Res : Type*} (dom : Set Res) : Cover Idx Res :=
  { c | ∃ r ∈ dom, c = Intension.rigid (W := Idx) r }

/-- Every concept in a name cover is rigid. -/
theorem nameCover_rigid {Idx Res : Type*} (dom : Set Res) :
    ∀ c ∈ nameCover (Idx := Idx) dom, Intension.IsRigid c := by
  intro c hc
  obtain ⟨r, _, hcr⟩ := hc
  subst hcr
  exact Intension.rigid_isRigid r

/-- The name cover is exhaustive over its domain. -/
theorem nameCover_isExhaustiveOn {Idx Res : Type*} (dom : Set Res) :
    (nameCover (Idx := Idx) dom).isExhaustiveOn dom := by
  intro p r hr
  refine ⟨Intension.rigid (W := Idx) r, ?_, rfl⟩
  exact ⟨r, hr, rfl⟩

/-- An entity in the name cover's domain is acquainted-with via the name
    cover at every index — names are rigid, so they identify entities at
    all evaluation points. -/
theorem nameCover_isAcquaintedWith_of_mem {Idx Res : Type*} (dom : Set Res)
    (r : Res) (hr : r ∈ dom) (p : Idx) :
    isAcquaintedWith r (nameCover (Idx := Idx) dom) p := by
  refine ⟨Intension.rigid (W := Idx) r, ⟨r, hr, rfl⟩, rfl⟩

end Semantics.Reference.Acquaintance
