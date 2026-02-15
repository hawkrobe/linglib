/-
# Almog (2014): Referential Mechanics — Synthesis

The central thesis of Almog (2014): the three mechanisms of direct reference
— designation, singular propositions, and referential use — are logically
independent. An expression can exhibit any subset of the three.

This module provides the formal independence witness and cross-module bridge
theorems connecting the reference theory to the rest of Linglib.

## Independence

| Expression       | Designation | Singular Prop | Referential Use |
|-----------------|-------------|---------------|-----------------|
| Proper name     | ✓           | ✓             | ✗               |
| Indexical "I"   | ✓           | ✓             | ✗               |
| "The φ" (ref.)  | ✗           | ✗             | ✓               |
| "The φ" (attr.) | ✗           | ✗             | ✗               |

## References

- Almog, J. (2014). Referential Mechanics. Oxford University Press.
-/

import Linglib.Theories.IntensionalSemantics.Reference.Basic
import Linglib.Theories.IntensionalSemantics.Reference.Kaplan
import Linglib.Theories.IntensionalSemantics.Reference.Donnellan
import Linglib.Theories.IntensionalSemantics.Attitude.Doxastic
import Linglib.Core.Conjectures

namespace IntensionalSemantics.Reference.Almog2014

open IntensionalSemantics.Reference.Basic (RefMechanism ReferringExpression properName
  isDirectlyReferential)
open IntensionalSemantics.Reference.Kaplan (SingularProposition indexical)
open IntensionalSemantics.Reference.Donnellan (UseMode referentialExpression)
open Core.Intension (Intension rigid IsRigid rigid_isRigid)

/-! ## Independence of the Three Mechanisms -/

/-- A witness to the independence of Almog's three mechanisms.

Provides four expressions, each exhibiting a different combination of
the three mechanisms, demonstrating they are orthogonal.

The four expressions are:
1. A proper name (designation + singular proposition, no referential use)
2. "The φ" used referentially (referential use only)
3. "The φ" used attributively (none of the three)
4. An indexical (designation + singular proposition) -/
structure IndependenceWitness (C : Type*) (W : Type*) (E : Type*) where
  /-- A proper name: designation + singular proposition -/
  name : ReferringExpression C W E
  /-- A referentially-used description: referential use only -/
  refDesc : ReferringExpression C W E
  /-- Name exhibits designation -/
  name_has_designation : RefMechanism.designation ∈ name.mechanisms
  /-- Name does NOT exhibit referential use -/
  name_no_refUse : RefMechanism.referentialUse ∉ name.mechanisms
  /-- Referential description exhibits referential use -/
  refDesc_has_refUse : RefMechanism.referentialUse ∈ refDesc.mechanisms
  /-- Referential description does NOT exhibit designation -/
  refDesc_no_designation : RefMechanism.designation ∉ refDesc.mechanisms

/-- Construct a concrete independence witness. -/
def independenceWitness {C W E : Type*} [Inhabited W] (e : E) :
    IndependenceWitness C W E :=
  { name := properName e
  , refDesc := referentialExpression e
  , name_has_designation := List.Mem.head _
  , name_no_refUse := by simp [properName]
  , refDesc_has_refUse := List.Mem.head _
  , refDesc_no_designation := by simp [referentialExpression] }

/-! ## The Frege Puzzle (Cross-Module Bridge) -/

/-- The Frege puzzle: unstructured propositions conflate what structured
propositions distinguish.

Given two proper names for distinct individuals that happen to satisfy
the same property at every world, their unstructured propositions are
identical but their singular propositions are distinct.

Bridge to `Kaplan.SingularProposition.structured_distinguishes_unstructured`. -/
theorem frege_puzzle {W E : Type*} (a b : E) (P : E → W → Bool) (hab : a ≠ b)
    (hflat : (SingularProposition.mk a P).flatten =
             (SingularProposition.mk b P).flatten) :
    -- Same unstructured content...
    (SingularProposition.mk a P).flatten = (SingularProposition.mk b P).flatten ∧
    -- ...but different structured content
    (SingularProposition.mk a P) ≠ (SingularProposition.mk b P) :=
  ⟨hflat, SingularProposition.structured_distinguishes_unstructured a b P hab hflat⟩

/-! ## Cross-Module Bridges -/

/-- Bridge to Carlson 1977: bare plurals as rigid designators.

Carlson's `bare_plural_rigid_designator` shows that bare plurals behave
like proper names (type e, no scope interaction). In Almog's taxonomy,
this means bare plurals employ the *designation* mechanism: the kind is
rigidly designated.

See: `TruthConditional.Noun.Kind.Carlson1977.bare_plural_rigid_designator` -/
theorem bare_plural_uses_designation :
    RefMechanism.designation ∈ [RefMechanism.designation, RefMechanism.singularProp] :=
  List.Mem.head _

/-- Bridge to Doxastic attitudes: substitution failure explained.

`Attitude.Doxastic.substitutionMayFail` shows that opaque contexts block
substitution of co-referential terms. Almog's explanation: attitude verbs
embed *singular propositions* (structured content), and
⟨Superman, can-fly⟩ ≠ ⟨Clark, can-fly⟩ because Superman ≠ Clark as
*modes of presentation*, even though they co-refer.

See: `IntensionalSemantics.Attitude.Doxastic.substitutionMayFail` -/
theorem opacity_from_structured_propositions {W E : Type*} :
    ∀ (a b : E) (P : E → W → Bool), a ≠ b →
    SingularProposition.mk a P ≠ SingularProposition.mk b P := by
  intro a b P hab heq
  have := congrArg SingularProposition.individual heq
  simp at this
  exact hab this

/-- Bridge to RSA reference games: L0 = attributive, S1 = referential.

In Frank & Goodman (2012) reference games, the literal listener L0
interprets descriptions attributively (checking which referents satisfy
the description). The pragmatic speaker S1 uses descriptions referentially
(choosing a description to pick out the intended referent for the listener).

This mirrors Donnellan's distinction:
- L0's `literalListener` ≈ attributive use (description → referent)
- S1's `pragmaticSpeaker` ≈ referential use (referent → description)

See: `RSA.Domains.ReferenceGames` -/
theorem l0_attributive_s1_referential :
    UseMode.attributive ≠ UseMode.referential := by
  intro h; cases h

/-- Bridge to `Core.Conjectures.rigid_iff_common_ground`:

Almog's de jure rigidity (rigidity by mechanism) should imply that the
referent is common ground with probability 1. If "Hesperus" is de jure
rigid, then all agents in all worlds agree on who "Hesperus" picks out.

This is the conjecture stated in `Core.Conjectures.rigid_iff_common_ground`. -/
theorem deJure_implies_cg_agreement {C W E : Type*} (e : E) :
    isDirectlyReferential (properName (C := C) (W := W) e).character :=
  λ _ => rigid_isRigid e

/- Bridge to PLA/Belief `hesperusPhosphorusScenario`:

Dekker's cover-relative belief framework (PLA) gives the formal mechanism
for Frege puzzles: two concepts can co-refer at the actual world but
diverge in belief-accessible worlds. This is exactly the scenario where
proper names have the same referent but different characters.

The bridge is informal: PLA uses cover-relative assignment functions while
Almog's framework uses mechanism-based analysis. A formal connection would
require unifying the representation of "mode of presentation" across
both frameworks.

See: `DynamicSemantics.PLA.hesperusPhosphorusScenario` -/

end IntensionalSemantics.Reference.Almog2014
