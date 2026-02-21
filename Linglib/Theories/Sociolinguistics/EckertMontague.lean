import Linglib.Theories.Sociolinguistics.SCM
import Linglib.Core.SocialMeaning
import Mathlib.Tactic.Linarith

/-!
# Eckert-Montague Lift (Burnett 2019, Definition 3.4)
@cite{burnett-2019}

Burnett's set-theoretic reinterpretation of Eckert's (2008) indexical
field. A variant's social meaning is formalized as the set of personae
compatible with the properties it indexes.

## The EM field

Given a grounded indexical field `F : Variant → Finset Property`, the
**Eckert-Montague lift** maps each variant to its compatible personae:

    EM(F)(v) = { p ∈ Persona | F(v) ⊆ p.properties }

This is analogous to Montague's lift from entities to generalized
quantifiers: a variant doesn't denote a single persona but a *set* of
personae — those consistent with the social properties it indexes.

## Bridge: `fromIndexicalField`

The `fromIndexicalField` function converts sign-valued indexical fields
(from `Core.SocialMeaning`) into grounded fields over the SCM property
space. This bridges existing studies (BSB2022, B&S2024) to Burnett's
formalism:
- positive association → positive pole property
- negative association → negative pole property
- zero association → no property indexed on that dimension

## References

* Burnett, H. (2019). Signalling Games, Sociolinguistic Variation,
  and the Construction of Style. *Linguistics & Philosophy* 42: 419–450.
* Eckert, P. (2008). Variation and the indexical field.
  *Journal of Sociolinguistics* 12(4): 453–476.
-/

namespace Sociolinguistics.EckertMontague

open Sociolinguistics
open Sociolinguistics.SCM

-- ============================================================================
-- §1. Grounded indexical field (Burnett Definition 3.4)
-- ============================================================================

/-- A grounded indexical field: maps each variant to a consistent set
    of properties from a property space.

    This is the set-theoretic version of Eckert's indexical field.
    Each variant indexes a set of social properties; the set must be
    internally consistent (no incompatible properties). -/
structure GroundedField (Variant : Type) (ps : PropertySpace) where
  /-- Properties indexed by each variant. -/
  indexedProperties : Variant → Finset ps.Property
  /-- The indexed property set is always consistent. -/
  indexed_consistent : ∀ (v : Variant), ps.isConsistent (indexedProperties v) = true

-- ============================================================================
-- §2. Eckert-Montague lift
-- ============================================================================

/-- The Eckert-Montague lift (Burnett Def. 3.4): the set of personae
    compatible with a variant's indexed properties.

    EM(F)(v) = { p ∈ allPersonaeSets | F(v) ⊆ p }

    More properties indexed → fewer compatible personae (antitonicity). -/
def emField {Variant : Type} {ps : PropertySpace}
    (gf : GroundedField Variant ps) (v : Variant) : Finset (Finset ps.Property) :=
  ps.allPersonaeSets.filter fun persona => gf.indexedProperties v ⊆ persona

/-- The EM lift is antitone: more indexed properties → fewer compatible personae. -/
theorem emField_antitone {Variant : Type} {ps : PropertySpace}
    (gf : GroundedField Variant ps) (v₁ v₂ : Variant)
    (h : gf.indexedProperties v₁ ⊆ gf.indexedProperties v₂) :
    emField gf v₂ ⊆ emField gf v₁ := by
  intro persona hp
  simp only [emField, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, Finset.Subset.trans h hp.2⟩

-- ============================================================================
-- §3. Bridge from sign-valued indexical fields to SCM grounded fields
-- ============================================================================

/-- Decidable predicate: whether an SCM property is indexed by a variant
    given a sign-valued field over social dimensions.

    Maps association signs to SCM poles:
    - `association(v, d) > 0` → positive pole of dimension d
    - `association(v, d) < 0` → negative pole of dimension d
    - `association(v, d) = 0` → no property on dimension d -/
def scmPropertyIndexed {Variant : Type}
    (field : Core.SocialMeaning.IndexicalField Variant SocialDimension)
    (v : Variant) : SCMProperty → Prop
  | .competent     => field.association v .competence > 0
  | .incompetent   => field.association v .competence < 0
  | .warm          => field.association v .warmth > 0
  | .cold          => field.association v .warmth < 0
  | .solidary      => field.association v .antiSolidarity < 0
  | .antiSolidary  => field.association v .antiSolidarity > 0

instance {Variant : Type}
    (field : Core.SocialMeaning.IndexicalField Variant SocialDimension)
    (v : Variant) : DecidablePred (scmPropertyIndexed field v) :=
  fun prop => match prop with
  | .competent     => inferInstanceAs (Decidable (_ > _))
  | .incompetent   => inferInstanceAs (Decidable (_ < _))
  | .warm          => inferInstanceAs (Decidable (_ > _))
  | .cold          => inferInstanceAs (Decidable (_ < _))
  | .solidary      => inferInstanceAs (Decidable (_ < _))
  | .antiSolidary  => inferInstanceAs (Decidable (_ > _))

def scmPropertiesFromField {Variant : Type}
    (field : Core.SocialMeaning.IndexicalField Variant SocialDimension)
    (v : Variant) : Finset SCMProperty :=
  Finset.univ.filter (scmPropertyIndexed field v)

/-- The SCM properties derived from a sign-valued field are always
    consistent: no variant can index both poles of the same dimension,
    because `x > 0` and `x < 0` cannot both hold. -/
theorem scmPropertiesFromField_consistent {Variant : Type}
    (field : Core.SocialMeaning.IndexicalField Variant SocialDimension)
    (v : Variant) :
    scmSpace.isConsistent (scmPropertiesFromField field v) = true := by
  simp only [PropertySpace.isConsistent]
  apply decide_eq_true
  intro p hp q hq hne
  simp only [scmPropertiesFromField, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  cases p <;> cases q <;>
    simp only [scmPropertyIndexed, scmIncompatible, scmSpace] at * <;>
    first | rfl | (exfalso; linarith)

/-- Convert a sign-valued `IndexicalField` to a `GroundedField` over
    the SCM property space. -/
def fromIndexicalField {Variant : Type}
    (field : Core.SocialMeaning.IndexicalField Variant SocialDimension) :
    GroundedField Variant scmSpace :=
  { indexedProperties := scmPropertiesFromField field
    indexed_consistent := scmPropertiesFromField_consistent field }

end Sociolinguistics.EckertMontague
