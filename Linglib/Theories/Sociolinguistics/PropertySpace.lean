import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

/-!
# Property Spaces and Personae (Burnett 2019, Definitions 3.1–3.3)
@cite{burnett-2019}

Burnett's formalization of Eckert's (2008) indexical field as a
*property space* — a set of social properties with incompatibility
constraints — from which *personae* emerge as maximal consistent subsets.

## Core concepts

**Property space** (Def. 3.1): A finite set of properties plus a
symmetric, irreflexive incompatibility relation. Two properties are
incompatible if they cannot co-occur in any coherent persona (e.g.,
"competent" and "incompetent").

**Consistency** (Def. 3.2): A set of properties is consistent if no
two distinct members are incompatible.

**Persona** (Def. 3.3): A maximal consistent subset of the property
space — a persona that takes a stance on every dimension (every
bipolar pair has exactly one pole selected).

## References

* Burnett, H. (2019). Signalling Games, Sociolinguistic Variation,
  and the Construction of Style. *Linguistics & Philosophy* 42: 419–450.
* Eckert, P. (2008). Variation and the indexical field.
  *Journal of Sociolinguistics* 12(4): 453–476.
-/

namespace Sociolinguistics

-- ============================================================================
-- §1. Property Space (Burnett Definition 3.1)
-- ============================================================================

/-- A property space (Burnett Def. 3.1): a finite set of social properties
    with a symmetric, irreflexive incompatibility relation.

    Incompatible properties cannot co-occur in any coherent persona.
    For example, "competent" and "incompetent" are incompatible: a
    coherent persona selects one pole of each bipolar dimension. -/
structure PropertySpace where
  /-- The type of social properties. -/
  Property : Type
  /-- Two properties are incompatible (cannot co-occur in a persona). -/
  incompatible : Property → Property → Bool
  /-- Incompatibility is symmetric. -/
  incomp_symm : ∀ (p q : Property), incompatible p q = true → incompatible q p = true
  /-- No property is incompatible with itself. -/
  incomp_irrefl : ∀ (p : Property), incompatible p p = false
  /-- Properties form a finite type. -/
  [propFintype : Fintype Property]
  /-- Properties have decidable equality. -/
  [propDecEq : DecidableEq Property]

attribute [instance] PropertySpace.propFintype PropertySpace.propDecEq

-- ============================================================================
-- §2. Consistency (Burnett Definition 3.2)
-- ============================================================================

/-- A set of properties is consistent if no two distinct members are
    incompatible (Burnett Def. 3.2). -/
def PropertySpace.isConsistent (ps : PropertySpace) (S : Finset ps.Property) : Bool :=
  decide (∀ p ∈ S, ∀ q ∈ S, p ≠ q → ps.incompatible p q = false)

-- ============================================================================
-- §3. Persona (Burnett Definition 3.3)
-- ============================================================================

/-- A persona (Burnett Def. 3.3): a maximal consistent subset of the
    property space. Every dimension is decided — a persona takes a
    stance on each bipolar opposition.

    The maximality condition ensures that a persona is as specific as
    possible: you can't add any property without creating an
    incompatibility. -/
structure Persona (ps : PropertySpace) where
  /-- The properties that characterize this persona. -/
  properties : Finset ps.Property
  /-- The property set is consistent (no incompatible pairs). -/
  consistent : ps.isConsistent properties = true
  /-- The property set is maximal: adding any property breaks consistency. -/
  maximal : ∀ (p : ps.Property), p ∉ properties →
    ∃ (q : ps.Property), q ∈ properties ∧ ps.incompatible p q = true

-- ============================================================================
-- §4. Enumeration
-- ============================================================================

/-- Enumerate all personae by filtering the powerset for maximal consistent
    subsets.

    For small property spaces (like the SCM with 6 properties), this is
    tractable. The result is a `Finset (Finset ps.Property)` containing
    exactly the property sets of all personae. -/
def PropertySpace.allPersonaeSets (ps : PropertySpace) : Finset (Finset ps.Property) :=
  Finset.univ.powerset.filter fun S =>
    ps.isConsistent S &&
    decide (∀ (p : ps.Property), p ∈ S ∨ ∃ q ∈ S, ps.incompatible p q = true)

end Sociolinguistics
