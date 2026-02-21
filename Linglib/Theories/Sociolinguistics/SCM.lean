import Mathlib.Data.Rat.Defs
import Linglib.Theories.Sociolinguistics.PropertySpace

/-!
# Stereotype Content Model (Fiske et al. 2002, 2007)
@cite{fiske-cuddy-glick-2007}

The SCM property space: 6 properties organized as 3 bipolar dimensions
(competence, warmth, solidarity). The `SocialDimension` type (axis
labels) and `SCMProperty` type (pole endpoints) live here rather than
in `Core/SocialMeaning.lean` because they are specific to the SCM
theoretical framework.

## Types

* `SCMProperty`: the 6 pole endpoints (competent, incompetent, warm,
  cold, solidary, antiSolidary)
* `SocialDimension`: the 3 axis labels (competence, warmth, antiSolidarity)
* `scmSpace`: the SCM property space with 3 incompatibility pairs

## Key results

* `scm_persona_count`: exactly 8 personae (2^3 from 3 binary dimensions)
* `scm_incomp_symm`, `scm_incomp_irrefl`: structural well-formedness

## References

* Fiske, S. T., Cuddy, A. J. C., Glick, P. & Xu, J. (2002). A model
  of (often mixed) stereotype content. *JPSP* 82(6): 878–902.
* Fiske, S. T., Cuddy, A. J. C. & Glick, P. (2007). Universal
  dimensions of social cognition: Warmth and competence.
  *Trends in Cognitive Sciences* 11(2): 77–83.
* Burnett, H. (2019). Signalling Games, Sociolinguistic Variation,
  and the Construction of Style. *Linguistics & Philosophy* 42: 419–450.
-/

namespace Sociolinguistics.SCM

open Sociolinguistics

-- ============================================================================
-- §1. SCM Properties (pole endpoints)
-- ============================================================================

/-- The 6 property endpoints of the SCM: two poles for each of the
    three dimensions.

    These are the *values* that a persona can take — a persona selects
    one pole from each dimension (e.g., competent + warm + solidary). -/
inductive SCMProperty where
  | competent
  | incompetent
  | warm
  | cold
  | solidary
  | antiSolidary
  deriving DecidableEq, BEq, Repr

instance : Fintype SCMProperty where
  elems := {.competent, .incompetent, .warm, .cold, .solidary, .antiSolidary}
  complete := by intro x; cases x <;> simp

-- ============================================================================
-- §2. Social Dimensions (axis labels)
-- ============================================================================

/-- Social-meaning dimensions, grounded in Fiske et al.'s (2002, 2007)
    universal dimensions of social cognition.

    * `competence`: precision, intelligence, reliability, education —
      Fiske et al.'s competence dimension; BSB2022's "Status" PCA factor
      (articulate, intelligent, confident, trustworthy)
    * `warmth`: friendliness, spontaneity, casualness, approachability —
      Fiske et al.'s warmth dimension; BSB2022's "Solidarity" PCA factor
      (friendly, cool, laid-back, likeable)
    * `antiSolidarity`: pedantic, uptight — the negative pole of warmth,
      factored out as an independent PCA component in BSB2022 because
      pedantic/uptight load separately from the positive warmth scales -/
inductive SocialDimension where
  | competence
  | warmth
  | antiSolidarity
  deriving DecidableEq, BEq, Repr

instance : Fintype SocialDimension where
  elems := {.competence, .warmth, .antiSolidarity}
  complete := by intro x; cases x <;> simp

-- ============================================================================
-- §3. Property–dimension mapping
-- ============================================================================

/-- Which dimension a pole belongs to. -/
def SCMProperty.dimension : SCMProperty → SocialDimension
  | .competent | .incompetent => .competence
  | .warm | .cold => .warmth
  | .solidary | .antiSolidary => .antiSolidarity

/-- Whether a pole is the positive end of its dimension. -/
def SCMProperty.isPositive : SCMProperty → Bool
  | .competent | .warm | .solidary => true
  | .incompetent | .cold | .antiSolidary => false

-- ============================================================================
-- §4. Incompatibility relation
-- ============================================================================

/-- Two SCM properties are incompatible iff they are opposite poles of
    the same dimension: competent/incompetent, warm/cold, solidary/antiSolidary. -/
def scmIncompatible : SCMProperty → SCMProperty → Bool
  | .competent, .incompetent | .incompetent, .competent => true
  | .warm, .cold | .cold, .warm => true
  | .solidary, .antiSolidary | .antiSolidary, .solidary => true
  | _, _ => false

theorem scm_incomp_symm (p q : SCMProperty) (h : scmIncompatible p q = true) :
    scmIncompatible q p = true := by
  cases p <;> cases q <;> simp_all [scmIncompatible]

theorem scm_incomp_irrefl (p : SCMProperty) : scmIncompatible p p = false := by
  cases p <;> rfl

-- ============================================================================
-- §5. The SCM property space
-- ============================================================================

/-- The SCM property space: 6 properties with 3 incompatibility pairs
    (opposite poles of each dimension). -/
def scmSpace : PropertySpace :=
  { Property := SCMProperty
    incompatible := scmIncompatible
    incomp_symm := scm_incomp_symm
    incomp_irrefl := scm_incomp_irrefl }

-- ============================================================================
-- §6. Persona count
-- ============================================================================

/-- The SCM has exactly 8 personae (2^3 from 3 binary dimensions). -/
theorem scm_persona_count :
    scmSpace.allPersonaeSets.card = 8 := by native_decide

/-- Incompatible properties are always on the same dimension. -/
theorem incomp_same_dimension (p q : SCMProperty)
    (h : scmIncompatible p q = true) :
    p.dimension = q.dimension := by
  cases p <;> cases q <;> simp_all [scmIncompatible, SCMProperty.dimension]

/-- Incompatible properties always have opposite polarity. -/
theorem incomp_opposite_polarity (p q : SCMProperty)
    (h : scmIncompatible p q = true) :
    p.isPositive ≠ q.isPositive := by
  cases p <;> cases q <;> simp_all [scmIncompatible, SCMProperty.isPositive]

end Sociolinguistics.SCM
