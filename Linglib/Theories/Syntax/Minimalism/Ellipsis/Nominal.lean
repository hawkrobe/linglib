import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Properties

/-!
# Nominal Ellipsis Licensing
@cite{merchant-2001} @cite{saab-2026} @cite{lobeck-1995}

NP-ellipsis is licensed when the Num head carries an [E] feature,
which permits PF-deletion of the nominal argument domain (complement
of Num — everything at or below nP).

## Nominal Argument Domain

The nominal argument domain is {N, n} (F0–F1), parallel to the verbal
argument domain {V, v}. Num (F2) and above are outside.
-/

namespace Minimalism.Ellipsis.Nominal

open Minimalism

-- ═══════════════════════════════════════════════════════════════
-- § 1: NP-Ellipsis Licensing
-- ═══════════════════════════════════════════════════════════════

/-- Nominal ellipsis license: Num[E] feature.
    NP-ellipsis is licensed when the Num head carries an [E] feature,
    which permits PF-deletion of the nominal argument domain (complement
    of Num — everything at or below nP). -/
structure NominalEllipsisLicense where
  /-- Does Num carry [E]? -/
  numHasE : Bool
  /-- The nominal argument domain boundary (n for full DPs). -/
  argDomainBoundary : Cat := .n
  deriving Repr, DecidableEq

/-- Is NP-ellipsis licensed? Requires Num[E]. -/
def NominalEllipsisLicense.isLicensed (nel : NominalEllipsisLicense) : Bool :=
  nel.numHasE

-- ═══════════════════════════════════════════════════════════════
-- § 2: Nominal Argument Domain (@cite{saab-2026})
-- ═══════════════════════════════════════════════════════════════

/-- N is within the nominal argument domain (F0 ≤ F1 = n). -/
theorem n_lexical_in_nominal_argdomain :
    isInArgumentDomain .N .D = true := by decide

/-- n is within the nominal argument domain (F1 ≤ F1). -/
theorem n_functional_in_nominal_argdomain :
    isInArgumentDomain .n .D = true := by decide

/-- Num is NOT in the nominal argument domain (F2 > F1 = n). -/
theorem num_not_in_nominal_argdomain :
    isInArgumentDomain .Num .D = false := by decide

/-- Q is NOT in the nominal argument domain (F3 > F1 = n). -/
theorem q_not_in_nominal_argdomain :
    isInArgumentDomain .Q .D = false := by decide

/-- D is NOT in the nominal argument domain (F4 > F1 = n). -/
theorem d_not_in_nominal_argdomain :
    isInArgumentDomain .D .D = false := by decide

/-- NP-ellipsis with Num[E]: pseudo-partitive/quantificational
    binominals license deletion of the nominal argument domain. -/
theorem pseudopartitive_licenses_npe :
    NominalEllipsisLicense.isLicensed ⟨true, .n⟩ = true := by decide

/-- NP-ellipsis without Num[E]: qualitative binominals
    (with EquP + indexical empty noun) block NP-ellipsis. -/
theorem qualitative_blocks_npe :
    NominalEllipsisLicense.isLicensed ⟨false, .n⟩ = false := by decide

end Minimalism.Ellipsis.Nominal
