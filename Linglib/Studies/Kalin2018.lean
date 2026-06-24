import Linglib.Syntax.Case.Assigner

/-!
# Kalin (2018) — Licensing and Differential Object Marking
[kalin-2018] [marantz-1991]

[kalin-2018] derives differential object marking (DOM) from nominal
*licensing* rather than object visibility, raising, or differentiation. Two
parameters interact: (i) which nominals *require* licensing (in Senaya, only
*specific* ones), and (ii) where the licensers are — every clause has one
obligatory **primary** licenser (always merged, licensing the closest
nominal) plus **secondary** licensers that merge only as a last resort, when
their absence would leave some needy nominal unlicensed. DOM is the visible
signature of a secondary licenser activating.

The motivating data are from the Neo-Aramaic language **Senaya**, where DOM
surfaces as differential verbal *agreement* (an L-suffix), not case — and
[kalin-2018] argues case and agreement are two reflexes of one licensing
process, so we model the agreement marking abstractly through the licensing
substrate's outcome (`Syntax/Case/Licensing.lean`). The Senaya facts (paper
examples around the object-agreement and aspect-split data): a *specific*
object triggers agreement, a *nonspecific* one does not, and — the crux — in
the **perfective** base the object position is *unlicensed*, so a specific
object (which needs licensing) is banned there entirely.

That perfective ban is [kalin-2018]'s argument *against* a no-licensing view
of case ([marantz-1991], [preminger-2014]): if nominals never needed abstract
licensing, the ban would be unexplained. The flagship theorem below states
this divergence formally, via the shared `Assigner` harness
(`Syntax/Case/Assigner.lean`): on the perfective object, a Marantz-style
total configurational account assigns a case, while Kalin licensing crashes —
the two accounts disagree precisely where licensing is unavailable.
-/

namespace Kalin2018

open Syntax.Case
open Syntax.Case.Licensing (ClauseLicensers Licenser LicensingOutcome LicensedNP
  licenseNPs getOutcomeOf)

/-! ### Senaya clause configurations

The aspect split as licenser availability: the imperfective base offers a
secondary licenser for a specific object (yielding DOM agreement); the
perfective base offers none (so a specific object cannot be licensed). The
`assignedCase` fields abstract the agreement marking — `nom` for the primary
(subject) relation, `acc` for the object relation. -/

/-- Imperfective base: a secondary licenser is available for a specific
    object. -/
def imperfectiveClause : ClauseLicensers :=
  { primary := { kind := .primary, head := "Asp.ipfv", assignedCase := .nom }
  , secondaries := [{ kind := .secondary, head := "v", assignedCase := .acc }] }

/-- Perfective base: no secondary licenser — the object position is
    unlicensed ([kalin-2018]'s central Senaya claim). -/
def perfectiveClause : ClauseLicensers :=
  { primary := { kind := .primary, head := "Asp.pfv", assignedCase := .nom }
  , secondaries := [] }

/-- A transitive clause with a **specific** object: both nominals carry the
    licensing requirement. -/
def specificObjectClause : List LicensedNP :=
  [ { label := "subj", lexicalCase := none, needsLicensing := true }
  , { label := "obj",  lexicalCase := none, needsLicensing := true } ]

/-- A transitive clause with a **nonspecific** object: the object lacks the
    licensing requirement, so it is interpretable in situ. -/
def nonspecificObjectClause : List LicensedNP :=
  [ { label := "subj", lexicalCase := none, needsLicensing := true }
  , { label := "obj",  lexicalCase := none, needsLicensing := false } ]

/-! ### The Senaya DOM pattern -/

/-- Imperfective: a specific object is licensed by the secondary licenser,
    surfacing as DOM agreement. -/
theorem specificObject_licensed_imperfective :
    getOutcomeOf "obj" (licenseNPs imperfectiveClause specificObjectClause)
      = some (.bySecondary "v" .acc) := by decide

/-- Perfective: a specific object **cannot be licensed** (no secondary
    licenser available) and crashes — Senaya's ban on specific objects in
    the perfective base. -/
theorem specificObject_unlicensed_perfective :
    getOutcomeOf "obj" (licenseNPs perfectiveClause specificObjectClause)
      = some .unlicensed := by decide

/-- A nonspecific object does not need licensing, so it is fine in the
    perfective (licensed trivially by the primary, no DOM marking). -/
theorem nonspecificObject_fine_perfective :
    getOutcomeOf "obj" (licenseNPs perfectiveClause nonspecificObjectClause)
      = some (.byPrimary "Asp.pfv" .nom) := by decide

/-- Subjects are *not* differential: the closest nominal to the obligatory
    primary licenser is always licensed, in either aspect. -/
theorem subject_always_licensed :
    getOutcomeOf "subj" (licenseNPs perfectiveClause specificObjectClause)
      = some (.byPrimary "Asp.pfv" .nom) ∧
    getOutcomeOf "subj" (licenseNPs imperfectiveClause specificObjectClause)
      = some (.byPrimary "Asp.ipfv" .nom) := by
  exact ⟨by decide, by decide⟩

/-! ### The flagship divergence: licensing vs. no-licensing -/

/-- On the perfective object, the two accounts assign **incompatible
    verdicts**: a Marantz-style total configurational account gives it a
    structural accusative, while Kalin licensing crashes it (`uncased`,
    caseless). This is the witness behind the divergence. -/
theorem perfective_object_verdicts :
    dependentAssigner .accusative specificObjectClause "obj"
      = some ⟨.structural, some .acc⟩ ∧
    kalinAssigner perfectiveClause specificObjectClause "obj"
      = some ⟨.uncased, none⟩ := by
  exact ⟨by decide, by decide⟩

/-- **Licensing diverges from total configurational case assignment**
    ([kalin-2018] vs [marantz-1991]). The two accounts disagree on the
    surface case of the perfective object: the dependent-case account assigns
    it accusative (case assignment is total — it never crashes), whereas
    Kalin licensing leaves it unlicensed. [kalin-2018]'s point: under a
    no-licensing view the perfective ban on specific objects is unexplained;
    under licensing it follows, because the perfective object position offers
    no licenser. -/
theorem dependentCase_vs_licensing_diverge_on_perfective_object :
    ¬ AgreesOnCase (dependentAssigner .accusative)
        (kalinAssigner perfectiveClause) specificObjectClause := by decide

end Kalin2018
