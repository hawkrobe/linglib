import Linglib.Core.Relativization.Basic
import Linglib.Typology.Relativization.Defs

/-!
# Hebrew Relativization Fragment
@cite{keenan-comrie-1977} @cite{sichel-2014}

Two relative clause markers (discussed §1.3.2):
- Complementizer *she-* with gap (-case, covers SU/DO)
- Same *she-* with resumptive pronoun (+case, covers DO–OCOMP)

DO is shared between both constructions.

## Two Types of Resumption (@cite{sichel-2014})

Hebrew has both bound and movement resumptive pronouns, though unlike
Swahili they are not morphologically distinct. @cite{sichel-2014} shows:

- **Optional resumption** (direct objects): alternation between gap and
  resumptive. When resumption is optional, a resumptive pronoun has the
  distribution of a bound pronoun, and a gap is a movement trace.
  Weak crossover effects distinguish the two (example (6) in
  @cite{scott-2021}).

- **Obligatory resumption** (PPs): always a movement copy (no gap
  alternative). The resumptive pronoun *oto* shows reconstruction
  effects (example (7) in @cite{scott-2021}), indicating movement.

Data from @cite{keenan-comrie-1977} Table 1 and §1.3.2.
-/

namespace Fragments.Hebrew

open Core

/-- Complementizer *she-*. NP_rel is deleted (gap).
    Covers subject and direct object.
    E.g., "ha-ish [she-halakh _]" 'the-man [that-left _]'. -/
def relSheGap : RelClauseMarker :=
  { form := "she-"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject, .directObject]
  , notes := "Complementizer she-; gap; covers SU/DO; §1.3.2" }

/-- Complementizer *she-* with resumptive pronoun. Same complementizer
    introduces the RC, but NP_rel is a resumptive personal pronoun.
    Covers DO–OCOMP (DO shared with gap construction).
    E.g., "ha-ir [she-garti ba-h]" 'the-city [that-lived-I in-it]'. -/
def relSheResumptive : RelClauseMarker :=
  { form := "she- + pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.directObject, .indirectObject, .oblique, .genitive, .objComparison]
  , notes := "Complementizer she-; resumptive; DO–OCOMP; DO shared; §1.3.2" }

/-- Complementizer *she-* with movement resumptive in PPs. Obligatory —
    the PP object cannot be a gap (no P-stranding in Hebrew). Shows
    reconstruction effects, indicating movement copy.
    @cite{sichel-2014}: "ha-ec she-hu tipes alav" 'the tree that he
    climbed on.it' — idiomatic reading preserved = reconstruction. -/
def relSheMovementResumptive : RelClauseMarker :=
  { form := "she- + movement RP"
  , npRel := .resumptiveMovement
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.oblique, .genitive]
  , notes := "she- + obligatory resumptive in PPs; movement copy; reconstruction; @cite{sichel-2014}" }

/-- Complementizer *she-* with bound resumptive for direct objects.
    Optional — alternates with gap. When used, behaves as a bound
    pronoun (no reconstruction, weak crossover sensitivity).
    @cite{sichel-2014}: "ze ha-yeled she-imo šelo ohevet oto"
    'this is the boy who his mother loves him' — oto is bound. -/
def relSheBoundResumptive : RelClauseMarker :=
  { form := "she- + bound RP"
  , npRel := .resumptiveBound
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.directObject]
  , notes := "she- + optional resumptive for DO; bound pronoun; no reconstruction; @cite{sichel-2014}" }

/-- All Hebrew relative clause markers. The legacy `relSheResumptive`
    marker is retained for backward compatibility with
    @cite{keenan-comrie-1977}-level typology. The Sichel markers
    provide finer-grained two-type classification. -/
def relMarkers : List RelClauseMarker := [relSheGap, relSheResumptive]

/-- Sichel-refined markers distinguishing bound vs. movement resumption. -/
def relMarkersSichel : List RelClauseMarker :=
  [relSheGap, relSheBoundResumptive, relSheMovementResumptive]

/-- Hebrew relativization profile (typological summary). -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .pronounRetention
  , rcPosition := .postNominal
  , lowestRelativizable := .oblique
  , notes := "Gap on subject, resumptive on obliques; "
          ++ "complementizer she-; classic Semitic AH shift" }

end Fragments.Hebrew
