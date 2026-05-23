import Linglib.Discourse.Centering.Defs
import Linglib.Features.Givenness
import Mathlib.Order.Basic

/-!
# Centering — Information-Status Cf Ranking
@cite{strube-hahn-1999} @cite{poesio-stevenson-eugenio-hitzeman-2004}
@cite{prince-1981} @cite{gundel-hedberg-zacharski-1993}

@cite{strube-hahn-1999} (their §4.2) propose ranking forward-looking
centers by **information status** (IS) — a non-grammatical-function
ranker originally argued for free-word-order languages, in particular
German. Their ranking projects @cite{prince-1981}'s familiarity scale
onto three tiers:

> HEARER-OLD ≺ MEDIATED ≺ HEARER-NEW

with linear-order tiebreak within each tier. The relation `≺` is
"more salient", so HEARER-OLD entities receive the highest Centering
rank; this file inverts the symbol and ranks HEARER-OLD = 2 / MEDIATED
= 1 / HEARER-NEW = 0.

@cite{poesio-stevenson-eugenio-hitzeman-2004} (henceforth PSDH)
re-evaluate Strube-Hahn's ranking on **English** corpus data (the
GNOME museum + pharmaceutical subcorpora; PSDH §3.2). Internally
HEARER-OLD subsumes Prince's evoked + unused entities (e.g.
*Margaret Thatcher* in a politically-knowledgeable context — presumed
shared knowledge); MEDIATED covers Prince's inferable, containing-
inferable, and anchored-brand-new (PSDH §2.4.3 fn 10); HEARER-NEW
covers brand-new entities.

**Empirical headline (PSDH §5.1.1).** With STRUBE-HAHN ranking, both
the IS and IF instantiations verify all three claims (Strong C1,
Rule 1 GJW95, Rule 2 BFP) at the .01 level. Switching to GFTHERELIN
(grammatical function + linear-order tiebreak), the same IS
instantiation verifies Rule 2 only at the .05 level (PSDH §4.4.1
end). The .01-vs-.05 elevation is what STRUBE-HAHN ranking buys —
not exclusivity over IF.

**Substrate source for IS.** The `ofGivenness` projection below
maps @cite{gundel-hedberg-zacharski-1993}'s 6-tier `GivennessStatus`
(in `Features/Givenness.lean`) onto Strube-Hahn's 3-tier IS — the
substantive linguistic bridge the two literatures imply. GHZ's
`uniquelyIdentifiable`/`referential` populate the MEDIATED tier
(Prince's inferable / containing-inferable / anchored-brand-new),
witnessed by `mediated_reachable` below.
-/

set_option autoImplicit false

namespace Discourse.Centering

open Features (GivennessStatus)

/-- @cite{strube-hahn-1999}'s information-status taxonomy as a
    Centering-instance-private enum. The 3-tier shape (HEARER-OLD /
    MEDIATED / HEARER-NEW) is preserved as the Strube-Hahn-native
    surface; the substrate source is GHZ-6 (see `ofGivenness` below).

    Strube-Hahn's HEARER-OLD covers @cite{prince-1981}'s discourse-old
    + unused/evoked entities (e.g. *Margaret Thatcher* in a UK political
    context — presumed shared knowledge). MEDIATED covers Prince's
    inferable, containing-inferable, and anchored-brand-new. HEARER-NEW
    covers brand-new entities. Per @cite{poesio-stevenson-eugenio-hitzeman-2004}
    §2.4.3 (their footnote 10 spells out the Prince-correspondence). -/
inductive StrubeHahnInfoStatus where
  /-- Hearer-old: discourse-old or unused/evoked. Highest salience. -/
  | hearerOld
  /-- Mediated: inferable, containing-inferable, or anchored-brand-new
      (@cite{prince-1981}'s middle category). -/
  | mediated
  /-- Hearer-new: brand-new entity. Lowest salience. -/
  | hearerNew
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Strube-Hahn IS rank on `Nat`: HEARER-OLD = 2 (highest Centering
    rank, matching `≺ = more salient`), MEDIATED = 1, HEARER-NEW = 0. -/
def StrubeHahnInfoStatus.rank : StrubeHahnInfoStatus → Nat
  | .hearerOld  => 2
  | .mediated   => 1
  | .hearerNew  => 0

/-- The Strube-Hahn Cf-ranker instance — sibling of `GrammaticalRole`,
    enabling the parametric Centering story PSDH §4.4 evaluate. -/
instance : CfRanker StrubeHahnInfoStatus where
  rank := StrubeHahnInfoStatus.rank

/-- Total order via the rank pullback, mirroring the `LinearOrder
    GrammaticalRole` instance in the sibling file. -/
instance : LinearOrder StrubeHahnInfoStatus := CfRanker.toLinearOrder _

/-- Project @cite{gundel-hedberg-zacharski-1993}'s 6-tier
    `Features.GivennessStatus` onto Strube-Hahn's 3-tier IS, following
    the GHZ→Prince→Strube-Hahn chain documented in
    @cite{poesio-stevenson-eugenio-hitzeman-2004} §2.4.3 fn 10:

    * `inFocus`, `activated`, `familiar` → `hearerOld` (Prince's
      Evoked + Unused: currently activated, in working memory, or in
      long-term memory). Strube-Hahn's HEARER-OLD includes Prince's
      Unused tier — entities like *Margaret Thatcher* that are part
      of shared knowledge but not currently activated.
    * `uniquelyIdentifiable`, `referential` → `mediated` (Prince's
      Inferable + Containing-Inferable + Anchored Brand-new — entities
      requiring inference or anchoring to be identified).
    * `typeIdentifiable` → `hearerNew` (Prince's bare Brand-new).

    The 3-2-1 split is the linguistically-defensible cut implied by
    Strube-Hahn's own definition. The previous 2-2-2 implementation
    here mistakenly pushed GHZ's `familiar` into MEDIATED. The
    MEDIATED tier has a substrate source (the prior projection from
    `DiscourseStatus` had no source for it, leaving MEDIATED
    unreachable). -/
def StrubeHahnInfoStatus.ofGivenness :
    GivennessStatus → StrubeHahnInfoStatus
  | .inFocus              => .hearerOld
  | .activated            => .hearerOld
  | .familiar             => .hearerOld
  | .uniquelyIdentifiable => .mediated
  | .referential          => .mediated
  | .typeIdentifiable     => .hearerNew

/-! ### MEDIATED-tier dissolution: substrate-anchor examples

The headline of the post-Krifka substrate refactor: GHZ-6's
`uniquelyIdentifiable` and `referential` finally supply the MEDIATED
tier that the old `DiscourseStatus`-based projection couldn't reach.
These `rfl` examples lock the dissolution as grep-anchored facts. -/

example : StrubeHahnInfoStatus.ofGivenness .uniquelyIdentifiable = .mediated := rfl
example : StrubeHahnInfoStatus.ofGivenness .referential = .mediated := rfl
example : StrubeHahnInfoStatus.ofGivenness .familiar = .hearerOld := rfl
example : StrubeHahnInfoStatus.ofGivenness .typeIdentifiable = .hearerNew := rfl

/-- MEDIATED is reachable: there exists a `GivennessStatus` that
    projects to it (in fact two — `uniquelyIdentifiable` and
    `referential`). Pre-Krifka the projection was from `DiscourseStatus`,
    which had no MEDIATED-suitable input. -/
theorem mediated_reachable :
    ∃ g : GivennessStatus, StrubeHahnInfoStatus.ofGivenness g = .mediated :=
  ⟨.uniquelyIdentifiable, rfl⟩

/-- The projection respects the salience ordering: more cognitively
    activated givenness statuses map to higher (or equal) Centering
    ranks. Sanity check on the substantive linguistic claim that the
    GHZ-6 hierarchy and Strube-Hahn's IS scale agree about which
    referents are more salient. -/
theorem ofGivenness_monotone (a b : GivennessStatus) :
    a.rank ≥ b.rank →
    (StrubeHahnInfoStatus.ofGivenness a).rank ≥
      (StrubeHahnInfoStatus.ofGivenness b).rank := by
  cases a <;> cases b <;> decide

end Discourse.Centering
