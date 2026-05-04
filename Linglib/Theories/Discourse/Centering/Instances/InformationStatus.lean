import Linglib.Theories.Discourse.Centering.Defs
import Linglib.Features.InformationStructure
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

**Relation to existing linglib enums.**
- `Features.InformationStructure.DiscourseStatus` (`focused | given
  | new`) and Strube-Hahn's IS taxonomy share a 3-tier shape but use
  different cuts: Strube-Hahn treat focus as **orthogonal** to old/new
  (their §4) and have no `focused` tier. The lossy `ofDiscourseStatus`
  projection below maps `given → hearerOld`, `focused → hearerOld`
  (the typical case for already-activated entities), `new → hearerNew`.
  This deliberately disagrees with `DiscourseStatus.rank` (which puts
  `focused` highest, `given` lowest) — the disagreement is captured as
  `ofDiscourseStatus_disagrees_with_DiscourseStatus_rank` below so the
  cross-file inversion is a theorem, not a buried gotcha.
- @cite{gundel-hedberg-zacharski-1993}'s **Givenness Hierarchy** (in
  focus > activated > familiar > uniquely identifiable > referential
  > type identifiable) is the principal 6-way alternative to
  Strube-Hahn's 3-way IS ranking. Linglib's GHZ enum lives at
  `Phenomena/Reference/Studies/Ariel2001.lean` (`GivennessStatus`);
  its middle tiers (`familiar`, `uniquelyIdentifiable`) cover the
  conceptual neighborhood of Strube-Hahn's MEDIATED. A
  `StrubeHahnInfoStatus.ofGivenness` projection would dissolve the
  MEDIATED orphan but requires GHZ's promotion to substrate (currently
  stuck behind Theories-cannot-import-Phenomena layering).
-/

set_option autoImplicit false

namespace Discourse.Centering

/-- @cite{strube-hahn-1999}'s information-status taxonomy as a
    Centering-instance-private enum. The existing
    `Features.InformationStructure.DiscourseStatus` (`focused | given |
    new`) uses different labels and treats `focused` as orthogonal to
    old/new — collapsing them into a single rank misrepresents
    Strube-Hahn. The lossy `ofDiscourseStatus` projection below bridges
    when needed, with the disagreement made explicit as a theorem.

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

/-- Lossy projection from `Features.InformationStructure.DiscourseStatus`
    to Strube-Hahn's IS taxonomy:

    * `given → hearerOld` — already in the discourse.
    * `focused → hearerOld` — focused entities are typically activated,
      so they project to the hearer-old tier in the dominant case.
      Strube-Hahn themselves bracket focus from the IS hierarchy
      (their §4); this projection is genuinely undefined for the
      atypical case of focus-marked discourse-new entities (e.g.,
      contrastive answers to wh-questions), where `hearerNew` would
      arguably be the better target.
    * `new → hearerNew` — brand-new.

    The MEDIATED tier is **not produced** by this projection — Prince
    1981's inferable / containing-inferable / anchored-brand-new
    distinctions have no analog in `DiscourseStatus`. Bridging from
    @cite{gundel-hedberg-zacharski-1993}'s 6-tier `GivennessStatus`
    (currently in `Phenomena/Reference/Studies/Ariel2001.lean`) would
    populate MEDIATED but requires that enum's promotion to substrate. -/
def StrubeHahnInfoStatus.ofDiscourseStatus :
    Features.InformationStructure.DiscourseStatus → StrubeHahnInfoStatus
  | .given   => .hearerOld
  | .focused => .hearerOld
  | .new     => .hearerNew

/-- Sanity-anchor for the `focused → hearerOld` mapping: a stable
    grep target for the projection's typical case. -/
example :
    StrubeHahnInfoStatus.ofDiscourseStatus .focused = .hearerOld := rfl

/-- The Strube-Hahn IS ranking and `DiscourseStatus.rank` (used by
    `LuPanDegen2025`, `CartnerEtAl2026`, `BackgroundedIslands` for
    extraction-acceptability and focus-comparison) **disagree** as
    orderings on the three shared values. `DiscourseStatus.rank` puts
    `given` lowest (0) and `focused` highest (2); under the projection,
    `given` becomes HEARER-OLD (highest rank 2) and `focused` collapses
    onto the same tier. The two cannot be reconciled by a monotone
    relabelling — IS-ranking and focus-prominence ranking are
    genuinely different orderings, not notational variants of one. -/
theorem ofDiscourseStatus_disagrees_with_DiscourseStatus_rank :
    ¬ (∀ a b : Features.InformationStructure.DiscourseStatus,
        a.rank ≤ b.rank ↔
        (StrubeHahnInfoStatus.ofDiscourseStatus a).rank ≤
          (StrubeHahnInfoStatus.ofDiscourseStatus b).rank) := by
  -- Witness: `given` and `new`. Under `DiscourseStatus.rank`,
  -- `given (= 0) ≤ new (= 1)` holds. After projection, `given` becomes
  -- `hearerOld` (rank 2) and `new` becomes `hearerNew` (rank 0); the
  -- corresponding inequality `2 ≤ 0` fails.
  intro h
  exact absurd ((h .given .new).mp (by decide)) (by decide)

end Discourse.Centering
