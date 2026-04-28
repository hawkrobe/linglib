import Linglib.Theories.Discourse.Centering.Defs
import Linglib.Features.InformationStructure

/-!
# Centering — Information-Status Cf Ranking
@cite{strube-hahn-1999} @cite{poesio-stevenson-eugenio-hitzeman-2004}

@cite{strube-hahn-1999} propose ranking forward-looking centers by
**information status** (IS) rather than grammatical function — a
non-English-default ranker motivated by German data. Their original
3-way ranking (per @cite{poesio-stevenson-eugenio-hitzeman-2004}
§2.4.3 p. 319) is:

> HEARER-OLD ≺ MEDIATED ≺ HEARER-NEW

with linear-order tiebreak within each tier. Lower (≺) = more salient,
so HEARER-OLD entities are the highest-ranked Cf elements.

This file projects the existing `Features.InformationStructure.DiscourseStatus`
3-way enum (`focused | given | new`) onto a Centering rank. The
labels differ from Strube-Hahn's (focused/given/new vs HEARER-NEW/
HEARER-OLD/MEDIATED), but the **3-tier ordering structure is the
same** — both posit a tripartite information-status taxonomy
producing distinct Cf rankings from grammatical function.

**Approximate correspondence** (PSDH §2.4.3 + the standard
information-status literature, Prince 1981):
- `DiscourseStatus.given` ≈ HEARER-OLD (entity already in the discourse)
- `DiscourseStatus.new` ≈ HEARER-NEW (brand-new entity)
- `DiscourseStatus.focused` ≈ marked salience (a different axis from
  the HEARER-OLD/MEDIATED/HEARER-NEW tripartition; @cite{strube-hahn-1999}
  treat "focused" as orthogonal to information status)

The MEDIATED tier (Prince's "inferable / containing-inferable /
anchored-brand-new") has no direct analog in the existing
`DiscourseStatus` enum. A future commit could introduce a finer
`StrubeHahnInfoStatus` enum if a downstream consumer needs the full
Strube-Hahn taxonomy.

PSDH's empirical headline (Table 15, §5.1.1): the **STRUBE-HAHN
ranking + IS instantiation** is the *only* parameter setting that
verifies all three centering claims (Strong C1, Rule 1, Rule 2 BFP)
simultaneously — making this a load-bearing instance for the
parametric story.
-/

set_option autoImplicit false

namespace Discourse.Centering

/-- @cite{strube-hahn-1999}'s information-status taxonomy, kept as a
    Centering-instance-private enum since the existing
    `Features.InformationStructure.DiscourseStatus` (`focused | given
    | new`) uses different labels and treats `focused` as orthogonal
    to old/new — collapsing them into a single rank misrepresents
    Strube-Hahn (per linguistics-domain-expert audit). The right
    relationship is a lossy projection from `DiscourseStatus` to this
    type when bridging is needed (not provided here; queued).

    PSDH §2.4.3 (p. 319) state Strube-Hahn's ranking verbatim:
    `HEARER-OLD ≺ MEDIATED ≺ HEARER-NEW` (lower ≺ = more salient).
    HEARER-OLD covers Prince 1981's discourse-old + unused/evoked
    entities (e.g., "Margaret Thatcher" in a UK political context —
    presumed shared knowledge). MEDIATED covers Prince's inferable
    / containing-inferable / anchored-brand-new. HEARER-NEW covers
    brand-new entities. -/
inductive StrubeHahnInfoStatus where
  /-- Hearer-old: discourse-old or unused/evoked. Highest salience. -/
  | hearerOld
  /-- Mediated: inferable / containing-inferable / anchored-brand-new
      (Prince 1981's middle category). -/
  | mediated
  /-- Hearer-new: brand-new entity. Lowest salience. -/
  | hearerNew
  deriving DecidableEq, Repr, Fintype

/-- Strube-Hahn IS rank: HEARER-OLD = 2 (highest Centering rank,
    matching their `≺ = more salient` convention), MEDIATED = 1,
    HEARER-NEW = 0. -/
def StrubeHahnInfoStatus.rank : StrubeHahnInfoStatus → Nat
  | .hearerOld  => 2
  | .mediated   => 1
  | .hearerNew  => 0

/-- The Strube-Hahn Cf-ranker instance — the second `CfRanker` instance
    in linglib (sibling to `GrammaticalRole`), enabling the parametric
    centering story PSDH §4.4.3 evaluate. -/
instance : CfRanker StrubeHahnInfoStatus where
  rank := StrubeHahnInfoStatus.rank

theorem hearerOld_rank_is_2 :
    CfRanker.rank StrubeHahnInfoStatus.hearerOld = 2 := rfl

theorem mediated_rank_is_1 :
    CfRanker.rank StrubeHahnInfoStatus.mediated = 1 := rfl

theorem hearerNew_rank_is_0 :
    CfRanker.rank StrubeHahnInfoStatus.hearerNew = 0 := rfl

/-- Lossy projection from `Features.InformationStructure.DiscourseStatus`
    to Strube-Hahn's IS taxonomy. The mapping:
    - `given` ≈ `hearerOld` (already in discourse)
    - `new` ≈ `hearerNew` (brand-new)
    - `focused` ≈ `hearerOld` — focused entities are by definition
      ones the hearer is being asked to attend to, which Strube-Hahn
      would treat as already in shared attention (closer to OLD than
      NEW). The audit flagged my prior collapse of `focused → 0`
      (lowest) as wrong-directional; this projection corrects that.
    The MEDIATED tier has no clean source in `DiscourseStatus`; the
    projection is genuinely lossy. -/
def StrubeHahnInfoStatus.ofDiscourseStatus :
    Features.InformationStructure.DiscourseStatus → StrubeHahnInfoStatus
  | .given   => .hearerOld
  | .focused => .hearerOld  -- focused → marked salience, treated as old
  | .new     => .hearerNew

end Discourse.Centering
