import Linglib.Core.Time.Reichenbach
import Linglib.Core.Time.Boundedness
import Linglib.Core.Time.Tense

/-!
# Tense Phenomena: Multi-Source Empirical Data (DEPRECATED — in dissolution)
@cite{abusch-1997} @cite{anand-nevins-2004} @cite{banfield-1982}
@cite{comrie-1985} @cite{deal-2020} @cite{declerck-1991}
@cite{declerck-2006} @cite{iatridou-2000} @cite{klecha-2016}
@cite{kratzer-1998} @cite{ogihara-sharvit-2012} @cite{schlenker-2004}
@cite{sharvit-2003} @cite{von-stechow-2009} @cite{wurmbrand-2014}
@cite{schlenker-2003}

**This file is being dissolved per-paper into individual Studies/
files** (see `Studies/Kratzer1998.lean` for §29, which has already
migrated). The original aggregation violated CLAUDE.md's per-paper
anchoring rule — every Lean file must anchor on one paper / named
framework / documented empirical pattern. The remaining sections
(§0–§28) await migration to their respective per-paper homes.

Was `Phenomena/TenseAspect/Data.lean`; relocated to `Studies/` per
the provenance-tracking policy. Per-section migration plan:
`Studies/Abusch1997.lean` (§1-3, 5, 9); `Studies/Ogihara1996.lean`
(§4, 14); `Studies/Klecha2016.lean` (§7); `Studies/Schlenker2004.lean`
(§12); `Studies/Sharvit2003.lean` (§6, 11, 18, 21);
`Studies/Iatridou2000.lean` (§8, 20); `Studies/Wurmbrand2014.lean`
(§15, 22); `Studies/AnandNevins2004.lean` (§17);
`Studies/Musan1995.lean` (§19); `Studies/Declerck1991.lean` (§23-26,
28); `Phenomena/Aspect/Studies/Declerck1991.lean` (§27). §0 +
§10 will be deleted (boilerplate / narration). The current consumer
`Studies/Schlenker2004.lean` will repoint to `Studies/Abusch1997.lean`
once the latter receives the `matrixSaid`/`embeddedSick*` symbols.

Coverage: 10+ temporal phenomena that distinguish tense theories,
absorbing the former `Phenomena/SequenceOfTense/Data.lean`.

## Phenomena Covered

### Baseline (§0)
0. Root-clause simple tenses: past, present, future

### Core comparison set (10 + 1 debate)
1. Past-under-past: "John said Mary was sick" (shifted + simultaneous)
2. Present-under-past: "John said Mary is sick" (double access)
3. Future-under-past: "John said Mary would leave"
4. SOT vs non-SOT: English vs Japanese
5. Upper Limit Constraint: no forward-shifted readings
6. Relative clause tense: "the man who was tall"
7. Modal-tense interaction: "John might have left"
8. Counterfactual tense: "If John were here..."
9. Temporal de re: "John believed it was raining"
10. Deletion vs ambiguity: same surface, different mechanisms

### Eventual targets (7)
11. SOT in indirect questions: "John asked who was sick"
12. Free indirect discourse: perspective shift without attitude verb
13. Historical/narrative present: "Napoleon enters the room"
14. Perfect tense interactions: "John said Mary had been sick"
15. Future-oriented complements: "John wanted to leave"
16. Tense in adjunct clauses: "Before John left, Mary was happy"
17. Indexical tense shift: Amharic/Zazaki tense under attitudes

### Extended phenomena (5) — Sharvit, Zeijlstra, Wurmbrand
18. Embedded present puzzle: "John will say Mary is sick"
19. Lifetime effects: "Aristotle was a philosopher"
20. Fake past: "If John were taller..."
21. Optional SOT (Hebrew-type)
22. Dependent vs independent tense

### Discourse-level phenomena (6) — @cite{declerck-1991}/2006
23. Temporal domain shift vs subordination
24. False tense: politeness and tentativeness
25. PPS vs FPS in conditionals
26. Temporal conjunctions with implicit TOs
27. Bounded/unbounded default interpretation (PUTI)
28. Present perfect vs preterit: time-sphere distinction

-/

namespace Phenomena.TenseAspect

open Core.Time.Reichenbach
open Core.Time (SituationBoundedness)
open Core.Time.Tense


-- (§13 migrated to Phenomena/TenseAspect/HistoricalPresent.lean — sub-phenomenon file,
--  no Reichenbach frame; the (S,P,R,E) tuple conflates morphology with interpretation
--  for HP, per memory feedback_reichenbach_morph_vs_interp_conflation)
-- (§16 migrated to Studies/ArreguiKusumoto1998.lean)
-- (§23-28 migrated to Studies/Declerck1991.lean — domain shift, modal past,
--  PPS/FPS conditionals, temporal conjunctions, PUTI, perfect/preterit time-sphere)

end Phenomena.TenseAspect

