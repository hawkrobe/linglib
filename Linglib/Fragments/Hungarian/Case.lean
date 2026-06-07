import Linglib.Features.Case.Basic
import Linglib.Syntax.Case.Order
/-!
# Hungarian Case Inventory [kenesei-vago-fenyvesi-1998] [rounds-2001] [caha-2008]

Hungarian's case inventory per the two standard reference grammars:
[kenesei-vago-fenyvesi-1998] list **18** cases (see their Symbols
table); [rounds-2001] adds **4 less-productive** cases (temporal
-kor, distributive-temporal -nta, sociative -stul / -stül, locative
fossilized -t / -tt) for a total of **22**. All marking is via
agglutinative suffixes.

Both reference grammars converge on three substantive points:

1. **No morphological genitive.** -nak / -nek is exclusively glossed as
   dative — even in possessive constructions where the possessor is
   "extracted" into a non-adjacent position. [kenesei-vago-fenyvesi-1998]
   §1.10 explicitly attributes the analysis to Szabolcsi 1986/1992,
   1994 and frames the possessor as **the dative possessor** (not GEN).
   [caha-2008] §5 (pp. 266–267) likewise states verbatim:
   "Hungarian has nominative, accusative, dative, instrumental and a
   number of spatial cases, but no genitive ... possessor inside a
   Noun phrase ... is expressed as a dative, or nominative, depending
   on word-order, among other things." Possession is head-marked on
   the possessum; see `Fragments/Hungarian/Possession.lean`.

2. **Local cases form a 3 × 3 matrix** (interior / exterior / near ×
   motion-toward / no-motion / motion-away) — see [rounds-2001]
   §6.2's "Locative system: parameters of motion and space" table.

3. **Hungarian is a known surface counterexample to Blake's hierarchy.**
   [caha-2008] fn. 8 cites Blake's own resolution: "the
   counterexamples are superficial, and are basically due to two
   factors: systematic syncretism (perhaps as in the case of Hungarian
   which uses dative to express possessor)..." Both Blake and Caha
   accept Hungarian as a typological exception explained by the
   dative-as-possessor analysis, not as a falsifying datum.

This Fragment exposes a 9-element `Finset Case` capturing the
broad case-functions that participate in Blake's hierarchy:

- **Grammatical**: NOM (∅), ACC (-t), DAT (-nak / -nek)
- **Local — the full 3 × 3 matrix**, as distinct cells via the shared
  `Region × PathDir` decomposition (`Syntax/Case/Order.lean`):
    - interior: inessive (-ban / -ben → `.ine`), elative
      (-ból / -ből → `.ela`), illative (-ba / -be → `.ill`)
    - exterior: adessive (-nál / -nél → `.ade`), ablative
      (-tól / -től → `.abl`), allative (-hoz → `.all`)
    - surface: superessive (-n / -on → `.sup`), delative
      (-ról / -ről → `.del`), sublative (-ra / -re → `.sub`)
- **Other**: INST (-val / -vel), COM (= INS-form per [kenesei-vago-fenyvesi-1998];
  separate Finset element here), CAUS (-ért, "causal-final")

**What `Case` still omits**:

- `.ess` (essive-modal -ul / -ül), `.transl` (translative -vá / -vé),
  `.ter` (terminative -ig), `.tem` (temporal -kor) — all attested in
  both grammars, omitted here.
- ESS-FOR (-ként, "essive-formal", listed separately by both grammars)
  has no `Case` constructor.
- DISTR (-nként), per [rounds-2001] §6.4, has no `Case`
  constructor — the only Hungarian case the substrate genuinely cannot
  express.

-/

namespace Hungarian.Case

/-- Hungarian case inventory. The 9 local cases are now distinct cells
    (the full 3 × 3 surface/interior/exterior × static/source/goal
    matrix). The omission of `.gen` reflects the descriptive-grammar
    consensus ([kenesei-vago-fenyvesi-1998], [rounds-2001]) and
    [caha-2008] §5 — Hungarian has no morphological genitive. -/
def caseInventory : Finset Case :=
  {.nom, .acc, .dat, .ine, .ade, .sup, .ela, .abl, .del, .ill, .all, .sub,
   .inst, .com, .caus}

/-- Hungarian's 9 local cases as `Region × PathDir` coordinates — the
    full 3 × 3 matrix the shared decomposition makes expressible. -/
def localCases : List (Case.Region × Case.PathDir) :=
  [ (.interior, .place), (.exterior, .place), (.surface, .place),
    (.interior, .source), (.exterior, .source), (.surface, .source),
    (.interior, .goal), (.exterior, .goal), (.surface, .goal) ]

/-- All 9 local cases project to *distinct* `Case` cells — the surface
    series (`.sup`/`.del`/`.sub`) is preserved, not collapsed to the
    direction-only triple. -/
theorem localCases_distinct :
    (localCases.filterMap (fun rd => Case.toCase rd.1 rd.2)).Nodup := by decide

/-- Hungarian fails Blake's strict contiguity at rank 5 (GEN), since
    the inventory has DAT (rank 4) without GEN. Parallels Finnish's
    failure at rank 4 (DAT) — `Finnish.Case.inventory_fails_strict`.
    [caha-2008] §5 (pp. 266–267) cites Hungarian as the textbook
    surface counterexample to Blake, resolved (per Blake fn. 8) by the
    dative-as-possessor syncretism. -/
theorem inventory_fails_strict :
    ¬ Case.IsValidInventory caseInventory := by decide

end Hungarian.Case
