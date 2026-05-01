import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Hungarian Case Inventory @cite{kenesei-vago-fenyvesi-1998} @cite{rounds-2001} @cite{caha-2008}

Hungarian's case inventory per the two standard reference grammars:
@cite{kenesei-vago-fenyvesi-1998} list **18** cases (see their Symbols
table); @cite{rounds-2001} adds **4 less-productive** cases (temporal
-kor, distributive-temporal -nta, sociative -stul / -stül, locative
fossilized -t / -tt) for a total of **22**. All marking is via
agglutinative suffixes.

Both reference grammars converge on three substantive points:

1. **No morphological genitive.** -nak / -nek is exclusively glossed as
   dative — even in possessive constructions where the possessor is
   "extracted" into a non-adjacent position. @cite{kenesei-vago-fenyvesi-1998}
   §1.10 explicitly attributes the analysis to Szabolcsi 1986/1992,
   1994 and frames the possessor as **the dative possessor** (not GEN).
   @cite{caha-2008} §5 (pp. 266–267) likewise states verbatim:
   "Hungarian has nominative, accusative, dative, instrumental and a
   number of spatial cases, but no genitive ... possessor inside a
   Noun phrase ... is expressed as a dative, or nominative, depending
   on word-order, among other things." Possession is head-marked on
   the possessum; see `Fragments/Hungarian/Possession.lean`.

2. **Local cases form a 3 × 3 matrix** (interior / exterior / near ×
   motion-toward / no-motion / motion-away) — see @cite{rounds-2001}
   §6.2's "Locative system: parameters of motion and space" table.

3. **Hungarian is a known surface counterexample to Blake's hierarchy.**
   @cite{caha-2008} fn. 8 cites Blake's own resolution: "the
   counterexamples are superficial, and are basically due to two
   factors: systematic syncretism (perhaps as in the case of Hungarian
   which uses dative to express possessor)..." Both Blake and Caha
   accept Hungarian as a typological exception explained by the
   dative-as-possessor analysis, not as a falsifying datum.

This Fragment exposes a 9-element `Finset Core.Case` capturing the
broad case-functions that participate in Blake's hierarchy:

- **Grammatical**: NOM (∅), ACC (-t), DAT (-nak / -nek)
- **Local — 3 × 3 matrix collapsed to direction only**:
    - static (→ `.loc`): inessive (-ban / -ben), adessive (-nál / -nél),
      superessive (-n / -on / -en / -ön)
    - source (→ `.abl`): elative (-ból / -ből), ablative (-tól / -től),
      delative (-ról / -ről)
    - goal   (→ `.all`): illative (-ba / -be), allative
      (-hoz / -hez / -höz), sublative (-ra / -re)
- **Other**: INST (-val / -vel), COM (= INS-form per @cite{kenesei-vago-fenyvesi-1998};
  separate Finset element here), CAUS (-ért, "causal-final")

**What `Core.Case` can express but this inventory omits**:

- `.Sup`, `.Sub`, `.Del` (PascalCase UD spatial constructors) would
  preserve Hungarian's surface-row local cases distinctly rather than
  collapsing to the direction-only triple.
- `.ess` (essive-modal -ul / -ül), `.transl` (translative -vá / -vé),
  `.ter` (terminative -ig), `.tem` (temporal -kor) — all attested in
  both grammars, omitted here.
- ESS-FOR (-ként, "essive-formal", listed separately by both grammars)
  has no `Core.Case` constructor.
- DISTR (-nként), per @cite{rounds-2001} §6.4, has no `Core.Case`
  constructor — the only Hungarian case the substrate genuinely cannot
  express.

-/

namespace Fragments.Hungarian.Case

/-- Hungarian case inventory: 9-element sample of `Core.Case`. The
    omission of `.gen` reflects the descriptive-grammar consensus
    (@cite{kenesei-vago-fenyvesi-1998}, @cite{rounds-2001}) and
    @cite{caha-2008} §5 — Hungarian has no morphological genitive. -/
def caseInventory : Finset Core.Case :=
  {.nom, .acc, .dat, .loc, .abl, .all, .inst, .com, .caus}

/-- Hungarian fails Blake's strict contiguity at rank 5 (GEN), since
    the inventory has DAT (rank 4) without GEN. Parallels Finnish's
    failure at rank 4 (DAT) — `Fragments.Finnish.Case.inventory_fails_strict`.
    @cite{caha-2008} §5 (pp. 266–267) cites Hungarian as the textbook
    surface counterexample to Blake, resolved (per Blake fn. 8) by the
    dative-as-possessor syncretism. -/
theorem inventory_fails_strict :
    ¬ Core.Case.IsValidInventory caseInventory := by decide

end Fragments.Hungarian.Case
