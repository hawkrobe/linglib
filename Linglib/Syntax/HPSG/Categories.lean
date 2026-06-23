/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Construction
import Linglib.Data.UD.Basic

/-!
# HPSG categories: grounding in Universal Dependencies and compatibility
[sag-2010]

The HPSG syntactic categories are the **cat sub-hierarchy** of the RSRL construct signature
(`Syntax/HPSG/Construction`): `cat > {verbal, nonverbal}`, `verbal > {verb, comp}`,
`nonverbal > {nominal, adj}`, `nominal > {noun, prep}`, with a genuine subsumption order. Empirical
data is tagged with **Universal Dependencies** POS tags (`UD.UPOS`); `udToCat` is the grounding bridge,
mapping each UD tag to its HPSG cat sort so UD-tagged data enters the category hierarchy by conversion
(the project's Layered-Grounding discipline) rather than `UD.UPOS` being used *as* the category type.

`udToCat` is **where the nominal conflation becomes principled**: `NOUN`/`PRON`/`PROPN` all map to
`noun`, so `categoriesMatch` treats them alike via the cat hierarchy's `≤` (`noun ≤ nominal`, etc.)
without any hand-coded `isNom` test. Tags with no HPSG cat correspondent (`ADV`, `DET`, `NUM`, …) map to
`none`, and `categoriesMatch` falls back to UD-tag equality for them.
-/

namespace HPSG

open HPSG.Construction (Srt)

/-- The HPSG cat sort a Universal Dependencies POS tag grounds to ([sag-2010]'s category hierarchy).
`NOUN`/`PRON`/`PROPN` → `noun` (NP), `ADP` → `prep` (PP), `VERB`/`AUX` → `verb`, `ADJ` → `adj`,
`SCONJ` → `comp` (complementizer); tags with no cat correspondent are `none`. -/
def udToCat : UD.UPOS → Option Srt
  | .NOUN => some .noun
  | .PRON => some .noun
  | .PROPN => some .noun
  | .ADP => some .prep
  | .VERB => some .verb
  | .AUX => some .verb
  | .ADJ => some .adj
  | .SCONJ => some .comp
  | _ => none

/-- Are two categories compatible? Grounded in the HPSG cat hierarchy: each UD tag maps to its cat sort
(`udToCat`) and the two must be comparable in the subsumption order — so all nominal categories
(`NOUN`/`PRON`/`PROPN` → `noun`) match each other without a hand-coded test, and a sort compares with its
supersorts. For tags with no cat correspondent it falls back to UD-tag equality. -/
def categoriesMatch (c1 c2 : UD.UPOS) : Bool :=
  match udToCat c1, udToCat c2 with
  | some a, some b => decide (a ≤ b) || decide (b ≤ a)
  | _, _ => c1 == c2

end HPSG
