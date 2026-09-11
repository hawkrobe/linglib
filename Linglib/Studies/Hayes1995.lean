import Linglib.Phonology.Prosody.Grid

/-!
# Hayes (1995): Metrical Stress Theory

This file formalizes the moraic-trochee analysis of Cairene Arabic stress in Section 4.1.3 of
[hayes-1995]: the word is parsed from left to right into moraic trochees, a heavy syllable or
two lights (13), and End Rule Right builds the word layer over the rightmost foot (16).
`parse` is that construction over the post-extrametricality weight string, `Tree.columns`
reads the stress off its grid, and the prominences of (12) follow, quantity moving the peak
from the antepenult of *kátaba* to the penult of *mudárris* and a heavy syllable restarting
the alternating count (`parseCells_heavy`). A single light syllable cannot form a foot, so the
stray final light of an odd-parity word is beyond the reach of End Rule Right: promoting it
would gap its grid column, which the Continuous Column Constraint of Section 3.4.2 forbids
(`promotedKataba_not_continuous`), while the attested grid is continuous by construction.

## Implementation notes

* The input is the weight profile after Consonant and Mora Extrametricality (14a–b), which
  demote a final CVC, and a final CV: of a Classical form, to light; those rules are upstream
  of the parse.

## References

* [hayes-1995]
* [prince-1983]
* [mccarthy-prince-1990]
-/

namespace Hayes1995

open Prosody RootedTree

/-! ### The moraic-trochee parse

A heavy syllable (`2 ≤ w`, bimoraic) is its own foot, two lights make a trochee with the head
on the left, and a light with no light to pair with is left stray. Foot heads are marked as the
parse builds them; `markHeadFoot` then promotes the rightmost foot to head foot, End Rule
Right. -/

/-- Foot Construction (14c): parse a weight string from left to right into moraic trochees. -/
def parseCells : Yield → List Tree
  | [] => []
  | [w] =>
      if Syllable.Weight.heavy ≤ w then [.ft false [.σ w true]]
      else [.σ w false]
  | w :: w2 :: rest =>
      if Syllable.Weight.heavy ≤ w then
        .ft false [.σ w true] :: parseCells (w2 :: rest)
      else if Syllable.Weight.heavy ≤ w2 then
        .σ w false :: parseCells (w2 :: rest)
      else
        .ft false [.σ w true, .σ w2 false] :: parseCells rest

/-- A heavy syllable is a foot of its own and restarts the count: it is necessarily followed
by a foot boundary (Section 4.1.3, after (15)). -/
theorem parseCells_heavy {w : Syllable.Weight} (hw : Syllable.Weight.heavy ≤ w) (rest : Yield) :
    parseCells (w :: rest) = .ft false [.σ w true] :: parseCells rest := by
  cases rest <;> simp [parseCells, hw]

/-- Is this ω-daughter an `f`-level foot? -/
def isFootChild : Tree → Bool
  | .node a _ => a.isFt

/-- End Rule Right (16): the first foot with no foot to its right is promoted to head foot. -/
def markHeadFoot : List Tree → List Tree
  | [] => []
  | .node a ds :: rest =>
      if a.isFt && !rest.any isFootChild then
        .ft true ds :: rest
      else
        .node a ds :: markHeadFoot rest

/-- The Cairene parse: a prosodic word over moraic trochees built left to right, the rightmost
foot heading the word. -/
def parse (y : Yield) : Tree := .om (markHeadFoot (parseCells y))

/-! ### Quantity-sensitive stress

The forms are those of (12), as their post-extrametricality weight profiles (`1` light CV, `2`
heavy). `Tree.columns ∘ parse` recovers the stress: the column of `3` is the primary, `2` a
secondary, `1` unstressed. -/

/-- *kátaba* 'he wrote' (Classical): all light. -/
def kataba : Yield := [1, 1, 1]
/-- *mudárris* 'teacher': heavy penult, the final CVC demoted to light. -/
def mudarris : Yield := [1, 2, 1]
/-- *ʔinkásara* 'it got broken' (Classical): heavy initial. -/
def Pinkasara : Yield := [2, 1, 1, 1]
/-- *katábt* 'I wrote': superheavy final, heavy after Consonant Extrametricality. -/
def katabt : Yield := [1, 2]
/-- *mudarrísit* 'teacher (f. construct)': heavy second syllable, the final CVC light. -/
def mudarrisit : Yield := [1, 2, 1, 1]
/-- *ʔadwiyatúhu* 'his drugs (nom.)' (Classical): heavy initial, then an even run of lights. -/
def Padwiyatuhu : Yield := [2, 1, 1, 1, 1]
/-- *šajaratuhúma:* 'their (dual) tree (nom.)' (Classical): six lights, the final CV: light by
Mora Extrametricality. -/
def sajaratuhuma : Yield := [1, 1, 1, 1, 1, 1]

/-- Antepenultimate stress (12c.ii), (15d): *kátaba* parses as `(ká.ta)ba`, the rightmost
foot heading the antepenult, the final light stray. -/
theorem gridColumns_kataba : Tree.columns (parse kataba) = [3, 1, 1] := by decide

/-- Penultimate stress on a heavy penult (12b), (15b): *mudárris* parses as `mu(dár)ri`. -/
theorem gridColumns_mudarris : Tree.columns (parse mudarris) = [1, 3, 1] := by decide

/-- The count restarts after a heavy, with secondary stress (12c.ii), (15d): *ʔinkásara* parses
as `(ʔìn)(ká.sa)ra`. -/
theorem gridColumns_Pinkasara : Tree.columns (parse Pinkasara) = [2, 3, 1, 1] := by decide

/-- Final stress on a superheavy (12a), (15a): *katábt* parses as `ka(tábt)`. -/
theorem gridColumns_katabt : Tree.columns (parse katabt) = [1, 3] := by decide

/-- A stray initial light before a heavy (12c.i), (15c): *mudarrísit* parses as
`mu(dàr)(rí.si)t`. -/
theorem gridColumns_mudarrisit : Tree.columns (parse mudarrisit) = [1, 2, 3, 1] := by decide

/-- Even parity after a heavy (12c.i), (15c): *ʔadwiyatúhu* parses as `(ʔàd)(wì.ya)(tú.hu)`. -/
theorem gridColumns_Padwiyatuhu : Tree.columns (parse Padwiyatuhu) = [2, 2, 1, 3, 1] := by
  decide

/-- Even parity from the left edge (12c.i), (15c): *šajaratuhúma:* parses as
`(šà.ja)(rà.tu)(hú.ma)`. -/
theorem gridColumns_sajaratuhuma :
    Tree.columns (parse sajaratuhuma) = [2, 1, 2, 1, 3, 1] := by decide

/-- The head terminal of *kátaba* is the head syllable of its head foot, read off the grid's
spine as an element rather than a height. -/
theorem headTerminals_kataba : Tree.headTerminals (parse kataba) = [.σ 1 true] := by decide

/-! ### The Continuous Column Constraint blocks final promotion

End Rule Right would, naively, mark the rightmost column, the stray final light of *kátaba*.
That column rests only on its syllable-layer beat: a word-layer mark over it would leave the
foot layer empty beneath, the gapped column of (17) that the Continuous Column Constraint (9)
of Section 3.4.2 rules out, so the mark falls on the rightmost foot head and the peak lands
inward. -/

/-- The attested grid of *kátaba*: a continuous staircase, the primary column of three on the
antepenult, the foot layer supporting it, the stray final light flat. -/
theorem toGrid_kataba :
    Grid.ofTree (parse kataba) =
      [[true, true, true], [true, false, false], [true, false, false]] := by
  decide

/-- The grid of *kátaba* satisfies the Continuous Column Constraint, as every grid read off a
tree does (`Prosody.Grid.ofTree_isContinuous`). -/
theorem cairene_grid_continuous : Marks.IsContinuous (Grid.ofTree (parse kataba)) :=
  Grid.ofTree_isContinuous _

/-- The grid *kátaba* would have if End Rule Right promoted the stray final light, (17): a
word-layer mark on the final column with no foot-layer mark beneath. -/
def promotedKataba : Marks := [[true, true, true], [true, false, false], [false, false, true]]

/-- Promoting the final light violates the Continuous Column Constraint: the final column of
`promotedKataba` is marked on layer 2 with nothing on layer 1. -/
theorem promotedKataba_not_continuous : ¬ Marks.IsContinuous promotedKataba := by decide

/-- The peak retracts off the right edge: the final stray light of *kátaba* is strictly weaker
than the primary, unlike the uniform right-strong words of [prince-1983], whose grids peak at
the edge. -/
theorem kataba_final_below_peak :
    (Tree.columns (parse kataba)).getLast?.getD 0 < Grid.peak (Tree.columns (parse kataba)) := by
  decide

end Hayes1995
