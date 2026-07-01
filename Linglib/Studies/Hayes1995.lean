import Linglib.Phonology.Prosody.Grid

/-!
# Moraic trochees in Cairene Arabic ([hayes-1995] §4.1.3)

Cairene Arabic stress is quantity-sensitive: where the prominence peak lands depends on
syllable weight. [hayes-1995] (after Mitchell 1960, McCarthy 1979a) derives the pattern by
parsing the word **left to right into moraic trochees** — a foot is either two light
syllables `(σ́σ)` or one heavy `(H́)`, bimoraic either way — and placing the main stress on
the head of the rightmost foot (**End Rule Right**). A single light syllable cannot form a
foot — independently supported by the absence of CV(C) content words in the language
([mccarthy-prince-1990]) — so a word ending in an odd light syllable leaves it *stray*
(unfooted).

`parse` is that algorithm on the weight string; reading the stress off the result with the
metrical grid (`Prosody.Grid.columns`) recovers the attested prominences — primary `3`,
secondary `2`, unstressed `1`. Quantity moves the peak: all-light `kataba` is stressed on the
**antepenult**, but a heavy penult (`mudarris`) draws stress to the **penult**. (The forms
`kataba` and `ʔinkasara` are Cairene *Classical*; [hayes-1995] shows these take the same
stressing as colloquial Cairene, so the analysis is label-independent.)

The grid stress-test turns on the **Continuous Column Constraint** ([prince-1983]; [hayes-1995]
§3.4.2 (9), formalised as `Prosody.Grid.ofTree_isContinuous`): End Rule Right cannot promote the stray
final light syllable, because a column raised over an unfooted syllable would have a *gap* —
a mark on a higher layer with none below — and the grid forbids that. So the peak retracts
*inward* off the right edge, unlike the uniform words of [prince-1983] whose peak sits at the
edge. The input here is the post-extrametricality weight profile; consonant/mora
extrametricality ([hayes-1995] (14a–b)), which adjusts final-syllable weight, is upstream.
-/

namespace Hayes1995

open Prosody RootedTree

/-! ### The moraic-trochee parse

Walk the weight string left to right. A heavy σ (`2 ≤ w`, bimoraic) is its own foot `(H́)`; two
lights make a trochee `(σ́σ)`, head on the left; a light with no light to pair with is left
stray. Foot heads are marked as the parse builds them; `markHeadFoot` then promotes the
**rightmost** foot to head foot — End Rule Right. -/

/-- Parse a (post-extrametricality) weight string into moraic-trochee cells, left to right:
    a heavy σ is a monosyllabic foot, two lights a trochee, a lone light a stray σ. Every foot
    marks its own head σ; the head *foot* is selected by `markHeadFoot`. -/
def parseCells : Yield → List Tree
  | [] => []
  | [w] =>
      if Syllable.Weight.heavy ≤ w then [.node (.ft false) [.node (.syl w true) []]]
      else [.node (.syl w false) []]
  | w :: w2 :: rest =>
      if Syllable.Weight.heavy ≤ w then
        .node (.ft false) [.node (.syl w true) []] :: parseCells (w2 :: rest)
      else if Syllable.Weight.heavy ≤ w2 then
        .node (.syl w false) [] :: parseCells (w2 :: rest)
      else
        .node (.ft false) [.node (.syl w true) [], .node (.syl w2 false) []] :: parseCells rest

/-- Is this ω-daughter an `f`-level foot? -/
def isFootChild : Tree → Bool
  | .node a _ => a.isFt

/-- **End Rule Right**: mark the rightmost foot as the head foot. The first foot with no foot
    to its right (scanning left to right) is promoted; everything else is left untouched. -/
def markHeadFoot : List Tree → List Tree
  | [] => []
  | .node a ds :: rest =>
      if a.isFt && !rest.any isFootChild then
        .node (.ft true) ds :: rest
      else
        .node a ds :: markHeadFoot rest

/-- The Cairene parse ([hayes-1995] §4.1.3): a prosodic word over moraic trochees built left to
    right, the rightmost foot heading the word. -/
def parse (y : Yield) : Tree := .node .om (markHeadFoot (parseCells y))

/-! ### Quantity-sensitive stress

The forms are [hayes-1995]'s, given as their post-extrametricality weight profiles
(`1` = light CV, `2` = heavy CVC/CVV). Reading `Grid.columns ∘ parse` recovers the attested
stress: the column of `3` is the primary, `2` a secondary, `1` unstressed. -/

/-- *kataba* `ka.ta.ba` 'he wrote' — all light (Cairene Classical). -/
def kataba : Yield := [1, 1, 1]
/-- *mudarri(s)* `mu.dar.ri` 'teacher' — heavy penult (colloquial). -/
def mudarris : Yield := [1, 2, 1]
/-- *ʔinkasara* `ʔin.ka.sa.ra` 'it got broken' — heavy initial (Cairene Classical). -/
def Pinkasara : Yield := [2, 1, 1, 1]

/-- **Antepenultimate stress** ([hayes-1995] (15d), (16d)): all-light `kataba` parses as
    `(ká.ta)ba`, the rightmost foot heading the antepenult; the final light is stray. -/
theorem gridColumns_kataba : Grid.columns (parse kataba) = [3, 1, 1] := by decide

/-- **Penultimate stress** ([hayes-1995] (12b), (15b)): with a heavy penult, `mudarris` parses
    as `mu(dár)ri` — the heavy is its own foot, rightmost, so quantity pulls the peak one
    syllable rightward off the antepenult. -/
theorem gridColumns_mudarris : Grid.columns (parse mudarris) = [1, 3, 1] := by decide

/-- **Restarting the count after a heavy, with secondary stress** ([hayes-1995] (15d), (16d)):
    `ʔinkasara` parses as `(ʔìn)(ká.sa)ra` — the heavy initial is its own foot (secondary `2`),
    the count restarts, the next two lights foot, and the antepenult `ka` takes primary `3`. -/
theorem gridColumns_Pinkasara : Grid.columns (parse Pinkasara) = [2, 3, 1, 1] := by decide

/-- **The head terminal is the antepenult head σ** ([liberman-prince-1977]): `kataba`'s head
    terminal — its primary stress, Liberman & Prince's head terminal — is the head
    syllable of the rightmost (head) foot, read off the grid's live column as an *element*, not
    just a height (cf. `gridColumns_kataba`'s `[3, 1, 1]`). -/
theorem headTerminals_kataba : Grid.headTerminals (parse kataba) = [.node (.syl 1 true) []] := by decide

/-! ### The Continuous Column Constraint blocks final promotion

Why the peak does not sit at the right edge. End Rule Right would, naively, mark the rightmost
*column* — the stray final light. But that column rests only on its syllable-layer beat: raising
a word-layer mark over it leaves the foot layer empty beneath, a gapped column the
**Continuous Column Constraint** rules out ([hayes-1995] §3.4.2 (9), §4.1.3 (17)). So the mark retracts to the
rightmost foot head, and the peak lands inward. The attested grid is continuous *by
construction* (`Prosody.Grid.ofTree_isContinuous`); the promotion is not. -/

/-- The attested grid of `kataba`: a continuous staircase, the primary column of three on the
    antepenult, the foot layer (`true` row 1) supporting it, the stray final light flat. -/
theorem toGrid_kataba :
    Grid.ofTree (parse kataba) = [[true, true, true], [true, false, false], [true, false, false]] := by
  decide

/-- **The grid is well-formed** ([hayes-1995] §3.4.2 (9)): `kataba`'s grid satisfies the Continuous
    Column Constraint — a consumer of the derived `Prosody.Grid.ofTree_isContinuous`, here doing the
    work that makes the inward peak the *only* legal reading. -/
theorem cairene_grid_continuous : Marks.IsContinuous (Grid.ofTree (parse kataba)) := Grid.ofTree_isContinuous _

/-- The grid `kataba` would have if End Rule Right promoted the stray final light: a word-layer
    mark on the final column (`[hayes-1995] (17)`, *(x)(x.)*) with no foot-layer mark beneath. -/
def promotedKataba : Marks := [[true, true, true], [true, false, false], [false, false, true]]

/-- **Promoting the final light violates the CCC** ([hayes-1995] (16d), (17)): the final
    column of `promotedKataba` is marked on layer 2 with nothing on layer 1 — a gap. This is
    exactly why End Rule Right cannot reach the edge, and the peak retracts inward. -/
theorem promotedKataba_not_continuous : ¬ Marks.IsContinuous promotedKataba := by decide

/-- **The peak retracts off the right edge** ([hayes-1995] (16d)): the final stray light of
    `kataba` is strictly weaker than the primary — unlike a uniform right-strong word
    ([prince-1983]), whose grid peaks at the edge. The blocked promotion above is why. -/
theorem kataba_final_below_peak :
    (Grid.columns (parse kataba)).getLast?.getD 0 < Grid.peak (Grid.columns (parse kataba)) := by
  decide

end Hayes1995
