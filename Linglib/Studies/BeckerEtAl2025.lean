import Linglib.Phonology.Prosody.Grid
import Linglib.Phonology.OptimalityTheory.Basic

/-!
# The incoherent stress of Kuikuro
[becker-etal-2025] [liberman-prince-1977] [hayes-1995]

Kuikuro (Cariban; Mato Grosso, Brazil) builds **iambic feet left to right**, with **final trochaic
reversal**: when an iamb would leave a phrase-final long vowel, the last two syllables parse as a
trochee instead ([becker-etal-2025] §3.1; [hayes-1995] §5.3b). The **last foot is the head foot**
of the word, and the **primary stress is the head of the head foot** ([becker-etal-2025] p. 2365)
— i.e. the syllable reached from the word ω by an all-head descent: the **head terminal**
(Liberman & Prince's *designated terminal element*, `Prosody.Grid.headTerminals`).

The paper's title result — *incoherent* stress ([gordon-2016]) — is that the default High tone does
**not** dock on this head terminal but surfaces displaced, on the last syllable of a tone domain
that starts at the primary stress and expands rightward to (but not including) the next foot head.
The metrically most prominent syllable is thereby dissociated from the high-toned salient one.

This file formalizes the **default-length metrical spine** the tonal analysis is anchored to: the
left-to-right iambic footing (with final trochaic reversal) of words in isolation, and the
certification that the primary stress is exactly the grid's head terminal. That a word has a
*unique* head terminal (`Prosody.Grid.IsHeaded`) is metrical culminativity — Liberman & Prince's DTE
uniqueness ([hyman-2006]). The paper's `Culminativity-H` (§4.2) is a *distinct, tonal* constraint
("one violation per High tone domain with more than one foot head"), part of the deferred tone
layer. Also deferred alongside tone: lexical long vowels (Max-μ, monosyllabic feet, §3.1), word
minimality (FtBin, §3.5), and final shortening (§4.1). Here the head terminal is the *anchor* the
tonal layer displaces from.

Weights: `1` = short (light) σ, `2` = a long (heavy) σ from iambic lengthening; a foot's `isHead`
σ is its head (iamb → final, trochee → initial), and the head foot is `isHead := true`.
-/

namespace BeckerEtAl2025

open Prosody Constraints OptimalityTheory

/-! ### Words in isolation ([becker-etal-2025] §3) -/

/-- *[(a.lá:)(ma.kí:)li]* 's/he fell' ([becker-etal-2025] Fig. 1): two iambs and a stray final σ.
    The rightmost foot `(ma.kí:)` heads the word, so the long `kí:` is the primary stress. -/
def fell : Tree :=
  .node .om
    [ .node (.ft false) [.node (.syl 1 false) [], .node (.syl 2 true) []],
      .node (.ft true)  [.node (.syl 1 false) [], .node (.syl 2 true) []],
      .node (.syl 1 false) [] ]

/-- *[(tsi.ha:)(la.ma:)(kí.li)]* 'we (exclusive) fell' ([becker-etal-2025] Fig. 2): even-parity, so
    the final two short syllables reverse to a **trochee** `(kí.li)` — the head foot — and the
    initial `kí` is the primary stress. -/
def weFell : Tree :=
  .node .om
    [ .node (.ft false) [.node (.syl 1 false) [], .node (.syl 2 true) []],
      .node (.ft false) [.node (.syl 1 false) [], .node (.syl 2 true) []],
      .node (.ft true)  [.node (.syl 1 true)  [], .node (.syl 1 false) []] ]

/-- *[(u.mí:)ŋi]* 'annatto' ([becker-etal-2025] Fig. 3): one iamb and a stray final σ; the long
    `mí:` is the primary stress. -/
def annatto : Tree :=
  .node .om
    [ .node (.ft true) [.node (.syl 1 false) [], .node (.syl 2 true) []],
      .node (.syl 1 false) [] ]

/-! ### The grid: secondary stress on every foot head, primary on the head foot's

Reading `Grid.columns ∘` the footing recovers the stress profile: `1` unstressed, `2` a secondary
(a non-head foot's head), `3` the primary (the head foot's head). -/

theorem gridColumns_fell    : Grid.columns fell    = [1, 2, 1, 3, 1] := by decide
theorem gridColumns_weFell  : Grid.columns weFell  = [1, 2, 1, 2, 3, 1] := by decide
theorem gridColumns_annatto : Grid.columns annatto = [1, 3, 1] := by decide

/-! ### Primary stress is the head terminal ([becker-etal-2025] p. 2365)

Each word has a **unique head terminal** (`Grid.IsHeaded` — metrical culminativity, Liberman & Prince's
DTE uniqueness; cf. [hyman-2006]), and it is exactly the head syllable of the head foot — the long
`kí:`/`mí:`, or the reversed-trochee's initial `kí`. The primary stress is read off the grid's live
column as an *element*. -/

theorem isHeaded_fell    : Grid.IsHeaded fell    := by decide
theorem isHeaded_weFell  : Grid.IsHeaded weFell  := by decide
theorem isHeaded_annatto : Grid.IsHeaded annatto := by decide

/-- 's/he fell': the head terminal is the long `kí:` (head of the rightmost iamb). -/
theorem headTerminals_fell : Grid.headTerminals fell = [.node (.syl 2 true) []] := by decide

/-- 'we fell': the head terminal is the reversed trochee's initial short `kí`. -/
theorem headTerminals_weFell : Grid.headTerminals weFell = [.node (.syl 1 true) []] := by decide

/-- 'annatto': the head terminal is the long `mí:`. -/
theorem headTerminals_annatto : Grid.headTerminals annatto = [.node (.syl 2 true) []] := by decide

/-- The same fact **declaratively** ([liberman-prince-1977]): `kí:` is the head terminal of `fell`
    — reached from ω by an all-head descent (ω → head foot → head σ), `Grid.IsHeadTerminal` — via the
    spec↔fold bridge `Grid.mem_headTerminals_iff`, not just by computing the list. -/
theorem isHeadTerminal_fell : Grid.IsHeadTerminal fell (.node (.syl 2 true) []) :=
  Grid.mem_headTerminals_iff.mp (by decide)

/-! ### The trochaic reversal is OT-optimal ([becker-etal-2025] §3.1, Table 2)

Why the final foot reverses to a trochee: an even-parity `/σσσσ/` parsed as two iambs leaves a
**phrase-final long vowel** (`*V:]φ`); leaving the last two σ unparsed violates `Parse-σ`; so they
parse as a trochee, violating only the low-ranked `Iamb`. Ranking `*V:]φ ≫ Parse-σ ≫ Iamb`
([becker-etal-2025] (1)–(3), Table 2). -/

/-- The three footings of `/σσσσ/` weighed in [becker-etal-2025]'s Table 2. -/
inductive FootingCand where
  /-- `(σ́σ:)(σ́σ:)` — two iambs; a final long vowel. -/
  | twoIambs
  /-- `(σ́σ:)σσ` — one iamb, the last two σ unparsed. -/
  | iambStrays
  /-- `(σ́σ:)(´σσ)` — an iamb and a final **trochee** (the optimum). -/
  | iambTrochee
  deriving DecidableEq, Repr

/-- Each candidate as a footed tree (rightmost foot the head). -/
def FootingCand.toTree : FootingCand → Tree
  | .twoIambs    => .node .om [ .node (.ft false) [.node (.syl 1 false) [], .node (.syl 2 true) []],
                                .node (.ft true)  [.node (.syl 1 false) [], .node (.syl 2 true) []] ]
  | .iambStrays  => .node .om [ .node (.ft true)  [.node (.syl 1 false) [], .node (.syl 2 true) []],
                                .node (.syl 1 false) [], .node (.syl 1 false) [] ]
  | .iambTrochee => .node .om [ .node (.ft false) [.node (.syl 1 false) [], .node (.syl 2 true) []],
                                .node (.ft true)  [.node (.syl 1 true)  [], .node (.syl 1 false) []] ]

/-- **Parse-σ** ([becker-etal-2025] (1)): one mark per unparsed (stray) σ — a σ-leaf under ω. -/
def cParse : Constraint FootingCand := fun c => match c.toTree with
  | .node _ cs => (cs.filter (fun d => d.label.isSyl)).length

/-- **Iamb** ([becker-etal-2025] (2)): one mark per foot that is not right-headed (head σ ≠ final). -/
def cIamb : Constraint FootingCand := fun c => match c.toTree with
  | .node _ cs => (cs.filter (fun d => match d with
      | .node a ds => a.isFt && !((ds.getLast?.map (·.label.isHead)).getD false))).length

/-- **`*V:]φ`** ([becker-etal-2025] (3)): one mark for a long vowel in the **phrase**-final σ (for a
    one-word phrase, the word-final σ). -/
def cStarV : Constraint FootingCand := fun c =>
  match (Grid.columnsLive c.toTree).getLast? with
  | some col => if decide (col.leaf.label.weight? = some 2) then 1 else 0
  | none     => 0

def candidates : List FootingCand := [.twoIambs, .iambStrays, .iambTrochee]
theorem candidates_ne : candidates ≠ [] := by decide

/-- The ranking `*V:]φ ≫ Parse-σ ≫ Iamb` ([becker-etal-2025] Table 2). -/
def footingRanking : List (Constraint FootingCand) := [cStarV, cParse, cIamb]

/-- The violation profiles ([becker-etal-2025] Table 2):

    | candidate     | `*V:]φ` | Parse-σ | Iamb |
    |----------------|---------|---------|------|
    | (σ́σ:)(σ́σ:)     |   1*    |   0     |  0   |
    | (σ́σ:)σσ        |   0     |   2*    |  0   |
    | ☞ (σ́σ:)(´σσ)   |   0     |   0     |  1   |

    Table 2's `Max-μ` (ranked `*V:]φ ≫ Max-μ ≫ Parse-σ`) is omitted — vacuous (`0`) on all three
    candidates; it governs lexical long vowels (Tables 4/6). -/
theorem starV_violations : candidates.map cStarV = [1, 0, 0] := by decide
theorem parse_violations : candidates.map cParse = [0, 2, 0] := by decide
theorem iamb_violations  : candidates.map cIamb  = [0, 0, 1] := by decide

/-- **The trochaic reversal wins** ([becker-etal-2025] Table 2): under `*V:]φ ≫ Parse-σ ≫ Iamb` the
    optimal footing of `/σσσσ/` is the iamb + final **trochee** — no final long vowel, no unparsed
    σ, at the cost of one (low-ranked) non-right-headed foot. -/
theorem footing_optimal :
    (Tableau.ofRanking candidates footingRanking candidates_ne).optimal = {.iambTrochee} := by decide

end BeckerEtAl2025
