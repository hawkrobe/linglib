import Linglib.Phonology.Prosody.Syllable

/-!
# Metrical Foot Structure
[hayes-1995] [kager-2007]

Foot types, metrical parsing, and OT constraints on metrical structure.

A metrical foot is a prosodic constituent grouping syllables into a
rhythmic unit. [hayes-1995] identifies three canonical foot types:

| Type              | Well-formed shapes | Stress system   |
|-------------------|--------------------|-----------------|
| Moraic trochee    | (H), (LL)         | Weight-sensitive |
| Syllabic trochee  | (σσ)               | Weight-insensitive |
| Iamb              | (LH), (LL), (H)   | Right-prominent  |

The foot's *head* (prominent syllable) determines stress: initial in
trochees, final in iambs.

## Main definitions

* `FootType` — the three canonical foot types.
* `ParseElement` / `MetricalParse` — an element of, and a complete, metrical
  parse of a prosodic domain.
* `footMorae`, `isWellFormedFoot`, `isDegenerate` — foot weight and shape.
* `ftBinViolations`, `parseSylViolations`, `allFtLeftViolations`,
  `allFtRightViolations` — OT metrical constraints.
-/

namespace Prosody

/-! ### Foot type -/

/-- The three canonical foot types ([hayes-1995]). -/
inductive FootType where
  /-- Moraic trochee: bimoraic with initial prominence.
      Well-formed shapes: (H) = 2μ, (LL) = 2μ.
      Used in weight-sensitive stress (Turkish, Latin, Telugu). -/
  | moraicTrochee
  /-- Syllabic trochee: bisyllabic with initial prominence.
      Well-formed shape: (σσ) regardless of weight.
      Used in weight-insensitive stress (Czech, Pintupi). -/
  | syllabicTrochee
  /-- Iamb: prominence on the heavier/final syllable.
      Well-formed shapes: (LH), (LL), (H).
      Used in right-prominent stress (Creek, Yupik). -/
  | iamb
  deriving DecidableEq, Repr

/-! ### Metrical parse -/

/-- An element in a metrical parse: either a foot grouping syllables
    or an unparsed (stray) syllable. The list preserves left-to-right
    linear order within the prosodic domain. -/
inductive ParseElement where
  /-- A foot containing one or more syllables (represented by weight). -/
  | foot : List Syllable.Weight → ParseElement
  /-- An unparsed syllable not dominated by any foot. -/
  | unfooted : Syllable.Weight → ParseElement
  deriving DecidableEq, Repr

/-- A metrical parse: a prosodic domain represented as a linear sequence
    of footed and unfooted syllables. -/
abbrev MetricalParse := List ParseElement

/-! ### Parse properties -/

/-- Extract all feet from a parse. -/
def MetricalParse.feet (p : MetricalParse) : List (List Syllable.Weight) :=
  p.filterMap λ | .foot ws => some ws | .unfooted _ => none

/-- Mora count of a single foot (each weight *is* a mora count). -/
def footMorae (ws : List Syllable.Weight) : Nat :=
  ws.foldl (· + ·) 0

/-- Total syllable count in a parse. -/
def MetricalParse.syllableCount (p : MetricalParse) : Nat :=
  p.foldl (λ acc e => acc + match e with
    | .foot ws => ws.length
    | .unfooted _ => 1) 0

/-- Number of unparsed syllables in a parse. -/
def MetricalParse.unparsedCount (p : MetricalParse) : Nat :=
  p.filter (λ | .unfooted _ => true | _ => false) |>.length

/-- Is a foot degenerate (subminimal)? A monomoraic foot (L) is
    degenerate — it fails to meet the bimoraic minimum. -/
def isDegenerate (ws : List Syllable.Weight) : Prop :=
  footMorae ws < 2

instance (ws : List Syllable.Weight) : Decidable (isDegenerate ws) := by
  unfold isDegenerate; infer_instance

/-- Is a foot well-formed for the given foot type?

    The iamb clause encodes Hayes' canonical right-prominent inventory
    `{(H), (LL), (LH)}` ([hayes-1995]): a bimoraic monosyllable,
    or a disyllable that is right-heavy-or-even (first syllable no heavier
    than the second) with two or three morae. This excludes the degenerate
    monomoraic `(L)`, the left-heavy `(HL)`, and the trimoraic monosyllable
    `(SH)` — the Iambic/Trochaic-Law asymmetry that the moraic-trochee
    clause (`footMorae = 2`) lacks. -/
def isWellFormedFoot (ft : FootType) (ws : List Syllable.Weight) : Prop :=
  match ft with
  | .moraicTrochee => footMorae ws = 2
  | .syllabicTrochee => ws.length = 2
  | .iamb =>
    (ws.length = 1 ∧ footMorae ws = 2) ∨
    (ws.length = 2 ∧ 2 ≤ footMorae ws ∧ footMorae ws ≤ 3 ∧
      ws.headD 0 ≤ ws.getLast?.getD 0)

instance (ft : FootType) (ws : List Syllable.Weight) :
    Decidable (isWellFormedFoot ft ws) := by
  unfold isWellFormedFoot; cases ft <;> infer_instance

/-! ### OT metrical constraints -/

/-- FT-BIN(μ): assign one violation for each foot that does not consist
    of exactly two morae ([kager-2007]).

    Well-formed moraic trochees: (H) = 2μ, (LL) = 2μ.
    Violations: degenerate (L) = 1μ, superheavy (SH) = 3μ. -/
def ftBinViolations (p : MetricalParse) : Nat :=
  p.feet.filter (λ ws => footMorae ws != 2) |>.length

/-- PARSE-SYL: assign one violation for each syllable not parsed into
    a foot ([kager-2007]). Drives exhaustive parsing. -/
def parseSylViolations (p : MetricalParse) : Nat :=
  p.unparsedCount

/-- ALL-FT-LEFT: for each foot, count the number of syllables
    intervening between the left edge of the prosodic domain and the
    left edge of the foot ([kager-2007]). Sum over all feet.

    A foot at syllable position k (0-indexed) incurs k violations.
    Drives left-to-right iterative footing. -/
def allFtLeftViolations (p : MetricalParse) : Nat :=
  let rec go : List ParseElement → Nat → Nat
    | [], _ => 0
    | .foot ws :: rest, pos => pos + go rest (pos + ws.length)
    | .unfooted _ :: rest, pos => go rest (pos + 1)
  go p 0

/-- ALL-FT-RIGHT: for each foot, count the number of syllables
    intervening between the right edge of the foot and the right edge
    of the prosodic domain. Sum over all feet.

    Drives right-to-left iterative footing. -/
def allFtRightViolations (p : MetricalParse) : Nat :=
  let total := p.syllableCount
  let rec go : List ParseElement → Nat → Nat
    | [], _ => 0
    | .foot ws :: rest, pos =>
      let rightEdge := pos + ws.length
      (total - rightEdge) + go rest rightEdge
    | .unfooted _ :: rest, pos => go rest (pos + 1)
  go p 0

/-! ### Worked examples

Anonymous `example`s rather than named lemmas: these lock in the non-trivial
`isWellFormedFoot` inventory and the OT-constraint counts, but are not reusable
API. -/

-- Moraic trochee: the canonical {(H), (LL)} inventory.
example : isWellFormedFoot .moraicTrochee [.heavy] := by decide
example : isWellFormedFoot .moraicTrochee [.light, .light] := by decide
example : ¬ isWellFormedFoot .moraicTrochee [.light] := by decide

-- Iamb: the canonical right-prominent inventory {(H), (LL), (LH)} only —
-- excluding the degenerate (L), the left-heavy (HL), and the trimoraic (SH).
example : isWellFormedFoot .iamb [.heavy] := by decide
example : isWellFormedFoot .iamb [.light, .light] := by decide
example : isWellFormedFoot .iamb [.light, .heavy] := by decide
example : ¬ isWellFormedFoot .iamb [.light] := by decide
example : ¬ isWellFormedFoot .iamb [.heavy, .light] := by decide
example : ¬ isWellFormedFoot .iamb [.superheavy] := by decide

-- Degeneracy: only the monomoraic (L) foot is subminimal.
example : isDegenerate [.light] := by decide
example : ¬ isDegenerate [.heavy] := by decide
example : ¬ isDegenerate [.light, .light] := by decide

-- OT metrical constraints on worked parses.
/-- (ˈCV.CV).CV: one bimoraic foot (LL) + one stray light syllable. -/
private abbrev parse_llU : MetricalParse := [.foot [.light, .light], .unfooted .light]
example : ftBinViolations parse_llU = 0 := rfl
example : parseSylViolations parse_llU = 1 := rfl
example : allFtLeftViolations parse_llU = 0 := rfl

/-- (ˈLL)(ˌH): two bimoraic feet — the Telugu stem parse of *samudr-am*. -/
private abbrev parse_llH : MetricalParse := [.foot [.light, .light], .foot [.heavy]]
example : ftBinViolations parse_llH = 0 := rfl
example : parseSylViolations parse_llH = 0 := rfl
example : allFtLeftViolations parse_llH = 2 := rfl

/-- Competing parses: a stray heavy (worse on PARSE-SYL), and three degenerate
    feet (worse on FT-BIN). -/
private abbrev parse_llU_heavy : MetricalParse := [.foot [.light, .light], .unfooted .heavy]
example : parseSylViolations parse_llU_heavy = 1 := rfl
private abbrev parse_lllH : MetricalParse := [.foot [.light], .foot [.light], .foot [.heavy]]
example : ftBinViolations parse_lllH = 2 := rfl

end Prosody
