import Linglib.Phonology.Prosody.Mora
import Linglib.Core.Data.RoseTree.Basic

/-!
# Syllables
[hayes-1989] [hyman-1985] [selkirk-1982] [clements-1990]

The syllable (σ) — the level above the mora in the prosodic hierarchy: a headed
**moraic** constituent ([hayes-1989]; [hyman-1985]). A non-moraic `onset` sits over a
moraic spine whose **head is the nucleus** — the sonority peak ([clements-1990]; the
"nucleus = head of σ" reading follows dependency/government phonology).
The nucleus mora is mandatory and structurally **initial** (a σ has ≥1 mora by
construction; there is no head-direction parameter — unlike the foot); `tail` carries
any further nuclear morae (long vowels) and a moraic coda.

The moraic structure is the **carrier** (weight is mora-based and load-bearing, so —
unlike the foot — the tree and onset-rime are secondary). The rival **onset-rime**
theory ([selkirk-1982]) is a re-representation (`toOnsetRime`), proved to agree with the
moraic carrier on weight; the segment string is the `yield`.

## Main definitions

* `Syllable` — a headed moraic σ: `onset`, a nucleus `head` mora, and a `tail` of morae.
* `Syllable.morae` / `nucleusMora` / `nucleusSegments` / `weight` / `moraCount`.
* `Syllable.IsHeavy` / `IsLight` — the weight inventory (sonority/SSP well-formedness is
  a syllabification follow-up).
* `Syllable.ofCV` / `mk'` — smart constructors (a non-empty nucleus is required).
* `Syllable.yield` / `toOnsetRime` — re-representations; `toOnsetRime_weight` is the
  weight-correspondence between the moraic and onset-rime theories.
* `Syllable.Weight` — `Nat` (the mora count), with `.light`/`.heavy`/`.superheavy`.
-/

namespace Prosody

open Phonology (Segment)

/-! ### Syllables -/

/-- σ — a headed moraic syllable ([hayes-1989]): a non-moraic `onset`, a nucleus `head`
    mora (the sonority peak; mandatory, so σ has ≥1 mora and the head is initial by
    construction), and a `tail` of further morae (long-vowel morae + a moraic coda). -/
structure Syllable where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The nucleus mora — the sonority peak; mandatory, so σ has ≥ 1 mora. -/
  head  : Mora
  /-- Further morae: long-vowel morae and a moraic coda. -/
  tail  : List Mora
  deriving DecidableEq

namespace Syllable

/-- Syllable weight is just the mora count — there is no separate weight type.
    `.light` (1μ), `.heavy` (2μ), `.superheavy` (3μ) name the common values for
    readable weight profiles in metrical and accentual computations. -/
abbrev Weight := Nat

namespace Weight
abbrev light : Weight := 1
abbrev heavy : Weight := 2
abbrev superheavy : Weight := 3
end Weight

/-- The moraic spine, nucleus (peak) first. -/
def morae (σ : Syllable) : List Mora := σ.head :: σ.tail

/-- The nucleus — the head mora (the sonority peak). -/
abbrev nucleusMora (σ : Syllable) : Mora := σ.head

/-- The nucleus segment(s). -/
def nucleusSegments (σ : Syllable) : List Segment := σ.head.dominates

/-- The number of morae — the syllable's weight. -/
def moraCount (σ : Syllable) : Nat := σ.morae.length

/-- The syllable's weight (= its mora count). -/
abbrev weight (σ : Syllable) : Weight := σ.moraCount

/-- A heavy syllable: at least two morae. -/
def IsHeavy (σ : Syllable) : Prop := Weight.heavy ≤ σ.weight
/-- A light syllable: exactly one mora. -/
def IsLight (σ : Syllable) : Prop := σ.weight = Weight.light

instance (σ : Syllable) : Decidable σ.IsHeavy := by unfold IsHeavy; infer_instance
instance (σ : Syllable) : Decidable σ.IsLight := by unfold IsLight; infer_instance

/-- Build a syllable from an explicit nucleus mora (+ optional further/coda morae). -/
def mk' (onset : List Segment) (nucleus : Mora) (coda : List Mora := []) : Syllable :=
  ⟨onset, nucleus, coda⟩

/-- Build a syllable from an onset and a non-empty mora spine (nucleus = first mora). -/
def ofMorae (onset : List Segment) (ms : List Mora) (h : ms ≠ [] := by simp) : Syllable :=
  ⟨onset, ms.head h, ms.tail⟩

/-- Build a syllable from a segmental onset–nucleus–coda string. Each nucleus segment
    projects a mora (the first is the nucleus head). Under Weight by Position
    ([hayes-1989]) the first coda segment projects its own mora and any further coda
    segments ride it, so the syllable stays at most bimoraic; without it the coda rides
    the last nucleus mora. A non-empty nucleus is required. -/
def ofCV (onset nucleus coda : List Segment) (wbp : Bool := true)
    (hn : nucleus ≠ [] := by simp) : Syllable :=
  match nucleus, hn with
  | [], h => (h rfl).elim
  | n₀ :: ns, _ =>
    match wbp, coda with
    | true, c :: cs => ⟨onset, Mora.of n₀, ns.map Mora.of ++ [(Mora.of c).attach cs]⟩
    | _, _ =>
      match (ns.map Mora.of).reverse with
      | last :: rest => ⟨onset, Mora.of n₀, rest.reverse ++ [last.attach coda]⟩
      | []           => ⟨onset, (Mora.of n₀).attach coda, []⟩

/-- The segment string (yield) of a syllable: onset followed by the moraic melody. -/
def yield (σ : Syllable) : List Segment := σ.onset ++ σ.morae.flatMap (·.dominates)

end Syllable

/-! ### Onset-rime re-representation -/

/-- The onset-rime structure ([selkirk-1982]): a rival theory of σ structure, an onset
    over a rime. Here a re-representation of the canonical moraic `Syllable`. -/
structure OnsetRime where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The rime: the moraic spine. -/
  rime  : List Mora
  deriving DecidableEq

/-- σ → onset-rime: the rime is the moraic spine ([selkirk-1982]). -/
def Syllable.toOnsetRime (σ : Syllable) : OnsetRime := ⟨σ.onset, σ.morae⟩

/-- **Weight correspondence**: the onset-rime rime's mora count equals σ's weight — the
    moraic and onset-rime theories agree on weight ([selkirk-1982]; [hayes-1989]). -/
theorem Syllable.toOnsetRime_weight (σ : Syllable) :
    σ.toOnsetRime.rime.length = σ.moraCount := rfl

/-! ### Yield -/

/-- A **yield**: the terminal σ-weight string of a prosodic structure — the
    unparsed input, or the leaves of a prosodic `Tree`. Distinct from the prosodic
    word ω (an `IsWord` tree), which is a *headed constituent*: a yield is just the
    weight profile, with no head and no constituency. -/
abbrev Yield := List Syllable.Weight

namespace Yield

/-- The weight profile of fully-moraified syllables — the σ → yield bridge. -/
def ofSyllables (σs : List Syllable) : Yield := σs.map Syllable.weight

/-- Total mora count (each weight *is* a mora count). -/
def moraCount (y : Yield) : Nat := y.sum

/-- The minimal-word *size* constraint ([mccarthy-prince-1993]): at least
    `minMorae` morae (default 2, the moraic-trochee minimum) — the moraic *size* floor on a
    prosodic word. Whether an ω must structurally contain a foot is a separate, non-presupposed
    matter (footless languages have ω directly over σ, [dolatian-2020]). -/
abbrev satisfiesMinWord (y : Yield) (minMorae : Nat := 2) : Prop := minMorae ≤ y.moraCount

end Yield

/-! ### The prosodic-tree carrier

The recursive prosodic constituent ([ito-mester-2003]): the Core ordered rose tree
`RoseTree` labeled by prosodic-level `Constituent`s — the **violable OT candidate
carrier** for ω/φ/… structures, including the ill-formed ones (a footless ω, a stray under
φ) that `IsWord` rules out. Its OT constraints are
`Constraints.Constraint Tree` values, defined alongside `IsWord`. Homed here because
`Constituent.weight`/`.syl` need `Syllable.Weight`; it inherits `DecidableEq`/`map` from
`RoseTree`. -/

/-- A prosodic node — the **level is the constructor**: a σ carries its mora `weight` and `isHead`,
    every non-root level carries `isHead` (whether it heads its parent). Constructor defaults match
    the former smart constructors, so node literals are unchanged; illegal nodes (a weight on a
    foot, a head on the ι root) are unrepresentable. -/
inductive Constituent
  /-- A syllable of the given `weight`, optionally the head of its foot. -/
  | syl (weight : Syllable.Weight := 0) (isHead : Bool := false)
  /-- A foot, optionally the head foot of its word. -/
  | ft (isHead : Bool := false)
  /-- A prosodic word ω, optionally the head word of its phrase. -/
  | om (isHead : Bool := false)
  /-- A phonological phrase φ, optionally the head phrase of its
  intonational phrase. -/
  | ph (isHead : Bool := false)
  /-- An intonational phrase ι — the root of the utterance-level
  hierarchy, headless. -/
  | iota
  deriving DecidableEq, Repr

namespace Constituent

/-- Whether a node heads its parent (a σ heads its foot, a foot heads its word, an ω its phrase,
    a φ its intonational phrase); `false` for the ι root. -/
def isHead : Constituent → Bool
  | .syl _ h => h | .ft h => h | .om h => h | .ph h => h | .iota => false

/-- The mora weight of a σ node; `none` for non-σ nodes. -/
def weight? : Constituent → Option Syllable.Weight
  | .syl w _ => some w | _ => none

/-- A syllable (σ) node. -/
def isSyl : Constituent → Bool | .syl .. => true | _ => false
/-- A foot (f) node. -/
def isFt : Constituent → Bool | .ft _ => true | _ => false
/-- A prosodic-word (ω) node. -/
def isOm : Constituent → Bool | .om _ => true | _ => false
/-- A phonological-phrase (φ) node. -/
def isPh : Constituent → Bool | .ph _ => true | _ => false
/-- An intonational-phrase (ι) node. -/
def isIota : Constituent → Bool | .iota => true | _ => false

/-- Two nodes at the same prosodic level (the same constructor, ignoring weight/head) — the
    same-category test the No-Recursion family reads off the carrier. -/
def sameLevel : Constituent → Constituent → Bool
  | .syl .., .syl .. | .ft _, .ft _ | .om _, .om _ | .ph _, .ph _
  | .iota, .iota => true
  | _, _ => false

/-- The level family is exclusive: a foot is not a syllable. -/
theorem isSyl_eq_false_of_isFt {x : Constituent} (h : x.isFt = true) : x.isSyl = false := by
  cases x <;> simp_all [isFt, isSyl]

/-- The level family is exclusive: a prosodic word is not a syllable. -/
theorem isSyl_eq_false_of_isOm {x : Constituent} (h : x.isOm = true) : x.isSyl = false := by
  cases x <;> simp_all [isOm, isSyl]

end Constituent

/-- A prosodic tree: the Core ordered rose tree `RoseTree` labeled by
    `Constituent`s. Ordered children give No-Tangling by construction. -/
abbrev Tree := RoseTree Constituent

/-- A σ-leaf — the metrical terminal: a syllable of weight `w`, head-marked `h`. -/
abbrev Tree.σ (w : Syllable.Weight := 0) (h : Bool := false) : Tree := .node (.syl w h) []

/-- A foot node over `cs`, optionally the head foot of its word. -/
abbrev Tree.ft (h : Bool) (cs : List Tree) : Tree := .node (.ft h) cs

/-- A prosodic-word (ω) node over `cs`. -/
abbrev Tree.om (cs : List Tree) : Tree := .node .om cs

/-- A phonological-phrase (φ) node over `cs` — interim, until `Prosody.Phrase` lands. -/
abbrev Tree.ph (cs : List Tree) : Tree := .node .ph cs

/-- **Leaf/branch induction on a prosodic tree.** A σ-leaf is a base case; every other node — a
    foot, word, phrase, or degenerate/ill-formed node — is a branch, carrying the induction
    hypothesis over its children and the fact that it is *not* a σ-leaf. This is what lets proofs
    reduce the σ-leaf `if` the reader equations carry (via `if_pos ⟨ha, rfl⟩` / `if_neg hne`)
    instead of `split`ting it. -/
@[elab_as_elim]
theorem Tree.recLeafBranch {motive : Tree → Prop}
    (leaf : ∀ a, a.isSyl → motive (.node a []))
    (branch : ∀ a cs, ¬(a.isSyl ∧ cs = []) → (∀ c ∈ cs, motive c) → motive (.node a cs))
    (t : Tree) : motive t := by
  induction t using RoseTree.rec' with
  | node a cs ih =>
    by_cases h : a.isSyl ∧ cs = []
    · obtain ⟨ha, rfl⟩ := h; exact leaf a ha
    · exact branch a cs h ih

end Prosody
