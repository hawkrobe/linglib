module

public import Mathlib.Data.PNat.Defs
public import Linglib.Phonology.Prosody.Mora
public import Linglib.Core.Data.RoseTree.Basic

/-!
# Syllables

The syllable σ is the level above the mora in the prosodic hierarchy, a headed moraic constituent
(Hayes 1989; Hyman 1985). A non-moraic `onset` sits over a moraic spine whose head is the nucleus,
the sonority peak (Clements 1990). The nucleus mora is mandatory and initial, so a σ has at least
one mora, and `tail` carries any further nuclear morae (long vowels) and a moraic coda. Weight is
mora-based, so the moraic structure is the carrier; Selkirk's (1982) rival onset-rime theory is a
re-representation (`toOnsetRime`) that agrees with it on weight. The file also defines the
prosodic constituents, the prosodic tree, and the Layeredness relation by which each constituent
licenses its daughters.

## Main definitions

* `Syllable` — a headed moraic σ: `onset`, a nucleus `head` mora, and a `tail` of morae.
* `Syllable.morae` / `nucleusMora` / `nucleusSegments` / `weight` / `moraCount` /
  `pnatMoraCount`.
* `Syllable.IsHeavy` / `IsLight` — the weight inventory (sonority/SSP well-formedness is
  a syllabification follow-up).
* `Syllable.ofCV` / `ofVowel` / `ofLongVowel` / `mk'` — smart constructors (a non-empty
  nucleus is required; a long vowel is two morae on one melody).
* `Syllable.yield` / `toOnsetRime` — re-representations; `toOnsetRime_weight` is the
  weight-correspondence between the moraic and onset-rime theories.
* `Syllable.Weight` — `Nat` (the mora count), with `.light`/`.heavy`/`.superheavy`.
* `Constituent`, `Tree` — the prosodic constituents and the prosodic tree over them.
* `Constituent.Licenses` — Layeredness: the daughters each constituent may dominate.

## References

* [hayes-1989]
* [hyman-1985]
* [clements-1990]
* [selkirk-1982]
* [mccarthy-prince-1993]
* [dolatian-2020]
* [ito-mester-2003]
-/

@[expose] public section

namespace Prosody

open Phonology (Segment)

/-! ### Syllables -/

/-- A syllable σ is a headed moraic constituent ([hayes-1989]) with a non-moraic `onset`, a
    nucleus `head` mora (the sonority peak; mandatory, so σ has at least one mora and the head is
    initial by construction), and a `tail` of further morae (long-vowel morae and a moraic
    coda). -/
structure Syllable where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The nucleus mora — the sonority peak; mandatory, so σ has ≥ 1 mora. -/
  head  : Mora
  /-- The further morae are long-vowel morae and a moraic coda. -/
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

/-- A syllable has at least its nucleus mora. -/
theorem moraCount_pos (σ : Syllable) : 0 < σ.moraCount := Nat.succ_pos _

/-- The mora count as a positive natural is the weight a `Tone.Registered` word reads. -/
def pnatMoraCount (σ : Syllable) : ℕ+ := ⟨σ.moraCount, σ.moraCount_pos⟩

/-- A syllable is heavy when it has at least two morae. -/
def IsHeavy (σ : Syllable) : Prop := Weight.heavy ≤ σ.weight
/-- A syllable is light when it has exactly one mora. -/
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

/-- The open syllable of an onset and a short vowel has one mora. -/
def ofVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, .of v, []⟩

/-- The open syllable of an onset and a long vowel has two morae dominating the same melody
([hayes-1989]). -/
def ofLongVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, .of v, [.of v]⟩

@[simp] theorem moraCount_ofVowel (onset : List Segment) (v : Segment) :
    (ofVowel onset v).moraCount = 1 := rfl

@[simp] theorem moraCount_ofLongVowel (onset : List Segment) (v : Segment) :
    (ofLongVowel onset v).moraCount = 2 := rfl

/-- The segment string, or yield, of a syllable is its onset followed by the moraic melody. -/
def yield (σ : Syllable) : List Segment := σ.onset ++ σ.morae.flatMap (·.dominates)

end Syllable

/-! ### Onset-rime re-representation -/

/-- The onset-rime structure of [selkirk-1982] is a rival theory of σ structure, an onset over a
    rime, here a re-representation of the canonical moraic `Syllable`. -/
structure OnsetRime where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The rime is the moraic spine. -/
  rime  : List Mora
  deriving DecidableEq

/-- Passing from σ to onset-rime structure, the rime is the moraic spine ([selkirk-1982]). -/
def Syllable.toOnsetRime (σ : Syllable) : OnsetRime := ⟨σ.onset, σ.morae⟩

/-- By **weight correspondence**, the onset-rime rime's mora count equals σ's weight, so the
    moraic and onset-rime theories agree on weight ([selkirk-1982]; [hayes-1989]). -/
theorem Syllable.toOnsetRime_weight (σ : Syllable) :
    σ.toOnsetRime.rime.length = σ.moraCount := rfl

/-! ### Yield -/

/-- A **yield** is the terminal σ-weight string of a prosodic structure, the unparsed input or
    the leaves of a prosodic `Tree`. Unlike the prosodic word ω (an `IsWord` tree), which is a
    headed constituent, a yield is just the weight profile, with no head and no constituency. -/
abbrev Yield := List Syllable.Weight

namespace Yield

/-- The weight profile of fully-moraified syllables — the σ → yield bridge. -/
def ofSyllables (σs : List Syllable) : Yield := σs.map Syllable.weight

/-- Total mora count (each weight *is* a mora count). -/
def moraCount (y : Yield) : Nat := y.sum

/-- The minimal-word size constraint of [mccarthy-prince-1993] asks for at least `minMorae`
    morae (default 2, the moraic-trochee minimum), the moraic size floor on a prosodic word.
    Whether an ω must structurally contain a foot is a separate, non-presupposed matter
    (footless languages have ω directly over σ, [dolatian-2020]). -/
abbrev satisfiesMinWord (y : Yield) (minMorae : Nat := 2) : Prop := minMorae ≤ y.moraCount

end Yield

/-! ### The prosodic-tree carrier

The recursive prosodic constituent ([ito-mester-2003]): the Core ordered rose tree
`RoseTree` labeled by prosodic-level `Constituent`s — the **violable OT candidate
carrier** for ω/φ/… structures, including the ill-formed ones (a footless ω, a stray under
φ) that `IsWord` rules out. Its OT constraints are
`OptimalityTheory.Constraint Tree` values, defined alongside `IsWord`. Homed here because
`Constituent.weight`/`.syl` need `Syllable.Weight`; it inherits `DecidableEq`/`map` from
`RoseTree`. -/

/-- In a prosodic node the **level is the constructor**. A σ carries its mora `weight` and
    `isHead`, and every non-root level carries `isHead` (whether it heads its parent).
    Constructor defaults match the former smart constructors, so node literals are unchanged;
    illegal nodes (a weight on a foot, a head on the ι root) are unrepresentable. -/
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

/-- Under Layeredness a σ dominates nothing, a foot a non-empty string of σs, an ω feet, ωs and
    σs, a φ ωs, and an ι φs; `Licenses a ks` says that `a` may dominate daughters labelled `ks`. -/
def Licenses : Constituent → List Constituent → Prop
  | .syl .., ks => ks = []
  | .ft _, ks => ks ≠ [] ∧ ∀ k ∈ ks, k.isSyl = true
  | .om _, ks => ∀ k ∈ ks, k.isFt = true ∨ k.isOm = true ∨ k.isSyl = true
  | .ph _, ks => ∀ k ∈ ks, k.isOm = true
  | .iota, ks => ∀ k ∈ ks, k.isPh = true

instance : ∀ (a : Constituent) (ks : List Constituent), Decidable (Licenses a ks)
  | .syl .., ks => inferInstanceAs (Decidable (ks = []))
  | .ft _, ks => inferInstanceAs (Decidable (ks ≠ [] ∧ ∀ k ∈ ks, k.isSyl = true))
  | .om _, ks =>
    inferInstanceAs (Decidable (∀ k ∈ ks, k.isFt = true ∨ k.isOm = true ∨ k.isSyl = true))
  | .ph _, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k.isOm = true))
  | .iota, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k.isPh = true))

/-- The levels are exclusive, so a foot is not a syllable. -/
theorem isSyl_eq_false_of_isFt {x : Constituent} (h : x.isFt = true) : x.isSyl = false := by
  cases x <;> simp_all [isFt, isSyl]

/-- The levels are exclusive, so a prosodic word is not a syllable. -/
theorem isSyl_eq_false_of_isOm {x : Constituent} (h : x.isOm = true) : x.isSyl = false := by
  cases x <;> simp_all [isOm, isSyl]

end Constituent

/-- A prosodic tree is an ordered rose tree labelled by `Constituent`s. Ordered children give
    No-Tangling by construction. -/
abbrev Tree := RoseTree Constituent

/-- A σ-leaf is the metrical terminal, a syllable of weight `w` with head mark `h`. -/
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
    reduce the σ-leaf `if` the reader equations carry (via `ite_eq_left ⟨ha, rfl⟩` or
    `ite_eq_right hne`) instead of `split`ting it. -/
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
