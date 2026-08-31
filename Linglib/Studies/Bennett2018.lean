import Linglib.Phonology.Prosody.Word
import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Bennett 2018: recursive prosodic words in Kaqchikel

This file formalizes Bennett's argument that the prosodic word recurses in Kaqchikel.
Prefixes fall into two prosodic classes: low-attaching prefixes are parsed into their stem's
prosodic word, `[ω Pref Stem]`, and high-attaching prefixes outside it, `[ω Pref [ω Stem]]`.
Two diagnostics converge on the split — an onsetless syllable at the left edge of an ω
receives epenthetic [ʔ], so a vowel-initial stem keeps its glottal stop after a high prefix
but loses it after a low one, and the OCP that fuses adjacent identical consonants is inert
across an ω boundary, so degemination applies across a low-prefix juncture but not a high
one. Stacked high prefixes each receive their own glottal stop, which a non-recursive
prosodic hierarchy could only reproduce by positing one new prosodic category per prefix.
The recursion follows from a lexical subcategorization frame on the high prefixes, ranked
above the constraint that every prosodic word correspond to a morphological word.

## Main definitions

* `flat`, `nested`: the two parses of a prefix sequence over a stem.
* `omegaInitial`, `omegaSeparates`: the structural side of the two diagnostics — the
  ω-initial leaves, and whether an ω boundary separates two leaves.
* `matchWord`, `matchOmega`, `subCat`: `Match (X⁰, ω)`, `Match (ω, X⁰)`, and the
  subcategorization frame, as constraints on prosodic trees.

## Main results

* `omegaInitial_nested`, `omegaInitial_flat`: every stacked high prefix is ω-initial in the
  recursive parse; only the first prefix is in the flat parse.
* `high_prefix_recursive`, `low_prefix_flat`: under `SubCat ≫ Match (ω, X⁰)` a
  high-attaching prefix is parsed recursively and a low-attaching one flat.

## References

* [bennett-2018]
* [selkirk-2011]: the Match constraints.
* [inkelas-1990]: prosodic subcategorization.
* [nespor-vogel-1986]: the Strict Layer Hypothesis and the Clitic Group.
-/

namespace Bennett2018

open Prosody Constraints OptimalityTheory

/-! ### Parses -/

/-- The flat parse `[ω Pref₁ … Prefₙ Stem]`, the structure of low-attaching prefixes (4a). -/
def flat (prefs : List Constituent) (stem : Constituent) : Tree :=
  .om ((prefs ++ [stem]).map RoseTree.leaf)

/-- The recursive parse `[ω Pref₁ [ω … [ω Prefₙ [ω Stem]]]]`, one ω per high-attaching
prefix ((19a), (23)). -/
def nested : List Constituent → Constituent → Tree
  | [], stem => .om [.leaf stem]
  | p :: ps, stem => .om [.leaf p, nested ps stem]

/-- A light prefix syllable. -/
def pref : Constituent := .syl 1

/-- A heavy stem syllable. -/
def stem : Constituent := .syl 2

/-- Each high-attaching prefix as an independent ω under a higher category (25a), the
carrier's φ standing in for a Clitic Group. -/
def phrasal : Tree := .ph [.om [.leaf pref], .om [.leaf stem]]

/-! ### Diagnostics -/

/-- The leftmost leaf of a tree. -/
def leftmost : Tree → Constituent := fun t => go t where
  go : Tree → Constituent
    | .node a cs => goList a cs
  goList : Constituent → List Tree → Constituent
    | a, [] => a
    | _, c :: _ => go c

/-- The ω-initial leaves, one per ω node: the left edge of an ω is where an onsetless
syllable receives epenthetic [ʔ], the ω being the domain of syllabification. -/
def omegaInitial : Tree → List Constituent := fun t => go t where
  go : Tree → List Constituent
    | .node a cs => (if a.isOm then [leftmost (.node a cs)] else []) ++ goList cs
  goList : List Tree → List Constituent
    | [] => []
    | c :: cs => go c ++ goList cs

/-- Whether `x` occurs as a leaf. -/
def containsLeaf (x : Constituent) : Tree → Bool := fun t => go t where
  go : Tree → Bool
    | .node a [] => a == x
    | .node _ (c :: cs) => go c || goList cs
  goList : List Tree → Bool
    | [] => false
    | c :: cs => go c || goList cs

/-- Whether some ω dominates the leaf `b` but not the leaf `a`: an ω boundary between them,
across which `OCP(X)ω` (18) is inert. -/
def omegaSeparates (a b : Constituent) : Tree → Bool := fun t => go t where
  go : Tree → Bool
    | .node c cs =>
      (c.isOm && containsLeaf b (.node c cs) && !containsLeaf a (.node c cs)) || goList cs
  goList : List Tree → Bool
    | [] => false
    | c :: cs => go c || goList cs

theorem omegaInitial_om (cs : List Tree) :
    omegaInitial (.om cs) = leftmost (.om cs) :: omegaInitial.goList cs := rfl

theorem omegaInitial_goList_cons (c : Tree) (cs : List Tree) :
    omegaInitial.goList (c :: cs) = omegaInitial c ++ omegaInitial.goList cs := rfl

theorem omegaInitial_goList_nil : omegaInitial.goList [] = [] := rfl

theorem omegaInitial_leaf {c : Constituent} (h : c.isOm = false) :
    omegaInitial (.leaf c) = [] := by
  simp [omegaInitial, omegaInitial.go, omegaInitial.goList, RoseTree.leaf, h]

theorem omegaInitial_goList_leaves {cs : List Constituent} (h : ∀ c ∈ cs, c.isOm = false) :
    omegaInitial.goList (cs.map RoseTree.leaf) = [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.map_cons, omegaInitial_goList_cons, omegaInitial_leaf (h c (List.mem_cons_self ..)),
      ih fun d hd => h d (List.mem_cons_of_mem c hd)]
    rfl

/-- In the recursive parse every stacked prefix and the stem is ω-initial: `n` high prefixes
over a vowel-initial stem give `n + 1` loci of [ʔ]-insertion ((21)–(23)). -/
theorem omegaInitial_nested {ps : List Constituent} {s : Constituent}
    (hps : ∀ p ∈ ps, p.isOm = false) (hs : s.isOm = false) :
    omegaInitial (nested ps s) = ps ++ [s] := by
  induction ps with
  | nil =>
    rw [nested, omegaInitial_om, omegaInitial_goList_cons, omegaInitial_leaf hs]
    rfl
  | cons p ps ih =>
    rw [nested, omegaInitial_om, omegaInitial_goList_cons, omegaInitial_goList_cons,
      omegaInitial_leaf (hps p (List.mem_cons_self ..)),
      ih fun q hq => hps q (List.mem_cons_of_mem p hq), omegaInitial_goList_nil,
      List.append_nil, List.nil_append]
    rfl

/-- In the flat parse only the first prefix is ω-initial: one locus of [ʔ]-insertion. -/
theorem omegaInitial_flat {p : Constituent} {ps : List Constituent} {s : Constituent}
    (hp : p.isOm = false) (hps : ∀ q ∈ ps, q.isOm = false) (hs : s.isOm = false) :
    omegaInitial (flat (p :: ps) s) = [p] := by
  rw [flat, List.cons_append, List.map_cons, omegaInitial_om, omegaInitial_goList_cons,
    omegaInitial_leaf hp, omegaInitial_goList_leaves]
  · rfl
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hps c hc
    · exact List.mem_singleton.1 hc ▸ hs

-- (22)–(23): three high prefixes and a vowel-initial root, four glottal stops.
example : omegaInitial (nested [pref, pref, pref] stem) = [pref, pref, pref, stem] := by decide

-- (15) vs (16)–(17): no ω boundary separates a low prefix from its stem, so `OCP(X)ω`
-- degeminates across the juncture; an ω boundary separates a high prefix from its stem.
example : omegaSeparates pref stem (flat [pref] stem) = false := by decide
example : omegaSeparates pref stem (nested [pref] stem) = true := by decide

/-! ### Constraints and the ranking -/

/-- `Match (X⁰, ω)` (13) for a single morphological word: a violation unless one ω dominates
all of its segments, i.e. unless the root is an ω. Undominated in Kaqchikel. -/
def matchWord : Constraint Tree := fun t => if t.value.isOm then 0 else 1

/-- The number of ω nodes. -/
def omegaCount : Tree → ℕ := fun t => go t where
  go : Tree → ℕ
    | .node a cs => (if a.isOm then 1 else 0) + goList cs
  goList : List Tree → ℕ
    | [] => 0
    | c :: cs => go c + goList cs

/-- `Match (ω, X⁰)` for a single morphological word: every ω other than a root ω fails to
correspond to a morphological word. -/
def matchOmega : Constraint Tree := fun t => omegaCount t - if t.value.isOm then 1 else 0

/-- Whether the leaf `p` is the left sister of an ω inside an ω: the subcategorization frame
`[ω p [ω ]]` (30) is realised. -/
def hasFrame (p : Constituent) : Tree → Bool := fun t => go t where
  go : Tree → Bool
    | .node a cs =>
      (a.isOm && match cs with
        | [.node q [], .node b _] => q == p && b.isOm
        | _ => false) || goList cs
  goList : List Tree → Bool
    | [] => false
    | c :: cs => go c || goList cs

/-- `SubCat`: one violation per high-attaching prefix whose frame (30) is not realised. -/
def subCat (prefs : List Constituent) : Constraint Tree := fun t =>
  (prefs.filter fun p => !hasFrame p t).length

/-- A high-attaching prefix is parsed recursively: under `SubCat ≫ Match (ω, X⁰)`, with
`Match (X⁰, ω)` undominated, the recursive parse is the unique optimum. -/
theorem high_prefix_recursive :
    (Tableau.ofRanking [nested [pref] stem, flat [pref] stem, phrasal]
      [matchWord, subCat [pref], matchOmega]).optimal = {nested [pref] stem} := by
  decide

/-- A low-attaching prefix, carrying no frame, is parsed flat: `Match (ω, X⁰)` alone rules
out the extra ω. -/
theorem low_prefix_flat :
    (Tableau.ofRanking [nested [pref] stem, flat [pref] stem, phrasal]
      [matchWord, matchOmega]).optimal = {flat [pref] stem} := by
  decide

-- The recursive optimum is a well-formed prosodic word: ω over ω is admitted by
-- Layeredness; only the violable `Match (ω, X⁰)` penalises it.
example : IsWord (nested [pref] stem) := by decide

end Bennett2018
