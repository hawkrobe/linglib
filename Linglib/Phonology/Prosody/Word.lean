import Linglib.Phonology.Prosody.Foot
import Linglib.Phonology.Constraints.Defs

/-!
# Prosodic words (ω)
[selkirk-1980] [nespor-vogel-1986] [liberman-prince-1977] [hayes-1995] [ito-mester-2009]
[mccarthy-prince-1993] [selkirk-1996] [ito-mester-2003] [prince-smolensky-1993] [dolatian-2020]

A prosodic word ω is a node of the prosodic tree (`Prosody.Tree`), and well-formedness is
a *declarative* property of that carrier rather than a separate inductive. `IsWord` carves
out the well-formed ω-trees as the **Strict-Layer** core ([selkirk-1996]): an ω-node whose
daughters are only feet, recursive sub-words (ω-over-ω), or stray (unfooted) syllables — the
inviolable **Layeredness** constraint (no φ/ι/AP inside an ω). The library's OT studies
score raw `Tree` candidates, so `Word := {t : Tree // IsWord t}` is exactly the carrier
restricted to the legal recursive words.

`Exhaustivity` and `No-Recursion` are *violable* OT constraints, not part of `IsWord`: a
stray σ (a free clitic) and an ω-over-ω (the extended prosodic word of [ito-mester-2009])
are both admitted. They are scored on the carrier by `parseInto`/`noRec` and ranked by a
grammar — that is where they belong. Headedness (that an ω dominates a foot, the minimal-word
effect of [selkirk-1996]) is the typical case but is *not* presupposed: footless languages
have ω directly over σ (DeLisi 2015, per [dolatian-2020]), and the OT recursion candidates
here abstract the foot level. Prominence-head marking is likewise a refinement, not enforced.

## Main definitions

* `isWordTree` — the structural `Bool` Layeredness checker (decide-reducible; the foot arm
  reuses `Foot.isFootTree`).
* `IsWord` / `Word` — the Layeredness predicate and the carrier subtype it cuts out.
* `Word.recursionCount` — the `No-Recursion` violation count, read off the carrier (`noRec`).
* `noRec` / `parseInto` — the violable OT constraints over the carrier (`Constraint Tree`).
* `feet` / `moraCount` / `unfootedCount` — carrier folds extracting feet, morae, stray σ.
* `MinimalWord` / `MaximalWord` / `PerfectWord` — the word-size notions over the carrier.
-/

namespace Prosody

open Features.Prosody

/-- The ω node label for the prosodic tree (`Prosody.Tree`) — the ω-level arm of
    `Prosody.Constituent`. -/
abbrev Constituent.om : Constituent := { level := .ω }
/-- The φ node label. Interim home: the φ object `Prosody.Phrase` lands in a later PR and
    will re-home this; for now φ-candidates ([ito-mester-2009]) need it here. -/
abbrev Constituent.ph : Constituent := { level := .φ }

/-! ### Prosodic OT constraints over the `Tree` carrier

The violable constraints scoring prosodic candidates are `Constraints.Constraint Tree`
values ([prince-smolensky-1993]); a grammar ranks them and scores with the OT engine
(`OptimalityTheory.Tableau.ofRanking`). They are defined on the **carrier** `Tree` (which
holds the ill-formed candidates a well-formed `Word` can't represent). List-recursion auxes
are local `where`s. -/

open Constraints

/-- **No-Recursion** ([ito-mester-2009]): parent–child pairs sharing a level (an element
    parsed into the same category twice). -/
def noRec : Constraint Tree := fun t => go t where
  go : Tree → Nat
    | .node a cs => (cs.filter (fun c => decide (c.label.level = a.level))).length + goList cs
  goList : List Tree → Nat
    | [] => 0
    | c :: cs => go c + goList cs

/-- **Parse-into-`lvl`** ([ito-mester-2003]): σ-leaves dominated by no `lvl`-node. -/
def parseInto (lvl : ProsodicLevel) : Constraint Tree := fun t => go false t where
  go (under : Bool) : Tree → Nat
    | .node a cs =>
        let u := under || decide (a.level = lvl)
        (if decide (a.level = .σ) && cs.isEmpty && !u then 1 else 0) + goList u cs
  goList (under : Bool) : List Tree → Nat
    | [] => 0
    | c :: cs => go under c + goList under cs

/-- The σ-weight content of a foot node's direct σ-daughters. -/
private def footContent (cs : List Tree) : List Syllable.Weight :=
  cs.filterMap fun c => match c with
    | .node a [] => if a.level = .σ then some a.weight else none
    | _ => none

/-- The feet of a prosodic tree: the σ-weight content of every `f`-node. -/
def feet : Tree → List (List Syllable.Weight) := fun t => go t where
  go : Tree → List (List Syllable.Weight)
    | .node a cs => (if a.level = .f then [footContent cs] else []) ++ goList cs
  goList : List Tree → List (List Syllable.Weight)
    | [] => []
    | t :: ts => go t ++ goList ts

/-- Syllables parsed into no foot — `parseInto .f`. -/
def unfootedCount (t : Tree) : Nat := parseInto .f t

/-- Total mora count: the sum of the tree's σ-weights. -/
def moraCount : Tree → Nat := fun t => go t where
  go : Tree → Nat
    | .node a cs => (if a.level = .σ then a.weight else 0) + goList cs
  goList : List Tree → Nat
    | [] => 0
    | t :: ts => go t + goList ts

/-! ### The well-formed prosodic word ω

`isWordTree` is the structural `Bool` realization of the inviolable Layeredness core
([selkirk-1996]); `IsWord` is the declarative predicate it backs, and `Word` the carrier
subtype. Both checkers mirror the `go`/`goList` structural recursion of `noRec`, so they
are `decide`-reducible — a winner can be certified `IsWord by decide`. -/

/-- The structural Layeredness checker: an ω-node every daughter of which is a well-formed
    foot (`isFootTree`, in `Foot`), a recursive ω (the ω-over-ω arm), or a stray σ-leaf. -/
def isWordTree : Tree → Bool := fun t => go t where
  go : Tree → Bool
    | .node a cs => decide (a.level = .ω) && goList cs
  goList : List Tree → Bool
    | [] => true
    | c :: cs =>
        (isFootTree c || go c || (decide (c.label.level = .σ) && c.children.isEmpty))
          && goList cs

/-- A well-formed prosodic word: an ω-node dominating only feet, recursive ω's, and stray σ
    — never φ/ι. This is the inviolable **Layeredness** core. Headedness (a foot daughter —
    the minimal-word effect, [selkirk-1996]) is the typical case but is *not* presupposed:
    footless languages have ω directly over σ (DeLisi 2015, per [dolatian-2020]), and the OT
    recursion candidates abstract the foot level. Exhaustivity (a stray σ) and Nonrecursivity
    (ω-over-ω) are violable OT constraints, so both are admitted here. -/
def IsWord (t : Tree) : Prop := isWordTree t

instance (t : Tree) : Decidable (IsWord t) :=
  inferInstanceAs (Decidable (isWordTree t = true))

/-- A well-formed prosodic word: the prosodic-tree carrier restricted to the legal
    recursive ω-trees (`IsWord`). -/
abbrev Word := {t : Tree // IsWord t}

namespace Word

/-- The `No-Recursion` violation count of a word ([ito-mester-2009]): its ω-over-ω depth,
    the carrier fold `noRec` read off the underlying tree. -/
def recursionCount (w : Word) : ℕ := noRec w.val

end Word

/-! ### Word-size predicates -/

variable {measure : List Syllable.Weight → ℕ} {t : Tree}

/-- Minimal word ([mccarthy-prince-1993]): contains a well-formed foot (PrWd ⊇ Ft). -/
def MinimalWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  ∃ f ∈ feet t, measure f = 2
instance : Decidable (MinimalWord measure t) := by unfold MinimalWord; infer_instance

/-- Maximal word ([uchihara-mendozaruiz-2021]): ≤ one well-formed foot, exhaustively
    parsed — the upper size bound. -/
def MaximalWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  (feet t).length ≤ 1 ∧ unfootedCount t = 0 ∧ ∀ f ∈ feet t, measure f = 2
instance : Decidable (MaximalWord measure t) := by unfold MaximalWord; infer_instance

/-- The perfect prosodic word ([ito-mester-2009]): ω coextensive with one well-formed foot. -/
def PerfectWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  (feet t).length = 1 ∧ (∀ f ∈ feet t, measure f = 2) ∧ unfootedCount t = 0
instance : Decidable (PerfectWord measure t) := by unfold PerfectWord; infer_instance

/-- A perfect word is minimal. -/
theorem PerfectWord.minimal (h : PerfectWord measure t) : MinimalWord measure t := by
  obtain ⟨hlen, hwf, _⟩ := h
  rcases hfeet : feet t with _ | ⟨f, fs⟩
  · rw [hfeet] at hlen; simp at hlen
  · exact ⟨f, by rw [hfeet]; simp, hwf f (by rw [hfeet]; simp)⟩

/-- A perfect word is maximal. -/
theorem PerfectWord.maximal (h : PerfectWord measure t) : MaximalWord measure t := by
  obtain ⟨hlen, hwf, hu⟩ := h
  exact ⟨hlen.le, hu, hwf⟩

/-- The perfect word is exactly minimal-and-maximal. -/
theorem perfectWord_iff_minimal_and_maximal :
    PerfectWord measure t ↔ MinimalWord measure t ∧ MaximalWord measure t := by
  refine ⟨fun h => ⟨h.minimal, h.maximal⟩, ?_⟩
  rintro ⟨⟨f, hf, _⟩, hle, hu, hwf⟩
  have h1 : 0 < (feet t).length := List.length_pos_of_mem hf
  exact ⟨le_antisymm hle (by omega), hwf, hu⟩

/-- Maximality entails minimality for a footed word ([uchihara-mendozaruiz-2021]). -/
theorem MaximalWord.minimal (hne : feet t ≠ []) (h : MaximalWord measure t) :
    MinimalWord measure t := by
  obtain ⟨_, _, hwf⟩ := h
  rcases hfeet : feet t with _ | ⟨f, fs⟩
  · exact absurd hfeet hne
  · exact ⟨f, by rw [hfeet]; simp, hwf f (by rw [hfeet]; simp)⟩

/-! ### Worked examples -/

-- A bimoraic foot, the perfect word over it, and a recursive (ω-over-ω) word.
private def exFoot : Tree := .node .ft [.node (.syl 2) []]
private def perfectW : Tree := .node .om [exFoot]
private def recursiveW : Tree := .node .om [.node (.syl 1) [], .node .om [exFoot]]

-- Well-formedness: a flat ω over a foot and a recursive ω are both legal words — ω-over-ω
-- is admitted (No-Recursion is violable). A φ-node inside an ω violates Layeredness.
example : IsWord perfectW := by decide
example : IsWord recursiveW := by decide
example : ¬ IsWord (.node .om [.node .ph []] : Tree) := by decide

-- `recursionCount` reads the No-Recursion cost off the carrier: the recursive word scores
-- one ω-over-ω, the flat one zero.
example : Word.recursionCount ⟨recursiveW, by decide⟩ = 1 := by decide
example : Word.recursionCount ⟨perfectW, by decide⟩ = 0 := by decide

end Prosody
