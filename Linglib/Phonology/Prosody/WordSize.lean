import Linglib.Phonology.Prosody.Tree
import Linglib.Phonology.Prosody.Foot

/-!
# Prosodic word size: minimality, maximality, and the perfect word

Size restrictions on the prosodic word, stated over the single carrier
`Prosody.Tree` (`Phonology/Prosody/Tree.lean`). The licit-foot test is a
`measure : List Syllable.Weight → ℕ` parameter (`measure f = 2` = well-formed;
callers pass `footMorae` for moraic or `List.length` for syllabic feet) — the
quantity axis, decoupled from headedness. The feet of a tree are the σ-weight
contents of its `f`-labelled nodes, so the size theory composes with the recursive
prosodic representation rather than duplicating a flat foot parse.

The three notions form a `≤`-chain: a *minimal* word contains a foot, a *maximal*
one is bounded by a foot, a *perfect* one is exactly a foot (Itô & Mester's
perfect prosodic word, ω coextensive with f). The reductionist result
([mccarthy-prince-1993], [uchihara-mendozaruiz-2021]) is that one constraint set
(`FtBin`, `AllFeetRight`, `Parse`) derives *both* bounds, with the typological
consequence that maximality entails minimality but not conversely.

## Main definitions

* `Prosody.feet` — the σ-weight content of each `f`-node (the tree's feet).
* `Prosody.unfootedCount` — syllables parsed into no foot.
* `Prosody.MinimalWord` / `MaximalWord` / `PerfectWord` — the size predicates.

## Implementation notes

Size predicates are theory-neutral structural facts (no OT import); the OT
derivation that the bimoraic foot is the optimum lives in the consuming study
(`Studies/Uchihara2021.lean`), composing the foot measures with
`Core.Optimization`'s `argMinSet`. `feet`/`unfootedCount` use structural mutual
recursion (mirroring `Planar.weight`), so the predicates reduce under `decide`.

## References

[mccarthy-prince-1993] [uchihara-mendozaruiz-2021]
-/

namespace Prosody

open RootedTree Features.Prosody

/-! ### Feet of a prosodic tree -/

/-- The σ-weight content of a foot node's direct syllable daughters. -/
def footContent (cs : List Tree) : List Syllable.Weight :=
  cs.filterMap fun c => match c with
    | .node a [] => if a.level = .σ then some a.weight else none
    | _          => none

mutual
/-- The feet of a prosodic tree: the syllable-weight content of every
    `f`-labelled node. -/
def feet : Tree → List (List Syllable.Weight)
  | .node a cs => (if a.level = .f then [footContent cs] else []) ++ feetList cs
/-- Auxiliary: feet across a list of subtrees. -/
def feetList : List Tree → List (List Syllable.Weight)
  | []      => []
  | t :: ts => feet t ++ feetList ts
end

mutual
/-- Auxiliary for `parseIntoViol`, threading whether we are already under an
    `lvl`-node. -/
def parseIntoAux (lvl : ProsodicLevel) (under : Bool) : Tree → Nat
  | .node a cs =>
      let nowUnder := under || decide (a.level = lvl)
      (if decide (a.level = .σ) && cs.isEmpty && !nowUnder then 1 else 0)
        + parseIntoAuxList lvl nowUnder cs
/-- Auxiliary over a list of subtrees. -/
def parseIntoAuxList (lvl : ProsodicLevel) (under : Bool) : List Tree → Nat
  | []      => 0
  | t :: ts => parseIntoAux lvl under t + parseIntoAuxList lvl under ts
end

/-- Parse-into-`lvl` violations ([ito-mester-2003]): syllables dominated by no
    `lvl`-node. -/
def parseIntoViol (lvl : ProsodicLevel) (t : Tree) : Nat := parseIntoAux lvl false t

/-- Syllables parsed into no foot (Parse-μ at the σ level) — `parseIntoViol .f`. -/
def unfootedCount (t : Tree) : Nat := parseIntoViol .f t

mutual
/-- Total mora count of a tree: the sum of its syllables' weights. -/
def moraCount : Tree → Nat
  | .node a cs => (if a.level = .σ then a.weight else 0) + moraCountList cs
/-- Auxiliary over a list of subtrees. -/
def moraCountList : List Tree → Nat
  | []      => 0
  | t :: ts => moraCount t + moraCountList ts
end

/-! ### Size predicates -/

variable {measure : List Syllable.Weight → ℕ} {t : Tree}

/-- Minimal word ([mccarthy-prince-1993]): the tree contains a well-formed foot —
    the smallest licit ω properly contains a foot (PrWd ⊇ Ft). -/
def MinimalWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  ∃ f ∈ feet t, measure f = 2

instance : Decidable (MinimalWord measure t) := by unfold MinimalWord; infer_instance

/-- Maximal word ([uchihara-mendozaruiz-2021]): no larger than one well-formed
    foot, exhaustively parsed — the upper size bound. -/
def MaximalWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  (feet t).length ≤ 1 ∧ unfootedCount t = 0 ∧ ∀ f ∈ feet t, measure f = 2

instance : Decidable (MaximalWord measure t) := by unfold MaximalWord; infer_instance

/-- The perfect prosodic word (Itô & Mester): ω coextensive with one well-formed
    foot — exactly one foot, well-formed, nothing unfooted. -/
def PerfectWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  (feet t).length = 1 ∧ (∀ f ∈ feet t, measure f = 2) ∧ unfootedCount t = 0

instance : Decidable (PerfectWord measure t) := by unfold PerfectWord; infer_instance

/-! ### Verification theorems -/

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

/-- The perfect word is exactly minimal-and-maximal: a word that both contains a
    foot and is bounded by one is coextensive with that foot. -/
theorem perfectWord_iff_minimal_and_maximal :
    PerfectWord measure t ↔ MinimalWord measure t ∧ MaximalWord measure t := by
  refine ⟨fun h => ⟨h.minimal, h.maximal⟩, ?_⟩
  rintro ⟨⟨f, hf, _⟩, hle, hu, hwf⟩
  have h1 : 0 < (feet t).length := List.length_pos_of_mem hf
  exact ⟨le_antisymm hle (by omega), hwf, hu⟩

/-- Typological direction ([uchihara-mendozaruiz-2021]): for a footed word,
    maximality entails minimality (the converse fails — a minimal word may exceed
    one foot). -/
theorem MaximalWord.minimal (hne : feet t ≠ []) (h : MaximalWord measure t) :
    MinimalWord measure t := by
  obtain ⟨_, _, hwf⟩ := h
  rcases hfeet : feet t with _ | ⟨f, fs⟩
  · exact absurd hfeet hne
  · exact ⟨f, by rw [hfeet]; simp, hwf f (by rw [hfeet]; simp)⟩

end Prosody
