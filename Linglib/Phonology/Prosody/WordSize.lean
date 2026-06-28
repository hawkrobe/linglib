import Linglib.Phonology.Prosody.Tree
import Linglib.Phonology.Prosody.Foot

/-!
# Prosodic word size: minimality, maximality, and the perfect word

Size restrictions on the prosodic word, stated over the single carrier
`Prosody.Tree` (`Phonology/Prosody/Tree.lean`) and reusing the *carrier-agnostic*
foot kernel from `Foot.lean` (`isWellFormedFoot`/`footMorae`, defined over
weight-lists). The feet of a tree are the σ-weight contents of its `f`-labelled
nodes, so the size theory composes with the recursive prosodic representation
rather than duplicating a flat foot parse.

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
/-- Auxiliary for `unfootedCount`, threading whether we are already inside a foot. -/
def unfootedAux (underFoot : Bool) : Tree → Nat
  | .node a cs =>
      let nowFoot := underFoot || decide (a.level = .f)
      (if decide (a.level = .σ) && cs.isEmpty && !nowFoot then 1 else 0)
        + unfootedAuxList nowFoot cs
/-- Auxiliary over a list of subtrees. -/
def unfootedAuxList (underFoot : Bool) : List Tree → Nat
  | []      => 0
  | t :: ts => unfootedAux underFoot t + unfootedAuxList underFoot ts
end

/-- Syllables parsed into no foot (Parse-μ violations at the σ level). -/
def unfootedCount (t : Tree) : Nat := unfootedAux false t

/-! ### Size predicates -/

variable {ft : FootType} {t : Tree}

/-- Minimal word ([mccarthy-prince-1993]): the tree contains a well-formed foot —
    the smallest licit ω properly contains a foot (PrWd ⊇ Ft). -/
def MinimalWord (ft : FootType) (t : Tree) : Prop :=
  ∃ f ∈ feet t, isWellFormedFoot ft f

instance : Decidable (MinimalWord ft t) := by unfold MinimalWord; infer_instance

/-- Maximal word ([uchihara-mendozaruiz-2021]): no larger than one well-formed
    foot, exhaustively parsed — the upper size bound. -/
def MaximalWord (ft : FootType) (t : Tree) : Prop :=
  (feet t).length ≤ 1 ∧ unfootedCount t = 0 ∧ ∀ f ∈ feet t, isWellFormedFoot ft f

instance : Decidable (MaximalWord ft t) := by unfold MaximalWord; infer_instance

/-- The perfect prosodic word (Itô & Mester): ω coextensive with one well-formed
    foot — exactly one foot, well-formed, nothing unfooted. -/
def PerfectWord (ft : FootType) (t : Tree) : Prop :=
  (feet t).length = 1 ∧ (∀ f ∈ feet t, isWellFormedFoot ft f) ∧ unfootedCount t = 0

instance : Decidable (PerfectWord ft t) := by unfold PerfectWord; infer_instance

/-! ### Verification theorems -/

/-- A perfect word is minimal. -/
theorem PerfectWord.minimal (h : PerfectWord ft t) : MinimalWord ft t := by
  obtain ⟨hlen, hwf, _⟩ := h
  rcases hfeet : feet t with _ | ⟨f, fs⟩
  · rw [hfeet] at hlen; simp at hlen
  · exact ⟨f, by rw [hfeet]; simp, hwf f (by rw [hfeet]; simp)⟩

/-- A perfect word is maximal. -/
theorem PerfectWord.maximal (h : PerfectWord ft t) : MaximalWord ft t := by
  obtain ⟨hlen, hwf, hu⟩ := h
  exact ⟨hlen.le, hu, hwf⟩

/-- The perfect word is exactly minimal-and-maximal: a word that both contains a
    foot and is bounded by one is coextensive with that foot. -/
theorem perfectWord_iff_minimal_and_maximal :
    PerfectWord ft t ↔ MinimalWord ft t ∧ MaximalWord ft t := by
  refine ⟨fun h => ⟨h.minimal, h.maximal⟩, ?_⟩
  rintro ⟨⟨f, hf, _⟩, hle, hu, hwf⟩
  have h1 : 0 < (feet t).length := List.length_pos_of_mem hf
  exact ⟨le_antisymm hle (by omega), hwf, hu⟩

/-- Typological direction ([uchihara-mendozaruiz-2021]): for a footed word,
    maximality entails minimality (the converse fails — a minimal word may exceed
    one foot). -/
theorem MaximalWord.minimal (hne : feet t ≠ []) (h : MaximalWord ft t) :
    MinimalWord ft t := by
  obtain ⟨_, _, hwf⟩ := h
  rcases hfeet : feet t with _ | ⟨f, fs⟩
  · exact absurd hfeet hne
  · exact ⟨f, by rw [hfeet]; simp, hwf f (by rw [hfeet]; simp)⟩

end Prosody
