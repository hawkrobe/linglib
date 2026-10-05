module

public import Linglib.Phonology.Prosody.Foot
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Mathlib.Order.Antichain
public import Linglib.Core.Data.RoseTree.Positions

/-!
# Prosodic words (ω)

A prosodic word ω is a node of the prosodic tree (`Prosody.Tree`), and well-formedness is a
declarative property of that carrier rather than a separate inductive. `IsWord` carves out the
well-formed ω-trees as the Strict-Layer core (Selkirk 1996): an ω-node whose daughters are only
feet, recursive sub-words, or stray syllables, the inviolable Layeredness constraint. The OT
studies score raw `Tree` candidates, so theorems take `IsWord` as a hypothesis on the carrier
rather than bundling a subtype.

Exhaustivity and No-Recursion are violable OT constraints, not part of `IsWord`: a stray σ (a
free clitic) and an ω-over-ω (Itô and Mester's 2009 extended prosodic word) are both admitted,
and `parseInto` and `noRec` score them on the carrier. Headedness, that an ω dominates a foot, is
the typical case but is not presupposed: footless languages have ω directly over σ (DeLisi 2015,
per Dolatian 2020).

## Main definitions

* `IsWord` — the Layeredness predicate, a tree rooted in an ω-node and licensed by
  `Constituent.Licenses`; theorems take it as a hypothesis on the carrier
  (mathlib's `Squarefree`-style), there is no bundled subtype.
* `noRec` / `parseInto` — the violable OT constraints over the carrier (`Constraint Tree`).
* `maximalProjections` / `minimalProjections` — the topmost / bottommost ℓ-positions, `Minimal`
  and `Maximal` under dominance; `NoLevelRecursion` — the ℓ-positions form an antichain.
* `feet` / `moraCount` / `unfootedCount` — carrier folds extracting feet, morae, stray σ.
* `MinimalWord` / `MaximalWord` / `PerfectWord` — the word-size notions over the carrier.

## Main results

* `maximalProjections_eq_minimalProjections` — under transitive No-Recursion at `ℓ`, the maximal
  and minimal ℓ-projections coincide (every ℓ-node is at once topmost and bottommost).

## References

* [selkirk-1980]
* [nespor-vogel-1986]
* [liberman-prince-1977]
* [hayes-1995]
* [mccarthy-prince-1993]
* [prince-smolensky-1993]
* [selkirk-1996]
* [ito-mester-2003]
* [ito-mester-2009]
* [dolatian-2020]
* [uchihara-mendozaruiz-2021]
-/

@[expose] public section

namespace Prosody

/-! ### Prosodic OT constraints over the `Tree` carrier

The violable constraints scoring prosodic candidates are `OptimalityTheory.Constraint Tree`
values ([prince-smolensky-1993]); a grammar ranks them and scores with the OT engine
(`OptimalityTheory.Tableau.ofRanking`). They are defined on the **carrier** `Tree` (which
holds the ill-formed candidates `IsWord` rules out). List-recursion auxes
are local `where`s. -/

open OptimalityTheory Core.Order

/-- **No-Recursion** ([ito-mester-2009]) counts parent–child pairs sharing a level, an element
    parsed into the same category twice. -/
def noRec : Constraint Tree := fun t => go t where
  go : Tree → Nat
    | .node a cs => (cs.filter (fun c => Constituent.sameLevel c.value a)).length + goList cs
  goList : List Tree → Nat
    | [] => 0
    | c :: cs => go c + goList cs

/-! #### Maximal and minimal projections

The **projections** of a level `ℓ` ([ito-mester-2009]) are its extremal nodes under dominance.
The **maximal** ℓ-projections are the ℓ-nodes no ℓ-node dominates, and the **minimal** ones are
the ℓ-nodes dominating no ℓ-node. Since the root is the least position, these are the `Minimal`
and `Maximal` members of the ℓ-positions. **Transitive No-Recursion** at `ℓ`, that no ℓ-node
properly dominates another, says that the ℓ-positions form an antichain, and it collapses the
two. `noRec` scores only a direct ℓ-over-ℓ, so `ω(f(ω))`, which recurses through an
intervening foot, has `noRec = 0` while its maximal and minimal ω-projections differ. The
intonational utterance υ is the maximal ι-projection. -/

/-- The positions of `t` at the level `ℓ`. -/
abbrev levelPositions (ℓ : Constituent → Bool) (t : Tree) : Set TreePath :=
  RoseTree.positionsWhere (fun s ↦ ℓ s.value) t

/-- The maximal `ℓ`-projections of `t`, its topmost `ℓ`-nodes. -/
abbrev maximalProjections (ℓ : Constituent → Bool) (t : Tree) : Set TreePath :=
  {p | Minimal (· ∈ levelPositions ℓ t) p}

/-- The minimal `ℓ`-projections of `t`, its bottommost `ℓ`-nodes. -/
abbrev minimalProjections (ℓ : Constituent → Bool) (t : Tree) : Set TreePath :=
  {p | Maximal (· ∈ levelPositions ℓ t) p}

/-- Transitive No-Recursion at `ℓ`: no `ℓ`-node of `t` properly dominates another. -/
abbrev NoLevelRecursion (ℓ : Constituent → Bool) (t : Tree) : Prop :=
  IsAntichain (· ≤ ·) (levelPositions ℓ t)

/-- **No-Recursion collapses the projections**: under transitive No-Recursion at `ℓ`, every
`ℓ`-node is at once topmost and bottommost. -/
theorem maximalProjections_eq_minimalProjections {ℓ : Constituent → Bool} {t : Tree}
    (h : NoLevelRecursion ℓ t) : maximalProjections ℓ t = minimalProjections ℓ t := by
  ext p
  exact h.minimal_mem_iff.trans h.maximal_mem_iff.symm

/-- **Parse-into-`p`** ([ito-mester-2003]) counts σ-leaves dominated by no `p`-node. -/
def parseInto (p : Constituent → Bool) : Constraint Tree := fun t => go false t where
  go (under : Bool) : Tree → Nat
    | .node a cs =>
        let u := under || p a
        (if a.isSyl && cs.isEmpty && !u then 1 else 0) + goList u cs
  goList (under : Bool) : List Tree → Nat
    | [] => 0
    | c :: cs => go under c + goList under cs

/-- The σ-weight content of a foot node's direct σ-daughters. -/
def footContent (cs : List Tree) : List Syllable.Weight :=
  cs.filterMap fun c => match c with
    | .node a [] => a.weight?
    | _ => none

/-- The feet of a prosodic tree are the σ-weight contents of its `f`-nodes. -/
def feet : Tree → List (List Syllable.Weight) := fun t => go t where
  go : Tree → List (List Syllable.Weight)
    | .node a cs => (if a.isFt then [footContent cs] else []) ++ goList cs
  goList : List Tree → List (List Syllable.Weight)
    | [] => []
    | t :: ts => go t ++ goList ts

/-- Syllables parsed into no foot — `parseInto (·.isFt)`. -/
def unfootedCount (t : Tree) : Nat := parseInto (·.isFt) t

/-- The total mora count is the sum of the tree's σ-weights. -/
def moraCount : Tree → Nat := fun t => go t where
  go : Tree → Nat
    | .node a cs => a.weight?.getD 0 + goList cs
  goList : List Tree → Nat
    | [] => 0
    | t :: ts => go t + goList ts

/-! ### The well-formed prosodic word ω

`IsWord` is the inviolable Layeredness core ([selkirk-1996]): a tree rooted in an ω-node and
licensed by `Constituent.Licenses`. Licensing is decidable by structural recursion, so a winner
can be certified `IsWord` by `decide`. -/

/-- A well-formed prosodic word is a licensed tree rooted in an ω-node, so an ω-node dominating
    only feet, recursive ω's, and stray σ, never φ or ι. This is the inviolable **Layeredness**
    core. Headedness (a foot daughter, the minimal-word effect of [selkirk-1996]) is the typical
    case but is not presupposed, since footless languages have ω directly over σ (DeLisi 2015,
    per [dolatian-2020]) and the OT recursion candidates abstract the foot level. Exhaustivity (a
    stray σ) and Nonrecursivity (ω-over-ω) are violable OT constraints, so both are admitted
    here. -/
abbrev IsWord : Tree → Prop := IsConstituent Constituent.isOm

/-- A non-recursive word is an ω over well-formed feet and stray σ-leaves, the structural content
    of `IsWord ∧ noRec = 0`, used to read the grid off a word. -/
theorem isWord_children {a : Constituent} {cs : List Tree}
    (hw : IsWord (.node a cs)) (hr : noRec (.node a cs) = 0) :
    a.isOm = true ∧ ∀ c ∈ cs, IsFoot c ∨ (c.value.isSyl = true ∧ c.children = []) := by
  obtain ⟨ha, hl⟩ := hw
  obtain ⟨hd, rfl⟩ : ∃ b, a = .om b := by
    cases a <;> first | exact ⟨_, rfl⟩ | simp_all [Constituent.isOm]
  have hr' : (cs.filter (fun c => Constituent.sameLevel c.value (.om hd))).length = 0 := by
    have e : noRec (.node (Constituent.om hd) cs)
        = (cs.filter (fun c => Constituent.sameLevel c.value (.om hd))).length
          + noRec.goList cs := rfl
    rw [hr] at e; omega
  have hnoω : ∀ c ∈ cs, Constituent.sameLevel c.value (.om hd) = false := by
    intro c hc
    by_contra h
    rw [Bool.not_eq_false] at h
    have hmem : c ∈ cs.filter (fun c => Constituent.sameLevel c.value (.om hd)) := by
      rw [List.mem_filter]; exact ⟨hc, h⟩
    rw [List.length_eq_zero_iff] at hr'
    rw [hr'] at hmem; exact List.not_mem_nil hmem
  refine ⟨ha, fun c hc => ?_⟩
  have hcl := hl.of_mem hc
  have hlab := (RoseTree.licensed_node_iff.mp hl).1 c.value (List.mem_map_of_mem hc)
  have hsl := hnoω c hc
  rcases c with ⟨cl, ccs⟩
  simp only [RoseTree.value_node] at hsl hlab
  have hcω : cl.isOm = false := by
    cases cl <;> simp_all [Constituent.sameLevel, Constituent.isOm]
  rcases hlab with hft | hom | hsyl
  · exact Or.inl ⟨hft, hcl⟩
  · simp [hcω] at hom
  · refine Or.inr ⟨hsyl, ?_⟩
    obtain ⟨w, h', rfl⟩ : ∃ w h', cl = .syl w h' := by
      cases cl <;> simp_all [Constituent.isSyl]
    simpa [Constituent.Licenses] using (RoseTree.licensed_node_iff.mp hcl).1

/-! ### Word-size predicates -/

variable {measure : List Syllable.Weight → ℕ} {t : Tree}

/-- A minimal word ([mccarthy-prince-1993]) contains a well-formed foot (PrWd ⊇ Ft). -/
def MinimalWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  ∃ f ∈ feet t, measure f = 2
instance : Decidable (MinimalWord measure t) := by unfold MinimalWord; infer_instance

/-- A maximal word ([uchihara-mendozaruiz-2021]) has at most one well-formed foot and is
    exhaustively parsed, the upper size bound. -/
def MaximalWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  (feet t).length ≤ 1 ∧ unfootedCount t = 0 ∧ ∀ f ∈ feet t, measure f = 2
instance : Decidable (MaximalWord measure t) := by unfold MaximalWord; infer_instance

/-- The perfect prosodic word ([ito-mester-2009]) is an ω coextensive with one well-formed
    foot. -/
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
private def exFoot : Tree := .ft false [.σ 2]
private def perfectW : Tree := .om [exFoot]
private def recursiveW : Tree := .om [.σ 1, .om [exFoot]]

-- Well-formedness: a flat ω over a foot and a recursive ω are both legal words — ω-over-ω
-- is admitted (No-Recursion is violable). A φ-node inside an ω violates Layeredness.
example : IsWord perfectW := by decide
example : IsWord recursiveW := by decide
example : ¬ IsWord (.om [.node .ph []] : Tree) := by decide

-- `noRec` reads the No-Recursion cost off the carrier: the recursive word scores
-- one ω-over-ω, the flat one zero.
example : noRec recursiveW = 1 := by decide
example : noRec perfectW = 0 := by decide

-- The ω-over-ω word has the outer ω as its sole maximal projection and the inner ω as its
-- sole minimal projection; the perfect (flat) word is both at once.
example : recursiveW.vertices.filter (⟨·⟩ ∈ maximalProjections (·.isOm) recursiveW) = [[]] := by
  decide
example : recursiveW.vertices.filter (⟨·⟩ ∈ minimalProjections (·.isOm) recursiveW) = [[1]] := by
  decide
example : perfectW.vertices.filter (⟨·⟩ ∈ maximalProjections (·.isOm) perfectW) = [[]] := by
  decide
example : perfectW.vertices.filter (⟨·⟩ ∈ minimalProjections (·.isOm) perfectW) = [[]] := by
  decide

end Prosody
