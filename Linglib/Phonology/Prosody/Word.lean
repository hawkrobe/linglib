import Linglib.Phonology.Prosody.Foot
import Linglib.Phonology.Constraints.Defs
import Linglib.Core.Order.Branching

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
* `maximalProjections` / `minimalProjections` / `IsMinimalProj` — the topmost / bottommost
  ℓ-nodes of the carrier, and the intrinsic minimal-projection predicate.
* `feet` / `moraCount` / `unfootedCount` — carrier folds extracting feet, morae, stray σ.
* `MinimalWord` / `MaximalWord` / `PerfectWord` — the word-size notions over the carrier.

## Main results

* `noLevelRec_imp_max_eq_min` — under transitive No-Recursion at `ℓ`, the maximal and
  minimal ℓ-projections coincide (every ℓ-node is at once topmost and bottommost).
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

/-! #### Maximal and minimal projections

The **projections** of a level `ℓ` ([ito-mester-2009]) are the same family of carrier folds
as `noRec` — `noRec` looks at same-level *parent–child* pairs, the projections at the
*extremal* same-level nodes. The **maximal** ℓ-projections are the topmost ℓ-nodes (no
ℓ-ancestor), read off by an `under`-flag fold (cf. `parseInto`) that prunes a subtree once
the first ℓ is hit; the **minimal** ℓ-projections are the bottommost ℓ-nodes (no
ℓ-descendant). The asymmetry is intentional: maximality is *context-relative* (membership in
`maximalProjections ℓ root`), whereas minimality is *intrinsic* to a node (`IsMinimalProj`),
so only the latter carries a one-argument predicate. The intonational utterance υ is just the
maximal ι-projection. `List` (not `Finset`) keeps the duplicate-position counts that
Match-style correspondence ([selkirk-1996]) reads. -/

/-- The **maximal ℓ-projections** of `t`: the topmost ℓ-nodes (those with no ℓ-ancestor),
    in tree order. A top-down `under`-flag fold (cf. `parseInto`) pruning a subtree once the
    first ℓ is hit. -/
def maximalProjections (ℓ : ProsodicLevel) (t : Tree) : List Tree := go false t where
  go (under : Bool) : Tree → List Tree
    | .node a cs =>
        if !under && decide (a.level = ℓ) then [.node a cs]
        else goList (under || decide (a.level = ℓ)) cs
  goList (under : Bool) : List Tree → List Tree
    | []      => []
    | c :: cs => go under c ++ goList under cs

/-- `ℓ` occurs somewhere in `t` (the root included). -/
def anyAtLevel (ℓ : ProsodicLevel) : Tree → Bool := go where
  go : Tree → Bool
    | .node a cs => decide (a.level = ℓ) || goList cs
  goList : List Tree → Bool
    | []      => false
    | c :: cs => go c || goList cs

/-- The intrinsic minimal-ℓ test: an ℓ-node no proper descendant of which is ℓ. -/
def isMinimalProj (ℓ : ProsodicLevel) : Tree → Bool
  | .node a cs => decide (a.level = ℓ) && !(cs.any (anyAtLevel ℓ))

/-- The **minimal ℓ-projections** of `t`: the bottommost ℓ-nodes (those with no
    ℓ-descendant), in tree order. -/
def minimalProjections (ℓ : ProsodicLevel) (t : Tree) : List Tree := go t where
  go : Tree → List Tree
    | .node a cs => (if isMinimalProj ℓ (.node a cs) then [.node a cs] else []) ++ goList cs
  goList : List Tree → List Tree
    | []      => []
    | c :: cs => go c ++ goList cs

/-- A **minimal ℓ-projection**: an ℓ-node none of whose proper descendants is ℓ — the
    intrinsic, context-free dual of (context-relative) maximality. -/
def IsMinimalProj (ℓ : ProsodicLevel) (t : Tree) : Prop := isMinimalProj ℓ t

instance (ℓ : ProsodicLevel) (t : Tree) : Decidable (IsMinimalProj ℓ t) :=
  inferInstanceAs (Decidable (isMinimalProj ℓ t = true))

/-- **Transitive No-Recursion at `ℓ`**: no ℓ-node properly dominates an ℓ-node — every
    ℓ-node is a minimal projection. This — not `noRec` — is what collapses the maximal and
    minimal ℓ-projections (`noLevelRec_imp_max_eq_min`): `noRec t = 0` forbids only *direct*
    ℓ-over-ℓ, while `ω(f(ω))` recurses through an intervening foot (`noRec = 0`, yet
    maximal ≠ minimal); the one-step `noRec` is the shadow this casts on the strictly-layered
    trees `IsWord` carves out. -/
def noLevelRec (ℓ : ProsodicLevel) : Tree → Bool := go where
  go : Tree → Bool
    | .node a cs => (!decide (a.level = ℓ) || isMinimalProj ℓ (.node a cs)) && goList cs
  goList : List Tree → Bool
    | []      => true
    | c :: cs => go c && goList cs

/-! ##### Properties

Each `where`-aux `goList` is the matching `List` combinator over its `go`
(`flatMap`/`any`/`all`), proved once below so every projection lemma is a single
`Branching.inductionOn` over the carrier (the principle `Tree` already rides,
`Core/Order/Branching.lean`) plus standard `List` reasoning. -/

private theorem maximalProjections.goList_eq (ℓ : ProsodicLevel) (under : Bool) (cs : List Tree) :
    maximalProjections.goList ℓ under cs = cs.flatMap (maximalProjections.go ℓ under) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [maximalProjections.goList, List.flatMap_cons, ih]

private theorem minimalProjections.goList_eq (ℓ : ProsodicLevel) (cs : List Tree) :
    minimalProjections.goList ℓ cs = cs.flatMap (minimalProjections.go ℓ) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [minimalProjections.goList, List.flatMap_cons, ih]

private theorem anyAtLevel.goList_eq (ℓ : ProsodicLevel) (cs : List Tree) :
    anyAtLevel.goList ℓ cs = cs.any (anyAtLevel ℓ) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [anyAtLevel.goList, List.any_cons, ih]; rfl

private theorem noLevelRec.goList_eq (ℓ : ProsodicLevel) (cs : List Tree) :
    noLevelRec.goList ℓ cs = cs.all (noLevelRec.go ℓ) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [noLevelRec.goList, List.all_cons, ih]

private theorem mem_maxProj_go {ℓ : ProsodicLevel} {s : Tree} :
    ∀ (under : Bool) (t : Tree), s ∈ maximalProjections.go ℓ under t → s.label.level = ℓ := by
  intro under t
  induction t using Core.Order.Branching.inductionOn generalizing under with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro hs
    rw [maximalProjections.go] at hs
    split at hs
    · rename_i hcond
      rw [List.mem_singleton] at hs; subst hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      simpa using hcond.2
    · rw [maximalProjections.goList_eq, List.mem_flatMap] at hs
      obtain ⟨c, hc, hsc⟩ := hs
      exact IH c (by simpa using hc) _ hsc

/-- Every maximal ℓ-projection is an ℓ-node. -/
theorem mem_maximalProjections_level {ℓ : ProsodicLevel} {s t : Tree}
    (h : s ∈ maximalProjections ℓ t) : s.label.level = ℓ := mem_maxProj_go _ _ h

private theorem isMin_go {ℓ : ProsodicLevel} {s : Tree} :
    ∀ t : Tree, s ∈ minimalProjections.go ℓ t → IsMinimalProj ℓ s := by
  intro t
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro hs
    rw [minimalProjections.go, List.mem_append, minimalProjections.goList_eq,
      List.mem_flatMap] at hs
    rcases hs with h | ⟨c, hc, hsc⟩
    · split at h
      · rename_i hcond; rw [List.mem_singleton] at h; subst h; exact hcond
      · simp only [List.not_mem_nil] at h
    · exact IH c (by simpa using hc) hsc

/-- Minimality is **intrinsic**: a node returned as a minimal ℓ-projection of any tree is
    itself a minimal ℓ-projection (`IsMinimalProj`) — it does not depend on the ambient tree.
    The maximal/minimal asymmetry: a node is maximal only *relative* to an ambient tree
    (its ℓ-ancestors), but minimal *in itself*. -/
theorem isMinimalProj_of_mem_minimalProjections {ℓ : ProsodicLevel} {s t : Tree}
    (h : s ∈ minimalProjections ℓ t) : IsMinimalProj ℓ s := isMin_go _ h

/-- A minimal ℓ-projection is an ℓ-node. -/
theorem isMinimalProj_level {ℓ : ProsodicLevel} {s : Tree} (h : IsMinimalProj ℓ s) :
    s.label.level = ℓ := by
  obtain ⟨a, cs⟩ := s
  simp only [IsMinimalProj, isMinimalProj, Bool.and_eq_true, decide_eq_true_eq] at h
  simpa using h.1

/-- Every minimal ℓ-projection is an ℓ-node. -/
theorem mem_minimalProjections_level {ℓ : ProsodicLevel} {s t : Tree}
    (h : s ∈ minimalProjections ℓ t) : s.label.level = ℓ :=
  isMinimalProj_level (isMin_go _ h)

/-- The intonational utterance υ is the maximal ι-projection: an ι-rooted tree is its own
    sole maximal ι-projection. -/
theorem utterance_eq_maximal_iota {t : Tree} (h : t.label.level = .ι) :
    maximalProjections .ι t = [t] := by
  obtain ⟨a, cs⟩ := t
  simp only [RootedTree.Planar.label_node] at h
  unfold maximalProjections maximalProjections.go
  simp [h]

private theorem noAny_go (ℓ : ProsodicLevel) :
    ∀ t : Tree, anyAtLevel.go ℓ t = false → minimalProjections.go ℓ t = [] := by
  intro t
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro h
    simp only [anyAtLevel.go, Bool.or_eq_false_iff] at h
    simp only [minimalProjections.go, isMinimalProj, h.1, Bool.false_and]
    show minimalProjections.goList ℓ cs = []
    rw [minimalProjections.goList_eq, List.flatMap_eq_nil_iff]
    intro c hc
    rw [anyAtLevel.goList_eq, List.any_eq_false] at h
    exact IH c (by simpa using hc) (by simpa [anyAtLevel] using h.2 c hc)

private theorem maxMin_go (ℓ : ProsodicLevel) :
    ∀ t : Tree, noLevelRec.go ℓ t = true →
      maximalProjections.go ℓ false t = minimalProjections.go ℓ t := by
  intro t
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro h
    simp only [noLevelRec.go, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hl : a.level = ℓ
    · have hmin : isMinimalProj ℓ (.node a cs) = true := by simpa [hl] using h1
      have hgoList : minimalProjections.goList ℓ cs = [] := by
        rw [minimalProjections.goList_eq, List.flatMap_eq_nil_iff]
        intro c hc
        have hany : cs.any (anyAtLevel ℓ) = false := by simpa [isMinimalProj, hl] using hmin
        rw [List.any_eq_false] at hany
        exact noAny_go ℓ c (by simpa [anyAtLevel] using hany c hc)
      simp only [maximalProjections.go, Bool.not_false, Bool.true_and, hl, decide_true,
        if_true, minimalProjections.go, hmin, if_true, hgoList, List.append_nil]
    · simp only [maximalProjections.go, Bool.not_false, Bool.true_and, hl, decide_false,
        Bool.or_false, minimalProjections.go, isMinimalProj, Bool.false_and]
      show maximalProjections.goList ℓ false cs = minimalProjections.goList ℓ cs
      rw [maximalProjections.goList_eq, minimalProjections.goList_eq]
      refine List.flatMap_congr fun c hc => ?_
      rw [noLevelRec.goList_eq, List.all_eq_true] at h2
      exact IH c (by simpa using hc) (h2 c (by simpa using hc))

/-- **No-Recursion collapses the projections.** Under transitive No-Recursion at `ℓ`
    (`noLevelRec`: no ℓ-node properly dominates an ℓ-node), the topmost and bottommost
    ℓ-nodes coincide — every ℓ-node is at once maximal and minimal. The naive `noRec t = 0`
    (no *direct* ℓ-over-ℓ) does **not** suffice — `ω(f(ω))` has `noRec = 0` yet maximal ≠
    minimal — but on the strictly-layered words `IsWord` cuts out, the two conditions agree. -/
theorem noLevelRec_imp_max_eq_min {ℓ : ProsodicLevel} {t : Tree}
    (h : noLevelRec ℓ t = true) : maximalProjections ℓ t = minimalProjections ℓ t :=
  maxMin_go ℓ t h

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

/-- The maximal ω-projections of a word: its topmost ω-nodes. A flat word is its own sole
    maximal projection; a recursive ω-over-ω ([ito-mester-2009]) has the outer ω. -/
def maximalProjections (w : Word) : List Tree := Prosody.maximalProjections .ω w.val

/-- The minimal ω-projections of a word: its innermost ω-nodes — the bottommost cores of
    an ω-over-ω recursion ([ito-mester-2009]). -/
def minimalProjections (w : Word) : List Tree := Prosody.minimalProjections .ω w.val

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

-- The ω-over-ω word has the outer ω as its sole maximal projection and the inner ω as its
-- sole minimal projection; the perfect (flat) word is both at once.
example : Word.maximalProjections ⟨recursiveW, by decide⟩ = [recursiveW] := by decide
example : Word.minimalProjections ⟨recursiveW, by decide⟩ = [.node Constituent.om [exFoot]] := by
  decide
example : Word.maximalProjections ⟨perfectW, by decide⟩ = [perfectW] := by decide
example : Word.minimalProjections ⟨perfectW, by decide⟩ = [perfectW] := by decide

/-! ### The metrical grid

The **metrical grid** ([liberman-prince-1977]) is the prominence representation dual to the
prosodic tree: a column of marks over each syllable, taller columns standing for greater
relative prominence (primary > secondary > unstressed). The *Relative Prominence Projection
Rule* (Liberman & Prince 1977, canonized in Prince's 1983 *Relating to the Grid*) reads the
grid off a tree by projecting one mark per syllable, plus one more for each layer of
headedness above it.

`gridColumns` makes the projection constructive: a σ-leaf's column height is `1` plus the
number of *contiguous head-edges* on the path up from the leaf — the run of consecutive heads
(stressed daughters, `Constituent.isHead`) starting at the leaf and broken by the first
non-head edge. A head syllable inside a head foot inside a head … reaches a tall column; a
non-head resets to the floor of `1`. `toGrid` stacks the columns into rows (row `r` marks the
syllables whose column exceeds `r`); the determinate level-by-level indexing is the bracketed
grid of Halle & Vergnaud 1987 and [hayes-1995].

The projection is **one-way**, a plain function rather than a structure-preserving functor:
distinct trees can share a grid (`toGrid_not_injective`), so constituency is genuinely lost —
the grid records prominence, not bracketing. There are no law-bearing tree morphisms for it
to act on; its lawfulness is instead the **Continuous Column Constraint**
(`toGrid_isContinuous`): no column has a gap, a *theorem* about the projection here rather
than a stipulated filter. -/

/-- A **metrical grid**: rows of head-marks, bottom row first. Row `r`, position `i` is
    `true` iff syllable `i` reaches grid level `r`. -/
abbrev Grid := List (List Bool)

/-- The **grid-column heights** of a tree's σ-frontier, left to right
    ([liberman-prince-1977]): each σ-leaf's height is `1` plus the contiguous run of
    head-edges above it. A top-down fold (cf. `parseInto`) threading `count`, the number of
    contiguous head-edges from the current node upward: a head child extends the run
    (`count + 1`), a non-head child resets it to `0`, and each σ-leaf emits `count + 1`. -/
def gridColumns (t : Tree) : List ℕ := go 0 t where
  go (count : ℕ) : Tree → List ℕ
    | .node a cs =>
        if decide (a.level = .σ) && cs.isEmpty then [count + 1]
        else goList count cs
  goList (count : ℕ) : List Tree → List ℕ
    | []      => []
    | c :: cs => go (if c.label.isHead then count + 1 else 0) c ++ goList count cs

private theorem gridColumns.goList_eq (count : ℕ) (cs : List Tree) :
    gridColumns.goList count cs =
      cs.flatMap (fun c => gridColumns.go (if c.label.isHead then count + 1 else 0) c) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [gridColumns.goList, List.flatMap_cons, ih]

/-- On a σ-leaf the fold emits a single column of height `count + 1`. -/
private theorem gridColumns.go_leaf (count : ℕ) (a : Constituent) (h : a.level = .σ) :
    gridColumns.go count (.node a []) = [count + 1] := by
  simp [gridColumns.go, h]

/-- The σ-leaf case keyed on `Constituent.syl`, for rewriting under a `flatMap` binder. -/
private theorem gridColumns.go_syl (count : ℕ) (wt : Syllable.Weight) (hd : Bool) :
    gridColumns.go count (.node (Constituent.syl wt hd) []) = [count + 1] :=
  gridColumns.go_leaf count _ rfl

/-- The **metrical grid** of a tree ([liberman-prince-1977]): the `gridColumns` heights stacked
    into rows, row `r` marking the syllables whose column exceeds `r` (so a height-`h` column
    is marked on exactly rows `0 … h-1`). Determinate level indexing à la Halle & Vergnaud
    1987 / [hayes-1995]. -/
def toGrid (t : Tree) : Grid :=
  (List.range ((gridColumns t).foldr max 0)).map
    (fun r => (gridColumns t).map (fun h => decide (r < h)))

/-- One row is a **submask** of another (the row below it): every position marked in `upper`
    is marked in `lower`. -/
private def rowSubmask (upper lower : List Bool) : Bool :=
  (upper.zip lower).all (fun p => !p.1 || p.2)

/-- The `Bool` Continuous-Column checker: each row is a submask of the row below it. -/
private def isContinuousGrid : Grid → Bool
  | []              => true
  | [_]             => true
  | lower :: upper :: rest => rowSubmask upper lower && isContinuousGrid (upper :: rest)

/-- The **Continuous Column Constraint** ([hayes-1995]): a grid has no gap in any column — if
    a syllable is marked at level `r` it is marked at every lower level. Equivalently (the
    `Bool` checker), each row is a submask of the row below it. A well-formed metrical grid
    satisfies CCC; here it is a *theorem* of `toGrid` (`toGrid_isContinuous`), not a filter. -/
def IsContinuous (g : Grid) : Prop := isContinuousGrid g

instance (g : Grid) : Decidable (IsContinuous g) :=
  inferInstanceAs (Decidable (isContinuousGrid g = true))

private theorem rowSubmask_gt (cols : List ℕ) (r : ℕ) :
    rowSubmask (cols.map (fun h => decide (r + 1 < h))) (cols.map (fun h => decide (r < h)))
      = true := by
  rw [rowSubmask, List.zip_map', List.all_map, List.all_eq_true]
  intro h _
  simp only [Function.comp_apply]
  by_cases hr : r + 1 < h
  · simp [hr, Nat.lt_of_succ_lt hr]
  · simp [hr]

private theorem isContinuousGrid_range' (F : ℕ → List Bool)
    (h : ∀ r, rowSubmask (F (r + 1)) (F r) = true) (k n : ℕ) :
    isContinuousGrid ((List.range' k n).map F) = true := by
  induction n generalizing k with
  | zero => rfl
  | succ m ih =>
    cases m with
    | zero => rfl
    | succ m' =>
      have hcons : (List.range' k (m' + 2)).map F
          = F k :: F (k + 1) :: (List.range' (k + 2) m').map F := by
        simp only [List.range'_succ, List.map_cons]
      have htail : (List.range' (k + 1) (m' + 1)).map F
          = F (k + 1) :: (List.range' (k + 2) m').map F := by
        simp only [List.range'_succ, List.map_cons]
      rw [hcons, isContinuousGrid, h k, Bool.true_and, ← htail]
      exact ih (k + 1)

/-- **The Continuous Column Constraint holds by construction.** Every grid `toGrid` produces
    has gapless columns: a height-`h` column is marked on a contiguous bottom run `0 … h-1`,
    because row `r` is `· > r`. CCC is thus a *theorem* of the projection ([hayes-1995]),
    not a stipulated well-formedness filter. -/
theorem toGrid_isContinuous (t : Tree) : IsContinuous (toGrid t) := by
  show isContinuousGrid (toGrid t) = true
  rw [toGrid, List.range_eq_range']
  exact isContinuousGrid_range' _ (fun r => rowSubmask_gt _ r) 0 _

/-- **Head-preservation through the grid** (the depth-1 / foot case, generalizing
    `Foot.headFlags_toProsTree`). A foot's prosodic tree projects to columns of height `2` at
    the head σ and `1` elsewhere: the grid records exactly the foot's headedness. -/
theorem gridColumns_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    gridColumns (f.toProsTree w) = (Foot.toGrid f).map (fun b => if b then 2 else 1) := by
  have hroot : gridColumns (f.toProsTree w)
      = gridColumns.goList 0 ((List.finRange f.syllables.length).map
          (fun i => (.node (Constituent.syl (w (f.syllables.get i)) (decide (i = f.head)))
            [] : Tree))) := rfl
  rw [hroot, gridColumns.goList_eq, List.flatMap_map]
  simp only [gridColumns.go_syl, RootedTree.Planar.label_node, Constituent.syl]
  rw [← List.map_eq_flatMap, Foot.toGrid, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  by_cases hi : i = f.head <;> simp [hi]

/-- The grid's **head row** recovers the foot's head profile: a foot's σ reaches grid level
    `2` exactly at its head, so the `> 1` row of `toGrid` equals `Foot.toGrid f`. Combined
    with `Foot.headFlags_toProsTree` (`Foot.toGrid f` = the prosodic tree's σ-leaf head
    flags), the grid's head row equals those head flags — head-preservation, now through the
    grid projection rather than the tree re-representation. -/
theorem foot_headRow {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    (gridColumns (f.toProsTree w)).map (fun h => decide (1 < h)) = Foot.toGrid f := by
  rw [gridColumns_toProsTree, List.map_map]
  refine List.map_id'' (fun b => ?_) _
  cases b <;> rfl

/-- **The grid loses constituency** ([liberman-prince-1977]). `toGrid` is not injective:
    distinct prosodic trees can project to the same grid. Witnesses — a single unstressed σ
    parsed into a foot vs. left bare under ω — share the column profile `[1]`, so the grid
    cannot recover whether a syllable is footed. Relating the grid to the bracketed tree
    surfaces the incompatibility: the grid encodes prominence, not bracketing. -/
theorem toGrid_not_injective :
    ∃ t₁ t₂ : Tree, t₁ ≠ t₂ ∧ toGrid t₁ = toGrid t₂ :=
  ⟨.node .om [.node .ft [.node (.syl 1) []]], .node .om [.node (.syl 1) []],
    by decide, by decide⟩

/-! #### Worked example

A three-syllable ω with a head foot (primary), a non-head foot (secondary), and a stray σ
(unstressed) projects to the column profile `[3, 2, 1]` and the staircase grid — the
canonical Liberman & Prince display. -/

private def exWord : Tree :=
  .node .om
    [ .node (.ft true)  [.node (.syl 1 true) []],
      .node (.ft false) [.node (.syl 1 true) []],
      .node (.syl 1 false) [] ]

example : gridColumns exWord = [3, 2, 1] := by decide
example : toGrid exWord =
    [[true, true, true], [true, true, false], [true, false, false]] := by decide
example : IsContinuous (toGrid exWord) := by decide

end Prosody
