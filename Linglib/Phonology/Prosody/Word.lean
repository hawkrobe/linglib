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
    | .node a cs => (cs.filter (fun c => Constituent.sameLevel c.label a)).length + goList cs
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

/-- The **maximal projections** of `t` selected by `p`: the topmost `p`-nodes (those with no
    `p`-ancestor), in tree order. A top-down `under`-flag fold (cf. `parseInto`) pruning a subtree
    once the first `p`-node is hit. -/
def maximalProjections (p : Constituent → Bool) (t : Tree) : List Tree := go false t where
  go (under : Bool) : Tree → List Tree
    | .node a cs =>
        if !under && p a then [.node a cs]
        else goList (under || p a) cs
  goList (under : Bool) : List Tree → List Tree
    | []      => []
    | c :: cs => go under c ++ goList under cs

/-- A `p`-node occurs somewhere in `t` (the root included). -/
def anyAtLevel (p : Constituent → Bool) : Tree → Bool := go where
  go : Tree → Bool
    | .node a cs => p a || goList cs
  goList : List Tree → Bool
    | []      => false
    | c :: cs => go c || goList cs

/-- The intrinsic minimal-`p` test: a `p`-node no proper descendant of which is a `p`-node. -/
def isMinimalProj (p : Constituent → Bool) : Tree → Bool
  | .node a cs => p a && !(cs.any (anyAtLevel p))

/-- The **minimal projections** of `t` selected by `p`: the bottommost `p`-nodes (those with no
    `p`-descendant), in tree order. -/
def minimalProjections (p : Constituent → Bool) (t : Tree) : List Tree := go t where
  go : Tree → List Tree
    | .node a cs => (if isMinimalProj p (.node a cs) then [.node a cs] else []) ++ goList cs
  goList : List Tree → List Tree
    | []      => []
    | c :: cs => go c ++ goList cs

/-- A **minimal `p`-projection**: a `p`-node none of whose proper descendants is a `p`-node — the
    intrinsic, context-free dual of (context-relative) maximality. -/
def IsMinimalProj (p : Constituent → Bool) (t : Tree) : Prop := isMinimalProj p t

instance (p : Constituent → Bool) (t : Tree) : Decidable (IsMinimalProj p t) :=
  inferInstanceAs (Decidable (isMinimalProj p t = true))

/-- **Transitive No-Recursion at `ℓ`**: no ℓ-node properly dominates an ℓ-node — every
    ℓ-node is a minimal projection. This — not `noRec` — is what collapses the maximal and
    minimal ℓ-projections (`noLevelRec_imp_max_eq_min`): `noRec t = 0` forbids only *direct*
    ℓ-over-ℓ, while `ω(f(ω))` recurses through an intervening foot (`noRec = 0`, yet
    maximal ≠ minimal); the one-step `noRec` is the shadow this casts on the strictly-layered
    trees `IsWord` carves out. -/
def noLevelRec (p : Constituent → Bool) : Tree → Bool := go where
  go : Tree → Bool
    | .node a cs => (!p a || isMinimalProj p (.node a cs)) && goList cs
  goList : List Tree → Bool
    | []      => true
    | c :: cs => go c && goList cs

/-! ##### Properties

Each `where`-aux `goList` is the matching `List` combinator over its `go`
(`flatMap`/`any`/`all`), proved once below so every projection lemma is a single
`Branching.inductionOn` over the carrier (the principle `Tree` already rides,
`Core/Order/Branching.lean`) plus standard `List` reasoning. -/

private theorem maximalProjections.goList_eq (p : Constituent → Bool) (under : Bool) (cs : List Tree) :
    maximalProjections.goList p under cs = cs.flatMap (maximalProjections.go p under) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [maximalProjections.goList, List.flatMap_cons, ih]

private theorem minimalProjections.goList_eq (p : Constituent → Bool) (cs : List Tree) :
    minimalProjections.goList p cs = cs.flatMap (minimalProjections.go p) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [minimalProjections.goList, List.flatMap_cons, ih]

private theorem anyAtLevel.goList_eq (p : Constituent → Bool) (cs : List Tree) :
    anyAtLevel.goList p cs = cs.any (anyAtLevel p) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [anyAtLevel.goList, List.any_cons, ih]; rfl

private theorem noLevelRec.goList_eq (p : Constituent → Bool) (cs : List Tree) :
    noLevelRec.goList p cs = cs.all (noLevelRec.go p) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [noLevelRec.goList, List.all_cons, ih]

private theorem mem_maxProj_go {p : Constituent → Bool} {s : Tree} :
    ∀ (under : Bool) (t : Tree), s ∈ maximalProjections.go p under t → p s.label = true := by
  intro under t
  induction t using Core.Order.Branching.inductionOn generalizing under with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro hs
    rw [maximalProjections.go] at hs
    split at hs
    · rename_i hcond
      rw [List.mem_singleton] at hs; subst hs
      simp only [Bool.and_eq_true] at hcond
      simpa using hcond.2
    · rw [maximalProjections.goList_eq, List.mem_flatMap] at hs
      obtain ⟨c, hc, hsc⟩ := hs
      exact IH c (by simpa using hc) _ hsc

/-- Every maximal `p`-projection is a `p`-node. -/
theorem mem_maximalProjections_level {p : Constituent → Bool} {s t : Tree}
    (h : s ∈ maximalProjections p t) : p s.label = true := mem_maxProj_go _ _ h

private theorem isMin_go {p : Constituent → Bool} {s : Tree} :
    ∀ t : Tree, s ∈ minimalProjections.go p t → IsMinimalProj p s := by
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
theorem isMinimalProj_of_mem_minimalProjections {p : Constituent → Bool} {s t : Tree}
    (h : s ∈ minimalProjections p t) : IsMinimalProj p s := isMin_go _ h

/-- A minimal `p`-projection is a `p`-node. -/
theorem isMinimalProj_level {p : Constituent → Bool} {s : Tree} (h : IsMinimalProj p s) :
    p s.label = true := by
  obtain ⟨a, cs⟩ := s
  simp only [IsMinimalProj, isMinimalProj, Bool.and_eq_true] at h
  simpa using h.1

/-- Every minimal `p`-projection is a `p`-node. -/
theorem mem_minimalProjections_level {p : Constituent → Bool} {s t : Tree}
    (h : s ∈ minimalProjections p t) : p s.label = true :=
  isMinimalProj_level (isMin_go _ h)

private theorem noAny_go (p : Constituent → Bool) :
    ∀ t : Tree, anyAtLevel.go p t = false → minimalProjections.go p t = [] := by
  intro t
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro h
    simp only [anyAtLevel.go, Bool.or_eq_false_iff] at h
    simp only [minimalProjections.go, isMinimalProj, h.1, Bool.false_and]
    show minimalProjections.goList p cs = []
    rw [minimalProjections.goList_eq, List.flatMap_eq_nil_iff]
    intro c hc
    rw [anyAtLevel.goList_eq, List.any_eq_false] at h
    exact IH c (by simpa using hc) (by simpa [anyAtLevel] using h.2 c hc)

private theorem maxMin_go (p : Constituent → Bool) :
    ∀ t : Tree, noLevelRec.go p t = true →
      maximalProjections.go p false t = minimalProjections.go p t := by
  intro t
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro h
    simp only [noLevelRec.go, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hl : p a = true
    · have hmin : isMinimalProj p (.node a cs) = true := by simpa [hl] using h1
      have hgoList : minimalProjections.goList p cs = [] := by
        rw [minimalProjections.goList_eq, List.flatMap_eq_nil_iff]
        intro c hc
        have hany : cs.any (anyAtLevel p) = false := by simpa [isMinimalProj, hl] using hmin
        rw [List.any_eq_false] at hany
        exact noAny_go p c (by simpa [anyAtLevel] using hany c hc)
      simp only [maximalProjections.go, Bool.not_false, Bool.true_and, hl,
        if_true, minimalProjections.go, hmin, if_true, hgoList, List.append_nil]
    · rw [Bool.not_eq_true] at hl
      simp only [maximalProjections.go, Bool.not_false, Bool.true_and, hl,
        Bool.or_false, minimalProjections.go, isMinimalProj, Bool.false_and]
      show maximalProjections.goList p false cs = minimalProjections.goList p cs
      rw [maximalProjections.goList_eq, minimalProjections.goList_eq]
      refine List.flatMap_congr fun c hc => ?_
      rw [noLevelRec.goList_eq, List.all_eq_true] at h2
      exact IH c (by simpa using hc) (h2 c (by simpa using hc))

/-- **No-Recursion collapses the projections.** Under transitive No-Recursion at `ℓ`
    (`noLevelRec`: no ℓ-node properly dominates an ℓ-node), the topmost and bottommost
    ℓ-nodes coincide — every ℓ-node is at once maximal and minimal. The naive `noRec t = 0`
    (no *direct* ℓ-over-ℓ) does **not** suffice — `ω(f(ω))` has `noRec = 0` yet maximal ≠
    minimal — but on the strictly-layered words `IsWord` cuts out, the two conditions agree. -/
theorem noLevelRec_imp_max_eq_min {p : Constituent → Bool} {t : Tree}
    (h : noLevelRec p t = true) : maximalProjections p t = minimalProjections p t :=
  maxMin_go p t h

/-- **Parse-into-`p`** ([ito-mester-2003]): σ-leaves dominated by no `p`-node. -/
def parseInto (p : Constituent → Bool) : Constraint Tree := fun t => go false t where
  go (under : Bool) : Tree → Nat
    | .node a cs =>
        let u := under || p a
        (if a.isSyl && cs.isEmpty && !u then 1 else 0) + goList u cs
  goList (under : Bool) : List Tree → Nat
    | [] => 0
    | c :: cs => go under c + goList under cs

/-- The σ-weight content of a foot node's direct σ-daughters. -/
private def footContent (cs : List Tree) : List Syllable.Weight :=
  cs.filterMap fun c => match c with
    | .node a [] => a.weight?
    | _ => none

/-- The feet of a prosodic tree: the σ-weight content of every `f`-node. -/
def feet : Tree → List (List Syllable.Weight) := fun t => go t where
  go : Tree → List (List Syllable.Weight)
    | .node a cs => (if a.isFt then [footContent cs] else []) ++ goList cs
  goList : List Tree → List (List Syllable.Weight)
    | [] => []
    | t :: ts => go t ++ goList ts

/-- Syllables parsed into no foot — `parseInto (·.isFt)`. -/
def unfootedCount (t : Tree) : Nat := parseInto (·.isFt) t

/-- Total mora count: the sum of the tree's σ-weights. -/
def moraCount : Tree → Nat := fun t => go t where
  go : Tree → Nat
    | .node a cs => a.weight?.getD 0 + goList cs
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
    | .node a cs => a.isOm && goList cs
  goList : List Tree → Bool
    | [] => true
    | c :: cs =>
        (isFootTree c || go c || (c.label.isSyl && c.children.isEmpty))
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
def maximalProjections (w : Word) : List Tree := Prosody.maximalProjections (·.isOm) w.val

/-- The minimal ω-projections of a word: its innermost ω-nodes — the bottommost cores of
    an ω-over-ω recursion ([ito-mester-2009]). -/
def minimalProjections (w : Word) : List Tree := Prosody.minimalProjections (·.isOm) w.val

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

end Prosody
