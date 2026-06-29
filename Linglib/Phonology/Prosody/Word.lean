import Linglib.Phonology.Prosody.Foot
import Linglib.Phonology.Constraints.Defs
import Linglib.Core.Order.Branching

/-!
# Prosodic words (ω)
[selkirk-1980] [nespor-vogel-1986] [liberman-prince-1977] [hayes-1995] [ito-mester-2009]
[mccarthy-prince-1993]

The canonical prosodic word ω: a **recursive, headed** constituent. Its daughters are
feet, **sub-words** (an ω-over-ω, the *extended prosodic word* / ω-adjunction of
[ito-mester-2009]), and stray (unfooted) syllables; one daughter is the distinguished
`head` (a constituent — a foot or a sub-word, never a stray). Recursion is **intrinsic
to ω** ([ito-mester-2009]; cf. [mccarthy-prince-1993]: ω, unlike the *intrinsic* foot and
syllable, is *extrinsic*/mapping-defined and so admits recursion), built directly into
the type — a single nested inductive over `List (Word.Daughter S)`.

Because the `head` is a constituent, the head-projection chain (`headFoot` →
`headSyllable`) bottoms out in a foot by construction, so the **minimal word**
([mccarthy-prince-1993]) — that an ω contains a foot — is a total function, not a
constraint. Foot binarity, exhaustive parsing, and `No-Recursion` are violable
constraints, *not* part of the type; ill-formed candidates (a footless ω, a stray under
φ) are exactly what a violable OT carrier (`Prosody.Tree`) represents, and `toProsTree`
re-represents this well-formed ω into that carrier.

## Main definitions

* `Word` — the recursive headed ω; `Word.Daughter` / `Word.Head` (foot / sub-ω / stray).
* `Word.headFoot` / `headSyllable` — the head-projection chain (the ω-DTE), recursive.
* `Word.daughters` / `feet` / `strays` — the daughter list and its foot/stray parts.
* `Word.recursionCount` — the `No-Recursion` violation count (ω-over-ω depth).
* `Word.toProsTree` — re-representation into `Prosody.Tree`, marking the head daughter.
-/

namespace Prosody

open Features.Prosody

/-- The ω node label for the prosodic tree (`Prosody.Tree`) — the ω-level arm of
    `Prosody.Constituent`, used by `Word.toProsTree`. -/
abbrev Constituent.om : Constituent := { level := .ω }
/-- The φ node label. Interim home: the φ object `Prosody.Phrase` lands in a later PR and
    will re-home this; for now φ-candidates ([ito-mester-2009]) need it here. -/
abbrev Constituent.ph : Constituent := { level := .φ }

/-! ### The recursive prosodic word -/

/-- The canonical prosodic word ω ([selkirk-1980]; [hayes-1995]; [ito-mester-2009]): a
    single nested inductive — a `head` constituent with `before`/`after` daughter lists,
    each daughter a foot, a sub-word (ω-over-ω), or a stray σ. -/
inductive Word (S : Type*) where
  | mk (before : List (Foot S ⊕ Word S ⊕ S)) (head : Foot S ⊕ Word S)
       (after : List (Foot S ⊕ Word S ⊕ S))
  deriving Repr

namespace Word
variable {S : Type*}

/-- A daughter of ω: a foot, a sub-word (ω-over-ω), or a stray (unfooted) σ. -/
abbrev Daughter (S : Type*) := Foot S ⊕ Word S ⊕ S
/-- The head of ω — a constituent (foot or sub-word), never a stray; this is what makes
    `headFoot` total and the minimal word hold by construction. -/
abbrev Head (S : Type*) := Foot S ⊕ Word S

@[match_pattern] def Daughter.foot (f : Foot S) : Daughter S := .inl f
@[match_pattern] def Daughter.sub  (w : Word S) : Daughter S := .inr (.inl w)
@[match_pattern] def Daughter.leaf (s : S)      : Daughter S := .inr (.inr s)
@[match_pattern] def Head.foot (f : Foot S) : Head S := .inl f
@[match_pattern] def Head.sub  (w : Word S) : Head S := .inr w

/-- The head viewed as a daughter (foot/sub, never a leaf). -/
def Head.toDaughter : Head S → Daughter S
  | Head.foot f => Daughter.foot f
  | Head.sub w  => Daughter.sub w

/-- All daughters in linear order (head included). -/
def daughters : Word S → List (Daughter S)
  | .mk before head after => before ++ Head.toDaughter head :: after

/-- The top-level feet (head foot included if the head is a foot). -/
def feet (w : Word S) : List (Foot S) :=
  w.daughters.filterMap (fun | Daughter.foot f => some f | _ => none)

/-- The stray (unfooted) syllables. -/
def strays (w : Word S) : List S :=
  w.daughters.filterMap (fun | Daughter.leaf s => some s | _ => none)

/-- A minimal ω consisting of a single foot. -/
def ofFoot (f : Foot S) : Word S := .mk [] (Head.foot f) []

/-! ### The head-projection chain (the ω-DTE) -/

/-- The head foot — descend the head chain through sub-words to the bottom foot. Total
    by construction (a `Head` is a constituent), so every ω contains a foot: this *is*
    the minimal word ([mccarthy-prince-1993]). -/
def headFoot : Word S → Foot S
  | .mk _ (Head.foot f) _ => f
  | .mk _ (Head.sub w) _  => headFoot w

/-- The ω-DTE: the primary-stressed syllable, the head σ of the head foot
    ([liberman-prince-1977]; the head chain projects to the bottom). -/
def headSyllable (w : Word S) : S := w.headFoot.headSyllable

/-! ### No-Recursion (ω-over-ω) -/

/-- The `No-Recursion` violation count ([ito-mester-2009]): the number of sub-word
    daughters, recursively — i.e. how many times ω is parsed into ω. The list-recursion
    aux is a local `where` (Lean can't auto-terminate recursion under `List.map`). -/
def recursionCount : Word S → Nat
  | .mk before head after => hRec head + lAux before + lAux after
where
  hRec : Head S → Nat
    | Head.foot _ => 0
    | Head.sub w  => 1 + recursionCount w
  lAux : List (Daughter S) → Nat
    | [] => 0
    | Daughter.sub w :: ds => 1 + recursionCount w + lAux ds
    | _ :: ds => lAux ds

/-! ### Re-representation into the prosodic tree -/

/-- Re-represent ω as a `Prosody.Tree` ([ito-mester-2009]): an `.ω` node over the
    daughters' subtrees, the **head** daughter marked `isHead` (the head foot via
    `Foot.toProsTree _ _ true`; a head sub-word recursively). Composes `Foot.toProsTree`. -/
def toProsTree (wt : S → Syllable.Weight) : Word S → Tree
  | .mk before head after => .node .om (lTree before ++ hTree head :: lTree after)
where
  hTree : Head S → Tree
    | Head.foot f => Foot.toProsTree wt f true
    | Head.sub w  => toProsTree wt w
  lTree : List (Daughter S) → List Tree
    | [] => []
    | d :: ds => dTree d :: lTree ds
  dTree : Daughter S → Tree
    | Daughter.foot f => Foot.toProsTree wt f
    | Daughter.sub w  => toProsTree wt w
    | Daughter.leaf s => .node (.syl (wt s) false) []

end Word

/-! ### Worked examples -/

-- A heavy monosyllabic stem foot, a flat ω over it, and an ω-over-ω (extended PWord).
private def stemFt : Foot Nat := Foot.monosyllable 2
private def innerW : Word Nat := .mk [] (Word.Head.foot stemFt) []
private def flatW  : Word Nat := .mk [Word.Daughter.leaf 1] (Word.Head.foot stemFt) []
private def recW   : Word Nat := .mk [Word.Daughter.leaf 1] (Word.Head.sub innerW) []

-- No-Recursion: the extended PWord scores one ω-over-ω; the flat ω scores zero.
example : flatW.recursionCount = 0 := by
  simp [flatW, Word.recursionCount, Word.recursionCount.hRec, Word.recursionCount.lAux]
example : recW.recursionCount = 1 := by
  simp [recW, innerW, Word.recursionCount, Word.recursionCount.hRec, Word.recursionCount.lAux]

-- The head-projection chain descends to the stem foot's head σ (the ω-DTE).
example : recW.headSyllable = 2 := by
  simp [recW, innerW, Word.headSyllable, Word.headFoot, stemFt, Foot.headSyllable,
    Foot.monosyllable]
example : flatW.headSyllable = 2 := by
  simp [flatW, Word.headSyllable, Word.headFoot, stemFt, Foot.headSyllable, Foot.monosyllable]

/-! ### Prosodic OT constraints over the `Tree` carrier

The violable constraints scoring prosodic candidates are `Constraints.Constraint Tree`
values ([prince-smolensky-1993]); a grammar ranks them and scores with the OT engine
(`OptimalityTheory.Tableau.ofRanking`). They are defined on the **carrier** `Tree` (which
holds the ill-formed candidates the typed `Word` can't represent); a typed ω reuses any of
them via `Constraint.comap (Word.toProsTree wt)`. List-recursion auxes are local `where`s. -/

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

/-! ### The carrier constraint, shared to the typed ω

A `Constraint Tree` is shared to the typed `Word` for free via `Constraint.comap` along the
`toProsTree` functor — *one* definition (`noRec` on the carrier) scoring both
representations. On a concrete ω it agrees with `Word.recursionCount` (the wt-free
specialization); the general identity `Word.recursionCount = noRec ∘ toProsTree` — the
commuting square — lands with the functor development. -/

example : (noRec.comap (Word.toProsTree id)) recW = Word.recursionCount recW := by decide

/-! ### `Word` induction via the Core `Branching` machinery

`Word` is a heterogeneous recursive tree, so it reuses Core's `Branching` tree-recursion
(the same machinery `Planar` rides): its **children** are its sub-word daughters, well-founded
because children strictly shrink `sizeOf`. This unlocks `Branching.inductionOn` — strong
induction over the sub-words — without a hand-rolled eliminator or a mutual rewrite. -/

namespace Word
variable {S : Type*}

open Core.Order

/-- The sub-words of an ω (its recursive ω-over-ω daughters) — `Word`'s children for the
    Core `Branching` tree-recursion machinery. -/
def subWords (w : Word S) : List (Word S) :=
  w.daughters.filterMap fun d => match d with | Daughter.sub w' => some w' | _ => none

instance : Branching (Word S) := ⟨subWords⟩

/-- A sub-word daughter is strictly smaller than its mother: the `sizeOf` decrease that
    makes `Word`'s child relation well-founded. -/
theorem sizeOf_lt_of_mem_subWords {c t : Word S} (h : c ∈ subWords t) :
    sizeOf c < sizeOf t := by
  obtain ⟨before, head, after⟩ := t
  rw [subWords, daughters, List.mem_filterMap] at h
  obtain ⟨d, hd, hdc⟩ := h
  rcases d with f | w' | s
  · simp at hdc
  · obtain rfl : c = w' := by simpa using hdc.symm
    rw [List.mem_append, List.mem_cons] at hd
    rcases hd with hb | hh | ha
    · have hb' := List.sizeOf_lt_of_mem hb
      simp only [Word.mk.sizeOf_spec, Sum.inl.sizeOf_spec, Sum.inr.sizeOf_spec] at hb' ⊢
      omega
    · rcases head with hf | hw
      · simp [Head.toDaughter, Daughter.foot] at hh
      · obtain rfl : c = hw := by simpa [Head.toDaughter, Daughter.sub, Head.sub] using hh
        simp only [Word.mk.sizeOf_spec, Sum.inr.sizeOf_spec]
        omega
    · have ha' := List.sizeOf_lt_of_mem ha
      simp only [Word.mk.sizeOf_spec, Sum.inl.sizeOf_spec, Sum.inr.sizeOf_spec] at ha' ⊢
      omega
  · simp at hdc

instance : IsFiniteBranching (Word S) :=
  .ofMeasure sizeOf (fun hc => sizeOf_lt_of_mem_subWords hc)

/-! ### The commuting square: `recursionCount = noRec ∘ toProsTree` -/

open RootedTree

private theorem noRec_eq_go (t : Tree) : noRec t = noRec.go t := rfl

private theorem noRec_go_leaf (a : Constituent) : noRec.go (.node a []) = 0 := by
  simp [noRec.go, noRec.goList]

/-- A list of leaf nodes contributes no No-Recursion violations. -/
private theorem noRec_goList_leafMap {β : Type*} (l : List β) (lab : β → Constituent) :
    noRec.goList (l.map (fun x => Planar.node (lab x) [])) = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, noRec.goList, ih, Nat.add_zero, noRec_go_leaf]

private theorem noRec_goList_append (xs ys : List Tree) :
    noRec.goList (xs ++ ys) = noRec.goList xs + noRec.goList ys := by
  induction xs with
  | nil => simp [noRec.goList]
  | cons x xs ih => simp only [List.cons_append, noRec.goList, ih]; omega

/-- A foot subtree (a depth-1 `f`-node over σ-leaves) scores no No-Recursion violations. -/
private theorem noRec_go_foot (wt : S → Syllable.Weight) (f : Foot S) (b : Bool) :
    noRec.go (Foot.toProsTree wt f b) = 0 := by
  rw [Foot.toProsTree, noRec.go]
  have hf : ((List.finRange f.syllables.length).map (fun i =>
      Planar.node (Constituent.syl (wt (f.syllables.get i)) (decide (i = f.head))) [])).filter
      (fun c => decide (c.label.level = (Constituent.ft b).level)) = [] := by
    rw [List.filter_eq_nil_iff]; intro c hc
    simp only [List.mem_map] at hc; obtain ⟨i, _, rfl⟩ := hc; simp
  rw [hf, noRec_goList_leafMap]; rfl

@[simp] private theorem foot_toProsTree_label (wt : S → Syllable.Weight) (f : Foot S) (b : Bool) :
    (Foot.toProsTree wt f b).label = Constituent.ft b := rfl

private theorem toProsTree_label (wt : S → Syllable.Weight) (w : Word S) :
    (w.toProsTree wt).label = Constituent.om := by obtain ⟨before, head, after⟩ := w; rfl

private theorem noRec_node_om (cs : List Tree) :
    noRec (.node Constituent.om cs) =
      (cs.filter (fun c => decide (c.label.level = ProsodicLevel.ω))).length
        + noRec.goList cs := rfl

private theorem mem_subWords_of_mem_daughters {w' t : Word S}
    (h : Daughter.sub w' ∈ daughters t) : w' ∈ subWords t := by
  rw [subWords, List.mem_filterMap]; exact ⟨Daughter.sub w', h, rfl⟩

/-- The per-daughter-list half of the commuting square: a daughter list's No-Recursion count
    splits into the ω-children it contributes (its sub-words) plus the recursive count of each
    child's subtree — exactly what `noRec` reads off the re-represented tree. -/
private theorem lAux_filter_goList (wt : S → Syllable.Weight) :
    ∀ ds : List (Daughter S),
      (∀ w', Daughter.sub w' ∈ ds → recursionCount w' = noRec (w'.toProsTree wt)) →
      recursionCount.lAux ds =
        ((toProsTree.lTree wt ds).filter
          (fun c => decide (c.label.level = ProsodicLevel.ω))).length
        + noRec.goList (toProsTree.lTree wt ds)
  | [], _ => by simp [recursionCount.lAux, toProsTree.lTree, noRec.goList]
  | d :: ds, IH => by
    have ih := lAux_filter_goList wt ds (fun w' h => IH w' (List.mem_cons_of_mem _ h))
    rcases d with f | w' | s
    · simp only [recursionCount.lAux, toProsTree.lTree, toProsTree.dTree, noRec.goList,
        List.filter_cons, foot_toProsTree_label, noRec_go_foot, ih]; simp
    · have hsub := IH w' (List.mem_cons_self ..)
      simp only [recursionCount.lAux, toProsTree.lTree, toProsTree.dTree, noRec.goList,
        List.filter_cons, toProsTree_label, ← noRec_eq_go, ← hsub, ih]
      simp only [decide_true, if_true, List.length_cons]; omega
    · simp only [recursionCount.lAux, toProsTree.lTree, toProsTree.dTree, noRec.goList,
        List.filter_cons, Planar.label_node, noRec_go_leaf, ih]; simp

/-- **The commuting square** ([ito-mester-2009]): the typed ω's No-Recursion count IS the
    carrier constraint `noRec` pulled back along the `toProsTree` functor. `recursionCount`
    is thus the wt-free ergonomic specialization of `noRec.comap (Word.toProsTree wt)`; the
    functor preserves the constraint. Proved by strong induction over the sub-words
    (`Branching.inductionOn`). -/
theorem recursionCount_eq_noRec_toProsTree (wt : S → Syllable.Weight) (w : Word S) :
    recursionCount w = noRec (w.toProsTree wt) := by
  induction w using Core.Order.Branching.inductionOn with
  | ih w IH =>
    obtain ⟨before, head, after⟩ := w
    have IH : ∀ c ∈ subWords (Word.mk before head after),
        recursionCount c = noRec (c.toProsTree wt) := IH
    have IHbefore : ∀ w', Daughter.sub w' ∈ before →
        recursionCount w' = noRec (w'.toProsTree wt) :=
      fun w' h => IH w' (mem_subWords_of_mem_daughters (List.mem_append_left _ h))
    have IHafter : ∀ w', Daughter.sub w' ∈ after →
        recursionCount w' = noRec (w'.toProsTree wt) :=
      fun w' h => IH w' (mem_subWords_of_mem_daughters
        (List.mem_append_right _ (List.mem_cons_of_mem _ h)))
    rw [recursionCount, toProsTree, noRec_node_om, lAux_filter_goList wt before IHbefore,
        lAux_filter_goList wt after IHafter, List.filter_append, List.length_append,
        noRec_goList_append]
    rcases head with f | w'
    · simp only [recursionCount.hRec, toProsTree.hTree, noRec.goList, List.filter_cons,
        foot_toProsTree_label, noRec_go_foot]
      simp; omega
    · have hsub : recursionCount w' = noRec (w'.toProsTree wt) :=
        IH w' (mem_subWords_of_mem_daughters
          (List.mem_append_right _ (List.mem_cons_self ..)))
      simp only [recursionCount.hRec, toProsTree.hTree, noRec.goList, List.filter_cons,
        toProsTree_label, ← noRec_eq_go, ← hsub]
      simp only [decide_true, if_true, List.length_cons]; omega

end Word

end Prosody
