/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Syntax.Projection
public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Syntax.Minimalist.SyntacticObject.Phase

/-!
# Chains on planar syntactic objects

A planar syntactic object is a copy-theoretic representation. A vertex `Vertex.lex tok` is a
pronounced copy of `tok` and a vertex `Vertex.traceOf tok` a deleted one, the trace Internal Merge
leaves, Marcolli, Chomsky and Berwick's cancellation `T/T_v` with the head of `T_v` remembered.
The chain of a token is the list of its copies, and a copy stands for the maximal projection of
its token, so a moved phrase sits where its head projects. A token moves when it has a deleted
copy. A token bound in situ by an operator, as for Pesetsky, has a single copy. A deleted copy
above the pronounced one is Huang's covert movement, and a pronounced copy between two deleted
ones is Sato and Ngui's partial movement, so where a phrase is pronounced and where it takes scope
come apart without a separate choice of the copy to spell out. A token with two pronounced copies
is shared, dominated by two mothers, Citko's Parallel Merge.

A copy is linked to the nearest copy above it, the one whose projection c-commands it with no
other copy's projection in between, c-command being Barker and Pullum's `PhraseStructure.CCommands`.
Locality constrains links. Chomsky's Phase Impenetrability Condition bars a link from the interior
of a phase, the positions its head c-commands, to a position outside the head's maximal
projection, so that the edge is the escape hatch (`Crosses`); an island is a domain no link may
leave (`Escapes`). A token with one copy has no link, so binding in situ is subject to neither
(`links_eq_nil_of_length_le_one`), and movement, covert movement included, is subject to both, as
Sato and Ngui find.

## Main definitions

* `Minimalist.tokenList`, `Minimalist.traceList`: the pronounced and the deleted copies.
* `occurrences`, `traces`, `chain`, `Moves`, `IsShared`: the copies of a token.
* `headIndex?`, `projectionAt`: the head daughter of a constituent, and the phrase a copy stands
  for, its maximal projection along head daughters (`PhraseStructure.maximalProjectionAt`).
* `HasAntecedent`, `orphanTraces`: whether a pronounced copy c-commands a deleted one, and the
  deleted copies without antecedents, seen from their own conjunct copies.
* `IsLink`, `links`, `chainTop`: the links of a chain and its scope position.
* `interior`, `Crosses`, `Escapes`: phases, islands, and the links that leave them.

## Main statements

* `cCommandsIn_leaf_iff`: c-command by a token occurring once is c-command from its position.
* `withinComplement_iff_exists_mem_interior`: the positions in `interior` carry the terms within
  the complement of a head that occurs once and projects wherever it occurs.

## Implementation notes

* Positions, not terms, individuate copies: two deleted copies of one token are the same term,
  so the phase interior of the unordered object (`SyntacticObject.phaseInterior`, the terms
  within the head's complement) cannot tell the links of a successive-cyclic chain apart.
  `interior` is the head's c-command domain on positions.
* The head of a constituent is found down its right spine (`headPos?`), a left leaf that selects
  nothing being a specifier. Where two saturated phrases are sisters, a specifier and its sister,
  the selection head `SyntacticObject.selHead` is undefined, as Marcolli, Chomsky and Berwick's
  head functions are, and the raising head (`SyntacticObject.raisingHead`) heads the object only
  where one of them has raised out of the other; `headPos?` takes the right sister, so that a
  phrase with a specifier has a maximal projection to locate a copy in.
* A chain here is the copies an object contains; the replay of a derivation
  (`Derivation.externalize?`) builds overt chains with bound traces, while covert movement,
  sharing and copies without antecedents are available to the representation only.

## TODO

* `CCommands t.val a b ↔ a.parent ≤ b ∧ ¬ a ≤ b` on a well-formed object, for `b` not the mother
  of `a`: c-command as sisterhood-plus-dominance.
* A successful `Derivation.externalize?` has no deleted copy without an antecedent.

## References

* [marcolli-chomsky-berwick-2025]
* [citko-2005]
* [pesetsky-1987]
* [huang-1982]
* [sato-ngui-2017]
* [barker-pullum-1990]
* [chomsky-2000]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order PhraseStructure

/-! ### Copies -/

/-- The positions of `t` whose label `f` accepts, with the values, in preorder. -/
def positions {β : Type*} (f : Vertex → Option β) (t : RoseTree Vertex) : List (TreePath × β) :=
  t.positionedSubtrees.filterMap fun x ↦ (f x.2.value).map (x.1, ·)

theorem mem_positions_iff {β : Type*} {f : Vertex → Option β} {t : RoseTree Vertex}
    {p : TreePath} {b : β} :
    (p, b) ∈ positions f t ↔ ∃ s, subtreeAt t p.toList = some s ∧ f s.value = some b := by
  simp only [positions, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists,
    mem_positionedSubtrees]
  exact ⟨fun ⟨_, s, hs, _, hb, rfl, rfl⟩ ↦ ⟨s, hs, hb⟩,
    fun ⟨s, hs, hb⟩ ↦ ⟨p, s, hs, b, hb, rfl, rfl⟩⟩

/-- The pronounced copies, left to right. -/
def tokenList : RoseTree Vertex → List (TreePath × LIToken) :=
  positions (Sum.elim id fun _ ↦ none)

/-- The deleted copies, left to right. -/
def traceList : RoseTree Vertex → List (TreePath × LIToken) :=
  positions (Sum.elim (fun _ ↦ none) id)

variable (t : PlanarSyntacticObject) (tok : LIToken)

/-- The positions of the pronounced copies of `tok`. -/
def occurrences : List TreePath :=
  (tokenList t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

variable {t tok} in
/-- A position is an occurrence of `tok` exactly when it carries `tok`. -/
theorem mem_occurrences_iff {p : TreePath} :
    p ∈ occurrences t tok ↔ ∃ s, t.val.subtreeAt p.toList = some s ∧ s.value = Vertex.lex tok := by
  simp only [occurrences, List.mem_filterMap, tokenList, Prod.exists]
  constructor
  · rintro ⟨q, tok', hq, he⟩
    split_ifs at he with htok
    cases he; subst htok
    obtain ⟨s, hs, hv⟩ := mem_positions_iff.1 hq
    refine ⟨s, hs, ?_⟩
    rcases hsv : s.value with o | o <;> rw [hsv] at hv <;> simp_all
  · rintro ⟨s, hs, hv⟩
    exact ⟨p, tok, mem_positions_iff.2 ⟨s, hs, by simp [hv]⟩, by simp⟩

/-- The positions of the deleted copies of `tok`. -/
def traces : List TreePath :=
  (traceList t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- The chain of `tok` lists the positions of its copies, pronounced or deleted, left to right. -/
def chain : List TreePath :=
  (positions (Sum.elim id id) t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- `tok` moves when it has a deleted copy. -/
def Moves : Prop := traces t tok ≠ []

instance : Decidable (Moves t tok) := inferInstanceAs (Decidable (_ ≠ _))

/-- `tok` is shared, dominated by two mothers, when it has two pronounced copies. -/
def IsShared : Prop := 2 ≤ (occurrences t tok).length

instance : Decidable (IsShared t tok) := inferInstanceAs (Decidable (_ ≤ _))

/-! ### The phrase a copy stands for -/

/-- The position of the head of a constituent, relative to its root. A token or trace leaf is its
own head; at a binary node a left leaf with nothing to select is a specifier and the head lies in
the right daughter, a left leaf that selects is the head, and otherwise the head lies in the right
daughter. -/
def headPos? : RoseTree Vertex → Option (List ℕ)
  | .node (.inl (some _)) _ | .node (.inr (some _)) _ => some []
  | .node (.inl none) [.node (.inl (some tok)) [], r] =>
      if tok.item.outerSel = [] then (headPos? r).map (1 :: ·) else some [0]
  | .node (.inl none) [_, r] => (headPos? r).map (1 :: ·)
  | .node (.inl none) _ => none
  | .node (.inr none) _ => none

/-- The head of a constituent is the token its head position carries. -/
def headToken? (s : RoseTree Vertex) : Option LIToken :=
  (headPos? s).bind fun q ↦ (subtreeAt s q).bind (Sum.elim id id ·.value)

/-- The index of a constituent's head daughter, the first step of its head path. -/
def headIndex? (s : RoseTree Vertex) : Option ℕ := (headPos? s).bind List.head?

/-- The maximal projection of the copy at `p` is the highest position reached from `p` by
climbing while the position is the head daughter of its mother. -/
def projectionAt (p : TreePath) : TreePath :=
  maximalProjectionAt (fun q ↦ (subtreeAt t.val q.toList).bind headIndex?) p

theorem projectionAt_le (p : TreePath) : projectionAt t p ≤ p := maximalProjectionAt_le _ p

/-- A deleted copy has an antecedent when the projection of a pronounced copy of its token
c-commands it. -/
def HasAntecedent (x : TreePath × LIToken) : Prop :=
  ∃ p ∈ occurrences t x.2, CCommands t.val (projectionAt t p) x.1

instance (x : TreePath × LIToken) : Decidable (HasAntecedent t x) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The deleted copies without antecedents. -/
def orphanTraces : List (TreePath × LIToken) := (traceList t.val).filter (¬ HasAntecedent t ·)

/-! ### Links -/

/-- The copy at `p` is linked to the copy at `q` below it when its projection c-commands `q` and
the projection of no other copy of `tok` lies between them. -/
def IsLink (p q : TreePath) : Prop :=
  CCommands t.val (projectionAt t p) q ∧
    ∀ r ∈ chain t tok, CCommands t.val (projectionAt t p) (projectionAt t r) →
      ¬ CCommands t.val (projectionAt t r) q

instance (p q : TreePath) : Decidable (IsLink t tok p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- The links of the chain of `tok` pair each copy with the projection of the copy linked to it. -/
def links : List (TreePath × TreePath) :=
  (chain t tok).flatMap fun q ↦
    ((chain t tok).filter fun p ↦ IsLink t tok p q).map fun p ↦ (projectionAt t p, q)

/-- The top of the chain of `tok` consists of the copies no copy's projection c-commands, where it
takes scope. -/
def chainTop : List TreePath :=
  (chain t tok).filter fun q ↦ (chain t tok).all fun p ↦ ¬ CCommands t.val (projectionAt t p) q

theorem not_isLink_self (p : TreePath) : ¬ IsLink t tok p p :=
  fun h ↦ h.1.2.1 (projectionAt_le t p)

/-- A token with at most one copy has no link. -/
theorem links_eq_nil_of_length_le_one (h : (chain t tok).length ≤ 1) : links t tok = [] := by
  simp only [links, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq]
  intro q hq p hp
  obtain rfl : p = q := by
    rcases hc : chain t tok with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [hc] at hp
    · simp only [hc, List.mem_singleton] at hp hq
      rw [hp, hq]
    · simp [hc] at h
  exact not_isLink_self t tok p

/-! ### Locality -/

/-- The interior of the phase headed at `h` is the set of positions the head c-commands. -/
def interior (h : TreePath) : Set TreePath := {q | CCommands t.val h q}

instance (h q : TreePath) : Decidable (q ∈ interior t h) :=
  inferInstanceAs (Decidable (CCommands _ _ _))

/-- C-command by a token occurring once, at `h`, is c-command from `h`: the leaf of the token
c-commands a term exactly when the term stands at a position `h` c-commands. -/
theorem cCommandsIn_leaf_iff {t : PlanarSyntacticObject} {ℓ : LIToken} {h : TreePath}
    (hocc : occurrences t ℓ = [h]) (x : SyntacticObject) :
    (t : SyntacticObject).cCommandsIn (SyntacticObject.leaf ℓ) x ↔
      ∃ q s, t.val.subtreeAt q.toList = some s ∧ UnorderedTree.mk s = x.val ∧
        CCommands t.val h q := by
  have hocc' : ∀ p, p ∈ occurrences t ℓ ↔ p = h := fun p ↦ by rw [hocc, List.mem_singleton]
  constructor
  · rintro ⟨z, -, ⟨w, hw, hwℓ, hwz, hne⟩, hzx⟩
    obtain ⟨pw, sw, hsw, hmw⟩ := PlanarSyntacticObject.mem_terms_iff.1 hw
    have hc : (SyntacticObject.leaf ℓ).val ∈ (UnorderedTree.mk sw).children := hmw ▸ hwℓ
    have hd : z.val ∈ (UnorderedTree.mk sw).children := hmw ▸ hwz
    rw [UnorderedTree.children_mk, Multiset.mem_coe, List.mem_map] at hc hd
    obtain ⟨c, hcmem, hcℓ⟩ := hc
    obtain ⟨d, hdmem, hdz⟩ := hd
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hcmem
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hdmem
    have hci : t.val.subtreeAt (pw ++ [i]) = some c := by simp [subtreeAt_append, hsw, hi]
    have hpos : (⟨pw ++ [i]⟩ : TreePath) = h :=
      (hocc' _).1 (mem_occurrences_iff.2 ⟨c, hci, (PlanarSyntacticObject.mk_eq_leaf_iff hci).1 hcℓ⟩)
    have hij : j ≠ i := by
      rintro rfl
      rw [hi] at hj
      cases hj
      exact hne (Subtype.ext (hcℓ.symm.trans hdz))
    have hx : x.val ∈ UnorderedTree.subtrees z.val := by
      rw [← map_val_terms]; exact Multiset.mem_map_of_mem _ (mem_terms.2 hzx)
    rw [← hdz, UnorderedTree.subtrees_mk, RoseTree.mem_unorderedSubtrees] at hx
    obtain ⟨r, s, hs, hsx⟩ := hx
    refine ⟨⟨pw ++ [j] ++ r⟩, s, by simp [subtreeAt_append, hsw, hj, hs], hsx, ?_, ?_, ?_⟩
    · intro y _ hyh
      rw [← hpos] at hyh
      refine (TreePath.le_parent_of_lt hyh).trans ?_
      simp [TreePath.le_def, List.append_assoc]
    · rw [← hpos, TreePath.mk_le_mk, List.append_assoc, List.prefix_append_right_inj]
      simpa using hij.symm
    · rw [← hpos, TreePath.mk_le_mk, List.append_assoc, List.prefix_append_right_inj]
      simp [hij]
  · rintro ⟨q, s, hs, hsx, hcc, hhq, hqh⟩
    obtain ⟨c, hc, hcv⟩ := mem_occurrences_iff.1 ((hocc' h).2 rfl)
    obtain ⟨pw, i, hpi⟩ : ∃ pw i, h.toList = pw ++ [i] := by
      rcases List.eq_nil_or_concat h.toList with h0 | ⟨pw, i, hpi⟩
      · exact absurd (TreePath.le_def.2 (by rw [h0]; exact List.nil_prefix)) hhq
      · exact ⟨pw, i, by simpa using hpi⟩
    rw [hpi, subtreeAt_append] at hc
    cases hpw : t.val.subtreeAt pw with
    | none => simp [hpw] at hc
    | some sw =>
    have hi : sw.children[i]? = some c := by simpa [hpw] using hc
    have hci : t.val.subtreeAt (pw ++ [i]) = some c := by simp [subtreeAt_append, hpw, hi]
    have hbr : IsBranchingAt t.val ⟨pw⟩ := by
      refine mem_positionsWhere.2 ⟨sw, hpw, ?_⟩
      obtain ⟨y, -, hy⟩ := PlanarSyntacticObject.exists_mem_terms_of_subtreeAt hpw
      obtain ⟨a, cs⟩ := sw
      have hne : cs ≠ [] := by rintro rfl; simp at hi
      rcases length_eq_zero_or_two (hy ▸ y.2) with h0 | h2
      · exact absurd (List.length_eq_zero_iff.1 h0) hne
      · simp [arity, h2]
    have hlt : (⟨pw⟩ : TreePath) < h := by
      refine lt_of_le_of_ne (TreePath.le_def.2 (by rw [hpi]; exact List.prefix_append _ _)) ?_
      intro he
      have := congrArg (fun p : TreePath ↦ p.toList.length) he
      simp [hpi] at this
    obtain ⟨rest, hrest⟩ := TreePath.le_def.1 (hcc ⟨pw⟩ hbr hlt)
    rcases rest with _ | ⟨j, r⟩
    · exact absurd (TreePath.le_def.2 (by rw [← hrest, hpi]; simp)) hqh
    have hij : j ≠ i := by
      rintro rfl
      exact hhq (TreePath.le_def.2 (by rw [hpi, ← hrest]; simp))
    rw [← hrest, show pw ++ j :: r = pw ++ [j] ++ r by simp, subtreeAt_append, subtreeAt_append,
      hpw] at hs
    obtain ⟨d, hj, hds⟩ : ∃ d, sw.children[j]? = some d ∧ d.subtreeAt r = some s := by
      cases hjd : sw.children[j]? with
      | none => simp [hjd] at hs
      | some d => exact ⟨d, rfl, by simpa [hjd] using hs⟩
    have hdj : t.val.subtreeAt (pw ++ [j]) = some d := by simp [subtreeAt_append, hpw, hj]
    obtain ⟨w, hw, hwv⟩ := PlanarSyntacticObject.exists_mem_terms_of_subtreeAt hpw
    obtain ⟨z, hz, hzv⟩ := PlanarSyntacticObject.exists_mem_terms_of_subtreeAt hdj
    refine ⟨z, hz, ⟨w, hw, ?_, ?_, ?_⟩, ?_⟩
    · show (SyntacticObject.leaf ℓ).val ∈ w.val.children
      rw [hwv, UnorderedTree.children_mk, Multiset.mem_coe, List.mem_map]
      exact ⟨c, List.mem_of_getElem? hi, (PlanarSyntacticObject.mk_eq_leaf_iff hci).2 hcv⟩
    · show z.val ∈ w.val.children
      rw [hwv, hzv, UnorderedTree.children_mk, Multiset.mem_coe]
      exact List.mem_map_of_mem (List.mem_of_getElem? hj)
    · intro hlz
      have hd : d.value = Vertex.lex ℓ :=
        (PlanarSyntacticObject.mk_eq_leaf_iff hdj).1 (hzv ▸ congrArg Subtype.val hlz.symm)
      have he := congrArg TreePath.toList
        ((hocc' ⟨pw ++ [j]⟩).1 (mem_occurrences_iff.2 ⟨d, hdj, hd⟩))
      rw [hpi] at he
      exact hij (by simpa using he)
    · refine mem_terms.1 ?_
      rw [← Multiset.mem_map_of_injective Subtype.val_injective, map_val_terms, hzv]
      exact RoseTree.mem_unorderedSubtrees.2 ⟨r, s, hds, hsx⟩

/-- The positions in the interior at `h` carry the terms within the complement of a token
occurring once, at `h`, and projecting wherever it occurs. -/
theorem withinComplement_iff_exists_mem_interior {t : PlanarSyntacticObject} {ℓ : LIToken}
    {h : TreePath} (hocc : occurrences t ℓ = [h])
    (hproj : ∀ m ∈ (t : SyntacticObject).terms,
      immediatelyContains m (SyntacticObject.leaf ℓ) → m.raisingHead = some ℓ)
    (x : SyntacticObject) :
    (t : SyntacticObject).WithinComplement ℓ x ↔
      ∃ q s, t.val.subtreeAt q.toList = some s ∧ UnorderedTree.mk s = x.val ∧ q ∈ interior t h := by
  rw [← mem_phaseInterior, phaseInterior_eq_domainIn hproj, mem_domainIn]
  exact cCommandsIn_leaf_iff hocc x

/-- A link of the chain of `tok` leaves the phase headed at `h` when it runs from the interior to
a position outside the head's maximal projection; the Phase Impenetrability Condition forbids it,
and a link to the edge does not leave. -/
def Crosses (h : TreePath) : Prop :=
  ∃ x ∈ links t tok, x.2 ∈ interior t h ∧ ¬ projectionAt t h ≤ x.1

instance (h : TreePath) : Decidable (Crosses t tok h) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A link of the chain of `tok` leaves the domain at `D` when it runs from inside `D` to outside,
as movement out of an island does. -/
def Escapes (D : TreePath) : Prop := ∃ x ∈ links t tok, D ≤ x.2 ∧ ¬ D ≤ x.1

instance (D : TreePath) : Decidable (Escapes t tok D) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem not_crosses_of_length_le_one (h : (chain t tok).length ≤ 1) (hd : TreePath) :
    ¬ Crosses t tok hd := by
  simp [Crosses, links_eq_nil_of_length_le_one t tok h]

theorem not_escapes_of_length_le_one (h : (chain t tok).length ≤ 1) (D : TreePath) :
    ¬ Escapes t tok D := by
  simp [Escapes, links_eq_nil_of_length_le_one t tok h]

end Minimalist
