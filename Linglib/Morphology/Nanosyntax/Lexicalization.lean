module

public import Linglib.Morphology.Nanosyntax.TreeSpellout

/-!
# Nanosyntax: the lexicalization algorithm

In nanosyntax features merge one at a time, and the phrase a merger creates must be lexicalized
before the next feature merges. Starke's algorithm says what happens when no entry matches the
new phrase. Material evacuates from the complement of the new feature, first the constituent
holding the bottom of the sequence and then ever larger constituents around it, until the remnant
is lexicalized. If no evacuation helps, the derivation returns to the previous merger and takes
its next option. An evacuated constituent keeps its exponent and the remnant gets one of its own,
so evacuation is what makes a suffix, and an entry that matches the whole new phrase overrides
the exponents inside it.

## Main definitions

* `mergeOptions`: the ways of lexicalizing a merger, in order of preference.
* `derivations`: the derivations of a feature sequence, in order of preference.
* `lexicalize`, `exponents`: the first derivation and its exponents.

## Main results

* `derivations_append`: deriving a sequence is deriving its first part and then, from each
  result in turn, the rest, which is backtracking.
* `exists_matches_of_mem_lexicalize`: every constituent of the derivation is matched by an entry
  carrying its exponent.
* `exponents_cons_of_forall_leaf`, `exponents_ofSupersetRule`: where no entry lexicalizes a
  feature above the bottom alone the algorithm never evacuates, so on a lexicon of containment
  entries its one exponent is the containment engine's spellout.

## Implementation notes

* A derivation is the row of constituents under its unlabelled root. Evacuation leaves no trace
  and projects no label, so the constituents to the right of the first are remnants and a
  remnant with nothing left in it is a leaf.
* `mergeOptions` follows the pied-piping formulation of the algorithm, which adds evacuations
  to Starke's original steps. On a lexicon whose trees do not branch only the original ones can
  be lexicalized (`length_le_of_mem_mergeOptions`).

## TODO

* The algorithm's last resort, a specifier built in a workspace of its own, which is where
  prefixes come from. The literature differs on what such a derivation starts from.
* Entries storing a whole row of constituents under an unlabelled root, and the override of a
  row they bring, by which De Clercq and colleagues derive inverse number marking.

## References

* [starke-2018]
* [declercq-et-al-2025]
* [caha-2009]
-/

@[expose] public section

namespace Morphology.Nanosyntax

open Morphology.Exponence RoseTree

variable {F α : Type*} [DecidableEq F] {L : RuleSet (LexicalEntry F α)} {f : F}

/-- A derivation in progress is the row of lexicalized constituents under its unlabelled root,
the one holding the bottom of the feature sequence first and the remnants of evacuation after
it, each with the exponent of the entry lexicalizing it. -/
abbrev Derivation (F α : Type*) := List (RoseTree F × α)

/-! ### One merger -/

/-- The ways of lexicalizing the merger of a feature with a derivation, in order of preference.
The new phrase is lexicalized whole, or the first `j` constituents of its complement evacuate
and the remnant is lexicalized, for `j` from one up to all of them. -/
def mergeOptions (L : RuleSet (LexicalEntry F α)) (d : Derivation F α) (f : F) :
    List (Derivation F α) :=
  (List.range (d.length + 1)).filterMap fun j ↦
    (treeSpellout L (node f ((d.drop j).map Prod.fst))).map fun x ↦
      d.take j ++ [(node f ((d.drop j).map Prod.fst), x)]

theorem mem_mergeOptions {d d' : Derivation F α} :
    d' ∈ mergeOptions L d f ↔ ∃ j ≤ d.length, ∃ x,
      treeSpellout L (node f ((d.drop j).map Prod.fst)) = some x ∧
        d' = d.take j ++ [(node f ((d.drop j).map Prod.fst), x)] := by
  simp only [mergeOptions, List.mem_filterMap, List.mem_range, Nat.lt_succ_iff,
    Option.map_eq_some_iff]
  simp only [eq_comm]

/-- The first feature is lexicalized as a phrase of its own. -/
theorem mergeOptions_nil (L : RuleSet (LexicalEntry F α)) (f : F) :
    mergeOptions L [] f = ((treeSpellout L (leaf f)).map fun x ↦ [(leaf f, x)]).toList := by
  cases h : treeSpellout L (leaf f) <;> simp [mergeOptions, h]

/-- A feature merged with a single constituent is lexicalized together with it, or else the
constituent evacuates and the feature is lexicalized alone, as a suffix. -/
theorem mergeOptions_singleton (L : RuleSet (LexicalEntry F α)) (t : RoseTree F) (x : α) (f : F) :
    mergeOptions L [(t, x)] f =
      ((treeSpellout L (node f [t])).map fun y ↦ [(node f [t], y)]).toList ++
        ((treeSpellout L (leaf f)).map fun y ↦ [(t, x), (leaf f, y)]).toList := by
  cases h : treeSpellout L (node f [t]) <;> cases h' : treeSpellout L (leaf f) <;>
    simp [mergeOptions, List.range_succ, h, h']

/-- On a lexicon whose stored trees do not branch a merger never fuses constituents. It grows
the last one, everything before it evacuating, or adds one, everything evacuating, which are
the specifier-to-specifier and complement movements of Starke's original steps. -/
theorem length_le_of_mem_mergeOptions
    (hL : ∀ e ∈ L, ∀ t, IsSubtree t e.tree → t.children.length ≤ 1) {d d' : Derivation F α}
    (h : d' ∈ mergeOptions L d f) : d.length ≤ d'.length := by
  obtain ⟨j, hj, x, hx, rfl⟩ := mem_mergeOptions.1 h
  obtain ⟨e, he, -, hw⟩ := treeSpellout_isElsewhereWinner hx
  have := hL e he _ hw.1.2
  simp only [children_node, List.length_map, List.length_drop] at this
  simp only [List.length_append, List.length_take, List.length_singleton]
  omega

/-! ### Derivations -/

/-- The derivations of a feature sequence from a derivation, in order of preference. Each
merger takes its options in turn and the rest of the sequence is derived from each. -/
def derivations (L : RuleSet (LexicalEntry F α)) :
    Derivation F α → List F → List (Derivation F α)
  | d, [] => [d]
  | d, f :: fs => (mergeOptions L d f).flatMap (derivations L · fs)

@[simp] theorem derivations_nil (d : Derivation F α) : derivations L d [] = [d] := rfl

@[simp] theorem derivations_cons (d : Derivation F α) (f : F) (fs : List F) :
    derivations L d (f :: fs) = (mergeOptions L d f).flatMap (derivations L · fs) := rfl

theorem derivations_singleton (d : Derivation F α) (f : F) :
    derivations L d [f] = mergeOptions L d f := by simp

/-- Deriving a sequence is deriving its first part and then the rest from each result in turn,
so a failure in the rest returns to the latest merger of the first part with an option left. -/
theorem derivations_append (d : Derivation F α) (fs gs : List F) :
    derivations L d (fs ++ gs) = (derivations L d fs).flatMap (derivations L · gs) := by
  induction fs generalizing d with
  | nil => simp
  | cons f fs ih => simp [ih, List.flatMap_assoc]

/-- The lexicalization algorithm returns the first derivation of a feature sequence, the bottom
of the sequence first. -/
def lexicalize (L : RuleSet (LexicalEntry F α)) (fs : List F) : Option (Derivation F α) :=
  (derivations L [] fs).head?

/-- The exponents the algorithm gives a feature sequence, in linear order. -/
def exponents (L : RuleSet (LexicalEntry F α)) (fs : List F) : Option (List α) :=
  (lexicalize L fs).map (·.map Prod.snd)

/-- A sequence of two features gets one exponent for its whole phrase, or else the exponent
of its first feature followed by a suffix for the second. -/
theorem exponents_pair (L : RuleSet (LexicalEntry F α)) (f₁ f₂ : F) :
    exponents L [f₁, f₂] = (treeSpellout L (leaf f₁)).bind fun x ↦
      ((treeSpellout L (node f₂ [leaf f₁])).map fun y ↦ [y]) <|>
        (treeSpellout L (leaf f₂)).map fun y ↦ [x, y] := by
  simp only [exponents, lexicalize, derivations_cons, derivations_nil, mergeOptions_nil]
  rcases treeSpellout L (leaf f₁) with - | x
  · rfl
  · simp only [Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, mergeOptions_singleton]
    rcases treeSpellout L (node f₂ [leaf f₁]) with - | y <;>
      rcases treeSpellout L (leaf f₂) with - | z <;> rfl

/-! ### Soundness -/

private theorem exists_matches_of_mem_derivations {d d' : Derivation F α} {fs : List F}
    (hd : ∀ p ∈ d, ∃ e ∈ L, e.Matches p.1 ∧ e.exponent = p.2) (h : d' ∈ derivations L d fs) :
    ∀ p ∈ d', ∃ e ∈ L, e.Matches p.1 ∧ e.exponent = p.2 := by
  induction fs generalizing d with
  | nil => exact List.mem_singleton.1 h ▸ hd
  | cons f fs ih =>
    obtain ⟨d₁, h₁, h⟩ := List.mem_flatMap.1 h
    obtain ⟨j, -, x, hx, rfl⟩ := mem_mergeOptions.1 h₁
    refine ih (fun p hp ↦ ?_) h
    rcases List.mem_append.1 hp with hp | hp
    · exact hd p (List.mem_of_mem_take hp)
    · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hx
      exact List.mem_singleton.1 hp ▸
        ⟨e, RuleSet.selectBy_mem he, RuleSet.selectBy_applies he, rfl⟩

/-- Every constituent of the derivation the algorithm returns is matched by an entry carrying
its exponent. -/
theorem exists_matches_of_mem_lexicalize {d : Derivation F α} {fs : List F}
    (h : lexicalize L fs = some d) {p : RoseTree F × α} (hp : p ∈ d) :
    ∃ e ∈ L, e.Matches p.1 ∧ e.exponent = p.2 :=
  exists_matches_of_mem_derivations (fun _ h ↦ absurd h List.not_mem_nil)
    (List.mem_of_mem_head? h) p hp

/-! ### Lexicons without suffixes -/

/-- Where no entry lexicalizes a feature alone, merging it with a single constituent can only
grow the constituent. -/
theorem mergeOptions_singleton_of_leaf (h : treeSpellout L (leaf f) = none) (t : RoseTree F)
    (x : α) : mergeOptions L [(t, x)] f =
      ((treeSpellout L (node f [t])).map fun y ↦ [(node f [t], y)]).toList := by
  simp [mergeOptions_singleton, h]

/-- Where no entry lexicalizes a feature above the bottom alone, the algorithm never evacuates,
and the sequence has at most one derivation, its one phrase lexicalized whole. -/
theorem derivations_cons_of_forall_leaf (f₀ : F) {fs : List F}
    (h : ∀ f ∈ fs, treeSpellout L (leaf f) = none) :
    derivations L [] (f₀ :: fs) =
      ((treeSpellout L (phrase f₀ fs)).map fun x ↦ [(phrase f₀ fs, x)]).toList := by
  induction fs using List.reverseRecOn with
  | nil => simp [mergeOptions_nil]
  | append_singleton fs f ih =>
    rw [← List.cons_append, derivations_append, ih fun g hg ↦ h g (List.mem_append_left _ hg),
      phrase_concat]
    rcases hx : treeSpellout L (phrase f₀ fs) with - | x
    · simp [treeSpellout_eq_none_of_isSubtree
        (.of_mem_children (t := node f [phrase f₀ fs]) (List.mem_singleton_self _)) hx]
    · simp [mergeOptions_singleton_of_leaf (h f (by simp))]

/-- Where no entry lexicalizes a feature above the bottom alone, the sequence gets a single
exponent, that of its one phrase, or none. -/
theorem exponents_cons_of_forall_leaf (f₀ : F) {fs : List F}
    (h : ∀ f ∈ fs, treeSpellout L (leaf f) = none) :
    exponents L (f₀ :: fs) = (treeSpellout L (phrase f₀ fs)).map fun x ↦ [x] := by
  rw [exponents, lexicalize, derivations_cons_of_forall_leaf f₀ h]
  cases treeSpellout L (phrase f₀ fs) <;> rfl

theorem exponents_singleton (L : RuleSet (LexicalEntry F α)) (f : F) :
    exponents L [f] = (treeSpellout L (leaf f)).map fun x ↦ [x] :=
  exponents_cons_of_forall_leaf f (fs := []) fun _ h ↦ absurd h List.not_mem_nil

section Containment

variable {n : ℕ} {feat : ℕ → F}

/-- No entry of the containment engine lexicalizes a feature above the bottom alone, each
storing a chain down to the bottom. -/
theorem treeSpellout_ofSupersetRule_leaf (hf : feat.Injective)
    (v : RuleSet (Containment.SupersetRule n α)) (k : ℕ) :
    treeSpellout (v.map (LexicalEntry.ofSupersetRule feat)) (leaf (feat (k + 1))) = none := by
  refine treeSpellout_eq_none_iff.2 fun e he hm ↦ ?_
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 he
  obtain ⟨j, -, hj⟩ := eq_chainTree_of_isSubtree hm
  obtain rfl : j = 0 := by simpa [chainTree_numNodes] using (congrArg numNodes hj).symm
  exact absurd (hf (node.inj hj).1) (Nat.succ_ne_zero k)

/-- On a lexicon of containment entries the algorithm never evacuates, and it gives each grade
the single exponent the containment engine spells out there. -/
theorem exponents_ofSupersetRule (hf : feat.Injective)
    (v : RuleSet (Containment.SupersetRule n α)) (g : Fin n) :
    exponents (v.map (LexicalEntry.ofSupersetRule feat)) ((List.range ((g : ℕ) + 1)).map feat) =
      (Containment.spellout v g).map fun x ↦ [x] := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, exponents_cons_of_forall_leaf,
    ← chainTree_eq_phrase, treeSpellout_ofSupersetRule]
  intro f hf'
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hf'
  exact treeSpellout_ofSupersetRule_leaf hf v k

end Containment

end Morphology.Nanosyntax
