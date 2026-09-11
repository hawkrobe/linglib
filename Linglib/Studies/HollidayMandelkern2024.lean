import Linglib.Semantics.Modality.Orthologic.Lifting
import Linglib.Semantics.Modality.Orthologic.RegularProp
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# Holliday and Mandelkern (2024): The orthologic of epistemic modals

This file formalizes [holliday-mandelkern-2024]'s possibility semantics for epistemic modals on
the paper's running example, the Epistemic Scale: the epistemic frame of the two-world Boolean
algebra of a coin flip (Example 5.3), whose five possibilities `x1`–`x5` run from knowing `p`
through settling `p`, full uncertainty and settling `¬p` to knowing `¬p`. The frame is built by
the general construction `Orthologic.epistemicFrame`, so the compatibility path of Figure 7 and
the accessibility relation of Figure 12 are derived rather than stipulated (`compat_iff`,
`access_iff`), and the truth values of Figure 13 follow by decision. On this model the desiderata
of §2 hold: Wittgenstein sentences are contradictions in both orders, while `◇¬p` does not
entail `¬p` and `p` does not entail `□p`; distributivity, disjunctive syllogism, orthomodularity
and pseudocomplementation fail at the point of full uncertainty `x3`, as the algebraic
Example 3.20 predicts; De Morgan's laws hold and `□¬p ∨ □p` is not a logical truth, the
contrasts (29) and (30) with state-based semantics. Levelwise classicality (Example 4.42) is
checked through the criterion of Proposition 4.39: within the Boolean level and within the modal
level `Level1`, compatible witnesses of two propositions always yield a common witness
(`stratified_level1`), while across levels `p` and `◇¬p` have compatible witnesses but no common
one.

## Implementation notes

* The Boolean algebra is `Finset (Fin 2)`, so every claim about the Scale is decidable; the
  general Lemma 5.4 is the substrate's `mem_box_embed` and `mem_diamond_embed`, and
  Theorem 5.7.4 is instantiated as `diamond_P_not_subset`.
* The paper contrasts its symmetric Wittgenstein's Law with the order asymmetry of dynamic
  semantics (§6); the update-semantic side is `UpdateSemantics.might_order_matters`, and no
  theorem here conjoins the two.
* The Epistemic Grid (Example 4.34), the logics EO and EO+ together with the completeness
  theorems for them, and the remaining principles of Proposition 5.12 are not formalized.

## References

* [holliday-mandelkern-2024]
-/

namespace HollidayMandelkern2024

open Orthologic Orthologic.Possibility

/-- The two-world Boolean algebra of the coin flip, Example 5.3. -/
abbrev Coin := Finset (Fin 2)

/-- The possibilities of the epistemic frame of `Coin`. -/
abbrev Poss := Possibility Coin

/-- The Epistemic Scale's modal compatibility frame. -/
abbrev scale : ModalCompatFrame Poss := (epistemicFrame Coin).toModalCompatFrame

/-- The Epistemic Scale's compatibility frame. -/
abbrev frame : CompatFrame Poss := scale.toCompatFrame

instance : DecidableRel scale.access := inferInstanceAs (DecidableRel (access (B := Coin)))

instance : DecidableRel frame.compat := inferInstanceAs (DecidableRel (compat (B := Coin)))

instance : DecidableRel scale.compat := inferInstanceAs (DecidableRel (compat (B := Coin)))

/-- Knows `p`: `({0}, {0})`. -/
def x1 : Poss := ⟨({0}, {0}), by decide⟩

/-- Settles `p` without knowing it: `({0}, {0, 1})`. -/
def x2 : Poss := ⟨({0}, {0, 1}), by decide⟩

/-- Full uncertainty: `({0, 1}, {0, 1})`. -/
def x3 : Poss := ⟨({0, 1}, {0, 1}), by decide⟩

/-- Settles `¬p` without knowing it: `({1}, {0, 1})`. -/
def x4 : Poss := ⟨({1}, {0, 1}), by decide⟩

/-- Knows `¬p`: `({1}, {1})`. -/
def x5 : Poss := ⟨({1}, {1}), by decide⟩

/-- Two worlds give five possibilities, the first row of Table 1. -/
theorem card_poss : Fintype.card Poss = 5 := by decide

/-- Figure 7 and Example 5.3: compatibility is the path `x1 — x2 — x3 — x4 — x5`. -/
theorem compat_iff : ∀ x y : Poss, frame.compat x y ↔ x = y ∨
    (x, y) ∈ [(x1, x2), (x2, x1), (x2, x3), (x3, x2), (x3, x4), (x4, x3), (x4, x5), (x5, x4)] := by
  decide

/-- Figure 12 and Example 5.3: `x2` accesses `x1` and `x3`, `x4` accesses `x3` and `x5`, and
every possibility accesses itself. -/
theorem access_iff : ∀ x y : Poss, scale.access x y ↔ x = y ∨
    (x, y) ∈ [(x2, x1), (x2, x3), (x4, x3), (x4, x5)] := by
  decide

/-- The proposition that the coin lands `0`, the embedded `{0}`. -/
abbrev P : Set Poss := embed ({0} : Coin)

/-- `¬p`. -/
abbrev nP : Set Poss := orthoNeg frame P

/-- `□p`. -/
abbrev bP : Set Poss := box scale P

/-- `□¬p`. -/
abbrev bnP : Set Poss := box scale nP

/-- `◇p`. -/
abbrev dP : Set Poss := diamond scale P

/-- `◇¬p`. -/
abbrev dnP : Set Poss := diamond scale nP

instance : DecidablePred (· ∈ P) := inferInstance
instance : DecidablePred (· ∈ nP) := inferInstance
instance : DecidablePred (· ∈ bP) := inferInstance
instance : DecidablePred (· ∈ bnP) := inferInstance
instance : DecidablePred (· ∈ dP) := inferInstance
instance : DecidablePred (· ∈ dnP) := inferInstance

/-! ### Example 4.33: the truth values of Figure 13 -/

theorem mem_P : ∀ x : Poss, x ∈ P ↔ x = x1 ∨ x = x2 := by decide

theorem mem_nP : ∀ x : Poss, x ∈ nP ↔ x = x4 ∨ x = x5 := by decide

theorem mem_bP : ∀ x : Poss, x ∈ bP ↔ x = x1 := by decide

theorem mem_bnP : ∀ x : Poss, x ∈ bnP ↔ x = x5 := by decide

theorem mem_dP : ∀ x : Poss, x ∈ dP ↔ x = x1 ∨ x = x2 ∨ x = x3 := by decide

theorem mem_dnP : ∀ x : Poss, x ∈ dnP ↔ x = x3 ∨ x = x4 ∨ x = x5 := by decide

/-- `◇p ∧ ◇¬p` holds only at the point of full uncertainty. -/
theorem mem_dP_inter_dnP : ∀ x : Poss, x ∈ dP ∩ dnP ↔ x = x3 := by decide

/-- `□p ∨ □¬p` holds exactly where something is known. -/
theorem mem_bP_disj_bnP : ∀ x : Poss, x ∈ disj frame bP bnP ↔ x = x1 ∨ x = x5 := by decide

instance (s : Finset Poss) : DecidablePred (· ∈ (↑s : Set Poss)) :=
  λ x => inferInstanceAs (Decidable (x ∈ s))

/-- Example 4.11: the compatibility frame has ten regular subsets. -/
theorem card_regular :
    ((Finset.univ : Finset (Finset Poss)).filter
      λ s : Finset Poss => IsRegular frame (↑s : Set Poss)).card = 10 := by
  decide

/-! ### The desiderata of §2 on the Scale -/

/-- (2) and (3): Wittgenstein sentences of both orders are contradictions, by Proposition 4.27
applied to `p` and to `¬p`, using that `¬¬p = p` for the regular `p`. -/
theorem wittgenstein : nP ∩ dP = ∅ ∧ P ∩ dnP = ∅ :=
  ⟨(epistemicFrame Coin).wittgensteinLaw P,
    by simpa only [orthoNeg_orthoNeg_of_isRegular frame (embed_isRegular _)] using
      (epistemicFrame Coin).wittgensteinLaw nP⟩

/-- §1: `◇¬p` does not entail `¬p`, and §2: `p` does not entail `□p`, the coin whose outcome is
unknown. -/
theorem diamond_neg_not_entail_neg : x3 ∈ dnP ∧ x3 ∉ nP := by decide

theorem not_entail_box : x2 ∈ P ∧ x2 ∉ bP := by decide

/-- (10) and Example 4.33: `(p ∨ ¬p) ∧ (◇p ∧ ◇¬p)` holds at `x3` but its distribution
`(p ∧ ◇¬p) ∨ (¬p ∧ ◇p)` does not. -/
theorem distributivity_fails :
    x3 ∈ disj frame P nP ∩ (dP ∩ dnP) ∧ x3 ∉ disj frame (P ∩ dnP) (nP ∩ dP) := by
  decide

/-- (13): `p ∨ □¬p` is a logical truth and `¬□¬p` holds at `x3`, yet `p` does not. -/
theorem disjunctive_syllogism_fails :
    (∀ x : Poss, x ∈ disj frame P bnP) ∧ x3 ∈ orthoNeg frame bnP ∧ x3 ∉ P := by
  decide

/-- (21) and Example 3.20: `p` entails `◇p`, but `◇p` does not entail `p ∨ (¬p ∧ ◇p)`. -/
theorem orthomodularity_fails :
    (∀ x : Poss, x ∈ P → x ∈ dP) ∧ x3 ∈ dP ∧ x3 ∉ disj frame P (nP ∩ dP) := by
  decide

/-- Example 3.20: `p ∧ ◇¬p = ⊥` although `◇¬p ≰ ¬p`, so orthonegation is not
pseudocomplementation. -/
theorem pseudocomplementation_fails : P ∩ dnP = ∅ ∧ x3 ∈ dnP ∧ x3 ∉ nP :=
  ⟨wittgenstein.2, by decide, by decide⟩

/-- (29): `◇p ∧ ◇¬p` is equivalent to `¬(□¬p ∨ □p)`, De Morgan's law. -/
theorem deMorgan : ∀ x : Poss, x ∈ dP ∩ dnP ↔ x ∈ orthoNeg frame (disj frame bnP bP) := by
  decide

/-- (30): `□¬p ∨ □p` is not a logical truth. -/
theorem not_known_either : x3 ∉ disj frame bnP bP := by decide

/-- Theorem 5.7.4: the diamond of `p` does not collapse to `p`. -/
theorem diamond_P_not_subset : ¬ dP ⊆ P :=
  not_diamond_embed_subset (by decide) (by decide)

/-! ### Example 4.42: levelwise classicality -/

/-- The Boolean level `B0 = {∅, p, ¬p, ⊤}`. -/
inductive Level0
  | bot
  | p
  | np
  | top
  deriving DecidableEq, Fintype

/-- The propositions of `B0`. -/
def Level0.set : Level0 → Set Poss
  | .bot => ∅
  | .p => P
  | .np => nP
  | .top => Set.univ

instance : ∀ l : Level0, DecidablePred (· ∈ l.set)
  | .bot => inferInstanceAs (DecidablePred (· ∈ (∅ : Set Poss)))
  | .p => inferInstanceAs (DecidablePred (· ∈ P))
  | .np => inferInstanceAs (DecidablePred (· ∈ nP))
  | .top => inferInstanceAs (DecidablePred (· ∈ (Set.univ : Set Poss)))

/-- The modal level `B1`, the eight propositions of Example 3.33. -/
inductive Level1
  | bot
  | bp
  | dnp
  | dp
  | bnp
  | knownEither
  | uncertain
  | top
  deriving DecidableEq, Fintype

/-- The propositions of `B1`. -/
def Level1.set : Level1 → Set Poss
  | .bot => ∅
  | .bp => bP
  | .dnp => dnP
  | .dp => dP
  | .bnp => bnP
  | .knownEither => disj frame bP bnP
  | .uncertain => dP ∩ dnP
  | .top => Set.univ

instance : ∀ l : Level1, DecidablePred (· ∈ l.set)
  | .bot => inferInstanceAs (DecidablePred (· ∈ (∅ : Set Poss)))
  | .bp => inferInstanceAs (DecidablePred (· ∈ bP))
  | .dnp => inferInstanceAs (DecidablePred (· ∈ dnP))
  | .dp => inferInstanceAs (DecidablePred (· ∈ dP))
  | .bnp => inferInstanceAs (DecidablePred (· ∈ bnP))
  | .knownEither => inferInstanceAs (DecidablePred (· ∈ disj frame bP bnP))
  | .uncertain => inferInstanceAs (DecidablePred (· ∈ dP ∩ dnP))
  | .top => inferInstanceAs (DecidablePred (· ∈ (Set.univ : Set Poss)))

/-- `B1` is closed under orthonegation and meet, and its members are regular. -/
theorem level1_closed :
    (∀ l : Level1, IsRegular frame l.set) ∧
    (∀ l : Level1, ∃ m : Level1, ∀ x, x ∈ orthoNeg frame l.set ↔ x ∈ m.set) ∧
    (∀ l m : Level1, ∃ n : Level1, ∀ x, x ∈ l.set ∩ m.set ↔ x ∈ n.set) := by
  refine ⟨by decide, by decide, by decide⟩

/-- Proposition 4.39's criterion within `B0`: compatible witnesses of two propositions yield a
common witness, so `B0` is Boolean. -/
theorem stratified_level0 :
    ∀ l m : Level0, (∃ x ∈ l.set, ∃ y ∈ m.set, frame.compat x y) →
      ∃ z, z ∈ l.set ∧ z ∈ m.set := by
  decide

/-- Proposition 4.39's criterion within `B1`, so `B1` is an eight-element Boolean algebra. -/
theorem stratified_level1 :
    ∀ l m : Level1, (∃ x ∈ l.set, ∃ y ∈ m.set, frame.compat x y) →
      ∃ z, z ∈ l.set ∧ z ∈ m.set := by
  decide

/-- Across levels the criterion fails: `x2` settles `p`, `x3` settles `◇¬p`, the two are
compatible, and nothing settles both. -/
theorem not_stratified_across_levels :
    x2 ∈ P ∧ x3 ∈ dnP ∧ frame.compat x2 x3 ∧ ∀ z : Poss, z ∉ P ∩ dnP := by
  decide

end HollidayMandelkern2024
