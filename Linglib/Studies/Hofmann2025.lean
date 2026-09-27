module

public import Linglib.Data.Examples.Hofmann2025
public import Linglib.Semantics.Dynamic.Update

/-!
# Hofmann (2025): Anaphoric Accessibility with Flat Update

This file formalizes [hofmann-2025]'s account of anaphora to negated indefinites in
Intensional CDRT, her intensional extension of the Compositional DRT of [muskens-1996], whose
discourse states assign individual concepts to individual drefs and propositions to
propositional drefs. Indefinites introduce their discourse referent globally, relative to the
propositional dref of their local context, and a pronoun is acceptable when its referent exists
throughout its own local context under a consistent assignment of speaker commitments (38).
The veridical, hypothetical and counterfactual drefs of (16) are defined relative to a
speaker's commitment set. The subset requirement (39)
follows from relative variable update (`localEntailment_iff_subset`), and a veridical anaphor
context admits only veridical antecedents (`veridicalIndiv_of_accessible`). The fragment of
Appendix C, `semDEC` and the sentential operators, is run on the paper's four-world model for
the bathroom discourses of §3 and §4: the veridical discourse of Figures 5 and 6, the negated
antecedent of Figure 7 whose veridical continuation no consistent extension admits
(`counterfactual_veridical_impossible`), the double negation of Figure 8, the bathroom
disjunction of Figure 9 and the disagreement of Figure 10 are outputs of the fragment's
updates from an initial state, with their pronouns accessible or not as the paper says.

## Implementation notes

* Discourse states are assignments updated relationally, the flat update of §1.2.1, not sets
  of world–assignment pairs, which footnote 6 sets aside. The falsifier ⋆ is `none`.
* The maximization operators of App. C (18) and (19), and of the displayed updates (41), (43) and
  (44), apply to updates that leave the maximized dref unchanged, so under the definition
  (40) they are vacuous (`propMaxOp_eq_of_fixes`): the fragment as printed does not exclude
  the nonmaximal rows of Table 3 (`negated_row4`). Maximizing the prejacent's context over
  the whole assertion selects the paper's row (`negated_max`), and the commitment set of
  Figure 6 is the pragmatically maximal one of (35) (`veridical_maximal`).
* Commitment sets are introduced at the initial state and never changed by an update, as in
  (33) and Table 1, so a derivation starts from the initial state whose commitment set its
  output shows; Figure 6's is narrower than Figure 5's.
* The modal-subordination discourse of §4.4 needs the eight-world model with a doxastic state
  for Sue and is not run.

## TODO

* The eight-world model of §4.4 and the attitude update (52).

## References

* [hofmann-2025]
* [muskens-1996]
* [stone-1999]
* [brasoveanu-2006]
* [krahmer-muskens-1995]
* [roberts-1989]
* [karttunen-1976]
-/

@[expose] public section

namespace Hofmann2025

open DynamicSemantics
open DynamicSemantics.Update (test)
open SetRel


/-! ### Discourse states -/

/-- A propositional variable, the name of a propositional dref. -/
structure PVar where
  idx : ℕ
  deriving DecidableEq, Repr

/-- An individual variable, the name of an individual dref. -/
structure IVar where
  idx : ℕ
  deriving DecidableEq, Repr

/-- A discourse state: an individual concept for each individual dref (type `s(we)`) and a
proposition for each propositional dref (type `s(wt)`). An individual dref is `none`, the
universal falsifier ⋆, at the worlds where it has no referent. -/
structure Assignment (W E : Type*) where
  indiv : IVar → W → Option E
  prop : PVar → Set W

namespace Assignment

variable {W E : Type*}

/-- Reassign an individual dref. -/
def updateIndiv (g : Assignment W E) (v : IVar) (e : W → Option E) : Assignment W E :=
  { g with indiv := Function.update g.indiv v e }

/-- Reassign a propositional dref. -/
def updateProp (g : Assignment W E) (p : PVar) (s : Set W) : Assignment W E :=
  { g with prop := Function.update g.prop p s }

@[simp] theorem updateProp_prop_self (g : Assignment W E) (p : PVar) (s : Set W) :
    (g.updateProp p s).prop p = s := by
  simp [updateProp]

@[simp] theorem updateProp_prop_of_ne (g : Assignment W E) {p q : PVar} (h : q ≠ p)
    (s : Set W) : (g.updateProp p s).prop q = g.prop q := by
  simp [updateProp, Function.update_of_ne h]

@[simp] theorem updateProp_indiv (g : Assignment W E) (p : PVar) (s : Set W) :
    (g.updateProp p s).indiv = g.indiv := rfl

@[simp] theorem updateIndiv_prop (g : Assignment W E) (v : IVar) (e : W → Option E) :
    (g.updateIndiv v e).prop = g.prop := rfl

@[simp] theorem updateIndiv_indiv_self (g : Assignment W E) (v : IVar) (e : W → Option E) :
    (g.updateIndiv v e).indiv v = e := by
  simp [updateIndiv]

@[simp] theorem updateIndiv_indiv_of_ne (g : Assignment W E) {v u : IVar} (h : u ≠ v)
    (e : W → Option E) : (g.updateIndiv v e).indiv u = g.indiv u := by
  simp [updateIndiv, Function.update_of_ne h]

end Assignment

variable {W E : Type*}

/-! ### Variable update (App. B (9), (11); (25)) -/

/-- `i[φ]j`: `j` differs from `i` at most in the value of `φ`. -/
def PropVarUp (φ : PVar) (i j : Assignment W E) : Prop :=
  (∀ q, q ≠ φ → j.prop q = i.prop q) ∧ ∀ v, j.indiv v = i.indiv v

/-- `i[υ]j`: `j` differs from `i` at most in the value of `υ`. -/
def IndivVarUp (v : IVar) (i j : Assignment W E) : Prop :=
  (∀ p, j.prop p = i.prop p) ∧ ∀ u, u ≠ v → j.indiv u = i.indiv u

/-- `i[δ₁, …, δₙ]j` (App. B (11b)): `j` differs from `i` at most in the listed drefs. -/
def MultiVarUp (ps : List PVar) (vs : List IVar) (i j : Assignment W E) : Prop :=
  (∀ p, p ∉ ps → j.prop p = i.prop p) ∧ ∀ v, v ∉ vs → j.indiv v = i.indiv v

theorem propVarUp_updateProp (p : PVar) (i : Assignment W E) (s : Set W) :
    PropVarUp p i (i.updateProp p s) :=
  ⟨fun _ hq ↦ Assignment.updateProp_prop_of_ne i hq s, fun _ ↦ rfl⟩

theorem indivVarUp_updateIndiv (v : IVar) (i : Assignment W E) (e : W → Option E) :
    IndivVarUp v i (i.updateIndiv v e) :=
  ⟨fun _ ↦ rfl, fun _ hu ↦ Assignment.updateIndiv_indiv_of_ne i hu e⟩

/-- Relative variable update `i[φ : υ]j` (25): an update of `υ` after which `υ` has a referent
in all and only the `φ`-worlds. The biconditional, where [stone-1999] has an implication, keeps
the referent of an indefinite under negation from existing outside its local context. -/
def RelVarUp (φ : PVar) (v : IVar) (i j : Assignment W E) : Prop :=
  IndivVarUp v i j ∧ ∀ w, w ∈ j.prop φ ↔ j.indiv v w ≠ none

/-! ### Conditions (App. B (7), (8); (27), (28)) -/

/-- Inclusion `φ₁ ⋐ φ₂` (App. B (7c)). -/
def DynInclusion (φ₁ φ₂ : PVar) (i : Assignment W E) : Prop := i.prop φ₁ ⊆ i.prop φ₂

/-- `φ₁ ≡ φ̄₂`, the condition negation places on its context and its prejacent's ((21a); App. B
(7b), (8a)). -/
def IsComplement (φ₁ φ₂ : PVar) (i : Assignment W E) : Prop := i.prop φ₁ = (i.prop φ₂)ᶜ

/-- Dynamic predication `R_φ(υ)` (27): `R` holds of `υ`'s referent at every world of the local
context `φ`. The falsifier ⋆ satisfies no relation (29). -/
def DynPred (R : E → W → Prop) (φ : PVar) (v : IVar) (i : Assignment W E) : Prop :=
  ∀ w ∈ i.prop φ,
    match i.indiv v w with
    | some e => R e w
    | none => False

/-- (29a): a dref without a referent at a world of the local context falsifies predication. -/
theorem not_dynPred_of_eq_none {R : E → W → Prop} {φ : PVar} {v : IVar} {i : Assignment W E}
    {w : W} (hw : w ∈ i.prop φ) (h : i.indiv v w = none) : ¬DynPred R φ v i := fun hp ↦ by
  simpa [h] using hp w hw

/-- `υ` is entailed in the context of `φ` (28): it has a referent at every `φ`-world. -/
def LocalEntailment (φ : PVar) (v : IVar) (i : Assignment W E) : Prop :=
  ∀ w ∈ i.prop φ, i.indiv v w ≠ none

/-! ### Commitment and veridicality ((16), (36), (37)) -/

/-- A veridical individual dref (36a): entailed in the commitment set. A dref is hypothetical
when it is not veridical (16b). -/
abbrev VeridicalIndiv (φ_DC : PVar) (v : IVar) (i : Assignment W E) : Prop :=
  LocalEntailment φ_DC v i

/-- A counterfactual individual dref (37a): without a referent throughout the commitment set. -/
def CounterfactualIndiv (φ_DC : PVar) (v : IVar) (i : Assignment W E) : Prop :=
  ∀ w ∈ i.prop φ_DC, i.indiv v w = none

/-- A counterfactual propositional dref (37b): disjoint from the commitment set. -/
def CounterfactualProp (φ_DC δ : PVar) (i : Assignment W E) : Prop :=
  i.prop φ_DC ∩ i.prop δ = ∅

/-- Under consistent commitments a counterfactual dref is not veridical, so it is hypothetical,
"more specifically, counterfactual" (16). -/
theorem CounterfactualIndiv.not_veridicalIndiv {φ_DC : PVar} {v : IVar} {i : Assignment W E}
    (hc : CounterfactualIndiv φ_DC v i) (hDC : (i.prop φ_DC).Nonempty) :
    ¬VeridicalIndiv φ_DC v i := fun hv ↦
  let ⟨w, hw⟩ := hDC; hv w hw (hc w hw)

/-- The condition of assertion ((20a); App. C (19)): the speaker's commitments entail the asserted
context. -/
abbrev DecCondition (φ_DC φ : PVar) (i : Assignment W E) : Prop := DynInclusion φ_DC φ i

/-- Negation under assertion makes its prejacent counterfactual: the commitments entail the
negation's context, the complement of the prejacent's. -/
theorem counterfactualProp_of_isComplement {φ_DC φ φ' : PVar} {i : Assignment W E}
    (hc : IsComplement φ φ' i) (hdec : DecCondition φ_DC φ i) : CounterfactualProp φ_DC φ' i :=
  Set.eq_empty_of_forall_notMem fun _ ⟨hw, hw'⟩ ↦ (hc ▸ hdec hw) hw'

/-! ### Accessibility ((38), (39)) -/

/-- Accessibility (38): `υ` is entailed in the anaphor's local context `φ` and the commitment
set is consistent. The paper's consistency (31) covers every interlocutor; this is one
interlocutor's. -/
def Accessible (φ : PVar) (v : IVar) (φ_DC : PVar) (i : Assignment W E) : Prop :=
  LocalEntailment φ v i ∧ (i.prop φ_DC).Nonempty

/-- The subset requirement (39): the anaphor's context lies within the antecedent's. -/
abbrev SubsetReq (φ_anaphor φ_antecedent : PVar) (i : Assignment W E) : Prop :=
  DynInclusion φ_anaphor φ_antecedent i

/-- A counterfactual antecedent admits no veridical anaphor (§3.4.2, (26)): an extension that
keeps the commitment set and the antecedent's context, entails the anaphor's context in the
commitments, and places it within the antecedent's, empties the commitment set. -/
theorem counterfactual_blocks_veridical (i j : Assignment W E) (φ_DC φ_anaphor φ_neg : PVar)
    (h_extends_DC : j.prop φ_DC = i.prop φ_DC) (h_extends_neg : j.prop φ_neg = i.prop φ_neg)
    (h_disjoint : CounterfactualProp φ_DC φ_neg i) (h_dec : DecCondition φ_DC φ_anaphor j)
    (h_subset : SubsetReq φ_anaphor φ_neg j) : ¬(j.prop φ_DC).Nonempty := by
  rintro ⟨w, hw⟩
  have hmem : w ∈ i.prop φ_DC ∩ i.prop φ_neg :=
    ⟨h_extends_DC ▸ hw, h_extends_neg ▸ h_subset (h_dec hw)⟩
  rw [h_disjoint] at hmem
  exact hmem

/-! ### Maximization (40) and attitudes -/

/-- Maximization `max_φ(D)` (40): the outputs of `D` at which no other output assigns `φ` a
proper superset. -/
def propMaxOp (φ : PVar) (D : Update (Assignment W E)) : Update (Assignment W E) :=
  {(i, j) | i ~[D] j ∧ ∀ k, i ~[D] k → ¬(j.prop φ ⊂ k.prop φ)}

/-- The condition of an attitude verb (App. C (18e)): the subject's doxastic state `dox` entails the
embedded context. -/
def BelieveCondition (φ : PVar) (dox : Assignment W E → Set W) (j : Assignment W E) : Prop :=
  dox j ⊆ j.prop φ

/-! ### Accessibility (38) and the subset requirement (39) -/

/-- The subset requirement (39): once `v` is introduced relative to `φ₂`, it is entailed in a
context `φ₁` exactly when `φ₁` is included in `φ₂`. -/
theorem localEntailment_iff_subset {φ₁ φ₂ : PVar} {v : IVar} {i j : Assignment W E}
    (h : RelVarUp φ₂ v i j) : LocalEntailment φ₁ v j ↔ j.prop φ₁ ⊆ j.prop φ₂ :=
  ⟨fun hl w hw ↦ (h.2 w).2 (hl w hw), fun hs w hw ↦ (h.2 w).1 (hs hw)⟩

/-- In a veridical anaphor context, one the speaker's commitments entail, only a veridical
dref is accessible. -/
theorem veridicalIndiv_of_accessible {φ φ_DC : PVar} {v : IVar} {j : Assignment W E}
    (hdec : DecCondition φ_DC φ j) (h : Accessible φ v φ_DC j) : VeridicalIndiv φ_DC v j :=
  fun w hw ↦ h.1 w (hdec hw)

/-! ### The fragment of Appendix C -/

/-- The type of predicates, `e(wt)`: an individual dref and a local context to an update. -/
abbrev SemE (W E : Type*) := IVar → PVar → Update (Assignment W E)

/-- The type of clauses, `wt`: a local context to an update. -/
abbrev SemW (W E : Type*) := PVar → Update (Assignment W E)

/-- The vacuous scope of an existential: the identity update. -/
def vacuousScope : SemE W E := fun _ _ ↦ SetRel.id

/-- App. C (15): a common noun is a test that its argument satisfies it in the local context. -/
def commonNoun (R : E → W → Prop) : SemE W E :=
  fun v φ ↦ test {j | DynPred R φ v j}

/-- An intransitive verb phrase, of the same shape as a common noun. -/
abbrev intransVP (R : E → W → Prop) : SemE W E := commonNoun R

/-- App. C (16): the indefinite introduces its dref relative to the local context, then runs its
restrictor and its scope. -/
def indefinite (v : IVar) (P P' : SemE W E) (φ : PVar) : Update (Assignment W E) :=
  {(i, j) | RelVarUp φ v i j} ○ P v φ ○ P' v φ

/-- App. C (17): a pronoun passes its index to the predicate. -/
def pronoun (v : IVar) (P : SemE W E) (φ : PVar) : Update (Assignment W E) := P v φ

/-- App. C (14): a proper name introduces a dref equal to its constant. -/
def properName (name : E) (v : IVar) (P : SemE W E) (φ : PVar) : Update (Assignment W E) :=
  {(i, j) | IndivVarUp v i j ∧ ∀ w : W, j.indiv v w = some name} ○ P v φ

/-- App. C (18a): negation introduces the complement of its context as the prejacent's context and
maximizes it over the prejacent. -/
def semNOT (φ' : PVar) (Sc : SemW W E) (φ : PVar) : Update (Assignment W E) :=
  {(i, j) | PropVarUp φ' i j ∧ IsComplement φ φ' j} ○ propMaxOp φ' (Sc φ')

/-- App. C (18b): disjunction introduces a context for each disjunct whose union is its own. -/
def semOR (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) : Update (Assignment W E) :=
  {(i, j) | MultiVarUp [φ', φ''] [] i j ∧ j.prop φ = j.prop φ' ∪ j.prop φ''} ○
    propMaxOp φ' (Sc' φ') ○ propMaxOp φ'' (Sc'' φ'')

/-- App. C (18c): the conditional's context is the union of the antecedent's complement and the
consequent's context. -/
def semIF (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) : Update (Assignment W E) :=
  {(i, j) | MultiVarUp [φ', φ''] [] i j ∧ j.prop φ = (j.prop φ')ᶜ ∪ j.prop φ''} ○
    propMaxOp φ' (Sc' φ') ○ propMaxOp φ'' (Sc'' φ'')

/-- App. C (18d): conjunction narrows the context through each conjunct in turn. -/
def semAND (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) : Update (Assignment W E) :=
  {(i, j) | PropVarUp φ' i j ∧ DynInclusion φ' φ j} ○ propMaxOp φ' (Sc' φ') ○
    {(i, j) | PropVarUp φ'' i j ∧ DynInclusion φ'' φ' j} ○ propMaxOp φ'' (Sc'' φ'')

/-- App. C (18e): an attitude verb introduces a context the subject's doxastic state entails. -/
def semBelieved (φ' : PVar) (dox : Assignment W E → Set W) (Sc : SemW W E) (_φ : PVar) :
    Update (Assignment W E) :=
  {(i, j) | PropVarUp φ' i j ∧ BelieveCondition φ' dox j} ○ propMaxOp φ' (Sc φ')

/-- App. C (19): the declarative introduces the assertion's context, which the speaker's
commitments entail, and maximizes it over the clause. -/
def semDEC (φ_DC : PVar) (φ : PVar) (Sc : SemW W E) : Update (Assignment W E) :=
  {(i, j) | PropVarUp φ i j ∧ DecCondition φ_DC φ j} ○ propMaxOp φ (Sc φ)

/-! ### Maximization of a dref an update leaves fixed -/

/-- An update fixes a propositional dref when no output changes its value. -/
def Fixes (φ : PVar) (D : Update (Assignment W E)) : Prop := ∀ i j, i ~[D] j → j.prop φ = i.prop φ

namespace Fixes

variable {φ : PVar}

theorem comp {D₁ D₂ : Update (Assignment W E)} (h₁ : Fixes φ D₁) (h₂ : Fixes φ D₂) :
    Fixes φ (D₁ ○ D₂) :=
  fun _ _ ⟨k, hk, hj⟩ ↦ (h₂ k _ hj).trans (h₁ _ k hk)

theorem propMaxOp {φ' : PVar} {D : Update (Assignment W E)} (h : Fixes φ D) :
    Fixes φ (propMaxOp φ' D) :=
  fun _ _ hD ↦ h _ _ hD.1

theorem and_right {D : Update (Assignment W E)} {C : Assignment W E → Prop} (h : Fixes φ D) :
    Fixes φ {(i, j) | i ~[D] j ∧ C j} :=
  fun _ _ hh ↦ h _ _ hh.1

theorem id : Fixes φ (SetRel.id : Update (Assignment W E)) := fun _ _ h ↦ SetRel.mem_id.mp h ▸ rfl

theorem test (C : Set (Assignment W E)) : Fixes φ (Update.test C) :=
  fun _ _ h ↦ h.1 ▸ rfl

theorem indivVarUp (v : IVar) : Fixes φ {(i, j) | IndivVarUp (W := W) (E := E) v i j} :=
  fun _ _ h ↦ h.1 φ

theorem relVarUp (φ' : PVar) (v : IVar) :
    Fixes φ {(i, j) | RelVarUp (W := W) (E := E) φ' v i j} :=
  fun _ _ h ↦ h.1.1 φ

theorem propVarUp {φ' : PVar} (h : φ' ≠ φ) :
    Fixes φ {(i, j) | PropVarUp (W := W) (E := E) φ' i j} :=
  fun _ _ hu ↦ hu.1 φ (Ne.symm h)

theorem multiVarUp {ps : List PVar} {vs : List IVar} (h : φ ∉ ps) :
    Fixes φ {(i, j) | MultiVarUp (W := W) (E := E) ps vs i j} :=
  fun _ _ hu ↦ hu.1 φ h

end Fixes

/-- Maximizing a dref an update fixes is vacuous: with the maximized dref unchanged by every
output, no output assigns it a proper superset. -/
theorem propMaxOp_eq_of_fixes {φ : PVar} {D : Update (Assignment W E)} (h : Fixes φ D) :
    propMaxOp φ D = D := by
  ext ⟨i, j⟩
  refine ⟨And.left, fun hD ↦ ⟨hD, fun k hk hlt ↦ ?_⟩⟩
  rw [h i j hD, h i k hk] at hlt
  exact hlt.2 subset_rfl

theorem commonNoun_fixes (φ : PVar) (R : E → W → Prop) (v : IVar) (φ' : PVar) :
    Fixes φ (commonNoun R v φ') :=
  Fixes.test _

theorem vacuousScope_fixes (φ : PVar) (v : IVar) (φ' : PVar) :
    Fixes φ (vacuousScope (W := W) (E := E) v φ') :=
  Fixes.id

theorem indefinite_fixes (φ : PVar) {v : IVar} {P P' : SemE W E} {φ' : PVar}
    (hP : Fixes φ (P v φ')) (hP' : Fixes φ (P' v φ')) : Fixes φ (indefinite v P P' φ') :=
  ((Fixes.relVarUp φ' v).comp hP).comp hP'

theorem pronoun_fixes (φ : PVar) {v : IVar} {P : SemE W E} {φ' : PVar} (h : Fixes φ (P v φ')) :
    Fixes φ (pronoun v P φ') := h

/-- Negation fixes every dref other than the one it introduces that its prejacent fixes. -/
theorem semNOT_fixes (φ : PVar) {φ' : PVar} {Sc : SemW W E} {φ₀ : PVar} (h : φ' ≠ φ)
    (hSc : Fixes φ (Sc φ')) : Fixes φ (semNOT φ' Sc φ₀) :=
  ((Fixes.propVarUp h).and_right).comp hSc.propMaxOp

theorem semOR_fixes (φ : PVar) {φ' φ'' : PVar} {Sc' Sc'' : SemW W E} {φ₀ : PVar}
    (h : φ ∉ [φ', φ'']) (h' : Fixes φ (Sc' φ')) (h'' : Fixes φ (Sc'' φ'')) :
    Fixes φ (semOR φ' φ'' Sc' Sc'' φ₀) :=
  (((Fixes.multiVarUp h).and_right).comp h'.propMaxOp).comp h''.propMaxOp

theorem semDEC_fixes (φ : PVar) {φ_DC φ' : PVar} {Sc : SemW W E} (h : φ' ≠ φ)
    (hSc : Fixes φ (Sc φ')) : Fixes φ (semDEC φ_DC φ' Sc) :=
  ((Fixes.propVarUp h).and_right).comp hSc.propMaxOp

/-! ### The model M₁ (§3.3.2) -/

/-- The four worlds: a bathroom that is upstairs, a bathroom that is not, no bathroom and
something upstairs, and neither. -/
inductive World where
  | w_bu
  | w_b
  | w_u
  | w_0
  deriving DecidableEq

/-- The one entity of the model, the bathroom. -/
inductive Ent where
  | b
  deriving DecidableEq

open World Ent

/-- `b` is a bathroom in the two bathroom worlds. -/
def bathroom : Ent → World → Prop
  | .b, .w_bu => True
  | .b, .w_b => True
  | .b, _ => False

/-- `b` is upstairs in the two upstairs worlds. -/
def upstairs : Ent → World → Prop
  | .b, .w_bu => True
  | .b, .w_u => True
  | .b, _ => False

/-- The individual dref of the bathroom, defined exactly in the bathroom worlds. -/
def bathroomRef : World → Option Ent
  | .w_bu => some .b
  | .w_b => some .b
  | _ => none

/-- The propositional drefs of the derivations: the assertion's context and the contexts of
embedded clauses. -/
def φ₁ : PVar := ⟨1⟩
def φ₂ : PVar := ⟨2⟩
def φ₃ : PVar := ⟨3⟩
def φ₄ : PVar := ⟨4⟩
/-- The commitment set of the speaker `S`. -/
def φDC : PVar := ⟨10⟩
/-- The commitment sets of the interlocutors `A` and `B` of §4.3. -/
def φDCA : PVar := ⟨11⟩
def φDCB : PVar := ⟨12⟩
/-- The individual dref of the indefinite. -/
def υ : IVar := ⟨0⟩

/-- The null assignment (32): no referents and no information. -/
def null : Assignment World Ent := ⟨fun _ _ ↦ none, fun _ ↦ Set.univ⟩

/-- An initial state (33) of a single speaker whose commitment set is `dc`. -/
def init (dc : Set World) : Assignment World Ent := null.updateProp φDC dc

/-- An initial state of the two interlocutors of §4.3. -/
def init₂ (dcA dcB : Set World) : Assignment World Ent :=
  (null.updateProp φDCA dcA).updateProp φDCB dcB

/-- *there is a bathroom* (24): the indefinite with the noun as restrictor and a vacuous
scope. -/
def thereIsABathroom : SemW World Ent := indefinite υ (commonNoun bathroom) vacuousScope

/-- *it is upstairs* (30): the pronoun with the verb phrase. -/
def itIsUpstairs : SemW World Ent := pronoun υ (intransVP upstairs)

theorem thereIsABathroom_fixes (φ φ' : PVar) : Fixes φ (thereIsABathroom φ') :=
  indefinite_fixes φ (commonNoun_fixes φ _ _ _) (vacuousScope_fixes φ _ _)

theorem itIsUpstairs_fixes (φ φ' : PVar) : Fixes φ (itIsUpstairs φ') :=
  pronoun_fixes φ (commonNoun_fixes φ _ _ _)

/-- The output of an assertion with `thereIsABathroom` as its clause: the dref is defined in
the bathroom worlds of the context, and the context is in the bathroom worlds. -/
theorem thereIsABathroom_output {φ : PVar} {k j : Assignment World Ent}
    (h : k ~[thereIsABathroom φ] j) :
    (∀ w, w ∈ j.prop φ ↔ j.indiv υ w ≠ none) ∧ j.prop φ ⊆ {w_bu, w_b} := by
  obtain ⟨m, ⟨l, hrel, rfl, hpred⟩, rfl⟩ := h
  refine ⟨hrel.2, fun w hw ↦ ?_⟩
  have := hpred w hw
  revert this
  cases hv : l.indiv υ w with
  | none => exact False.elim
  | some e => cases e; cases w <;> simp [bathroom]

/-- The output of an assertion with `itIsUpstairs` as its clause: the dref is defined and
upstairs throughout the context. -/
theorem itIsUpstairs_output {φ : PVar} {k j : Assignment World Ent} (h : k ~[itIsUpstairs φ] j) :
    k = j ∧ ∀ w ∈ j.prop φ, j.indiv υ w ≠ none ∧ w ∈ ({w_bu, w_u} : Set World) := by
  obtain ⟨rfl, hpred⟩ := h
  refine ⟨rfl, fun w hw ↦ ?_⟩
  have := hpred w hw
  revert this
  cases hv : k.indiv υ w with
  | none => exact False.elim
  | some e => cases e; cases w <;> simp [upstairs]

/-! ### The veridical discourse (19a) and (30), Figures 5 and 6 -/

/-- *There is a bathroom. It is upstairs.* -/
def veridical : Update (Assignment World Ent) :=
  semDEC φDC φ₁ thereIsABathroom ○ semDEC φDC φ₃ itIsUpstairs

/-- The output of Figure 6. -/
def j₆ : Assignment World Ent :=
  ((((init {w_bu}).updateProp φ₁ {w_bu, w_b}).updateIndiv υ bathroomRef).updateProp φ₃ {w_bu})

/-- Figure 6 is an output of the veridical discourse from the initial state whose commitment
set it shows. -/
theorem veridical_run : init {w_bu} ~[veridical] j₆ := by
  refine ⟨((init {w_bu}).updateProp φ₁ {w_bu, w_b}).updateIndiv υ bathroomRef, ?_, ?_⟩
  · refine ⟨(init {w_bu}).updateProp φ₁ {w_bu, w_b}, ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
    · intro w hw
      simp only [init, Assignment.updateProp_prop_self,
        Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
      simp_all
    · rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)]
      refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, fun w ↦ ?_⟩, rfl, fun w hw ↦ ?_⟩, rfl⟩
      · cases w <;> simp [bathroomRef, init, Assignment.updateProp_prop_self]
      · simp only [Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
        cases w <;> simp_all [bathroomRef, bathroom]
  · refine ⟨j₆, ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
    · intro w hw
      simp only [j₆, init, Assignment.updateProp_prop_self, Assignment.updateIndiv_prop,
        Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
        Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
      exact hw
    · rw [propMaxOp_eq_of_fixes (itIsUpstairs_fixes _ _)]
      refine ⟨rfl, fun w hw ↦ ?_⟩
      simp only [j₆, Assignment.updateProp_prop_self] at hw
      cases w <;> simp_all [j₆, bathroomRef, upstairs]

/-- The dref is veridical, entailed in the speaker's commitment set. -/
theorem veridical_veridicalIndiv : VeridicalIndiv φDC υ j₆ := by
  intro w hw
  simp only [j₆, init, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
    Assignment.updateIndiv_prop, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
    Assignment.updateProp_prop_self] at hw
  cases w <;> simp_all [j₆, bathroomRef]

/-- The veridical anaphor is accessible (Figure 6). -/
theorem veridical_accessible : Accessible φ₃ υ φDC j₆ :=
  ⟨fun w hw ↦ by
    simp only [j₆, Assignment.updateProp_prop_self] at hw
    cases w <;> simp_all [j₆, bathroomRef],
   ⟨w_bu, by simp [j₆, init, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)]⟩⟩

/-- Pragmatic maximization (35): the commitment set of Figure 6 is maximal among the outputs
of the discourse from any initial state, since every output commits the speaker to the
bathroom being upstairs. -/
theorem veridical_maximal (dc : Set World) (h : Assignment World Ent)
    (hrun : init dc ~[veridical] h) : ¬ (j₆.prop φDC ⊂ h.prop φDC) := by
  obtain ⟨h₁, ⟨k₁, ⟨hup₁, hdec₁⟩, hmax₁⟩, ⟨k₂, ⟨hup₂, hdec₂⟩, hmax₂⟩⟩ := hrun
  rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)] at hmax₁
  rw [propMaxOp_eq_of_fixes (itIsUpstairs_fixes _ _)] at hmax₂
  obtain ⟨hbi, _⟩ := thereIsABathroom_output hmax₁
  obtain ⟨rfl, hup⟩ := itIsUpstairs_output hmax₂
  have hDC : k₂.prop φDC = dc := by
    rw [hup₂.1 φDC (by decide), (thereIsABathroom_fixes φDC φ₁) _ _ hmax₁,
      hup₁.1 φDC (by decide)]
    simp [init]
  have hυ : k₂.indiv υ = h₁.indiv υ := hup₂.2 υ
  have hsub : dc ⊆ {w_bu} := fun w hw ↦ by
    have hw' := hdec₂ (hDC ▸ hw)
    obtain ⟨hne, hu⟩ := hup w hw'
    rw [hυ] at hne
    have hb : w ∈ h₁.prop φ₁ := (hbi w).2 hne
    have hb' := (thereIsABathroom_output hmax₁).2 hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb' hu ⊢
    rcases hb' with rfl | rfl <;> rcases hu with h | h <;> simp_all
  intro hlt
  rw [hDC] at hlt
  exact hlt.2 (fun w hw ↦ by
    have := hsub hw
    simp only [j₆, init, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
      Assignment.updateIndiv_prop, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
      Assignment.updateProp_prop_self]
    exact this)

/-! ### The negated antecedent (41), Figure 7 -/

/-- *There isn't a bathroom.* -/
def negated : Update (Assignment World Ent) := semDEC φDC φ₁ (semNOT φ₂ thereIsABathroom)

/-- The output of Figure 7, the first row of Table 3. -/
def j₇ : Assignment World Ent :=
  (((init {w_u, w_0}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b}).updateIndiv υ
    bathroomRef

theorem negated_run : init {w_u, w_0} ~[negated] j₇ := by
  refine ⟨(init {w_u, w_0}).updateProp φ₁ {w_u, w_0}, ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
  · intro w hw
    simp only [init, Assignment.updateProp_prop_self,
      Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
    exact hw
  · rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))]
    refine ⟨((init {w_u, w_0}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b},
      ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
    · show _ = _ᶜ
      ext w
      cases w <;> simp [Assignment.updateProp_prop_self,
        Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]
    · rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)]
      refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, fun w ↦ ?_⟩, rfl, fun w hw ↦ ?_⟩, rfl⟩
      · cases w <;> simp [bathroomRef, Assignment.updateProp_prop_self]
      · simp only [Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
        cases w <;> simp_all [bathroomRef, bathroom]

/-- The dref is counterfactual: undefined throughout the speaker's commitment set. -/
theorem negated_counterfactualIndiv : CounterfactualIndiv φDC υ j₇ := by
  intro w hw
  simp only [j₇, init, Assignment.updateIndiv_prop,
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
    Assignment.updateProp_prop_self] at hw
  cases w <;> simp_all [j₇, bathroomRef]

/-- The assertion's context is the complement of the prejacent's. -/
theorem negated_isComplement : IsComplement φ₁ φ₂ j₇ := by
  show _ = _ᶜ
  ext w
  cases w <;> simp [j₇, Assignment.updateProp_prop_self,
    Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]

/-- Every output of (41) makes the prejacent counterfactual: the commitments entail the
assertion's context, the complement of the prejacent's. -/
theorem negated_counterfactualProp {i j : Assignment World Ent} (h : i ~[negated] j) :
    CounterfactualProp φDC φ₂ j := by
  obtain ⟨k, ⟨_, hdec⟩, hmax⟩ := h
  rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))] at hmax
  obtain ⟨m, ⟨hup, hc⟩, hmax⟩ := hmax
  rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)] at hmax
  have hdec' : DecCondition φDC φ₁ m := by
    rw [DecCondition, DynInclusion, hup.1 φDC (by decide), hup.1 φ₁ (by decide)]
    exact hdec
  rw [CounterfactualProp, thereIsABathroom_fixes φDC φ₂ _ _ hmax,
    thereIsABathroom_fixes φ₂ φ₂ _ _ hmax]
  exact counterfactualProp_of_isComplement hc hdec'

/-- No consistent extension of Figure 7 admits the veridical anaphor (30): a context the
commitments entail that lies within the prejacent's context empties the commitment set
(§3.4.2). -/
theorem counterfactual_veridical_impossible (j : Assignment World Ent)
    (hDC : j.prop φDC = j₇.prop φDC) (hφ₂ : j.prop φ₂ = j₇.prop φ₂)
    (hdec : DecCondition φDC φ₃ j) (hsub : SubsetReq φ₃ φ₂ j) : ¬ (j.prop φDC).Nonempty :=
  counterfactual_blocks_veridical j₇ j φDC φ₃ φ₂ hDC hφ₂ (negated_counterfactualProp negated_run)
    hdec hsub

/-- The last row of Table 3, with the prejacent's context empty and the dref nowhere defined,
is also an output of (41): the printed maximization does not exclude it. -/
def jRow4 : Assignment World Ent :=
  ((init Set.univ).updateProp φ₁ Set.univ).updateProp φ₂ ∅

theorem negated_row4 : init Set.univ ~[negated] jRow4 := by
  refine ⟨(init Set.univ).updateProp φ₁ Set.univ, ⟨propVarUp_updateProp _ _ _, fun _ _ ↦ trivial⟩,
    ?_⟩
  rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))]
  refine ⟨jRow4, ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
  · show _ = _ᶜ
    simp [jRow4, Assignment.updateProp_prop_self,
      Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]
  · rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)]
    refine ⟨jRow4, ⟨jRow4, ⟨⟨fun _ ↦ rfl, fun _ _ ↦ rfl⟩, fun w ↦ ?_⟩, rfl, fun w hw ↦ ?_⟩, rfl⟩
    · simp [jRow4, init, null, Assignment.updateProp_prop_self]
    · simp [jRow4, Assignment.updateProp_prop_self] at hw

/-- Maximizing the prejacent's context over the whole assertion selects Figure 7: every output
from the same initial state keeps that context within the bathroom worlds. -/
theorem negated_max : init {w_u, w_0} ~[propMaxOp φ₂ negated] j₇ := by
  refine ⟨negated_run, fun k hk hlt ↦ ?_⟩
  obtain ⟨k₁, ⟨_, _⟩, hmax⟩ := hk
  rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))] at hmax
  obtain ⟨k₂, ⟨_, _⟩, hmax₂⟩ := hmax
  rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)] at hmax₂
  have hsub := (thereIsABathroom_output hmax₂).2
  refine hlt.2 (fun w hw ↦ ?_)
  have := hsub hw
  simp only [j₇, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self]
  exact this

/-! ### Double negation (43), Figure 8 -/

/-- *It's not the case that there isn't a bathroom.* -/
def doubleNeg : Update (Assignment World Ent) :=
  semDEC φDC φ₁ (semNOT φ₂ (semNOT φ₃ thereIsABathroom))

/-- The output of Figure 8. -/
def j₈ : Assignment World Ent :=
  ((((init {w_bu, w_b}).updateProp φ₁ {w_bu, w_b}).updateProp φ₂ {w_u, w_0}).updateProp φ₃
    {w_bu, w_b}).updateIndiv υ bathroomRef

theorem doubleNeg_run : init {w_bu, w_b} ~[doubleNeg] j₈ := by
  refine ⟨(init {w_bu, w_b}).updateProp φ₁ {w_bu, w_b}, ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
  · intro w hw
    simp only [init, Assignment.updateProp_prop_self,
      Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
    exact hw
  · rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₁ (by decide)
      (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _)))]
    refine ⟨((init {w_bu, w_b}).updateProp φ₁ {w_bu, w_b}).updateProp φ₂ {w_u, w_0},
      ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
    · show _ = _ᶜ
      ext w
      cases w <;> simp [Assignment.updateProp_prop_self,
        Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]
    · rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₂ (by decide) (thereIsABathroom_fixes _ _))]
      refine ⟨(((init {w_bu, w_b}).updateProp φ₁ {w_bu, w_b}).updateProp φ₂ {w_u, w_0}).updateProp
        φ₃ {w_bu, w_b}, ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
      · show _ = _ᶜ
        ext w
        cases w <;> simp [Assignment.updateProp_prop_self,
          Assignment.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₃)]
      · rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)]
        refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, fun w ↦ ?_⟩, rfl, fun w hw ↦ ?_⟩, rfl⟩
        · cases w <;> simp [bathroomRef, Assignment.updateProp_prop_self]
        · simp only [Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
          cases w <;> simp_all [bathroomRef, bathroom]

/-- Double complementation returns the assertion's context to the innermost one. -/
theorem doubleNeg_prop_eq : j₈.prop φ₁ = j₈.prop φ₃ := by
  simp [j₈, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self,
    Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₃),
    Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]

/-- The doubly negated dref is veridical. -/
theorem doubleNeg_veridicalIndiv : VeridicalIndiv φDC υ j₈ := by
  intro w hw
  simp only [j₈, init, Assignment.updateIndiv_prop,
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
    Assignment.updateProp_prop_self] at hw
  cases w <;> simp_all [j₈, bathroomRef]

/-- The veridical anaphor is accessible after double negation (§4.1). -/
theorem doubleNeg_accessible : Accessible φ₃ υ φDC j₈ :=
  ⟨fun w hw ↦ by
    simp only [j₈, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
    cases w <;> simp_all [j₈, bathroomRef],
   ⟨w_bu, by simp [j₈, init, Assignment.updateIndiv_prop,
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)]⟩⟩

/-! ### The bathroom disjunction (44), Figure 9 -/

/-- *Either there isn't a bathroom, or it's upstairs.* -/
def bathDisj : Update (Assignment World Ent) :=
  semDEC φDC φ₁ (semOR φ₂ φ₃ (semNOT φ₄ thereIsABathroom) itIsUpstairs)

/-- The output of Figure 9. -/
def j₉ : Assignment World Ent :=
  (((((init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0}).updateProp φ₂ {w_u, w_0}).updateProp
    φ₃ {w_bu}).updateProp φ₄ {w_bu, w_b}).updateIndiv υ bathroomRef

theorem bathDisj_run : init {w_bu, w_u, w_0} ~[bathDisj] j₉ := by
  refine ⟨(init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0},
    ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
  · intro w hw
    simp only [init, Assignment.updateProp_prop_self,
      Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
    exact hw
  · rw [propMaxOp_eq_of_fixes (semOR_fixes φ₁ (by decide)
      (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _)) (itIsUpstairs_fixes _ _))]
    refine ⟨j₉, ⟨(((init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0}).updateProp φ₂
      {w_u, w_0}).updateProp φ₃ {w_bu}, ⟨⟨fun q hq ↦ ?_, fun _ _ ↦ rfl⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp [Assignment.updateProp_prop_of_ne _ hq.1, Assignment.updateProp_prop_of_ne _ hq.2]
    · ext w
      cases w <;> simp [Assignment.updateProp_prop_self,
        Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₃),
        Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂),
        Assignment.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₃)]
    · rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₂ (by decide) (thereIsABathroom_fixes _ _))]
      refine ⟨((((init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0}).updateProp φ₂
        {w_u, w_0}).updateProp φ₃ {w_bu}).updateProp φ₄ {w_bu, w_b},
        ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
      · show _ = _ᶜ
        ext w
        cases w <;> simp [Assignment.updateProp_prop_self,
          Assignment.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₄),
          Assignment.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₃)]
      · rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)]
        refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, fun w ↦ ?_⟩, rfl, fun w hw ↦ ?_⟩, rfl⟩
        · cases w <;> simp [bathroomRef, Assignment.updateProp_prop_self]
        · simp only [Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
          cases w <;> simp_all [bathroomRef, bathroom]
    · rw [propMaxOp_eq_of_fixes (itIsUpstairs_fixes _ _)]
      refine ⟨rfl, fun w hw ↦ ?_⟩
      simp only [j₉, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self,
        Assignment.updateProp_prop_of_ne _ (by decide : φ₃ ≠ φ₄)] at hw
      cases w <;> simp_all [j₉, bathroomRef, upstairs]

/-- The disjunction's context is the union of the disjuncts' contexts. -/
theorem bathDisj_union : j₉.prop φ₁ = j₉.prop φ₂ ∪ j₉.prop φ₃ := by
  ext w
  cases w <;> simp [j₉, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self,
    Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₄),
    Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₃),
    Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂),
    Assignment.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₄),
    Assignment.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₃),
    Assignment.updateProp_prop_of_ne _ (by decide : φ₃ ≠ φ₄)]

/-- The dref is counterfactual for the speaker yet accessible in the second disjunct
(§4.2): the disjuncts' contexts need not overlap the commitment set. -/
theorem bathDisj_accessible : Accessible φ₃ υ φDC j₉ :=
  ⟨fun w hw ↦ by
    simp only [j₉, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self,
      Assignment.updateProp_prop_of_ne _ (by decide : φ₃ ≠ φ₄)] at hw
    cases w <;> simp_all [j₉, bathroomRef],
   ⟨w_bu, by simp [j₉, init, Assignment.updateIndiv_prop,
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₄),
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)]⟩⟩

/-! ### Disagreement (47) and (48), Figure 10 -/

/-- `A`: *There isn't a bathroom.* `B`: *It is upstairs.* -/
def disagree : Update (Assignment World Ent) :=
  semDEC φDCA φ₁ (semNOT φ₂ thereIsABathroom) ○ semDEC φDCB φ₃ itIsUpstairs

/-- The output of Figure 10. -/
def j₁₀ : Assignment World Ent :=
  ((((init₂ {w_u, w_0} {w_bu}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b}).updateIndiv υ
    bathroomRef).updateProp φ₃ {w_bu}

theorem disagree_run : init₂ {w_u, w_0} {w_bu} ~[disagree] j₁₀ := by
  refine ⟨(((init₂ {w_u, w_0} {w_bu}).updateProp φ₁ {w_u, w_0}).updateProp φ₂
    {w_bu, w_b}).updateIndiv υ bathroomRef, ?_, ?_⟩
  · refine ⟨(init₂ {w_u, w_0} {w_bu}).updateProp φ₁ {w_u, w_0}, ⟨propVarUp_updateProp _ _ _, ?_⟩,
      ?_⟩
    · intro w hw
      simp only [init₂, Assignment.updateProp_prop_self,
        Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₁),
        Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φDCB)] at hw ⊢
      exact hw
    · rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))]
      refine ⟨((init₂ {w_u, w_0} {w_bu}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b},
        ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
      · show _ = _ᶜ
        ext w
        cases w <;> simp [Assignment.updateProp_prop_self,
          Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]
      · rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)]
        refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, fun w ↦ ?_⟩, rfl, fun w hw ↦ ?_⟩, rfl⟩
        · cases w <;> simp [bathroomRef, Assignment.updateProp_prop_self]
        · simp only [Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
          cases w <;> simp_all [bathroomRef, bathroom]
  · refine ⟨j₁₀, ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
    · intro w hw
      simp only [j₁₀, init₂, Assignment.updateProp_prop_self, Assignment.updateIndiv_prop,
        Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₃),
        Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₂),
        Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₁)] at hw ⊢
      exact hw
    · rw [propMaxOp_eq_of_fixes (itIsUpstairs_fixes _ _)]
      refine ⟨rfl, fun w hw ↦ ?_⟩
      simp only [j₁₀, Assignment.updateProp_prop_self] at hw
      cases w <;> simp_all [j₁₀, bathroomRef, upstairs]

/-- The dref is counterfactual for `A`. -/
theorem disagree_counterfactual_A : CounterfactualIndiv φDCA υ j₁₀ := by
  intro w hw
  simp only [j₁₀, init₂, Assignment.updateIndiv_prop,
    Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₃),
    Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₂),
    Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₁),
    Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φDCB),
    Assignment.updateProp_prop_self] at hw
  cases w <;> simp_all [j₁₀, bathroomRef]

/-- The same dref is veridical for `B`. -/
theorem disagree_veridical_B : VeridicalIndiv φDCB υ j₁₀ := by
  intro w hw
  simp only [j₁₀, init₂, Assignment.updateIndiv_prop,
    Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₃),
    Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₂),
    Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₁),
    Assignment.updateProp_prop_self] at hw
  cases w <;> simp_all [j₁₀, bathroomRef]

/-- Both interlocutors keep consistent commitments although they contradict each other, and
`B`'s anaphor is accessible (§4.3). -/
theorem disagree_accessible :
    (j₁₀.prop φDCA).Nonempty ∧ Accessible φ₃ υ φDCB j₁₀ :=
  ⟨⟨w_u, by simp [j₁₀, init₂, Assignment.updateIndiv_prop,
     Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₃),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₂),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₁),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φDCB)]⟩,
   fun w hw ↦ by
     simp only [j₁₀, Assignment.updateProp_prop_self] at hw
     cases w <;> simp_all [j₁₀, bathroomRef],
   ⟨w_bu, by simp [j₁₀, init₂, Assignment.updateIndiv_prop,
     Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₃),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₂),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₁)]⟩⟩

end Hofmann2025
