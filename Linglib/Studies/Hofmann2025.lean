import Linglib.Data.Examples.Hofmann2025
import Linglib.Semantics.Dynamic.ICDRT.Basic

/-!
# Hofmann (2025): Anaphoric Accessibility with Flat Update

This file formalizes [hofmann-2025]'s account of anaphora to negated indefinites in
Intensional CDRT, the substrate `Semantics/Dynamic/ICDRT`. Indefinites introduce their
discourse referent globally, relative to the propositional dref of their local context, and a
pronoun is acceptable when its referent exists throughout its own local context under a
consistent assignment of speaker commitments, Definition (38). The subset requirement (39)
follows from relative variable update (`localEntailment_iff_subset`), and a veridical anaphor
context admits only veridical antecedents (`veridicalIndiv_of_accessible`). The fragment of
Appendix C, `semDEC` and the sentential operators, is run on the paper's four-world model for
the bathroom discourses of §3 and §4: the veridical discourse of Figures 5 and 6, the negated
antecedent of Figure 7 whose veridical continuation no consistent extension admits
(`counterfactual_veridical_impossible`), the double negation of Figure 8, the bathroom
disjunction of Figure 9 and the disagreement of Figure 10 are outputs of the fragment's
updates from an initial state, with their pronouns accessible or not as the paper says.

## Implementation notes

* The maximization operators of (18) and (19), and of the displayed updates (41), (43) and
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

namespace Hofmann2025

open DynamicSemantics DynamicSemantics.ICDRT
open DynamicSemantics.Update (seq)

variable {W E : Type*}

/-! ### Accessibility (38) and the subset requirement (39) -/

/-- The subset requirement (39): once `v` is introduced relative to `φ₂`, it is entailed in a
context `φ₁` exactly when `φ₁` is included in `φ₂`. -/
theorem localEntailment_iff_subset {φ₁ φ₂ : PVar} {v : IVar} {i j : Assignment W E}
    (h : relVarUp φ₂ v i j) : localEntailment φ₁ v j ↔ j.prop φ₁ ⊆ j.prop φ₂ :=
  ⟨λ hl w hw => (h.2 w).2 (hl w hw), λ hs w hw => (h.2 w).1 (hs hw)⟩

/-- In a veridical anaphor context, one the speaker's commitments entail, only a veridical
dref is accessible. -/
theorem veridicalIndiv_of_accessible {φ φ_DC : PVar} {v : IVar} {j : Assignment W E}
    (hdec : decCondition φ_DC φ j) (h : accessible φ v φ_DC j) : veridicalIndiv φ_DC v j :=
  λ w hw => h.1 w (hdec hw)

/-! ### The fragment of Appendix C -/

/-- The type of predicates, `e(wt)`: an individual dref and a local context to an update. -/
abbrev SemE (W E : Type*) := IVar → PVar → ICDRT.Update W E

/-- The type of clauses, `wt`: a local context to an update. -/
abbrev SemW (W E : Type*) := PVar → ICDRT.Update W E

/-- The vacuous scope of an existential: the identity update. -/
def vacuousScope : SemE W E := λ _ _ => ICDRT.idUp

/-- (15): a common noun is a test that its argument satisfies it in the local context. -/
def commonNoun (R : E → W → Prop) : SemE W E :=
  λ v φ => λ i j => i = j ∧ dynPred R φ v j

/-- An intransitive verb phrase, of the same shape as a common noun. -/
abbrev intransVP (R : E → W → Prop) : SemE W E := commonNoun R

/-- (16): the indefinite introduces its dref relative to the local context, then runs its
restrictor and its scope. -/
def indefinite (v : IVar) (P P' : SemE W E) (φ : PVar) : ICDRT.Update W E :=
  seq (seq (λ i j => relVarUp φ v i j) (P v φ)) (P' v φ)

/-- (17): a pronoun passes its index to the predicate. -/
def pronoun (v : IVar) (P : SemE W E) (φ : PVar) : ICDRT.Update W E := P v φ

/-- (14): a proper name introduces a dref equal to its constant. -/
def properName (name : E) (v : IVar) (P : SemE W E) (φ : PVar) : ICDRT.Update W E :=
  seq (λ i j => indivVarUp v i j ∧ ∀ w : W, j.indiv v w = .some name) (P v φ)

/-- (18a): negation introduces the complement of its context as the prejacent's context and
maximizes it over the prejacent. -/
def semNOT (φ' : PVar) (Sc : SemW W E) (φ : PVar) : ICDRT.Update W E :=
  seq (λ i j => propVarUp φ' i j ∧ isComplement φ φ' j) (propMaxOp φ' (Sc φ'))

/-- (18b): disjunction introduces a context for each disjunct whose union is its own. -/
def semOR (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) : ICDRT.Update W E :=
  seq
    (seq (λ i j => multiVarUp [φ', φ''] [] i j ∧ j.prop φ = j.prop φ' ∪ j.prop φ'')
      (propMaxOp φ' (Sc' φ')))
    (propMaxOp φ'' (Sc'' φ''))

/-- (18c): the conditional's context is the union of the antecedent's complement and the
consequent's context. -/
def semIF (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) : ICDRT.Update W E :=
  seq
    (seq (λ i j => multiVarUp [φ', φ''] [] i j ∧ j.prop φ = (j.prop φ')ᶜ ∪ j.prop φ'')
      (propMaxOp φ' (Sc' φ')))
    (propMaxOp φ'' (Sc'' φ''))

/-- (18d): conjunction narrows the context through each conjunct in turn. -/
def semAND (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) : ICDRT.Update W E :=
  seq
    (seq (seq (λ i j => propVarUp φ' i j ∧ dynInclusion φ' φ j) (propMaxOp φ' (Sc' φ')))
      (λ i j => propVarUp φ'' i j ∧ dynInclusion φ'' φ' j))
    (propMaxOp φ'' (Sc'' φ''))

/-- (18e): an attitude verb introduces a context the subject's doxastic state entails. -/
def semBelieved (φ' : PVar) (dox : ICDRT.Assignment W E → Set W) (Sc : SemW W E) (_φ : PVar) :
    ICDRT.Update W E :=
  seq (λ i j => propVarUp φ' i j ∧ believeCondition φ' dox j) (propMaxOp φ' (Sc φ'))

/-- (19): the declarative introduces the assertion's context, which the speaker's
commitments entail, and maximizes it over the clause. -/
def semDEC (φ_DC : PVar) (φ : PVar) (Sc : SemW W E) : ICDRT.Update W E :=
  seq (λ i j => propVarUp φ i j ∧ decCondition φ_DC φ j) (propMaxOp φ (Sc φ))

/-! ### Maximization of a dref an update leaves fixed -/

/-- An update fixes a propositional dref when no output changes its value. -/
def Fixes (φ : PVar) (D : ICDRT.Update W E) : Prop := ∀ i j, D i j → j.prop φ = i.prop φ

namespace Fixes

variable {φ : PVar}

theorem seq {D₁ D₂ : ICDRT.Update W E} (h₁ : Fixes φ D₁) (h₂ : Fixes φ D₂) :
    Fixes φ (seq D₁ D₂) :=
  λ _ _ ⟨k, hk, hj⟩ => (h₂ k _ hj).trans (h₁ _ k hk)

theorem propMaxOp {φ' : PVar} {D : ICDRT.Update W E} (h : Fixes φ D) :
    Fixes φ (propMaxOp φ' D) :=
  λ _ _ hD => h _ _ hD.1

theorem and_right {D : ICDRT.Update W E} {C : Assignment W E → Prop} (h : Fixes φ D) :
    Fixes φ (λ i j => D i j ∧ C j) :=
  λ _ _ hh => h _ _ hh.1

theorem idUp : Fixes φ (ICDRT.idUp : ICDRT.Update W E) := λ _ _ h => h ▸ rfl

theorem test (C : Assignment W E → Prop) : Fixes φ (λ i j => i = j ∧ C j) :=
  λ _ _ h => h.1 ▸ rfl

theorem indivVarUp (v : IVar) : Fixes φ (λ i j : Assignment W E => indivVarUp v i j) :=
  λ _ _ h => h.1 φ

theorem relVarUp (φ' : PVar) (v : IVar) :
    Fixes φ (λ i j : Assignment W E => relVarUp φ' v i j) :=
  λ _ _ h => h.1.1 φ

theorem propVarUp {φ' : PVar} (h : φ' ≠ φ) :
    Fixes φ (λ i j : Assignment W E => propVarUp φ' i j) :=
  λ _ _ hu => hu.1 φ (Ne.symm h)

theorem multiVarUp {ps : List PVar} {vs : List IVar} (h : φ ∉ ps) :
    Fixes φ (λ i j : Assignment W E => multiVarUp ps vs i j) :=
  λ _ _ hu => hu.1 φ h

end Fixes

/-- Maximizing a dref an update fixes is vacuous: with the maximized dref unchanged by every
output, no output assigns it a proper superset. -/
theorem propMaxOp_eq_of_fixes {φ : PVar} {D : ICDRT.Update W E} (h : Fixes φ D) :
    propMaxOp φ D = D := by
  funext i j
  refine propext ⟨And.left, λ hD => ⟨hD, λ k hk hlt => ?_⟩⟩
  rw [h i j hD, h i k hk] at hlt
  exact hlt.2 subset_rfl

theorem commonNoun_fixes (φ : PVar) (R : E → W → Prop) (v : IVar) (φ' : PVar) :
    Fixes φ (commonNoun R v φ') :=
  Fixes.test _

theorem vacuousScope_fixes (φ : PVar) (v : IVar) (φ' : PVar) :
    Fixes φ (vacuousScope (W := W) (E := E) v φ') :=
  Fixes.idUp

theorem indefinite_fixes (φ : PVar) {v : IVar} {P P' : SemE W E} {φ' : PVar}
    (hP : Fixes φ (P v φ')) (hP' : Fixes φ (P' v φ')) : Fixes φ (indefinite v P P' φ') :=
  ((Fixes.relVarUp φ' v).seq hP).seq hP'

theorem pronoun_fixes (φ : PVar) {v : IVar} {P : SemE W E} {φ' : PVar} (h : Fixes φ (P v φ')) :
    Fixes φ (pronoun v P φ') := h

/-- Negation fixes every dref other than the one it introduces that its prejacent fixes. -/
theorem semNOT_fixes (φ : PVar) {φ' : PVar} {Sc : SemW W E} {φ₀ : PVar} (h : φ' ≠ φ)
    (hSc : Fixes φ (Sc φ')) : Fixes φ (semNOT φ' Sc φ₀) :=
  ((Fixes.propVarUp h).and_right).seq hSc.propMaxOp

theorem semOR_fixes (φ : PVar) {φ' φ'' : PVar} {Sc' Sc'' : SemW W E} {φ₀ : PVar}
    (h : φ ∉ [φ', φ'']) (h' : Fixes φ (Sc' φ')) (h'' : Fixes φ (Sc'' φ'')) :
    Fixes φ (semOR φ' φ'' Sc' Sc'' φ₀) :=
  (((Fixes.multiVarUp h).and_right).seq h'.propMaxOp).seq h''.propMaxOp

theorem semDEC_fixes (φ : PVar) {φ_DC φ' : PVar} {Sc : SemW W E} (h : φ' ≠ φ)
    (hSc : Fixes φ (Sc φ')) : Fixes φ (semDEC φ_DC φ' Sc) :=
  ((Fixes.propVarUp h).and_right).seq hSc.propMaxOp

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
def bathroomRef : World → Entity Ent
  | .w_bu => .some .b
  | .w_b => .some .b
  | _ => .star

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
def null : Assignment World Ent := ⟨λ _ _ => .star, λ _ => Set.univ⟩

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
    (h : thereIsABathroom φ k j) :
    (∀ w, w ∈ j.prop φ ↔ j.indiv υ w ≠ .star) ∧ j.prop φ ⊆ {w_bu, w_b} := by
  obtain ⟨m, ⟨l, hrel, rfl, hpred⟩, rfl⟩ := h
  refine ⟨hrel.2, λ w hw => ?_⟩
  have := hpred w hw
  revert this
  cases hv : l.indiv υ w with
  | star => exact False.elim
  | some e => cases e; cases w <;> simp [bathroom]

/-- The output of an assertion with `itIsUpstairs` as its clause: the dref is defined and
upstairs throughout the context. -/
theorem itIsUpstairs_output {φ : PVar} {k j : Assignment World Ent} (h : itIsUpstairs φ k j) :
    k = j ∧ ∀ w ∈ j.prop φ, j.indiv υ w ≠ .star ∧ w ∈ ({w_bu, w_u} : Set World) := by
  obtain ⟨rfl, hpred⟩ := h
  refine ⟨rfl, λ w hw => ?_⟩
  have := hpred w hw
  revert this
  cases hv : k.indiv υ w with
  | star => exact False.elim
  | some e => cases e; cases w <;> simp [upstairs]

/-! ### The veridical discourse (19a) and (30), Figures 5 and 6 -/

/-- *There is a bathroom. It is upstairs.* -/
def veridical : ICDRT.Update World Ent :=
  seq (semDEC φDC φ₁ thereIsABathroom) (semDEC φDC φ₃ itIsUpstairs)

/-- The output of Figure 6. -/
def j₆ : Assignment World Ent :=
  ((((init {w_bu}).updateProp φ₁ {w_bu, w_b}).updateIndiv υ bathroomRef).updateProp φ₃ {w_bu})

/-- Figure 6 is an output of the veridical discourse from the initial state whose commitment
set it shows. -/
theorem veridical_run : veridical (init {w_bu}) j₆ := by
  refine ⟨((init {w_bu}).updateProp φ₁ {w_bu, w_b}).updateIndiv υ bathroomRef, ?_, ?_⟩
  · refine ⟨(init {w_bu}).updateProp φ₁ {w_bu, w_b}, ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
    · intro w hw
      simp only [init, Assignment.updateProp_prop_self,
        Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
      simp_all
    · rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)]
      refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, λ w => ?_⟩, rfl, λ w hw => ?_⟩, rfl⟩
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
      refine ⟨rfl, λ w hw => ?_⟩
      simp only [j₆, Assignment.updateProp_prop_self] at hw
      cases w <;> simp_all [j₆, bathroomRef, upstairs]

/-- The dref is veridical, entailed in the speaker's commitment set. -/
theorem veridical_veridicalIndiv : veridicalIndiv φDC υ j₆ := by
  intro w hw
  simp only [j₆, init, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
    Assignment.updateIndiv_prop, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
    Assignment.updateProp_prop_self] at hw
  cases w <;> simp_all [j₆, bathroomRef]

/-- The veridical anaphor is accessible (Figure 6). -/
theorem veridical_accessible : accessible φ₃ υ φDC j₆ :=
  ⟨λ w hw => by
    simp only [j₆, Assignment.updateProp_prop_self] at hw
    cases w <;> simp_all [j₆, bathroomRef],
   ⟨w_bu, by simp [j₆, init, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)]⟩⟩

/-- Pragmatic maximization (35): the commitment set of Figure 6 is maximal among the outputs
of the discourse from any initial state, since every output commits the speaker to the
bathroom being upstairs. -/
theorem veridical_maximal (dc : Set World) (h : Assignment World Ent)
    (hrun : veridical (init dc) h) : ¬ (j₆.prop φDC ⊂ h.prop φDC) := by
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
  have hsub : dc ⊆ {w_bu} := λ w hw => by
    have hw' := hdec₂ (hDC ▸ hw)
    obtain ⟨hne, hu⟩ := hup w hw'
    rw [hυ] at hne
    have hb : w ∈ h₁.prop φ₁ := (hbi w).2 hne
    have hb' := (thereIsABathroom_output hmax₁).2 hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb' hu ⊢
    rcases hb' with rfl | rfl <;> rcases hu with h | h <;> simp_all
  intro hlt
  rw [hDC] at hlt
  exact hlt.2 (λ w hw => by
    have := hsub hw
    simp only [j₆, init, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
      Assignment.updateIndiv_prop, Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
      Assignment.updateProp_prop_self]
    exact this)

/-! ### The negated antecedent (41), Figure 7 -/

/-- *There isn't a bathroom.* -/
def negated : ICDRT.Update World Ent := semDEC φDC φ₁ (semNOT φ₂ thereIsABathroom)

/-- The output of Figure 7, the first row of Table 3. -/
def j₇ : Assignment World Ent :=
  (((init {w_u, w_0}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b}).updateIndiv υ
    bathroomRef

theorem negated_run : negated (init {w_u, w_0}) j₇ := by
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
      refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, λ w => ?_⟩, rfl, λ w hw => ?_⟩, rfl⟩
      · cases w <;> simp [bathroomRef, Assignment.updateProp_prop_self]
      · simp only [Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
        cases w <;> simp_all [bathroomRef, bathroom]

/-- The dref is counterfactual: undefined throughout the speaker's commitment set. -/
theorem negated_counterfactualIndiv : counterfactualIndiv φDC υ j₇ := by
  intro w hw
  simp only [j₇, init, Assignment.updateIndiv_prop,
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
    Assignment.updateProp_prop_self] at hw
  cases w <;> simp_all [j₇, bathroomRef]

/-- The assertion's context is the complement of the prejacent's. -/
theorem negated_isComplement : isComplement φ₁ φ₂ j₇ := by
  show _ = _ᶜ
  ext w
  cases w <;> simp [j₇, Assignment.updateProp_prop_self,
    Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]

/-- No consistent extension of Figure 7 admits the veridical anaphor (30): a context the
commitments entail that lies within the prejacent's context empties the commitment set
(§3.4.2). -/
theorem counterfactual_veridical_impossible (j : Assignment World Ent)
    (hDC : j.prop φDC = j₇.prop φDC) (hφ₂ : j.prop φ₂ = j₇.prop φ₂)
    (hdec : decCondition φDC φ₃ j) (hsub : subsetReq φ₃ φ₂ j) : ¬ (j.prop φDC).Nonempty :=
  counterfactual_blocks_veridical j₇ j φDC φ₃ φ₂ hDC hφ₂
    (by
      ext w
      cases w <;> simp [j₇, init, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self,
        Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
        Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)])
    hdec hsub

/-- The last row of Table 3, with the prejacent's context empty and the dref nowhere defined,
is also an output of (41): the printed maximization does not exclude it. -/
def jRow4 : Assignment World Ent :=
  ((init Set.univ).updateProp φ₁ Set.univ).updateProp φ₂ ∅

theorem negated_row4 : negated (init Set.univ) jRow4 := by
  refine ⟨(init Set.univ).updateProp φ₁ Set.univ, ⟨propVarUp_updateProp _ _ _, λ _ _ => trivial⟩,
    ?_⟩
  rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))]
  refine ⟨jRow4, ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
  · show _ = _ᶜ
    simp [jRow4, Assignment.updateProp_prop_self,
      Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]
  · rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)]
    refine ⟨jRow4, ⟨jRow4, ⟨⟨λ _ => rfl, λ _ _ => rfl⟩, λ w => ?_⟩, rfl, λ w hw => ?_⟩, rfl⟩
    · simp [jRow4, init, null, Assignment.updateProp_prop_self]
    · simp [jRow4, Assignment.updateProp_prop_self] at hw

/-- Maximizing the prejacent's context over the whole assertion selects Figure 7: every output
from the same initial state keeps that context within the bathroom worlds. -/
theorem negated_max : propMaxOp φ₂ negated (init {w_u, w_0}) j₇ := by
  refine ⟨negated_run, λ k hk hlt => ?_⟩
  obtain ⟨k₁, ⟨_, _⟩, hmax⟩ := hk
  rw [propMaxOp_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))] at hmax
  obtain ⟨k₂, ⟨_, _⟩, hmax₂⟩ := hmax
  rw [propMaxOp_eq_of_fixes (thereIsABathroom_fixes _ _)] at hmax₂
  have hsub := (thereIsABathroom_output hmax₂).2
  refine hlt.2 (λ w hw => ?_)
  have := hsub hw
  simp only [j₇, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self]
  exact this

/-! ### Double negation (43), Figure 8 -/

/-- *It's not the case that there isn't a bathroom.* -/
def doubleNeg : ICDRT.Update World Ent :=
  semDEC φDC φ₁ (semNOT φ₂ (semNOT φ₃ thereIsABathroom))

/-- The output of Figure 8. -/
def j₈ : Assignment World Ent :=
  ((((init {w_bu, w_b}).updateProp φ₁ {w_bu, w_b}).updateProp φ₂ {w_u, w_0}).updateProp φ₃
    {w_bu, w_b}).updateIndiv υ bathroomRef

theorem doubleNeg_run : doubleNeg (init {w_bu, w_b}) j₈ := by
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
        refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, λ w => ?_⟩, rfl, λ w hw => ?_⟩, rfl⟩
        · cases w <;> simp [bathroomRef, Assignment.updateProp_prop_self]
        · simp only [Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
          cases w <;> simp_all [bathroomRef, bathroom]

/-- Double complementation returns the assertion's context to the innermost one. -/
theorem doubleNeg_prop_eq : j₈.prop φ₁ = j₈.prop φ₃ := by
  simp [j₈, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self,
    Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₃),
    Assignment.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]

/-- The doubly negated dref is veridical. -/
theorem doubleNeg_veridicalIndiv : veridicalIndiv φDC υ j₈ := by
  intro w hw
  simp only [j₈, init, Assignment.updateIndiv_prop,
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
    Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
    Assignment.updateProp_prop_self] at hw
  cases w <;> simp_all [j₈, bathroomRef]

/-- The veridical anaphor is accessible after double negation (§4.1). -/
theorem doubleNeg_accessible : accessible φ₃ υ φDC j₈ :=
  ⟨λ w hw => by
    simp only [j₈, Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
    cases w <;> simp_all [j₈, bathroomRef],
   ⟨w_bu, by simp [j₈, init, Assignment.updateIndiv_prop,
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
     Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)]⟩⟩

/-! ### The bathroom disjunction (44), Figure 9 -/

/-- *Either there isn't a bathroom, or it's upstairs.* -/
def bathDisj : ICDRT.Update World Ent :=
  semDEC φDC φ₁ (semOR φ₂ φ₃ (semNOT φ₄ thereIsABathroom) itIsUpstairs)

/-- The output of Figure 9. -/
def j₉ : Assignment World Ent :=
  (((((init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0}).updateProp φ₂ {w_u, w_0}).updateProp
    φ₃ {w_bu}).updateProp φ₄ {w_bu, w_b}).updateIndiv υ bathroomRef

theorem bathDisj_run : bathDisj (init {w_bu, w_u, w_0}) j₉ := by
  refine ⟨(init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0},
    ⟨propVarUp_updateProp _ _ _, ?_⟩, ?_⟩
  · intro w hw
    simp only [init, Assignment.updateProp_prop_self,
      Assignment.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
    exact hw
  · rw [propMaxOp_eq_of_fixes (semOR_fixes φ₁ (by decide)
      (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _)) (itIsUpstairs_fixes _ _))]
    refine ⟨j₉, ⟨(((init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0}).updateProp φ₂
      {w_u, w_0}).updateProp φ₃ {w_bu}, ⟨⟨λ q hq => ?_, λ _ _ => rfl⟩, ?_⟩, ?_⟩, ?_⟩
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
        refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, λ w => ?_⟩, rfl, λ w hw => ?_⟩, rfl⟩
        · cases w <;> simp [bathroomRef, Assignment.updateProp_prop_self]
        · simp only [Assignment.updateIndiv_prop, Assignment.updateProp_prop_self] at hw
          cases w <;> simp_all [bathroomRef, bathroom]
    · rw [propMaxOp_eq_of_fixes (itIsUpstairs_fixes _ _)]
      refine ⟨rfl, λ w hw => ?_⟩
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
theorem bathDisj_accessible : accessible φ₃ υ φDC j₉ :=
  ⟨λ w hw => by
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
def disagree : ICDRT.Update World Ent :=
  seq (semDEC φDCA φ₁ (semNOT φ₂ thereIsABathroom)) (semDEC φDCB φ₃ itIsUpstairs)

/-- The output of Figure 10. -/
def j₁₀ : Assignment World Ent :=
  ((((init₂ {w_u, w_0} {w_bu}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b}).updateIndiv υ
    bathroomRef).updateProp φ₃ {w_bu}

theorem disagree_run : disagree (init₂ {w_u, w_0} {w_bu}) j₁₀ := by
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
        refine ⟨_, ⟨_, ⟨indivVarUp_updateIndiv _ _ _, λ w => ?_⟩, rfl, λ w hw => ?_⟩, rfl⟩
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
      refine ⟨rfl, λ w hw => ?_⟩
      simp only [j₁₀, Assignment.updateProp_prop_self] at hw
      cases w <;> simp_all [j₁₀, bathroomRef, upstairs]

/-- The dref is counterfactual for `A`. -/
theorem disagree_counterfactual_A : counterfactualIndiv φDCA υ j₁₀ := by
  intro w hw
  simp only [j₁₀, init₂, Assignment.updateIndiv_prop,
    Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₃),
    Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₂),
    Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₁),
    Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φDCB),
    Assignment.updateProp_prop_self] at hw
  cases w <;> simp_all [j₁₀, bathroomRef]

/-- The same dref is veridical for `B`. -/
theorem disagree_veridical_B : veridicalIndiv φDCB υ j₁₀ := by
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
    (j₁₀.prop φDCA).Nonempty ∧ accessible φ₃ υ φDCB j₁₀ :=
  ⟨⟨w_u, by simp [j₁₀, init₂, Assignment.updateIndiv_prop,
     Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₃),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₂),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₁),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCA ≠ φDCB)]⟩,
   λ w hw => by
     simp only [j₁₀, Assignment.updateProp_prop_self] at hw
     cases w <;> simp_all [j₁₀, bathroomRef],
   ⟨w_bu, by simp [j₁₀, init₂, Assignment.updateIndiv_prop,
     Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₃),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₂),
     Assignment.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₁)]⟩⟩

end Hofmann2025
