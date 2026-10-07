/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Part
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Logic.Trivalent.Prop3
public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Semantics.Alternatives.Competition
public import Linglib.Semantics.Focus.Particles
public import Linglib.Data.Examples.CoppockBeaver2015

/-!
# Coppock and Beaver's definiteness and determinacy

This file formalizes Coppock and Beaver's theory of definiteness: definite, indefinite and
possessive descriptions are underlyingly predicates, the definite article presupposes weak
uniqueness and no existence, and a description acquires existential import only through the
type shifts that place it in argument position. The entries are terms of the paper's Weak
Kleene logic with the presupposition operator of Beaver and Krahmer, and the definite
article competes with the indefinite under an expression-level Maximize Presupposition.

## Main statements

- `anti_uniqueness`: *Scott is not the only author of Waverley* is true exactly when Scott
  is an author and so is someone else, and presupposes only that Scott is an author
  (`anti_uniqueness_presup`); the Fregean rival entry can never make it true
  (`no_anti_uniqueness_fregean`).
- `the_dominates_an`, `an_only_blocked`: the definite article presuppositionally dominates
  the indefinite, so *an only P* is blocked in every context; blocking is
  derivation-sensitive, since the derivation scoping *a plane crash* inside the description
  is not blocked (`Crash.an_only_survivor_not_blocked`) while the high-scope one is
  (`Crash.the_only_survivor_blocked`).
- `not_blocked_sentence_an_only`: no sentence-level Maximize Presupposition blocks
  *an only P*, because the definite contributes nothing to an *only* phrase and the two
  sentences mean the same (`sentence_the_only_eq_an_only`); the principle must compare
  expressions.
- `no_determinate_indefinites`: an indefinite that survives blocking has no defined update
  under the iota shift, while iota and the existential shift update alike where unique
  existence is settled (`readings_agree_of_existsUnique`).
- `only_eval_answer`: the adjectival entry is the earlier paper's exclusive schema at the
  question *what things are P*, with answers ranked by entailment.
- `Scenario.restrictor_rows`, `Lobner.rows`: the paper's predicative judgments are decided
  by weak uniqueness of the restrictor.

## Implementation notes

* Predicates are trivalent properties; the counting abbreviation `|P| ≤ 1` and the exclusive
  component of *only* are read on the positive extension, so the entries are computable
  given decidability, which finite models supply; the same abbreviations as formulas of the
  paper's logic, with Haug's universal quantifier, are proved pointwise equal.
* Relative Presuppositional Strength (71) as printed transposes the two expressions: it
  would make the indefinite dominate the definite, against the paper's own derivation on the
  same page, so the definition used is the transposition that derivation needs.
  Competitorhood, clause (i) of Maximize Presupposition (75), is glossed only in the
  appendix and is carried here by classical equivalence.
* The rival entries of Table 1 are classical and noncomputable, since only their
  presupposition profiles are stated. Lowering the individual-denoting Fregean entry by
  Partee's `ident` reads the undefined individual through `Option`, since the paper's logic
  makes identity bivalent even on the undefined individual; Löbner's individual-noun row of
  Table 2 is not of the article's type and is not compared.
* The appendix's possessive type shift prints the possessor arguments in the opposite order
  from the main text's sortal-to-relational shift; the main text is followed.
* The judgments the paper reports are the rows of `Data/Examples/CoppockBeaver2015.json`.
  Not modelled: Type Simplicity and the entity-introducing bias of §3.4–3.5, whose rows
  carry a `verb` feature and readings only; the accommodation comparison of §2.2.3 beyond
  the inconsistency it turns on; the determinate possessor, the possessor being a parameter;
  salience; plurals; the syntax of IL3 and its Pronouns and Traces rule; the focus on *only*
  behind the inference that Anna gave a talk.

## TODO

* The argumental Löbner rows compare iota-shifted possessives, which are classical; a
  computable iota over a finite type would let them join the `decide` ties.

## References

* [E. Coppock, D. Beaver, *Definiteness and determinacy* (2015)][coppock-beaver-2015]
* [E. Coppock, D. Beaver, *Principles of the exclusive muddle* (2014)][coppock-beaver-2014]
* [D. Beaver, E. Krahmer, *A Partial Account of Presupposition Projection*
  (2001)][beaver-krahmer-2001]
* [D. Haug, *Partial Dynamic Semantics for Anaphora: Compositionality without Syntactic
  Coindexation* (2014)][haug-2014]
* [Y. Winter, *Flexibility Principles in Boolean Semantics: The Interpretation of
  Coordination, Plurality, and Scope in Natural Language* (2001)][winter-2001b]
* [D. G. Fara, *Descriptions as Predicates* (2001)][fara-2001]
* [B. Partee, *Noun Phrase Interpretation and Type-shifting Principles* (1987)][partee-1987]
* [I. Heim, *Artikel und Definitheit* (1991)][heim-1991]
* [O. Percus, *Antipresuppositions* (2006)][percus-2006]
* [P. Elbourne, *Definite Descriptions* (2013)][elbourne-2013]
* [C. Vikner, P. A. Jensen, *A Semantic Analysis of the English Genitive: Interaction of
  Lexical and Formal Semantics* (2002)][vikner-jensen-2002]
-/

@[expose] public section

namespace CoppockBeaver2015

open Trivalent Trivalent.Prop3 Reference DynamicSemantics

variable {E W : Type*}

/-! ### Weak uniqueness and the lexical entries -/

/-- A predicate is weakly unique, the paper's `|P| ≤ 1`, when its positive extension is a
subsingleton. -/
def WeakUnique (P : Prop3 E) : Prop := P.posExt.Subsingleton

instance [Fintype E] [DecidableEq E] (P : Prop3 E) : Decidable (WeakUnique P) := by
  unfold WeakUnique Set.Subsingleton; infer_instance

/-- Nothing other than `x` is a `P` — the exclusive component of *only* (57). -/
def Exclusive (P : Prop3 E) (x : E) : Prop := ∀ y, y ≠ x → P y ≠ .true

instance [Fintype E] [DecidableEq E] : DecidableRel (Exclusive (E := E)) :=
  fun P x ↦ inferInstanceAs (Decidable (∀ y, y ≠ x → P y ≠ .true))

theorem not_exclusive_iff {P : Prop3 E} {x : E} :
    ¬ Exclusive P x ↔ ∃ y, y ≠ x ∧ P y = .true := by
  simp [Exclusive]

/-- Exclusivity is containment of the positive extension in the singleton. -/
theorem exclusive_iff_subset_singleton {P : Prop3 E} {x : E} :
    Exclusive P x ↔ P.posExt ⊆ {x} :=
  ⟨fun h y hy ↦ not_not.1 fun hyx ↦ h y hyx hy, fun h _ hyx hy ↦ hyx (h hy)⟩

/-- The Weak Fregean definite article (50) returns the restrictor, presupposing weak
uniqueness and no existence. -/
def the [DecidablePred (WeakUnique (E := E))] (P : Prop3 E) : Prop3 E :=
  fun x ↦ meetWeak (presuppose (ofProp (WeakUnique P))) (P x)

/-- The indefinite article (65) is an identity on predicates. -/
def an (P : Prop3 E) : Prop3 E := P

/-- Adjectival *only* (57) presupposes the prejacent and asserts exclusivity. -/
def only [DecidableRel (Exclusive (E := E))] (P : Prop3 E) : Prop3 E :=
  fun x ↦ meetWeak (presuppose (P x)) (ofProp (Exclusive P x))

section Only

variable [DecidableRel (Exclusive (E := E))] {P : Prop3 E} {x : E}

theorem only_eq_true_iff : only P x = .true ↔ P x = .true ∧ Exclusive P x := by simp [only]

theorem only_eq_false_iff : only P x = .false ↔ P x = .true ∧ ∃ y, y ≠ x ∧ P y = .true := by
  simp only [only, meetWeak_eq_false_iff, presuppose_ne_false, presuppose_eq_indet_iff,
    ofProp_eq_false_iff, not_exclusive_iff, false_and, false_or, ne_eq, not_not]

/-- *Only* presupposes its prejacent. -/
theorem only_eq_indet_iff : only P x = .indet ↔ P x ≠ .true := by simp [only]

/-- There is never more than one only `P`: an *only* phrase satisfies weak uniqueness. -/
theorem weakUnique_only (P : Prop3 E) : WeakUnique (only P) := fun _ hx y hy ↦
  not_not.1 fun h ↦ (only_eq_true_iff.1 hx).2 y (Ne.symm h) (only_eq_true_iff.1 hy).1

end Only

section The

variable [DecidablePred (WeakUnique (E := E))] {P : Prop3 E} {x : E}

theorem the_eq_of_weakUnique (h : WeakUnique P) : the P = P := by
  funext x; simp [the, h]

theorem the_eq_indet_of_not_weakUnique (h : ¬ WeakUnique P) (x : E) : the P x = .indet := by
  simp [the, h]

theorem the_eq_indet_iff : the P x = .indet ↔ ¬ WeakUnique P ∨ P x = .indet := by
  simp [the]

/-- The definite is classical exactly on weakly unique restrictors, where the noun is. -/
theorem the_ne_indet_iff : the P x ≠ .indet ↔ WeakUnique P ∧ P x ≠ .indet := by
  rw [ne_eq, the_eq_indet_iff, not_or, not_not]

/-- The uniqueness presupposition projects through negation, (45)–(46): the negated definite
is undefined exactly where the definite is. -/
theorem neg_the_eq_indet_iff : neg (the P x) = .indet ↔ ¬ WeakUnique P ∨ P x = .indet :=
  neg_eq_indet_iff.trans the_eq_indet_iff

/-- The empty restrictor is weakly unique, so the definite of an empty noun is false rather
than undefined — uniqueness without existence, the predicative reading of (13). -/
theorem the_false (x : E) : the (fun _ ↦ .false) x = .false :=
  congrFun (the_eq_of_weakUnique fun _ h ↦ by simp at h) x

/-- Existence does not project, (45a): *that is not the heart* is true when there are no
hearts. -/
theorem neg_the_false (x : E) : neg (the (fun _ ↦ .false) x) = .true := by rw [the_false]; rfl

/-- Two subjects of a true predicative definite coincide: weak uniqueness is what makes
Löbner's negation test contradictory and his conjunction test equivalent, (114)–(115). -/
theorem eq_of_the_eq_true {a b : E} (ha : the P a = .true) (hb : the P b = .true) : a = b := by
  have hne : the P a ≠ .indet := by rw [ha]; decide
  have hU : WeakUnique P := (the_ne_indet_iff.1 hne).1
  rw [the_eq_of_weakUnique hU] at ha hb
  exact hU ha hb

variable [DecidableRel (Exclusive (E := E))]

/-- The uniqueness presupposition of *the* is trivially satisfied by an *only* phrase, so
*the only P* means *only P*, (60). -/
theorem the_only (P : Prop3 E) : the (only P) = only P :=
  the_eq_of_weakUnique (weakUnique_only P)

/-- *x is not the only P* is true exactly when `x` is a `P` and so is something else: the
anti-uniqueness inference (64). -/
theorem anti_uniqueness :
    neg (the (only P) x) = .true ↔ P x = .true ∧ ∃ y, y ≠ x ∧ P y = .true := by
  rw [the_only, neg_eq_true_iff, only_eq_false_iff]

/-- The presupposition of *only* projects through negation (63): *x is not the only P* is
undefined exactly when `x` is no `P`. -/
theorem anti_uniqueness_presup : neg (the (only P) x) = .indet ↔ P x ≠ .true := by
  rw [the_only, neg_eq_indet_iff, only_eq_indet_iff]

end The

/-! ### The entries as formulas of the paper's logic

The abbreviation `|P| ≤ 1` of footnote 18 and the exclusive component of (57) are formulas
of IL3, read with Haug's universal quantifier and the Weak Kleene conditional. On a
restrictor that is somewhere defined the first is classical weak uniqueness, and where the
prejacent holds the second is classical exclusivity, so the entries above are the paper's
pointwise. -/

open Classical in
/-- `|P| ≤ 1` as a formula is `∀x[P(x) → ∀y[P(y) → x = y]]`. -/
noncomputable def atMostOneFormula (P : Prop3 E) : Trivalent :=
  forall' (fun x ↦ joinWeak (neg (P x)) (forall' (fun y ↦ joinWeak (neg (P y)) (ofProp (x = y)))))

open Classical in
/-- The exclusive component of *only* as a formula is `∀y[x ≠ y → ¬P(y)]`. -/
noncomputable def exclusiveFormula (P : Prop3 E) (x : E) : Trivalent :=
  forall' (fun y ↦ joinWeak (neg (ofProp (x ≠ y))) (neg (P y)))

theorem atMostOne_eq_ofProp {P : Prop3 E} [Decidable (WeakUnique P)] (h : ∃ x, P x ≠ .indet) :
    atMostOneFormula P = ofProp (WeakUnique P) := by
  obtain ⟨x₀, hx₀⟩ := h
  refine eq_of_indet_iff_of_true_iff ?_ ?_
  · simp only [atMostOneFormula, forall'_eq_indet_iff, joinWeak_eq_indet_iff, neg_eq_indet_iff,
      ofProp_ne_indet, or_false, iff_false]
    exact fun hall ↦ (hall x₀).elim hx₀ fun hy ↦ hx₀ (hy x₀)
  · simp only [atMostOneFormula, forall'_eq_true_iff, joinWeak_eq_indet_iff,
      joinWeak_eq_false_iff, neg_eq_indet_iff, neg_eq_false_iff, forall'_eq_indet_iff,
      forall'_eq_false_iff, ofProp_ne_indet, ofProp_eq_true_iff, ofProp_eq_false_iff, or_false,
      ne_eq]
    constructor
    · rintro ⟨-, hu⟩ x hx y hy
      by_contra hxy
      exact hu x ⟨hx, y, hy, hxy⟩
    · intro hu
      exact ⟨⟨x₀, fun h ↦ h.elim hx₀ fun hy ↦ hx₀ (hy x₀)⟩,
        fun x ⟨hx, y, hy, hxy⟩ ↦ hxy (hu hx hy)⟩

/-- The definite article is the paper's entry (50) pointwise. -/
theorem the_eq_meetWeak_atMostOne [DecidablePred (WeakUnique (E := E))] (P : Prop3 E) (x : E) :
    the P x = meetWeak (presuppose (atMostOneFormula P)) (P x) := by
  by_cases h : ∃ y, P y ≠ .indet
  · rw [atMostOne_eq_ofProp h]; rfl
  · push Not at h
    simp only [the, h x, meetWeak_indet_right]

theorem exclusiveFormula_eq_ofProp {P : Prop3 E} {x : E} [Decidable (Exclusive P x)]
    (h : P x = .true) :
    exclusiveFormula P x = ofProp (Exclusive P x) := by
  refine eq_of_indet_iff_of_true_iff ?_ ?_
  · simp only [exclusiveFormula, forall'_eq_indet_iff, joinWeak_eq_indet_iff, neg_eq_indet_iff,
      ofProp_ne_indet, false_or, iff_false]
    exact fun hall ↦ by simpa [h] using hall x
  · simp only [exclusiveFormula, forall'_eq_true_iff, joinWeak_eq_indet_iff,
      joinWeak_eq_false_iff, neg_eq_indet_iff, neg_eq_false_iff, ofProp_ne_indet,
      ofProp_eq_true_iff, false_or, ne_eq]
    constructor
    · rintro ⟨-, he⟩ y hyx hy
      exact he y ⟨Ne.symm hyx, hy⟩
    · intro he
      exact ⟨⟨x, by simp [h]⟩, fun y ⟨hxy, hy⟩ ↦ he y (Ne.symm hxy) hy⟩

/-- Adjectival *only* is the paper's entry (57) pointwise. -/
theorem only_eq_meetWeak_exclusiveFormula [DecidableRel (Exclusive (E := E))] (P : Prop3 E)
    (x : E) : only P x = meetWeak (presuppose (P x)) (exclusiveFormula P x) := by
  by_cases h : P x = .true
  · rw [exclusiveFormula_eq_ofProp h]; rfl
  · rw [only_eq_indet_iff.2 h, presuppose_eq_indet_iff.2 h, meetWeak_indet_left]

/-! ### The exclusive schema

Footnote 22: adjectival *only* instantiates the exclusive schema of [coppock-beaver-2014],
whose entry for the adjectival case constrains the current question to *what things are P*,
its answers ranked by entailment and predicating cumulative sums. Read on the space of
extensions of the noun, those answers are the propositions that the `P`s include a given
collection — upper sets, with the vacuous answer weakest and inert — and the schema's value
at an extension is the entry (57). -/

section Schema

/-- A partial answer to *what things are P* on the space of extensions says that the `P`s
include `X`. -/
def answer (X : Set E) : Set (Set E) := Set.Ici X

/-- Some true answer is at least as strong as the prejacent exactly when the `P`s include
`x`: the schema's presupposition is the prejacent. -/
theorem mem_atLeast_answer {w : Set E} {x : E} :
    w ∈ Focus.Particles.atLeast (· ⊆ ·) (Set.range answer) (answer {x}) ↔ x ∈ w := by
  simp only [Focus.Particles.mem_atLeast]
  constructor
  · rintro ⟨_, ⟨X, rfl⟩, hwX, hXx⟩
    exact hwX (Set.singleton_subset_iff.1 (hXx Set.self_mem_Ici))
  · exact fun hx ↦ ⟨answer {x}, ⟨{x}, rfl⟩, Set.singleton_subset_iff.2 hx, subset_rfl⟩

/-- No true answer is stronger than the prejacent exactly when the `P`s are contained in
`{x}`: the schema's assertion is exclusivity. -/
theorem mem_atMost_answer {w : Set E} {x : E} :
    w ∈ Focus.Particles.atMost (· ⊆ ·) (Set.range answer) (answer {x}) ↔ w ⊆ {x} := by
  simp only [Focus.Particles.mem_atMost, Set.forall_mem_range]
  constructor
  · intro h y hy
    exact Set.singleton_subset_iff.1
      (Set.Ici_subset_Ici.1 (h {y} (Set.singleton_subset_iff.2 hy)))
  · exact fun h X hX ↦ Set.Ici_subset_Ici.2 (hX.trans h)

/-- Adjectival *only* is the exclusive schema at the question *what things are P*: the
schema of [coppock-beaver-2014] over the answers, on the entailment scale, evaluated at an
extension, is the entry (57) of the predicate with that extension. -/
theorem only_eval_answer [DecidableRel (Exclusive (E := E))] (w : Set E)
    [DecidablePred (· ∈ w)] (x : E) :
    (Focus.Particles.only (· ⊆ ·) (Set.range answer) (answer {x})).eval w =
      only (fun y ↦ ofProp (y ∈ w)) x := by
  have hw : (Prop3.posExt fun y : E ↦ ofProp (y ∈ w)) = w := Set.ext fun y ↦ ofProp_eq_true_iff
  have hiff : Exclusive (fun y ↦ ofProp (y ∈ w)) x ↔ w ⊆ {x} := by
    rw [exclusive_iff_subset_singleton, hw]
  refine eq_of_indet_iff_of_true_iff ?_ ?_
  · rw [Presupposition.PartialProp.eval_eq_indet_iff, Focus.Particles.only_presup,
      only_eq_indet_iff, ne_eq, ofProp_eq_true_iff, not_iff_not]
    exact mem_atLeast_answer
  · rw [Presupposition.PartialProp.eval_eq_true_iff, Focus.Particles.only_presup,
      Focus.Particles.only_assertion, only_eq_true_iff, ofProp_eq_true_iff]
    exact and_congr mem_atLeast_answer (mem_atMost_answer.trans hiff.symm)

end Schema

/-! ### Presupposition profiles of the entries in Table 1 -/

/-- An entry presupposes uniqueness when it is classical only on weakly unique restrictors. -/
def PresupposesUniqueness (D : Prop3 E → Prop3 E) : Prop :=
  ∀ P x, D P x ≠ .indet → WeakUnique P

/-- An entry presupposes existence when it is classical only on nonempty restrictors. -/
def PresupposesExistence (D : Prop3 E → Prop3 E) : Prop :=
  ∀ P x, D P x ≠ .indet → P.posExt.Nonempty

/-- An entry classical on the full restrictor presupposes no uniqueness. -/
theorem not_presupposesUniqueness_of_ne_indet [Nontrivial E] {D : Prop3 E → Prop3 E} {x : E}
    (h : D (fun _ ↦ .true) x ≠ .indet) : ¬ PresupposesUniqueness D := fun hD ↦
  let ⟨_, _, hab⟩ := exists_pair_ne E
  hab (hD _ x h rfl rfl)

/-- An entry classical on the empty restrictor presupposes no existence. -/
theorem not_presupposesExistence_of_ne_indet {D : Prop3 E → Prop3 E} {x : E}
    (h : D (fun _ ↦ .false) x ≠ .indet) : ¬ PresupposesExistence D := fun hD ↦ by
  obtain ⟨y, hy⟩ := hD _ x h
  simp at hy

section Rivals

open Classical in
/-- The Russellian predicative entry (52a) asserts existence and uniqueness. -/
noncomputable def theRussellian (P : Prop3 E) : Prop3 E :=
  fun x ↦ meetWeak (ofProp (∃! y, P y = .true)) (P x)

open Classical in
/-- The Fregean predicative entry (52b) presupposes existence and uniqueness. -/
noncomputable def theFregean (P : Prop3 E) : Prop3 E :=
  fun x ↦ meetWeak (presuppose (ofProp (∃! y, P y = .true))) (P x)

open Classical in
/-- The Russellian quantificational entry (53a) asserts unique existence of the restrictor. -/
noncomputable def theRussellianGQ (P Q : Prop3 E) : Trivalent :=
  meetWeak (ofProp (∃! y, P y = .true)) (ofProp (P.posExt ⊆ Q.posExt))

open Classical in
/-- The Fregean quantificational entry (53b) presupposes unique existence of the restrictor. -/
noncomputable def theFregeanGQ (P Q : Prop3 E) : Trivalent :=
  meetWeak (presuppose (ofProp (∃! y, P y = .true))) (ofProp (P.posExt ⊆ Q.posExt))

open Classical in
/-- Partee's `be` lowers a generalized quantifier to a predicate. -/
noncomputable def be (G : Prop3 E → Trivalent) : Prop3 E := fun x ↦ G (fun y ↦ ofProp (y = x))

open Classical in
/-- Partee's `ident` applied to the individual-denoting Fregean entry yields the property of
being the unique `P`, undefined when there is none (Table 2). -/
noncomputable def identIota (P : Prop3 E) : Prop3 E :=
  fun x ↦ (Reference.iota (P · = .true)).elim .indet fun j ↦ ofProp (x = j)

theorem presupposesUniqueness_the [DecidablePred (WeakUnique (E := E))] :
    PresupposesUniqueness (the (E := E)) :=
  fun _ _ h ↦ (the_ne_indet_iff.1 h).1

theorem not_presupposesExistence_the [Nonempty E] [DecidablePred (WeakUnique (E := E))] :
    ¬ PresupposesExistence (the (E := E)) :=
  not_presupposesExistence_of_ne_indet (x := Classical.arbitrary E) (by rw [the_false]; decide)

theorem not_presupposesUniqueness_theRussellian [Nontrivial E] :
    ¬ PresupposesUniqueness (theRussellian (E := E)) :=
  not_presupposesUniqueness_of_ne_indet (x := Classical.arbitrary E) (by simp [theRussellian])

theorem not_presupposesExistence_theRussellian [Nonempty E] :
    ¬ PresupposesExistence (theRussellian (E := E)) :=
  not_presupposesExistence_of_ne_indet (x := Classical.arbitrary E) (by simp [theRussellian])

theorem theFregean_ne_indet_iff {P : Prop3 E} {x : E} :
    theFregean P x ≠ .indet ↔ (∃! y, P y = .true) ∧ P x ≠ .indet := by
  simp [theFregean, not_or]

theorem presupposesUniqueness_theFregean : PresupposesUniqueness (theFregean (E := E)) :=
  fun _ _ h ↦ (existsUnique_iff_nonempty_subsingleton.1 (theFregean_ne_indet_iff.1 h).1).2

theorem presupposesExistence_theFregean : PresupposesExistence (theFregean (E := E)) :=
  fun _ _ h ↦ (existsUnique_iff_nonempty_subsingleton.1 (theFregean_ne_indet_iff.1 h).1).1

/-- Lowering the Russellian quantifier by `be` presupposes nothing (Table 2). -/
theorem not_presupposesUniqueness_be_theRussellianGQ [Nontrivial E] :
    ¬ PresupposesUniqueness (fun P : Prop3 E ↦ be (theRussellianGQ P)) :=
  not_presupposesUniqueness_of_ne_indet (x := Classical.arbitrary E)
    (by simp [be, theRussellianGQ])

theorem not_presupposesExistence_be_theRussellianGQ [Nonempty E] :
    ¬ PresupposesExistence (fun P : Prop3 E ↦ be (theRussellianGQ P)) :=
  not_presupposesExistence_of_ne_indet (x := Classical.arbitrary E)
    (by simp [be, theRussellianGQ])

theorem be_theFregeanGQ_ne_indet_iff {P : Prop3 E} {x : E} :
    be (theFregeanGQ P) x ≠ .indet ↔ ∃! y, P y = .true := by
  simp [be, theFregeanGQ]

/-- Lowering the Fregean quantifier by `be` presupposes both existence and uniqueness. -/
theorem presupposesUniqueness_be_theFregeanGQ :
    PresupposesUniqueness (fun P : Prop3 E ↦ be (theFregeanGQ P)) := fun _ _ h ↦
  (existsUnique_iff_nonempty_subsingleton.1 (be_theFregeanGQ_ne_indet_iff.1 h)).2

theorem presupposesExistence_be_theFregeanGQ :
    PresupposesExistence (fun P : Prop3 E ↦ be (theFregeanGQ P)) := fun _ _ h ↦
  (existsUnique_iff_nonempty_subsingleton.1 (be_theFregeanGQ_ne_indet_iff.1 h)).1

theorem identIota_ne_indet_iff {P : Prop3 E} {x : E} :
    identIota P x ≠ .indet ↔ ∃! y, P y = .true := by
  classical
  rw [identIota, ← Reference.iota_isSome_iff]
  cases Reference.iota (P · = .true) <;> simp

/-- Lowering the individual-denoting Fregean entry by `ident` presupposes both existence and
uniqueness (Table 2). -/
theorem presupposesUniqueness_identIota : PresupposesUniqueness (identIota (E := E)) :=
  fun _ _ h ↦ (existsUnique_iff_nonempty_subsingleton.1 (identIota_ne_indet_iff.1 h)).2

theorem presupposesExistence_identIota : PresupposesExistence (identIota (E := E)) :=
  fun _ _ h ↦ (existsUnique_iff_nonempty_subsingleton.1 (identIota_ne_indet_iff.1 h)).1

/-- Under the Fregean entry *x is not the only P* is never true (§2.2.3): the presupposition
that there is exactly one only `P` is inconsistent with the assertion that `x`, a `P`, is
not one. The Weak Fregean entry has no such clash (`anti_uniqueness`). -/
theorem no_anti_uniqueness_fregean [DecidableRel (Exclusive (E := E))] (P : Prop3 E) (x : E) :
    neg (theFregean (only P) x) ≠ .true := by
  classical
  intro h
  rw [neg_eq_true_iff, theFregean] at h
  by_cases hu : ∃! y, only P y = .true
  · rw [ofProp_eq_true_iff.2 hu, presuppose_true, meetWeak_true_left] at h
    obtain ⟨y, hy, -⟩ := hu
    obtain ⟨hx, z, hzx, hz⟩ := only_eq_false_iff.1 h
    have hy' := only_eq_true_iff.1 hy
    by_cases hyx : y = x
    · subst hyx; exact hy'.2 z hzx hz
    · exact hy'.2 x (Ne.symm hyx) hx
  · rw [ofProp_eq_false_iff.2 hu, presuppose_false, meetWeak_indet_left] at h
    exact absurd h (by decide)

end Rivals

/-! ### Maximize Presupposition -/

/-- Two entries are classically equivalent (70) when, on bivalent restrictors, they agree
wherever both are classical. -/
def ClassicallyEquivalent (α β : Prop3 E → Prop3 E) : Prop :=
  ∀ P : Prop3 E, P.isBivalent → ∀ x, α P x ≠ .indet → β P x ≠ .indet → α P x = β P x

/-- `α` is presuppositionally at least as strong as `β` when, on bivalent restrictors,
wherever `α` is classical so is `β`. As printed, (71) quantifies the other way
around, which with (72) would have the indefinite dominate the definite; the paper's own
derivation of the opposite on the same page needs this transposition. -/
def AtLeastAsStrong (α β : Prop3 E → Prop3 E) : Prop :=
  ∀ P : Prop3 E, P.isBivalent → ∀ x, α P x ≠ .indet → β P x ≠ .indet

/-- `α` presuppositionally dominates `β` (72) when the two are classically equivalent and
`α` is strictly stronger. -/
def Dominates (α β : Prop3 E → Prop3 E) : Prop :=
  ClassicallyEquivalent α β ∧ AtLeastAsStrong α β ∧ ¬ AtLeastAsStrong β α

/-- The definite article dominates the indefinite. -/
theorem the_dominates_an [Nontrivial E] [DecidablePred (WeakUnique (E := E))] :
    Dominates (the (E := E)) an := by
  refine ⟨fun P _ x h _ ↦ ?_, fun P hP x _ ↦ ?_, fun h ↦ ?_⟩
  · rw [the_eq_of_weakUnique (the_ne_indet_iff.1 h).1]; rfl
  · exact (isBivalent_iff_forall_ne_indet P).1 hP x
  · obtain ⟨x, y, hxy⟩ := exists_pair_ne E
    have := h (fun _ ↦ .true) (fun _ ↦ .inl rfl) x (by simp [an])
    exact hxy ((the_ne_indet_iff.1 this).1 rfl rfl)

/-- Under Maximize Presupposition (75), `α` blocks its competitor `β` in context `C` and
derivation `D`, the sentence meaning as a function of the article's meaning, when `α`
dominates `β` and the two derivations update `C` alike; the update of a context with a
meaning (74) is the substrate's Heimian partial update `CCP.Partial.ofProp3`. Clause (i),
competitorhood, is glossed in the appendix as classical equivalence with a high-frequency
item and is carried by `Dominates`. -/
def Blocks (C : Set W) (D : (Prop3 E → Prop3 E) → Prop3 W) (α β : Prop3 E → Prop3 E) :
    Prop :=
  Dominates α β ∧ CCP.Partial.ofProp3 (D α) C = CCP.Partial.ofProp3 (D β) C

section Derivations

variable [DecidablePred (WeakUnique (E := E))] {C : Set W} (F : W → Prop3 E → Trivalent)
  (π : W → Prop3 E)

/-- Where the restrictor is weakly unique throughout the context, *the* blocks *a* in every
derivation applying the article to it. -/
theorem blocks_of_weakUnique [Nontrivial E] (h : ∀ w ∈ C, WeakUnique (π w)) :
    Blocks C (fun α w ↦ F w (α (π w))) the an :=
  ⟨the_dominates_an,
    CCP.Partial.ofProp3_congr fun w hw ↦ congrArg (F w) (the_eq_of_weakUnique (h w hw))⟩

/-- Where weak uniqueness fails at a world of the context, *the* fails to block *a* provided
the indefinite sentence is classical on the context and the material around the description
is strict in its undefinedness. -/
theorem not_blocks_of_not_weakUnique (hF : ∀ w, F w (fun _ ↦ .indet) = .indet) {w : W}
    (hw : w ∈ C) (h : ¬ WeakUnique (π w)) (hdom : ∀ w ∈ C, F w (π w) ≠ .indet) :
    ¬ Blocks C (fun α w ↦ F w (α (π w))) the an := by
  intro hb
  have hd : (CCP.Partial.ofProp3 (fun w ↦ F w (the (π w))) C).Dom := hb.2 ▸ hdom
  exact hd hw (by simp only [funext (the_eq_indet_of_not_weakUnique h), hF])

variable [DecidableRel (Exclusive (E := E))]

/-- *An only P* is blocked in every context (66): an *only* phrase meets the definite's
presupposition, so the two derivations coincide. -/
theorem an_only_blocked [Nontrivial E] :
    Blocks C (fun α w ↦ F w (α (only (π w)))) the an :=
  blocks_of_weakUnique F (fun w ↦ only (π w)) fun _ _ ↦ weakUnique_only _

/-- The sentence with *the* and the sentence with *a(n)* mean the same whenever the
description is an *only* phrase: the article contributes nothing to an inherently unique
description. -/
theorem sentence_the_only_eq_an_only :
    (fun w ↦ F w (the (only (π w)))) = fun w ↦ F w (an (only (π w))) := by
  funext w; rw [the_only]; rfl

/-- With the *the*-sentence as the alternative, the *an*-sentence is not blocked at sentence
level, although `an_only_blocked` blocks it at expression level: Maximize Presupposition
must compare expressions rather than sentences. -/
theorem not_blocked_sentence_an_only :
    ¬ Alternatives.Blocked
        (Alternatives.sameAssertion (fun p ↦ {w | p w = .true})
          (fun _ ↦ {fun w ↦ F w (the (only (π w)))}))
        (fun p ↦ {w | p w ≠ .indet}) (fun w ↦ F w (an (only (π w)))) := by
  rw [← sentence_the_only_eq_an_only]
  rintro ⟨q, ⟨hq, -⟩, hss⟩
  rw [Set.mem_singleton_iff] at hq
  subst hq
  exact hss.ne rfl

end Derivations

/-! ### Existence in argument position -/

/-- The iota shift (84) returns the unique satisfier, or the undefined individual. -/
noncomputable def iota (P : Prop3 E) : Option E := Reference.iota (P · = .true)

theorem iota_isSome_iff (P : Prop3 E) : (iota P).isSome ↔ ∃! x, P x = .true :=
  Reference.iota_isSome_iff _

theorem iota_eq_none_iff (P : Prop3 E) : iota P = none ↔ ¬ ∃! x, P x = .true := by
  rw [← Option.not_isSome_iff_eq_none, iota_isSome_iff]

/-- On the argumental reading of (14), the empty restrictor has no referent. -/
theorem iota_false : iota (fun _ ↦ .false : Prop3 E) = none :=
  (iota_eq_none_iff _).2 fun ⟨_, hx, _⟩ ↦ by simp at hx

/-- Under iota the article's presupposition adds nothing: iota presupposes uniqueness. -/
theorem iota_the [DecidablePred (WeakUnique (E := E))] (P : Prop3 E) :
    iota (the P) = iota P := by
  by_cases h : WeakUnique P
  · rw [the_eq_of_weakUnique h]
  · rw [(iota_eq_none_iff _).2 fun ⟨_, hx, _⟩ ↦ by
        simp [the_eq_indet_of_not_weakUnique h] at hx,
      (iota_eq_none_iff _).2 fun hu ↦ h (existsUnique_iff_nonempty_subsingleton.1 hu).2]

/-- On the determinate reading (87), undefinedness of the individual percolates (86), so the
sentence is classical exactly when the description has exactly one satisfier. -/
theorem elim_iota_ne_indet_iff (P : Prop3 E) (f : E → Trivalent) (hf : ∀ x, f x ≠ .indet) :
    (iota P).elim .indet f ≠ .indet ↔ ∃! x, P x = .true := by
  rw [← iota_isSome_iff]
  cases iota P <;> simp [hf]

/-- The existential shift (85) asserts a common satisfier of restrictor and scope. -/
noncomputable def ex (P Q : Prop3 E) : Trivalent := exists' (fun x ↦ meetWeak (P x) (Q x))

theorem ex_indet_left (Q : Prop3 E) : ex (fun _ ↦ .indet) Q = .indet :=
  (exists'_eq_indet_iff _).2 fun _ ↦ meetWeak_indet_left _

/-- The type shift of footnote 26 scopes an argument quantifier inside the modified
description — the further existential within the nominal that intervenes between the
determiner and the exclusive. -/
def scopeInside (T : E → Prop3 E) (Q : Prop3 E → Trivalent) (M : Prop3 E → Prop3 E) :
    Prop3 E :=
  fun x ↦ Q fun z ↦ M (fun y ↦ T z y) x

/-- Where some world of the context lacks a unique satisfier, the determinate reading has no
defined update (§3.2–3.3). -/
theorem not_update_dom_iota {C : Set W} {π : W → Prop3 E} (G : W → E → Trivalent) {w : W}
    (hw : w ∈ C) (h : ¬ ∃! x, π w x = .true) :
    ¬ (CCP.Partial.ofProp3 (fun w ↦ (iota (π w)).elim .indet (G w)) C).Dom := fun hd ↦
  hd hw (show (iota (π w)).elim .indet (G w) = .indet by
    rw [(iota_eq_none_iff _).2 h]
    rfl)

/-- Where every world of the context has exactly one satisfier, the determinate and the
indeterminate readings update the context alike (§3.4). -/
theorem readings_agree_of_existsUnique {C : Set W} {π Q : W → Prop3 E}
    (hπ : ∀ w ∈ C, (π w).isBivalent) (hQ : ∀ w ∈ C, (Q w).isBivalent)
    (h : ∀ w ∈ C, ∃! x, π w x = .true) :
    CCP.Partial.ofProp3 (fun w ↦ (iota (π w)).elim .indet (Q w)) C =
      CCP.Partial.ofProp3 (fun w ↦ ex (π w) (Q w)) C := by
  refine CCP.Partial.ofProp3_congr fun w hw ↦ ?_
  obtain ⟨x, hx, hu⟩ := h w hw
  have hi : iota (π w) = some x := (Reference.iota_eq_some_iff _).2 ⟨hx, hu⟩
  rw [hi, Option.elim_some, ex]
  refine (eq_of_indet_iff_of_true_iff ?_ ?_).symm
  · simp only [exists'_eq_indet_iff, meetWeak_eq_indet_iff, (hπ w hw).ne_indet,
      (hQ w hw).ne_indet, or_self]
    exact iff_of_false (fun h' ↦ h' x) id
  · simp only [exists'_eq_true_iff, meetWeak_eq_true_iff]
    exact ⟨fun ⟨y, hy, hq⟩ ↦ hu y hy ▸ hq, fun hq ↦ ⟨x, hx, hq⟩⟩

/-- An indefinite the definite fails to block has, at some world of the context, a
restrictor without a unique satisfier, so its reading under iota has no defined update —
no determinate indefinites (§3.3). -/
theorem no_determinate_indefinites [Nontrivial E] [DecidablePred (WeakUnique (E := E))]
    (F : W → Prop3 E → Trivalent) (π : W → Prop3 E) (G : W → E → Trivalent) {C : Set W}
    (h : ¬ Blocks C (fun α w ↦ F w (α (π w))) the an) :
    ¬ (CCP.Partial.ofProp3 (fun w ↦ (iota (π w)).elim .indet (G w)) C).Dom := fun hd ↦
  h <| blocks_of_weakUnique F π fun _ hw ↦
    (existsUnique_iff_nonempty_subsingleton.1 <| not_not.1 fun hu ↦
      not_update_dom_iota G hw hu hd).2

section AntiUniqueness

variable [DecidablePred (WeakUnique (E := E))] [DecidableRel (Exclusive (E := E))]
  {P Q : Prop3 E}

/-- Under the existential shift, negated *the only P* presupposes that there is a `P` and
denies that any sole `P` bears `Q`, by Quantifier Projection (A.4.2): the anti-uniqueness
reading (89)–(94). -/
theorem neg_ex_the_only (hP : P.isBivalent) (hQ : Q.isBivalent) :
    neg (ex (the (only P)) Q) =
      meetWeak (exists' (fun x ↦ presuppose (P x)))
        (neg (exists' (fun x ↦ meetWeak (P x) (meetWeak (ofProp (Exclusive P x)) (Q x))))) := by
  have hψ : isBivalent (fun x : E ↦ meetWeak (ofProp (Exclusive P x)) (Q x)) :=
    (isBivalent_iff_forall_ne_indet _).2 fun x ↦ by simp [hQ.ne_indet x]
  rw [ex, the_only]
  simp only [only, meetWeak_assoc]
  rw [exists'_meetWeak_presuppose hP hψ, neg_meetWeak_of_ne_false (exists'_presuppose_ne_false _)]

/-- The argumental reading presupposes a `P`, not an only `P` (§3.2): it is undefined
exactly when there is no `P`. -/
theorem argumental_anti_uniqueness_presup (hQ : Q.isBivalent) :
    neg (ex (the (only P)) Q) = .indet ↔ ∀ x, P x ≠ .true := by
  simp [ex, the_only, only, hQ.ne_indet]

/-- The argumental anti-uniqueness reading is true exactly when there is a `P` and no sole
`P` bears `Q`: (80a) with several talks, one of which Anna gave. -/
theorem argumental_anti_uniqueness (hQ : Q.isBivalent) :
    neg (ex (the (only P)) Q) = .true ↔
      (∃ x, P x = .true) ∧ ∀ x, P x = .true → Exclusive P x → Q x ≠ .true := by
  simp [ex, the_only, only, hQ.ne_indet]

end AntiUniqueness

/-! ### Possessives -/

/-- The sortal-to-relational shift (129) sends a noun to the `P`s possessed by `y`. The
appendix's TS3 prints the possessor arguments in the opposite order; the main text's is
followed. -/
def toRelational (poss : E → E → Trivalent) (P : Prop3 E) (y : E) : Prop3 E :=
  fun x ↦ meetWeak (P x) (poss x y)

/-- A possessive predicate presupposes nothing beyond its parts (§4.1, §4.3): it is classical
wherever noun and possession are, so predicative possessives signal no uniqueness. -/
theorem isBivalent_toRelational {poss : E → E → Trivalent} {P : Prop3 E} (hP : P.isBivalent)
    (hposs : ∀ x y, poss x y ≠ .indet) (y : E) : (toRelational poss P y).isBivalent :=
  (isBivalent_iff_forall_ne_indet _).2 fun x ↦ by simp [toRelational, hP.ne_indet x, hposs x y]

/-- Possessives do not compete with the definite article (§4): a possessive predicate is not
classically equivalent to *the*, since a weakly unique noun true of an individual the
possessor does not own separates them. -/
theorem possessive_not_competitor [DecidableEq E]
    [DecidablePred (WeakUnique (E := E))] {poss : E → E → Trivalent} {x y : E}
    (h : poss x y = .false) : ¬ ClassicallyEquivalent (fun P ↦ toRelational poss P y) the := by
  intro hc
  have hU : WeakUnique (fun z : E ↦ ofProp (z = x)) := fun a ha b hb ↦
    (ofProp_eq_true_iff.1 ha).trans (ofProp_eq_true_iff.1 hb).symm
  have h₁ : toRelational poss (fun z ↦ ofProp (z = x)) y x = .false := by
    show meetWeak (ofProp (x = x)) (poss x y) = .false
    rw [ofProp_eq_true_iff.2 rfl, meetWeak_true_left, h]
  have h₂ : the (fun z ↦ ofProp (z = x)) x = .true := by
    rw [the_eq_of_weakUnique hU]; exact ofProp_eq_true_iff.2 rfl
  have := hc (fun z ↦ ofProp (z = x))
    ((isBivalent_iff_forall_ne_indet _).2 fun _ ↦ ofProp_ne_indet)
    x (by dsimp only; rw [h₁]; decide) (by rw [h₂]; decide)
  dsimp only at this
  rw [h₁, h₂] at this
  exact absurd this (by decide)

/-- On the indeterminate reading of an argumental possessive (134), *he didn't make his only
appearance* presupposes an appearance and denies that he made any sole appearance of his. -/
theorem possessive_anti_uniqueness [DecidableRel (Exclusive (E := E))]
    {poss : E → E → Trivalent} {P Q : Prop3 E} (hQ : Q.isBivalent)
    (hposs : ∀ x y, poss x y ≠ .indet) (y : E) :
    neg (ex (toRelational poss (only P) y) Q) = .true ↔
      (∃ x, P x = .true) ∧
        ∀ x, P x = .true → Exclusive P x → poss x y = .true → Q x ≠ .true := by
  simp [ex, toRelational, only, hQ.ne_indet, hposs]

/-! ### The paper's models

Two worlds settle whether Frida wrote one book or two, the contexts of (73); two crashes
with a single survivor each make *only survivor of a plane crash*, with the crash scoped
inside the description as in (69), hold of two people. -/

namespace Frida

inductive Book | one | two
  deriving DecidableEq, Fintype

instance : Nontrivial Book := ⟨⟨.one, .two, by decide⟩⟩

inductive World | oneBook | twoBooks
  deriving DecidableEq, Fintype

/-- At one world Frida wrote one book; at the other, two. -/
def wrote : World → Prop3 Book
  | .oneBook, .one => .true
  | .oneBook, .two => .false
  | .twoBooks, _ => .true

/-- The speaker is reading the first book. -/
def reading (_ : World) : Prop3 Book := fun b ↦ ofProp (b = .one)

/-- `sentence α` interprets *I'm now reading (a/the) book she wrote* with the description
shifted existentially. -/
noncomputable def sentence (α : Prop3 Book → Prop3 Book) : Prop3 World :=
  fun w ↦ ex (α (wrote w)) (reading w)

private theorem sentence_an_eq_true (w : World) : sentence an w = .true :=
  (exists'_eq_true_iff _).2 ⟨.one, by cases w <;> decide⟩

/-- Once the context settles that Frida wrote exactly one book, *the* blocks *a*, (73b). -/
theorem blocks_of_one : Blocks {World.oneBook} sentence the an :=
  blocks_of_weakUnique (fun w P ↦ ex P (reading w)) wrote (by decide)

/-- While the context leaves the number of books open, *a* is not blocked, (73a). -/
theorem not_blocks_of_open : ¬ Blocks Set.univ sentence the an :=
  not_blocks_of_not_weakUnique (fun w P ↦ ex P (reading w)) wrote (fun w ↦ ex_indet_left _)
    (Set.mem_univ World.twoBooks) (by decide) fun w _ ↦
      ne_of_eq_of_ne (sentence_an_eq_true w) (by decide)

end Frida

namespace Crash

inductive Ind | crash₁ | crash₂ | scott | sam
  deriving DecidableEq, Fintype

instance : Nontrivial Ind := ⟨⟨.scott, .sam, by decide⟩⟩

/-- `crash` holds of the two crash individuals. -/
def crash : Prop3 Ind := fun z ↦ ofProp (z = .crash₁ ∨ z = .crash₂)

/-- Each crash has a single survivor: Scott of the first, Sam of the second. -/
def survived (z : Ind) : Prop3 Ind :=
  fun y ↦ ofProp ((z = .crash₁ ∧ y = .scott) ∨ (z = .crash₂ ∧ y = .sam))

/-- In *only survivor of a plane crash* (69), the type shift of footnote 26 scopes the crash
inside the description. -/
noncomputable def onlySurvivor : Prop3 Ind :=
  scopeInside survived (fun M ↦ exists' fun z ↦ meetWeak (crash z) (M z)) only

private theorem onlySurvivor_scott : onlySurvivor .scott = .true :=
  (exists'_eq_true_iff _).2 ⟨.crash₁, by decide⟩

private theorem onlySurvivor_sam : onlySurvivor .sam = .true :=
  (exists'_eq_true_iff _).2 ⟨.crash₂, by decide⟩

/-- The description holds of as many people as there are crashes with a single survivor. -/
theorem not_weakUnique_onlySurvivor : ¬ WeakUnique onlySurvivor := fun h ↦
  absurd (h onlySurvivor_scott onlySurvivor_sam) (by decide)

/-- *An only survivor of a plane crash* is not blocked on the derivation scoping the crash
inside the description, (68). -/
theorem an_only_survivor_not_blocked :
    ¬ Blocks Set.univ (fun α (_ : Unit) ↦ α onlySurvivor .scott) the an :=
  not_blocks_of_not_weakUnique (fun (_ : Unit) (P : Prop3 Ind) ↦ P .scott)
    (fun _ ↦ onlySurvivor) (fun _ ↦ rfl) (Set.mem_univ ()) not_weakUnique_onlySurvivor
    fun _ _ ↦ ne_of_eq_of_ne onlySurvivor_scott (by decide)

/-- The high-scope derivation places the crash above the article. -/
noncomputable def high (α : Prop3 Ind → Prop3 Ind) (_ : Unit) : Trivalent :=
  exists' fun z ↦ meetWeak (crash z) (α (only (survived z)) .scott)

/-- On the high-scope derivation the definite contributes nothing: each crash has a single
survivor. -/
private theorem high_the_eq_high_an : high the = high an := by
  funext u
  simp only [high, the_only]
  rfl

/-- *The only survivor of a plane crash* with the crash scoped high means what *an only
survivor of a plane crash* means with the crash scoped low. -/
theorem high_the_eq_low_an : high the = fun _ ↦ an onlySurvivor .scott := by
  funext u
  rw [high_the_eq_high_an]
  rfl

/-- On the high-scope derivation *the* blocks *a*: together with
`an_only_survivor_not_blocked`, blocking compares derivations rather than strings, so the
surviving surface form owes its life to the low-scope derivation. -/
theorem the_only_survivor_blocked : Blocks Set.univ high the an :=
  ⟨the_dominates_an, by rw [high_the_eq_high_an]⟩

end Crash

/-! ### The paper's judgments

The rows of `Data/Examples/CoppockBeaver2015.json` with a `restrictor` feature are the
predicative definites whose felicity turns on weak uniqueness alone, (10)–(12) and
(44)–(46): a restrictor that holds of nothing, the scenario in which iguanas have no hearts,
one that holds of both items of a two-item scenario, and an *only* phrase over the latter.
The rows with an `expression` feature are Löbner's predicative tests (114)–(115), in the
scenario where both subjects satisfy the noun. -/

namespace Scenario

inductive Item | this | that
  deriving DecidableEq, Fintype

/-- `restrictors` maps a row's `restrictor` feature to its predicate. -/
def restrictors : List (String × Prop3 Item) :=
  [("uniqueIfAny", fun _ ↦ .false), ("multiple", fun _ ↦ .true), ("only", only (fun _ ↦ .true))]

/-- A predicative-definite row is acceptable exactly when the definite of its restrictor is
classical of the subject. -/
theorem restrictor_rows : ∀ row ∈ Examples.all, ∀ P ∈ row.parse? "restrictor" restrictors,
    (row.judgment = .acceptable ↔ the P .this ≠ .indet) := by
  decide +kernel

end Scenario

namespace Lobner

/-- `expressions` maps a row's expression to the predicate it forms from the noun, in the
scenario where both subjects satisfy it: a predicative definite, indefinite, or possessive
with a single possessor. -/
def expressions : List (String × Prop3 Scenario.Item) :=
  [("predicativeDefinite", the fun _ ↦ .true), ("predicativeIndefinite", an fun _ ↦ .true),
   ("predicativePossessive", toRelational (fun _ _ ↦ .true) (fun _ ↦ .true) .this)]

/-- `verdicts` reads a row's verdict as whether its test forces the two subjects to
coincide. -/
def verdicts : List (String × Bool) :=
  [("contradictory", true), ("equivalent", true), ("notContradictory", false),
   ("notEquivalent", false)]

/-- With both subjects satisfying the noun, a row's test verdict is coincidence of the two
subjects exactly for the definite (`eq_of_the_eq_true`), the predicative tests
(114)–(115). -/
theorem rows : ∀ row ∈ Examples.all, ∀ p ∈ row.parse? "expression" expressions,
    ∀ v ∈ row.parse? "verdict" verdicts,
      (v = Bool.true ↔ ∀ a b, meetWeak (p a) (p b) = .true → a = b) := by
  decide +kernel

end Lobner

end CoppockBeaver2015
