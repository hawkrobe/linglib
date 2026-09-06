import Mathlib.Data.Part
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.DeriveFintype
import Linglib.Logic.Trivalent.Prop3
import Linglib.Semantics.Definiteness.Maximality
import Linglib.Semantics.Dynamic.Partial
import Linglib.Data.Examples.CoppockBeaver2015

/-!
# Coppock and Beaver's definiteness and determinacy

Definite, indefinite and possessive descriptions are underlyingly predicates, and existence
enters only when a description fills an argument position. The definite article contributes
a presupposition of weak uniqueness, that its restrictor holds of at most one individual, and
no existence presupposition, so that a predicative definite is felicitous when there may be
nothing satisfying it at all, and *Scott is not the only author of Waverley* presupposes that
Scott is an author while denying that he is the only one. The article and adjectival *only*
are entries in the Weak Kleene logic with ∂ of Beaver and Krahmer, in which the uniqueness
presupposition of *the* is trivially met by an *only* phrase and so contributes nothing; the
indefinite article is an identity on predicates that the definite blocks through a Maximize
Presupposition principle comparing expressions rather than sentences and sensitive to the
derivation, so that *an only author* is out in every context, *an only survivor of a plane
crash* survives because the crash scopes inside the description, and *a book she wrote* is
blocked exactly when the context settles that there is at most one. In argument position a
description is shifted by iota, which presupposes existence and uniqueness, or by an
existential shift under which the presupposition of *only* projects as the existence of a
satisfier of the noun rather than of the whole description, the anti-uniqueness reading of
*Anna didn't give the only invited talk*; an indefinite that survives blocking has no
defined update under iota, so there are no determinate indefinites. Possessives are
relational predicates carrying no presupposition and shift the same two ways. The judgments
the paper reports are the rows of `Data/Examples/CoppockBeaver2015.json`.

## Implementation notes

* Predicates are trivalent properties. The paper's counting abbreviations `|P| ≤ 1` and
  `|P| = 1` and the exclusive component of *only* are read on the positive extension through
  the substrate's `Uniqueness` and `Existence`, so that the entries are computable given
  decidability of weak uniqueness, which finite models supply; the same abbreviations as
  formulas of the paper's logic, with Haug's universal quantifier and the Weak Kleene
  conditional, are shown to give the same entries pointwise.
* Classical equivalence, relative presuppositional strength and domination are stated at
  the article's type over bivalent restrictors, the paper's defined entities. A derivation is
  the sentence meaning as a function of the article's meaning, the paper's replacement of one
  lexical item; the update of a context is the substrate's Heimian partial update of the
  meaning read as a partial proposition, defined when the meaning is classical throughout.
  Competitors, clause (i) of Maximize Presupposition, are the two articles, and
  clause (iii) is equality of the two updates as partial values, so that two undefined
  updates count as alike and the non-blocking theorem asks for the indefinite's update to be
  defined. The blocking theorems cover any derivation whose remaining material is strict in
  an undefined description, which the predicative and the existential continuations are.
* The rival entries of Table 1 are classical and noncomputable, since only their
  presupposition profiles are stated. The two rows of Table 2 lowered by `ident` from an
  individual-denoting entry are not of the article's type and are not compared.
* Predicates are indexed by worlds where contexts matter; the undefined individual is the
  `none` of `Option`.
* Not modelled: Type Simplicity (§3.4) and the entity-introducing bias of §3.5, whose rows
  carry a `verb` feature and readings only; the argument against local accommodation of
  §2.2.3; Löbner's tests (112)–(115), carried as rows; the determinate possessor of (130),
  the possessor being a parameter; salience; plurals (footnote 21); the syntax of IL3 and
  its Pronouns and Traces rule; the focus on *only* behind the inference that Anna gave a
  talk.

## TODO

* Relative Presuppositional Strength (71) as printed makes the presuppositions of `α` at
  least as strong as those of `β` when `α` is classical wherever `β` is, which would have the
  indefinite dominate the definite against the paper's own conclusion that the definite
  dominates; the definition used is the one that conclusion needs.
* The type shift of footnote 26 that scopes an indefinite inside an *only* phrase is
  instantiated in the plane-crash model rather than stated as an operator.

## References

* [E. Coppock, D. Beaver, *Definiteness and determinacy* (2015)][coppock-beaver-2015]
* [D. Beaver, E. Krahmer, *A Partial Account of Presupposition Projection*
  (2001)][beaver-krahmer-2001]
* [D. Haug, *Partial dynamic semantics for anaphora* (2014)][haug-2014]
* [Y. Winter, *Flexibility Principles in Boolean Semantics* (2001)][winter-2001b]
* [D. Graff, *Descriptions as predicates* (2001)][fara-2001]
* [B. Partee, *Noun phrase interpretation and type-shifting principles*
  (1987)][partee-1987]
* [I. Heim, *Artikel und Definitheit* (1991)][heim-1991]
* [O. Percus, *Antipresuppositions* (2006)][percus-2006]
* [P. Elbourne, *Definite Descriptions* (2013)][elbourne-2013]
* [C. Vikner, P. A. Jensen, *A semantic analysis of the English genitive*
  (2002)][vikner-jensen-2002]
-/

namespace CoppockBeaver2015

open Trivalent Trivalent.Prop3 Definiteness

variable {E W : Type*}

/-! ### Weak uniqueness and the lexical entries -/

/-- Weak uniqueness `|P| ≤ 1`: the substrate's `Uniqueness` on the positive extension. -/
def WeakUnique (P : Prop3 E) : Prop := Uniqueness (P · = .true)

instance [Fintype E] [DecidableEq E] (P : Prop3 E) : Decidable (WeakUnique P) := by
  unfold WeakUnique Uniqueness; infer_instance

/-- Nothing other than `x` is a `P`: the exclusive component of *only* (57). -/
def Exclusive (P : Prop3 E) (x : E) : Prop := ∀ y, y ≠ x → P y ≠ .true

instance [Fintype E] [DecidableEq E] : DecidableRel (Exclusive (E := E)) := λ _ _ => by
  unfold Exclusive; infer_instance

theorem not_exclusive_iff {P : Prop3 E} {x : E} :
    ¬ Exclusive P x ↔ ∃ y, y ≠ x ∧ P y = .true := by
  simp [Exclusive]

/-- The Weak Fregean definite article (50): the restrictor, presupposing weak uniqueness. -/
def the [DecidablePred (WeakUnique (E := E))] (P : Prop3 E) : Prop3 E :=
  λ x => meetWeak (presuppose (ofProp (WeakUnique P))) (P x)

/-- The indefinite article (65), an identity on predicates. -/
def an (P : Prop3 E) : Prop3 E := P

/-- Adjectival *only* (57): presupposes the prejacent and asserts exclusivity. -/
def only [DecidableRel (Exclusive (E := E))] (P : Prop3 E) : Prop3 E :=
  λ x => meetWeak (presuppose (P x)) (ofProp (Exclusive P x))

section Only

variable [DecidableRel (Exclusive (E := E))] {P : Prop3 E} {x : E}

theorem only_eq_true_iff : only P x = .true ↔ P x = .true ∧ Exclusive P x := by simp [only]

theorem only_eq_false_iff : only P x = .false ↔ P x = .true ∧ ∃ y, y ≠ x ∧ P y = .true := by
  simp only [only, meetWeak_eq_false_iff, presuppose_ne_false, presuppose_eq_indet_iff,
    ofProp_eq_false_iff, not_exclusive_iff, false_and, false_or, ne_eq, not_not]

/-- *Only* presupposes its prejacent. -/
theorem only_eq_indet_iff : only P x = .indet ↔ P x ≠ .true := by simp [only]

/-- There is never more than one only `P`: an *only* phrase satisfies weak uniqueness. -/
theorem weakUnique_only (P : Prop3 E) : WeakUnique (only P) := λ x y hx hy => by
  by_contra h
  exact (only_eq_true_iff.1 hx).2 y (Ne.symm h) (only_eq_true_iff.1 hy).1

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

/-- Uniqueness without existence: the empty restrictor is weakly unique, so the definite of
an empty noun is false rather than undefined, the predicative reading of (13). -/
theorem the_false (x : E) : the (λ _ => .false) x = .false :=
  congrFun (the_eq_of_weakUnique λ _ _ h => by simp at h) x

/-- Existence does not project, (45a): *that is not the heart* is true when there are no
hearts. -/
theorem neg_the_false (x : E) : neg (the (λ _ => .false) x) = .true := by rw [the_false]; rfl

variable [DecidableRel (Exclusive (E := E))]

/-- (60): the uniqueness presupposition of *the* is trivially satisfied by an *only* phrase,
so *the only P* means *only P*. -/
theorem the_only (P : Prop3 E) : the (only P) = only P :=
  the_eq_of_weakUnique (weakUnique_only P)

/-- The anti-uniqueness inference (64): *x is not the only P* is true exactly when `x` is a
`P` and so is something else. -/
theorem neg_the_only_eq_true_iff :
    neg (the (only P) x) = .true ↔ P x = .true ∧ ∃ y, y ≠ x ∧ P y = .true := by
  rw [the_only, neg_eq_true_iff, only_eq_false_iff]

/-- The presupposition of *only* projects through negation (63): *x is not the only P* is
undefined exactly when `x` is no `P`. -/
theorem neg_the_only_eq_indet_iff : neg (the (only P) x) = .indet ↔ P x ≠ .true := by
  rw [the_only, neg_eq_indet_iff, only_eq_indet_iff]

end The

/-! ### The entries as formulas of the paper's logic

The abbreviation `|P| ≤ 1` of footnote 18 and the exclusive component of (57) are formulas
of IL3, read with Haug's universal quantifier and the Weak Kleene conditional. On a
restrictor that is somewhere defined the first is classical weak uniqueness, and where the
prejacent holds the second is classical exclusivity, so the entries above are the paper's
pointwise. -/

open Classical in
/-- `|P| ≤ 1` as a formula: `∀x[P(x) → ∀y[P(y) → x = y]]`. -/
noncomputable def atMostOneFormula (P : Prop3 E) : Trivalent :=
  forall' (λ x => joinWeak (neg (P x)) (forall' (λ y => joinWeak (neg (P y)) (ofProp (x = y)))))

open Classical in
/-- The exclusive component of *only* as a formula: `∀y[x ≠ y → ¬P(y)]`. -/
noncomputable def exclusiveFormula (P : Prop3 E) (x : E) : Trivalent :=
  forall' (λ y => joinWeak (neg (ofProp (x ≠ y))) (neg (P y)))

theorem atMostOne_eq_ofProp {P : Prop3 E} [Decidable (WeakUnique P)] (h : ∃ x, P x ≠ .indet) :
    atMostOneFormula P = ofProp (WeakUnique P) := by
  obtain ⟨x₀, hx₀⟩ := h
  refine eq_of_indet_iff_of_true_iff ?_ ?_
  · simp only [atMostOneFormula, forall'_eq_indet_iff, joinWeak_eq_indet_iff, neg_eq_indet_iff,
      ofProp_ne_indet, or_false, iff_false]
    exact λ hall => (hall x₀).elim hx₀ λ hy => hx₀ (hy x₀)
  · simp only [atMostOneFormula, forall'_eq_true_iff, joinWeak_eq_indet_iff,
      joinWeak_eq_false_iff, neg_eq_indet_iff, neg_eq_false_iff, forall'_eq_indet_iff,
      forall'_eq_false_iff, ofProp_ne_indet, ofProp_eq_true_iff, ofProp_eq_false_iff, or_false,
      ne_eq]
    constructor
    · rintro ⟨-, hu⟩ x y hx hy
      by_contra hxy
      exact hu x ⟨hx, y, hy, hxy⟩
    · intro hu
      exact ⟨⟨x₀, λ h => h.elim hx₀ λ hy => hx₀ (hy x₀)⟩,
        λ x ⟨hx, y, hy, hxy⟩ => hxy (hu x y hx hy)⟩

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
    exact λ hall => by simpa [h] using hall x
  · simp only [exclusiveFormula, forall'_eq_true_iff, joinWeak_eq_indet_iff, joinWeak_eq_false_iff,
      neg_eq_indet_iff, neg_eq_false_iff, ofProp_ne_indet, ofProp_eq_true_iff, false_or, ne_eq]
    constructor
    · rintro ⟨-, he⟩ y hyx hy
      exact he y ⟨Ne.symm hyx, hy⟩
    · intro he
      exact ⟨⟨x, by simp [h]⟩, λ y ⟨hxy, hy⟩ => he y (Ne.symm hxy) hy⟩

/-- Adjectival *only* is the paper's entry (57) pointwise. -/
theorem only_eq_meetWeak_exclusiveFormula [DecidableRel (Exclusive (E := E))] (P : Prop3 E)
    (x : E) : only P x = meetWeak (presuppose (P x)) (exclusiveFormula P x) := by
  by_cases h : P x = .true
  · rw [exclusiveFormula_eq_ofProp h]; rfl
  · rw [only_eq_indet_iff.2 h, presuppose_eq_indet_iff.2 h, meetWeak_indet_left]

/-! ### Presupposition profiles of the entries in Table 1 -/

/-- An entry presupposes uniqueness when it is classical only on weakly unique restrictors. -/
def PresupposesUniqueness (D : Prop3 E → Prop3 E) : Prop :=
  ∀ P x, D P x ≠ .indet → WeakUnique P

/-- An entry presupposes existence when it is classical only on nonempty restrictors. -/
def PresupposesExistence (D : Prop3 E → Prop3 E) : Prop :=
  ∀ P x, D P x ≠ .indet → Existence (P · = .true)

section Rivals

open Classical in
/-- The Russellian predicative entry (52a): existence and uniqueness asserted. -/
noncomputable def theRussellian (P : Prop3 E) : Prop3 E :=
  λ x => meetWeak (ofProp (∃! y, P y = .true)) (P x)

open Classical in
/-- The Fregean predicative entry (52b): existence and uniqueness presupposed. -/
noncomputable def theFregean (P : Prop3 E) : Prop3 E :=
  λ x => meetWeak (presuppose (ofProp (∃! y, P y = .true))) (P x)

open Classical in
/-- The Russellian quantificational entry (53a). -/
noncomputable def theRussellianGQ (P Q : Prop3 E) : Trivalent :=
  meetWeak (ofProp (∃! y, P y = .true)) (ofProp (P.posExt ⊆ Q.posExt))

open Classical in
/-- The Fregean quantificational entry (53b). -/
noncomputable def theFregeanGQ (P Q : Prop3 E) : Trivalent :=
  meetWeak (presuppose (ofProp (∃! y, P y = .true))) (ofProp (P.posExt ⊆ Q.posExt))

open Classical in
/-- Partee's `be`, lowering a generalized quantifier to a predicate. -/
noncomputable def be (G : Prop3 E → Trivalent) : Prop3 E := λ x => G (λ y => ofProp (y = x))

theorem presupposesUniqueness_the [DecidablePred (WeakUnique (E := E))] :
    PresupposesUniqueness (the (E := E)) :=
  λ _ _ h => (the_ne_indet_iff.1 h).1

theorem not_presupposesExistence_the [Nonempty E] [DecidablePred (WeakUnique (E := E))] :
    ¬ PresupposesExistence (the (E := E)) := by
  intro h
  obtain ⟨y, hy⟩ := h (λ _ => .false) (Classical.arbitrary E) (by rw [the_false]; decide)
  simp at hy

theorem not_presupposesUniqueness_theRussellian [Nontrivial E] :
    ¬ PresupposesUniqueness (theRussellian (E := E)) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne E
  exact hxy (h (λ _ => .true) x (by simp [theRussellian]) x y rfl rfl)

theorem not_presupposesExistence_theRussellian [Nonempty E] :
    ¬ PresupposesExistence (theRussellian (E := E)) := by
  intro h
  obtain ⟨y, hy⟩ :=
    h (λ _ => .false) (Classical.arbitrary E) (by simp [theRussellian])
  simp at hy

theorem theFregean_ne_indet_iff {P : Prop3 E} {x : E} :
    theFregean P x ≠ .indet ↔ (∃! y, P y = .true) ∧ P x ≠ .indet := by
  simp [theFregean, not_or]

theorem presupposesUniqueness_theFregean : PresupposesUniqueness (theFregean (E := E)) :=
  λ _ _ h => ((existsUnique_iff_existence_and_uniqueness _).1 (theFregean_ne_indet_iff.1 h).1).2

theorem presupposesExistence_theFregean : PresupposesExistence (theFregean (E := E)) :=
  λ _ _ h => ((existsUnique_iff_existence_and_uniqueness _).1 (theFregean_ne_indet_iff.1 h).1).1

/-- Lowering the Russellian quantifier by `be` presupposes nothing (Table 2). -/
theorem not_presupposesUniqueness_be_theRussellianGQ [Nontrivial E] :
    ¬ PresupposesUniqueness (λ P : Prop3 E => be (theRussellianGQ P)) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne E
  exact hxy (h (λ _ => .true) x (by simp [be, theRussellianGQ]) x y rfl rfl)

theorem not_presupposesExistence_be_theRussellianGQ [Nonempty E] :
    ¬ PresupposesExistence (λ P : Prop3 E => be (theRussellianGQ P)) := by
  intro h
  obtain ⟨y, hy⟩ := h (λ _ => .false) (Classical.arbitrary E)
    (by simp [be, theRussellianGQ])
  simp at hy

theorem be_theFregeanGQ_ne_indet_iff {P : Prop3 E} {x : E} :
    be (theFregeanGQ P) x ≠ .indet ↔ ∃! y, P y = .true := by
  simp [be, theFregeanGQ]

/-- Lowering the Fregean quantifier by `be` presupposes both existence and uniqueness. -/
theorem presupposesUniqueness_be_theFregeanGQ :
    PresupposesUniqueness (λ P : Prop3 E => be (theFregeanGQ P)) := λ _ _ h =>
  ((existsUnique_iff_existence_and_uniqueness _).1 (be_theFregeanGQ_ne_indet_iff.1 h)).2

theorem presupposesExistence_be_theFregeanGQ :
    PresupposesExistence (λ P : Prop3 E => be (theFregeanGQ P)) := λ _ _ h =>
  ((existsUnique_iff_existence_and_uniqueness _).1 (be_theFregeanGQ_ne_indet_iff.1 h)).1

end Rivals

/-! ### Maximize Presupposition -/

/-- Classical equivalence (70) at the article's type: on bivalent restrictors the two entries
agree wherever both are classical. -/
def ClassicallyEquivalent (α β : Prop3 E → Prop3 E) : Prop :=
  ∀ P : Prop3 E, P.isBivalent → ∀ x, α P x ≠ .indet → β P x ≠ .indet → α P x = β P x

/-- Relative presuppositional strength (71): `α` is at least as strong as `β` when, on
bivalent restrictors, wherever `α` is classical so is `β`. -/
def AtLeastAsStrong (α β : Prop3 E → Prop3 E) : Prop :=
  ∀ P : Prop3 E, P.isBivalent → ∀ x, α P x ≠ .indet → β P x ≠ .indet

/-- Presuppositional domination (72). -/
def Dominates (α β : Prop3 E → Prop3 E) : Prop :=
  ClassicallyEquivalent α β ∧ AtLeastAsStrong α β ∧ ¬ AtLeastAsStrong β α

/-- The definite article dominates the indefinite. -/
theorem the_dominates_an [Nontrivial E] [DecidablePred (WeakUnique (E := E))] :
    Dominates (the (E := E)) an := by
  refine ⟨λ P _ x h _ => ?_, λ P hP x _ => ?_, λ h => ?_⟩
  · rw [the_eq_of_weakUnique (the_ne_indet_iff.1 h).1]; rfl
  · exact (isBivalent_iff_forall_ne_indet P).1 hP x
  · obtain ⟨x, y, hxy⟩ := exists_pair_ne E
    have := h (λ _ => .true) (λ _ => .inl rfl) x (by simp [an])
    exact hxy ((the_ne_indet_iff.1 this).1 x y rfl rfl)

/-- The update of a context with a sentential meaning (74), the Heimian partial update of
the meaning read as a partial proposition: defined when the meaning is classical throughout
the context, and then the worlds of the context where it is true. -/
def update (C : Set W) (p : Prop3 W) : Part (Set W) :=
  DynamicSemantics.CCP.Partial.ofPartialProp (Presupposition.PartialProp.ofProp3 p) C

/-- Meanings that agree on the context update it alike. -/
theorem update_congr {C : Set W} {p q : Prop3 W} (h : ∀ w ∈ C, p w = q w) :
    update C p = update C q :=
  Part.ext' (forall₂_congr λ w hw => show p w ≠ .indet ↔ q w ≠ .indet by rw [h w hw])
    λ _ _ => Set.ext λ w => and_congr_right λ hw => show p w = .true ↔ q w = .true by rw [h w hw]

/-- Maximize Presupposition (75): in context `C`, `α` blocks its competitor `β` in the
derivation `D`, the sentence meaning as a function of the article's meaning, when `α`
dominates `β` and the two derivations update `C` alike. -/
def Blocks (C : Set W) (D : (Prop3 E → Prop3 E) → Prop3 W) (α β : Prop3 E → Prop3 E) :
    Prop :=
  Dominates α β ∧ update C (D α) = update C (D β)

section Derivations

variable [DecidablePred (WeakUnique (E := E))] {C : Set W} (F : W → Prop3 E → Trivalent)
  (π : W → Prop3 E)

/-- Where the restrictor is weakly unique throughout the context, *the* blocks *a* in every
derivation applying the article to it. -/
theorem blocks_of_weakUnique [Nontrivial E] (h : ∀ w ∈ C, WeakUnique (π w)) :
    Blocks C (λ α w => F w (α (π w))) the an :=
  ⟨the_dominates_an, update_congr λ w hw => congrArg (F w) (the_eq_of_weakUnique (h w hw))⟩

/-- Where weak uniqueness fails at a world of the context, *the* fails to block *a* provided
the indefinite sentence is classical on the context and the material around the description
is strict in its undefinedness. -/
theorem not_blocks_of_not_weakUnique (hF : ∀ w, F w (λ _ => .indet) = .indet) {w : W}
    (hw : w ∈ C) (h : ¬ WeakUnique (π w)) (hdom : ∀ w ∈ C, F w (π w) ≠ .indet) :
    ¬ Blocks C (λ α w => F w (α (π w))) the an := by
  intro hb
  have hd : (update C (λ w => F w (the (π w)))).Dom := hb.2 ▸ hdom
  exact hd hw (by simp only [funext (the_eq_indet_of_not_weakUnique h), hF])

/-- *An only P* is blocked in every context (66): an *only* phrase meets the definite's
presupposition, so the two derivations coincide. -/
theorem blocks_only [Nontrivial E] [DecidableRel (Exclusive (E := E))] :
    Blocks C (λ α w => F w (α (only (π w)))) the an :=
  blocks_of_weakUnique F (λ w => only (π w)) λ _ _ => weakUnique_only _

end Derivations

/-! ### Existence in argument position -/

/-- The iota shift (84): the unique satisfier, or the undefined individual. -/
noncomputable def iota (P : Prop3 E) : Option E := russellIota (P · = .true)

theorem iota_isSome_iff (P : Prop3 E) : (iota P).isSome ↔ ∃! x, P x = .true :=
  russellIota_isSome_iff_exists_unique _

theorem iota_eq_none_iff (P : Prop3 E) : iota P = none ↔ ¬ ∃! x, P x = .true := by
  rw [← Option.not_isSome_iff_eq_none, iota_isSome_iff]

/-- The argumental reading of (14): the empty restrictor has no referent. -/
theorem iota_false : iota (λ _ => .false : Prop3 E) = none :=
  (iota_eq_none_iff _).2 λ ⟨_, hx, _⟩ => by simp at hx

/-- Under iota the article's presupposition adds nothing: iota presupposes uniqueness. -/
theorem iota_the [DecidablePred (WeakUnique (E := E))] (P : Prop3 E) : iota (the P) = iota P := by
  by_cases h : WeakUnique P
  · rw [the_eq_of_weakUnique h]
  · rw [(iota_eq_none_iff _).2 λ ⟨_, hx, _⟩ => by simp [the_eq_indet_of_not_weakUnique h] at hx,
      (iota_eq_none_iff _).2 λ hu => h ((existsUnique_iff_existence_and_uniqueness _).1 hu).2]

/-- The determinate reading (87): undefinedness of the individual percolates (86), so the
sentence is classical exactly when the description has exactly one satisfier. -/
theorem elim_iota_ne_indet_iff (P : Prop3 E) (f : E → Trivalent) (hf : ∀ x, f x ≠ .indet) :
    (iota P).elim .indet f ≠ .indet ↔ ∃! x, P x = .true := by
  rw [← iota_isSome_iff]
  cases iota P <;> simp [hf]

/-- The existential shift (85). -/
noncomputable def ex (P Q : Prop3 E) : Trivalent := exists' (λ x => meetWeak (P x) (Q x))

theorem ex_indet_left (Q : Prop3 E) : ex (λ _ => .indet) Q = .indet :=
  (exists'_eq_indet_iff _).2 λ _ => meetWeak_indet_left _

/-- No determinate indefinites (§3.3): an indefinite the definite fails to block has, at some
world of the context, a restrictor without a unique satisfier, so its reading under iota has
no defined update. -/
theorem not_update_dom_iota_of_not_blocks [Nontrivial E] [DecidablePred (WeakUnique (E := E))]
    (F : W → Prop3 E → Trivalent) (π : W → Prop3 E) (G : W → E → Trivalent) {C : Set W}
    (h : ¬ Blocks C (λ α w => F w (α (π w))) the an) :
    ¬ (update C (λ w => (iota (π w)).elim .indet (G w))).Dom := λ hd =>
  h (blocks_of_weakUnique F π λ w hw => by
    have hne : (iota (π w)).elim .indet (G w) ≠ .indet := hd hw
    rcases hi : iota (π w) with _ | x
    · simp [hi] at hne
    · exact ((existsUnique_iff_existence_and_uniqueness _).1
        ((iota_isSome_iff _).1 (by rw [hi]; rfl))).2)

section AntiUniqueness

variable [DecidablePred (WeakUnique (E := E))] [DecidableRel (Exclusive (E := E))]
  {P Q : Prop3 E}

/-- The anti-uniqueness reading (89)–(94), by Quantifier Projection (A.4.2): under the
existential shift, negated *the only P* presupposes that there is a `P` and denies that any
sole `P` bears `Q`. -/
theorem neg_ex_the_only (hP : P.isBivalent) (hQ : Q.isBivalent) :
    neg (ex (the (only P)) Q) =
      meetWeak (exists' (λ x => presuppose (P x)))
        (neg (exists' (λ x => meetWeak (P x) (meetWeak (ofProp (Exclusive P x)) (Q x))))) := by
  have hψ : isBivalent (λ x : E => meetWeak (ofProp (Exclusive P x)) (Q x)) :=
    (isBivalent_iff_forall_ne_indet _).2 λ x => by simp [hQ.ne_indet x]
  rw [ex, the_only]
  simp only [only, meetWeak_assoc]
  rw [exists'_meetWeak_presuppose hP hψ, neg_meetWeak_of_ne_false (exists'_presuppose_ne_false _)]

/-- The reading presupposes a `P`, not an only `P` (§3.2): it is undefined exactly when
there is no `P`. -/
theorem neg_ex_the_only_eq_indet_iff (hQ : Q.isBivalent) :
    neg (ex (the (only P)) Q) = .indet ↔ ∀ x, P x ≠ .true := by
  simp [ex, the_only, only, hQ.ne_indet]

/-- The reading is true exactly when there is a `P` and no sole `P` bears `Q`: (80a) with
several talks, one of which Anna gave. -/
theorem neg_ex_the_only_eq_true_iff (hQ : Q.isBivalent) :
    neg (ex (the (only P)) Q) = .true ↔
      (∃ x, P x = .true) ∧ ∀ x, P x = .true → Exclusive P x → Q x ≠ .true := by
  simp [ex, the_only, only, hQ.ne_indet]

end AntiUniqueness

/-! ### Possessives -/

/-- The sortal-to-relational shift (129): the `P`s possessed by `y`. -/
def toRelational (poss : E → E → Trivalent) (P : Prop3 E) (y : E) : Prop3 E :=
  λ x => meetWeak (P x) (poss x y)

/-- A possessive predicate presupposes nothing beyond its parts (§4.1, §4.3): it is classical
wherever noun and possession are, so predicative possessives signal no uniqueness. -/
theorem isBivalent_toRelational {poss : E → E → Trivalent} {P : Prop3 E} (hP : P.isBivalent)
    (hposs : ∀ x y, poss x y ≠ .indet) (y : E) : (toRelational poss P y).isBivalent :=
  (isBivalent_iff_forall_ne_indet _).2 λ x => by simp [toRelational, hP.ne_indet x, hposs x y]

/-- Possessives do not compete with the definite article (§4): a possessive predicate is not
classically equivalent to *the*, since a weakly unique noun true of an individual the
possessor does not own separates them. -/
theorem not_classicallyEquivalent_toRelational_the [DecidableEq E]
    [DecidablePred (WeakUnique (E := E))] {poss : E → E → Trivalent} {x y : E}
    (h : poss x y = .false) : ¬ ClassicallyEquivalent (λ P => toRelational poss P y) the := by
  intro hc
  have hU : WeakUnique (λ z : E => ofProp (z = x)) := λ a b ha hb =>
    (ofProp_eq_true_iff.1 ha).trans (ofProp_eq_true_iff.1 hb).symm
  have h₁ : toRelational poss (λ z => ofProp (z = x)) y x = .false := by
    show meetWeak (ofProp (x = x)) (poss x y) = .false
    rw [ofProp_eq_true_iff.2 rfl, meetWeak_true_left, h]
  have h₂ : the (λ z => ofProp (z = x)) x = .true := by
    rw [the_eq_of_weakUnique hU]; exact ofProp_eq_true_iff.2 rfl
  have := hc (λ z => ofProp (z = x)) ((isBivalent_iff_forall_ne_indet _).2 λ _ => ofProp_ne_indet)
    x (by dsimp only; rw [h₁]; decide) (by rw [h₂]; decide)
  dsimp only at this
  rw [h₁, h₂] at this
  exact absurd this (by decide)

/-- The indeterminate reading of an argumental possessive (134): *he didn't make his only
appearance* presupposes an appearance and denies that he made any sole appearance of his. -/
theorem neg_ex_toRelational_only [DecidableRel (Exclusive (E := E))]
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

/-- What Frida wrote at each world. -/
def wrote : World → Prop3 Book
  | .oneBook, .one => .true
  | .oneBook, .two => .false
  | .twoBooks, _ => .true

/-- What the speaker is reading. -/
def reading (_ : World) : Prop3 Book := λ b => ofProp (b = .one)

/-- *I'm now reading (a/the) book she wrote*, with the description shifted existentially. -/
noncomputable def sentence (α : Prop3 Book → Prop3 Book) : Prop3 World :=
  λ w => ex (α (wrote w)) (reading w)

theorem sentence_an_eq_true (w : World) : sentence an w = .true :=
  (exists'_eq_true_iff _).2 ⟨.one, by cases w <;> decide⟩

/-- (73b): once the context settles that Frida wrote exactly one book, *the* blocks *a*. -/
theorem blocks_of_one : Blocks {World.oneBook} sentence the an :=
  blocks_of_weakUnique (λ w P => ex P (reading w)) wrote (by decide)

/-- (73a): while the context leaves the number of books open, *a* is not blocked. -/
theorem not_blocks_of_open : ¬ Blocks Set.univ sentence the an :=
  not_blocks_of_not_weakUnique (λ w P => ex P (reading w)) wrote (λ w => ex_indet_left _)
    (Set.mem_univ World.twoBooks) (by decide) λ w _ =>
      ne_of_eq_of_ne (sentence_an_eq_true w) (by decide)

end Frida

namespace Crash

inductive Ind | crash₁ | crash₂ | scott | sam
  deriving DecidableEq, Fintype

/-- The plane crashes. -/
def crash : Prop3 Ind := λ z => ofProp (z = .crash₁ ∨ z = .crash₂)

/-- Who survived which crash: one survivor each. -/
def survived (z : Ind) : Prop3 Ind :=
  λ y => ofProp ((z = .crash₁ ∧ y = .scott) ∨ (z = .crash₂ ∧ y = .sam))

/-- (69): *only survivor of a plane crash* with the crash scoped inside the description. -/
noncomputable def onlySurvivor : Prop3 Ind :=
  λ x => exists' (λ z => meetWeak (crash z) (only (survived z) x))

theorem onlySurvivor_scott : onlySurvivor .scott = .true :=
  (exists'_eq_true_iff _).2 ⟨.crash₁, by decide⟩

theorem onlySurvivor_sam : onlySurvivor .sam = .true :=
  (exists'_eq_true_iff _).2 ⟨.crash₂, by decide⟩

/-- The description holds of as many people as there are crashes with a single survivor. -/
theorem not_weakUnique_onlySurvivor : ¬ WeakUnique onlySurvivor := λ h =>
  absurd (h .scott .sam onlySurvivor_scott onlySurvivor_sam) (by decide)

/-- (68): *an only survivor of a plane crash* is not blocked on this derivation. -/
theorem not_blocks : ¬ Blocks Set.univ (λ α (_ : Unit) => α onlySurvivor .scott) the an :=
  not_blocks_of_not_weakUnique (λ (_ : Unit) (P : Prop3 Ind) => P .scott) (λ _ => onlySurvivor)
    (λ _ => rfl) (Set.mem_univ ()) not_weakUnique_onlySurvivor
    λ _ _ => ne_of_eq_of_ne onlySurvivor_scott (by decide)

end Crash

/-! ### The paper's judgments

The rows of `Data/Examples/CoppockBeaver2015.json` with a `restrictor` feature are the
predicative definites whose felicity turns on weak uniqueness alone, (10)–(12) and
(44)–(46): a restrictor that holds of nothing, the scenario in which iguanas have no hearts,
one that holds of both items of a two-item scenario, and an *only* phrase over the latter.
The definite is felicitous exactly when it is classical of the subject. -/

namespace Scenario

inductive Item | this | that
  deriving DecidableEq, Fintype

/-- The restrictor a row's `restrictor` feature names. -/
def restrictors : List (String × Prop3 Item) :=
  [("uniqueIfAny", λ _ => .false), ("multiple", λ _ => .true), ("only", only (λ _ => .true))]

/-- Row consistency: a predicative definite is acceptable exactly when the definite of its
restrictor is classical of the subject. -/
theorem restrictor_rows : ∀ row ∈ Examples.all, ∀ P ∈ row.parse? "restrictor" restrictors,
    (row.judgment = .acceptable ↔ the P .this ≠ .indet) := by
  decide +kernel

end Scenario

end CoppockBeaver2015
