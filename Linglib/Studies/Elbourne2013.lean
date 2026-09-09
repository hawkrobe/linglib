import Linglib.Data.Examples.Elbourne2013
import Linglib.Semantics.Definiteness.Maximality
import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Quantification.ChoiceFunction
import Mathlib.Order.Minimal

/-!
# Elbourne (2013): Definite Descriptions

This file formalizes [elbourne-2013]'s Fregean situation semantics for the definite article.
Situations are parts of possible worlds, ordered by parthood, with worlds the maximal situations
([kratzer-1989], [barwise-perry-1983]); quantifiers range over minimal situations. The article
takes a property and a situation and, on the domain condition that exactly one thing has the
property in that situation, denotes that thing, so a definite description is a partial function
from situations to individuals. Its situation pronoun may be free, referring to a contextually
given situation, or bound by the abstractor of the containing proposition. The choice yields the
book's unifications: a free pronoun discharges the uniqueness presupposition at its referent and
makes the sentence about a particular individual, Donnellan's referential use; a bound pronoun
carries the presupposition to the situation the proposition is applied to, the attributive use,
by the rule λ-Conversion II. Binding below an intensional operator gives the de dicto reading,
reference to the actual world inside it the de re reading, and binding above it Kripke's
attributive-yet-de-re number of the planets. Under attitude verbs the presupposition projects to
the subject's beliefs ([karttunen-1974-presupposition]), which is why a definite description,
unlike its Russellian paraphrase, makes Hans inconsistent when he is unsure whether there is a
ghost in his attic. Donkey-anaphoric descriptions are bound to the minimal situations introduced
by the restrictor, each of which contains exactly one donkey, so *every man who owns a donkey
beats the donkey* gets the strong reading; and since a description depends only on its situation,
a downstressed repetition of *the donkey* has no sloppy reading, unlike the relation-variable
descriptions of [stanley-szab-2000]. Pronouns have the article's lexical entry, their noun phrase
supplied by NP-deletion.

## Implementation notes

* Situations are any partial order; minimality is mathlib's `Minimal`, and the lexical entries of
  §2.3.3 are transcribed with it. The article is `russellIota` at the situation, so its domain
  condition is `∃!` (`the_isSome_iff`), and a sentence is `PartialProp.presupOfReferent` of the
  description; the free/bound status of a situation pronoun is the substrate's `SitVarStatus`,
  whose two values the book introduced. A description inside a scope contributes `∃ z ∈ the f s`,
  the assertion of `presupOfReferent` with `Option` membership.
* Intensional operators are universal over an accessibility relation and lift partial
  propositions by requiring presupposition and assertion throughout the accessible situations;
  attitude verbs check the presupposition in the subject's doxastic alternatives and the
  assertion in the verb's own, Karttunen's projection.
* The village of ch. 6 and ch. 9 is a concrete model: situations are finite sets of atomic
  facts ordered by inclusion, [kratzer-1989]'s states of affairs, so minimal situations are
  computed and the strong reading of the donkey sentence is a theorem rather than a reading of
  the truth conditions.
* The examples are `Data.Examples.Elbourne2013`.

## TODO

* Ch. 4's projection through possibility modals, disjunction and negation, ch. 7's modal
  subordination and counterfactuals, and ch. 10's descriptive indexicals are not represented.

## References

* [elbourne-2013]
* [elbourne-2005]
* [kratzer-1989]
* [barwise-perry-1983]
* [heim-kratzer-1998]
* [buring-2004]
* [strawson-1950]
* [russell-1905]
* [donnellan-1966]
* [kripke-1977]
* [karttunen-1974-presupposition]
* [stanley-szab-2000]
* [geach-1962]
-/

namespace Elbourne2013

open Definiteness Presupposition Quantification.ChoiceFunction

/-! ### Quantification over minimal situations (§2.3.3) -/

section Quantification

variable {S : Type*} [PartialOrder S] {E : Type*}

/-- The morpheme `Q` (22): an extended situation, a minimal situation between `s'` and `s` in
which `x` has the property. -/
def Q (f : E → S → Prop) (x : E) (s s' : S) : Prop :=
  ∃ s'', Minimal (λ s'' => s' ≤ s'' ∧ s'' ≤ s ∧ f x s'') s''

/-- `every` (20): every minimal situation, within the restrictor situation `s₀` and the
truth-supporting situation `s`, in which an individual has the restrictor property satisfies the
nuclear scope. -/
def every (s₀ : S) (f : E → S → Prop) (g : E → S → S → Prop) (s : S) : Prop :=
  ∀ x s', Minimal (λ s' => s' ≤ s₀ ∧ s' ≤ s ∧ f x s') s' → g x s s'

/-- `a` (21): some minimal restrictor situation satisfies the nuclear scope. -/
def a (s₀ : S) (f : E → S → Prop) (g : E → S → S → Prop) (s : S) : Prop :=
  ∃ x s', Minimal (λ s' => s' ≤ s₀ ∧ s' ≤ s ∧ f x s') s' ∧ g x s s'

/-- `always` (33): every minimal situation in `s` satisfying the antecedent satisfies the
consequent. -/
def always (p : S → Prop) (q : S → S → Prop) (s : S) : Prop :=
  ∀ s', Minimal (λ s' => s' ≤ s ∧ p s') s' → q s s'

/-- The morpheme `Q_A` (34), the propositional counterpart of `Q`. -/
def QA (p : S → Prop) (s s' : S) : Prop :=
  ∃ s'', Minimal (λ s'' => s' ≤ s'' ∧ s'' ≤ s ∧ p s'') s''

end Quantification

/-! ### The article and its situation pronoun (ch. 3–5) -/

section Article

variable {S E : Type*}

/-- The definite article, (3) of ch. 3: `λf.λs : ∃!x f(x)(s). ιx f(x)(s)`, a partial function
from situations to the unique satisfier of the property in the situation. -/
noncomputable def the (f : E → S → Prop) (s : S) : Option E := russellIota (f · s)

/-- The domain condition of the article: exactly one satisfier in the situation. -/
theorem the_isSome_iff (f : E → S → Prop) (s : S) : (the f s).isSome ↔ ∃! x, f x s :=
  russellIota_isSome_iff_exists_unique _

theorem the_eq_some_iff (f : E → S → Prop) (s : S) (x : E) :
    the f s = some x ↔ f x s ∧ ∀ y, f y s → y = x :=
  russellIota_eq_some_iff _ _

/-- A pronoun, (4b) of ch. 10: the article's entry, its noun phrase supplied by NP-deletion. -/
noncomputable def pronoun (np : E → S → Prop) : S → Option E := the np

/-- The situation a situation pronoun contributes at evaluation situation `s`: its referent `s₀`
when free, the situation abstracted over by the containing proposition when bound (Situation
Binding I and λ-Conversion II). -/
def sitValue : SitVarStatus → S → S → S
  | .free, s₀, _ => s₀
  | .bound, _, s => s

/-- `[[the NP] sᵢ]`, (4) of ch. 3: the description with its situation pronoun. -/
noncomputable def description (st : SitVarStatus) (s₀ : S) (f : E → S → Prop) (s : S) :
    Option E :=
  the f (sitValue st s₀ s)

/-- `[[[the NP] sᵢ] VP]`: the sentence as a partial proposition, (3) of ch. 4 for a free pronoun
and (4) for a bound one. -/
noncomputable def sentence (st : SitVarStatus) (s₀ : S) (f vp : E → S → Prop) : PartialProp S :=
  PartialProp.presupOfReferent (description st s₀ f) vp

/-- A referential situation pronoun discharges the domain condition at its referent, whatever
situation the proposition is applied to. -/
theorem sentence_free_presup (s₀ : S) (f vp : E → S → Prop) (s : S) :
    (sentence .free s₀ f vp).presup s ↔ ∃! x, f x s₀ :=
  the_isSome_iff f s₀

/-- A bound situation pronoun carries the domain condition to the topic situation: the
proposition is partial, and presupposes exactly one satisfier where it is applied. -/
theorem sentence_bound_presup (s₀ : S) (f vp : E → S → Prop) (s : S) :
    (sentence .bound s₀ f vp).presup s ↔ ∃! x, f x s :=
  the_isSome_iff f s

/-- Where the description denotes, the sentence says of that individual what the predicate says
of it; a referential description makes the proposition object-dependent, (12) of ch. 5. -/
theorem sentence_assertion (st : SitVarStatus) (s₀ : S) (f vp : E → S → Prop) {s : S} {x : E}
    (h : description st s₀ f s = some x) : (sentence st s₀ f vp).assertion s ↔ vp x s :=
  Iff.of_eq (PartialProp.presupOfReferent_assertion_some _ _ _ _ h)

/-- Attributive use, (15) of ch. 5: the description is bound, so which individual is described
is a function of the situation of evaluation, not of the context. -/
theorem description_bound (s₀ : S) (f : E → S → Prop) (s : S) :
    description .bound s₀ f s = the f s :=
  rfl

/-- Referential use, (11) of ch. 5: the referent enters via the context and is the same at every
situation of evaluation. -/
theorem description_free (s₀ : S) (f : E → S → Prop) (s s' : S) :
    description .free s₀ f s = description .free s₀ f s' :=
  rfl

/-! ### Intensional operators: de re, de dicto, attributive de re (ch. 7) -/

/-- A universal intensional operator over an accessibility relation, on partial propositions:
presupposition and assertion of the prejacent are required throughout the accessible
situations, as in (12) and (14) of ch. 7. -/
def box (R : S → Set S) (p : PartialProp S) : PartialProp S where
  presup := λ s => ∀ w ∈ R s, p.presup w
  assertion := λ s => ∀ w ∈ R s, p.assertion w

/-- De dicto, (11) of ch. 7: the situation pronoun bound by `ς` immediately below the operator. -/
noncomputable def deDicto (R : S → Set S) (s₀ : S) (f vp : E → S → Prop) : PartialProp S :=
  box R (sentence .bound s₀ f vp)

/-- De re, (13) of ch. 7: a referential situation pronoun, to the actual world `w₀`, inside the
operator. -/
noncomputable def deRe (R : S → Set S) (w₀ : S) (f vp : E → S → Prop) : PartialProp S :=
  box R (sentence .free w₀ f vp)

/-- Attributive de re, (17) and (25) of ch. 7: the pronoun bound above the operator, so the
description is evaluated at the topic situation and only the predicate is modalized. -/
noncomputable def attributiveDeRe (R : S → Set S) (f vp : E → S → Prop) : PartialProp S :=
  PartialProp.presupOfReferent (the f) λ x s => ∀ w ∈ R s, vp x w

/-- De dicto: every accessible situation must contain exactly one satisfier, and the satisfiers
may differ. -/
theorem deDicto_presup (R : S → Set S) (s₀ : S) (f vp : E → S → Prop) (s : S) :
    (deDicto R s₀ f vp).presup s ↔ ∀ w ∈ R s, ∃! x, f x w :=
  forall₂_congr λ w _ => sentence_bound_presup s₀ f vp w

/-- De re: the satisfier is fixed in the actual world, and need not satisfy the property in the
accessible situations. -/
theorem deRe_presup (R : S → Set S) (w₀ : S) (f vp : E → S → Prop) (s : S) :
    (deRe R w₀ f vp).presup s ↔ ∀ w ∈ R s, ∃! x, f x w₀ :=
  forall₂_congr λ w _ => sentence_free_presup w₀ f vp w

/-- Attributive de re presupposes exactly one satisfier in the topic situation. -/
theorem attributiveDeRe_presup (R : S → Set S) (f vp : E → S → Prop) (s : S) :
    (attributiveDeRe R f vp).presup s ↔ ∃! x, f x s :=
  the_isSome_iff f s

/-- Kripke's number of the planets, (16) of ch. 7: attributive, since the speaker need not know
which number, yet de re, since the number in the topic situation is what is odd in every
accessible world. -/
theorem attributiveDeRe_assertion (R : S → Set S) (f vp : E → S → Prop) {s : S} {x : E}
    (h : the f s = some x) : (attributiveDeRe R f vp).assertion s ↔ ∀ w ∈ R s, vp x w :=
  Iff.of_eq (PartialProp.presupOfReferent_assertion_some _ _ _ _ h)

/-! ### Existence entailments (ch. 8) -/

/-- An attitude verb with [karttunen-1974-presupposition]'s projection (§8.6): the complement's
presupposition is presupposed to hold throughout the subject's doxastic alternatives, its
assertion throughout the verb's own alternatives, doxastic for *believe* and bouletic for
*want*. -/
def attitude (dox R : S → Set S) (p : PartialProp S) : PartialProp S where
  presup := λ s => ∀ w ∈ dox s, p.presup w
  assertion := λ s => ∀ w ∈ R s, p.assertion w

/-- (40)–(41) of ch. 8: *Hans wants the ghost in his attic to be quiet* presupposes that Hans
believes there is exactly one ghost in his attic. -/
theorem attitude_presup (dox R : S → Set S) (s₀ : S) (f vp : E → S → Prop) (s : S) :
    (attitude dox R (sentence .bound s₀ f vp)).presup s ↔ ∀ w ∈ dox s, ∃! x, f x w :=
  forall₂_congr λ w _ => sentence_bound_presup s₀ f vp w

/-- (31) with (33b): a subject unsure whether there is a ghost in his attic cannot felicitously
want the ghost in his attic to be quiet, since the presupposition attributes the belief to him. -/
theorem attitude_inconsistent_of_agnostic (dox R : S → Set S) (s₀ : S) (f vp : E → S → Prop)
    {s : S} (h : ∃ w ∈ dox s, ¬ ∃ x, f x w) :
    ¬ (attitude dox R (sentence .bound s₀ f vp)).presup s := by
  rw [attitude_presup]
  intro hp
  obtain ⟨w, hw, hno⟩ := h
  exact hno (hp w hw).exists

/-- The Russellian paraphrase (33a): existence and uniqueness asserted inside the attitude. -/
def russellian (R : S → Set S) (f vp : E → S → Prop) (s : S) : Prop :=
  ∀ w ∈ R s, ∃ x, f x w ∧ (∀ y, f y w → y = x) ∧ vp x w

/-- (39) of ch. 8: the antecedent of a conditional is a hole, so the existence presupposition of
the description projects to the whole conditional. -/
theorem conditional_presup (s₀ : S) (f vp : E → S → Prop) (q : PartialProp S) (s : S) :
    (PartialProp.imp (sentence .bound s₀ f vp) q).presup s ↔ (∃! x, f x s) ∧ q.presup s :=
  and_congr_left' (sentence_bound_presup s₀ f vp s)

end Article

/-- (31) with (33a): the Russellian paraphrase is consistent with agnosticism, since the
existence claim sits inside the bouletic alternatives; a witness with two situations, one
without a ghost that the subject leaves open and one with a quiet ghost that he wants. -/
theorem russellian_consistent :
    ∃ (dox R : Bool → Set Bool) (f vp : Unit → Bool → Prop),
      (∃ w ∈ dox true, ¬ ∃ x, f x w) ∧ russellian R f vp true :=
  ⟨λ _ => Set.univ, λ _ => {true}, λ _ w => w = true, λ _ _ => True,
    ⟨false, Set.mem_univ _, by simp⟩, λ w hw => ⟨(), hw, λ _ _ => rfl, trivial⟩⟩

/-- (36) of ch. 8: under an attitude verb the description commits the subject, not the speaker,
to a fountain of youth. The presupposition holds although there is none in the topic
situation. -/
theorem attitude_presup_not_speaker :
    ∃ (dox R : Bool → Set Bool) (f vp : Unit → Bool → Prop) (s : Bool),
      (attitude dox R (sentence .bound s f vp)).presup s ∧ ¬ ∃ x, f x s :=
  ⟨λ _ => {true}, λ _ => {true}, λ _ w => w = true, λ _ _ => True, false,
    (attitude_presup _ _ _ _ _ _).mpr λ w hw => ⟨(), hw, λ _ _ => rfl⟩, by simp⟩

/-! ### The village: situations as sets of facts (ch. 6, ch. 9) -/

/-- Atomic facts of a village: [kratzer-1989]'s states of affairs, thin particulars instantiating
properties and relations. -/
inductive Fact (E : Type*)
  | farmer (x : E)
  | donkey (x : E)
  | priest (x : E)
  | table (x : E)
  | covered (x : E)
  | owns (x y : E)
  | beats (x y : E)
  deriving DecidableEq

/-- A situation is a finite set of facts, parthood is inclusion, and a world is the set of all
the facts that hold in it. -/
abbrev Village (E : Type*) := Finset (Fact E)

section Village

variable {E : Type*}

/-- The minimal situations containing a fact within two bounds are the singleton. -/
theorem exists_minimal_singleton_iff {t u : Village E} (φ : Fact E) (g : Village E → Prop) :
    (∃ s, Minimal (λ s => s ≤ t ∧ s ≤ u ∧ φ ∈ s) s ∧ g s) ↔ φ ∈ t ∧ φ ∈ u ∧ g {φ} := by
  have hmin (ht : φ ∈ t) (hu : φ ∈ u) (s : Village E) :
      Minimal (λ s => s ≤ t ∧ s ≤ u ∧ φ ∈ s) s ↔ s = {φ} :=
    minimal_iff_eq ⟨Finset.singleton_subset_iff.mpr ht, Finset.singleton_subset_iff.mpr hu,
      Finset.mem_singleton_self φ⟩ λ _ h => Finset.singleton_subset_iff.mpr h.2.2
  constructor
  · rintro ⟨s, hs, hg⟩
    have ht := hs.prop.1 hs.prop.2.2
    have hu := hs.prop.2.1 hs.prop.2.2
    exact ⟨ht, hu, (hmin ht hu s).mp hs ▸ hg⟩
  · rintro ⟨ht, hu, hg⟩
    exact ⟨{φ}, (hmin ht hu _).mpr rfl, hg⟩

variable [DecidableEq E]

/-- An extended situation for a set of facts exists exactly when the facts hold in the
truth-supporting situation. -/
theorem Q_subset_iff (Φ : E → Village E) (x : E) (s s' : Village E) :
    Q (λ x s'' => Φ x ⊆ s'') x s s' ↔ s' ≤ s ∧ Φ x ⊆ s := by
  constructor
  · rintro ⟨s'', hs''⟩
    exact ⟨hs''.prop.1.trans hs''.prop.2.1, hs''.prop.2.2.trans hs''.prop.2.1⟩
  · rintro ⟨hle, hsub⟩
    exact ⟨s' ∪ Φ x, (minimal_iff_eq ⟨Finset.subset_union_left, Finset.union_subset hle hsub,
      Finset.subset_union_right⟩ λ _ h => Finset.union_subset h.1 h.2.2).mpr rfl⟩

/-- The singleton case: an extended situation for a fact. -/
theorem Q_mem_iff (φ : E → Fact E) (x : E) (s s' : Village E) :
    Q (λ x s'' => φ x ∈ s'') x s s' ↔ s' ≤ s ∧ φ x ∈ s := by
  simpa only [Finset.singleton_subset_iff] using Q_subset_iff (λ x => {φ x}) x s s'

/-- *man who owns a donkey*, the restrictor of (4) in ch. 6 with `a` and `Q` inside the relative
clause. -/
def ownsADonkey (s₀ : Village E) (x : E) (s' : Village E) : Prop :=
  Fact.farmer x ∈ s' ∧
    a s₀ (λ y (s : Village E) => Fact.donkey y ∈ s)
      (λ y => Q (λ y (s : Village E) => Fact.owns x y ∈ s) y) s'

/-- The relative clause unfolds to facts in the situation. -/
theorem ownsADonkey_iff (s₀ : Village E) (x : E) {s' : Village E} (h : s' ≤ s₀) :
    ownsADonkey s₀ x s' ↔ Fact.farmer x ∈ s' ∧ ∃ y, Fact.donkey y ∈ s' ∧ Fact.owns x y ∈ s' := by
  simp only [ownsADonkey, a, exists_minimal_singleton_iff, Q_mem_iff, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨hf, y, -, hd, -, ho⟩
    exact ⟨hf, y, hd, ho⟩
  · rintro ⟨hf, y, hd, ho⟩
    exact ⟨hf, y, h hd, hd, hd, ho⟩

/-- The minimal situations of a farmer owning a donkey within the world: one per owned donkey,
consisting of the farmer, the donkey and the owning. -/
theorem minimal_ownsADonkey_iff (w : Village E) (x : E) (s' : Village E) :
    Minimal (λ s' => s' ≤ w ∧ s' ≤ w ∧ ownsADonkey w x s') s' ↔
      ∃ y, Fact.farmer x ∈ w ∧ Fact.donkey y ∈ w ∧ Fact.owns x y ∈ w ∧
        s' = {Fact.farmer x, Fact.donkey y, Fact.owns x y} := by
  constructor
  · intro hs
    obtain ⟨hw, -, hr⟩ := hs.prop
    obtain ⟨hf, y, hd, ho⟩ := (ownsADonkey_iff w x hw).mp hr
    have hsub : ({Fact.farmer x, Fact.donkey y, Fact.owns x y} : Village E) ≤ s' := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hf, hd, ho⟩
    have hA : ({Fact.farmer x, Fact.donkey y, Fact.owns x y} : Village E) ≤ w := hsub.trans hw
    refine ⟨y, hw hf, hw hd, hw ho, hs.eq_of_ge ⟨hA, hA, ?_⟩ hsub⟩
    rw [ownsADonkey_iff w x hA]
    simp
  · rintro ⟨y, hf, hd, ho, rfl⟩
    have hA : ({Fact.farmer x, Fact.donkey y, Fact.owns x y} : Village E) ≤ w := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hf, hd, ho⟩
    refine ⟨⟨hA, hA, ?_⟩, ?_⟩
    · rw [ownsADonkey_iff w x hA]
      simp
    · intro s hs hle
      obtain ⟨hf', y', hd', ho'⟩ := (ownsADonkey_iff w x hs.1).mp hs.2.2
      have hy : y' = y := by
        have := hle hd'
        simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or, or_false,
          Fact.donkey.injEq] at this
        exact this
      subst hy
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hf', hd', ho'⟩

/-- In the minimal situation of a farmer owning a donkey, *the donkey* denotes that donkey:
uniqueness from minimality. -/
theorem the_donkey_minimal (x y : E) :
    the (λ z (s : Village E) => Fact.donkey z ∈ s) {Fact.farmer x, Fact.donkey y, Fact.owns x y} =
      some y := by
  rw [the_eq_some_iff]
  refine ⟨by simp, λ z hz => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or, or_false,
    Fact.donkey.injEq] at hz
  exact hz

/-- The domain condition of the donkey-anaphoric description is met by minimality: every minimal
situation of a farmer owning a donkey contains exactly one donkey, §6.2. -/
theorem existsUnique_donkey_of_minimal (w : Village E) (x : E) {s' : Village E}
    (hs : Minimal (λ s' => s' ≤ w ∧ s' ≤ w ∧ ownsADonkey w x s') s') :
    ∃! z, Fact.donkey z ∈ s' := by
  obtain ⟨y, -, -, -, rfl⟩ := (minimal_ownsADonkey_iff w x s').mp hs
  exact (the_isSome_iff (λ z (s : Village E) => Fact.donkey z ∈ s) _).mp
    (by rw [the_donkey_minimal]; rfl)

/-- The nuclear scope of (4) in ch. 6, `σ₃ [Q [beats [the donkey s₃]]]`: Situation Binding III
binds the description to the restrictor's minimal situation `s'`, and `Q` extends `s'` to a
situation in which the beating holds. -/
noncomputable def beatsTheDonkey (x : E) (s s' : Village E) : Prop :=
  Q (λ x s'' => ∃ z ∈ the (λ z (s : Village E) => Fact.donkey z ∈ s) s', Fact.beats x z ∈ s'')
    x s s'

/-- (3) of ch. 6, *every man who owns a donkey beats the donkey*, with the LF (4). -/
noncomputable def everyOwnerBeatsTheDonkey (s₀ s : Village E) : Prop :=
  every s₀ (ownsADonkey s₀) beatsTheDonkey s

/-- (10a) of ch. 10, *every man who owns a donkey beats it*: the pronoun with its deleted noun
phrase in place of the description. -/
noncomputable def everyOwnerBeatsIt (s₀ s : Village E) : Prop :=
  every s₀ (ownsADonkey s₀)
    (λ x s s' => Q (λ x s'' => ∃ z ∈ pronoun (λ z (s : Village E) => Fact.donkey z ∈ s) s',
      Fact.beats x z ∈ s'') x s s') s

private theorem beatsTheDonkey_iff (w : Village E) (x y : E) :
    beatsTheDonkey x w {Fact.farmer x, Fact.donkey y, Fact.owns x y} ↔
      {Fact.farmer x, Fact.donkey y, Fact.owns x y} ≤ w ∧ Fact.beats x y ∈ w := by
  unfold beatsTheDonkey
  rw [the_donkey_minimal]
  simp only [Option.mem_def, Option.some.injEq, exists_eq_left']
  exact Q_mem_iff (λ x => Fact.beats x y) x w _

/-- The neat semantics for donkey sentences (§6.2): in the village world, the sentence is true
iff every farmer beats every donkey he owns. The bound description picks out the unique donkey
of each minimal owning situation, so the reading is the strong one. -/
theorem everyOwnerBeatsTheDonkey_iff (w : Village E) :
    everyOwnerBeatsTheDonkey w w ↔
      ∀ x y, Fact.farmer x ∈ w → Fact.donkey y ∈ w → Fact.owns x y ∈ w → Fact.beats x y ∈ w := by
  constructor
  · intro h x y hf hd ho
    exact ((beatsTheDonkey_iff w x y).mp
      (h x _ ((minimal_ownsADonkey_iff w x _).mpr ⟨y, hf, hd, ho, rfl⟩))).2
  · intro h x s' hs
    obtain ⟨y, hf, hd, ho, rfl⟩ := (minimal_ownsADonkey_iff w x s').mp hs
    exact (beatsTheDonkey_iff w x y).mpr ⟨hs.prop.1, h x y hf hd ho⟩

/-- The pronoun sentence has the same meaning, being the same LF up to the null noun phrase. -/
theorem everyOwnerBeatsIt_iff (w : Village E) :
    everyOwnerBeatsIt w w ↔
      ∀ x y, Fact.farmer x ∈ w → Fact.donkey y ∈ w → Fact.owns x y ∈ w → Fact.beats x y ∈ w :=
  everyOwnerBeatsTheDonkey_iff w

/-! ### Incompleteness and the argument from sloppy identity (ch. 9) -/

/-- The room of (4) in ch. 9, with one table, covered with books. -/
def room : Village Bool := {Fact.table true, Fact.covered true}

/-- The world containing the room and a second table. -/
def world : Village Bool := {Fact.table true, Fact.table false, Fact.covered true}

theorem room_le_world : room ≤ world := by decide

/-- Incompleteness, (4) of ch. 9: *the table is covered with books* said in a room with one table.
The referential situation pronoun to the room satisfies the domain condition although the world
contains two tables. -/
theorem incomplete_description :
    (sentence .free room (λ x (s : Village Bool) => Fact.table x ∈ s)
        (λ x s => Fact.covered x ∈ s)).presup world ∧
      ¬ ∃! x, Fact.table x ∈ world :=
  ⟨(sentence_free_presup _ _ _ _).mpr ⟨true, by decide, by decide⟩, λ ⟨_, _, h⟩ =>
    Bool.noConfusion ((h true (by decide)).trans (h false (by decide)).symm)⟩

/-- A relation-variable description, §9.2.1: `the [f v] NP`, the unique NP-satisfier standing in
the covert relation to the individual variable `v`, which a higher quantifier may bind. -/
noncomputable def relDescription {S : Type*} (rel : E → E → S → Prop) (np : E → S → Prop) (v : E)
    (s : S) : Option E :=
  russellIota λ x => np x s ∧ rel x v s

omit [DecidableEq E] in
/-- The relation-variable description covaries with its individual variable: *the donkey* as
*the donkey v owns* denotes each owner's own donkey, which licenses the sloppy reading of (17b)
in ch. 9 and would wrongly license one for (17a). -/
theorem relDescription_eq_some_iff {S : Type*} (rel : E → E → S → Prop) (np : E → S → Prop)
    (v : E) (s : S) (x : E) :
    relDescription rel np v s = some x ↔
      (np x s ∧ rel x v s) ∧ ∀ y, np y s → rel y v s → y = x := by
  rw [relDescription, russellIota_eq_some_iff]
  simp only [and_imp]

/-- (29) of ch. 9 with the LF (31): *every farmer who owns a donkey beats the donkey, and the
priest beats the donkey too*. The quantifier scopes over the conjunction, and both occurrences of
*the donkey* are bound by `σ` to the same minimal situation. -/
noncomputable def everyOwnerBeatsTheDonkeyAndThePriestToo (s₀ s : Village E) : Prop :=
  every s₀ (ownsADonkey s₀)
    (λ x s s' => Q (λ x s'' => ∃ z ∈ the (λ z (s : Village E) => Fact.donkey z ∈ s) s',
      Fact.beats x z ∈ s'' ∧
        ∃ p ∈ the (λ p (s : Village E) => Fact.priest p ∈ s) s₀, Fact.beats p z ∈ s'') x s s') s

/-- The strict reading, (32) of ch. 9: the priest beats each farmer's donkey. A sloppy reading,
on which the priest beats his own donkey, would need the description to depend on an individual
variable, which the situation-variable description lacks. -/
theorem everyOwnerBeatsTheDonkeyAndThePriestToo_iff (w : Village E) {p : E}
    (hp : the (λ p (s : Village E) => Fact.priest p ∈ s) w = some p) :
    everyOwnerBeatsTheDonkeyAndThePriestToo w w ↔
      ∀ x y, Fact.farmer x ∈ w → Fact.donkey y ∈ w → Fact.owns x y ∈ w →
        Fact.beats x y ∈ w ∧ Fact.beats p y ∈ w := by
  have key (x y : E) : Q (λ x' s'' => ∃ z ∈ the (λ z (s : Village E) => Fact.donkey z ∈ s)
        {Fact.farmer x, Fact.donkey y, Fact.owns x y}, Fact.beats x' z ∈ s'' ∧
          ∃ p ∈ the (λ p (s : Village E) => Fact.priest p ∈ s) w, Fact.beats p z ∈ s'')
        x w {Fact.farmer x, Fact.donkey y, Fact.owns x y} ↔
      {Fact.farmer x, Fact.donkey y, Fact.owns x y} ≤ w ∧
        Fact.beats x y ∈ w ∧ Fact.beats p y ∈ w := by
    rw [the_donkey_minimal, hp]
    simp only [Option.mem_def, Option.some.injEq, exists_eq_left']
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      Q_subset_iff (λ x => {Fact.beats x y, Fact.beats p y}) x w
        {Fact.farmer x, Fact.donkey y, Fact.owns x y}
  constructor
  · intro h x y hf hd ho
    exact ((key x y).mp (h x _ ((minimal_ownsADonkey_iff w x _).mpr ⟨y, hf, hd, ho, rfl⟩))).2
  · intro h x s' hs
    obtain ⟨y, hf, hd, ho, rfl⟩ := (minimal_ownsADonkey_iff w x s').mp hs
    exact (key x y).mpr ⟨hs.prop.1, h x y hf hd ho⟩

end Village

end Elbourne2013
