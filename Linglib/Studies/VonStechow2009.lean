module

public import Linglib.Semantics.Tense.Defs
public import Linglib.Data.Examples.VonStechow2009
public import Mathlib.Order.Bounds.Basic

/-!
# von Stechow (2009): Tenses in Compositional Semantics

This file formalizes [von-stechow-2009]'s compositional fragment for English tense. The
semantic tenses are the deictic Present, the speech time, and an indefinite relative Past that
shifts the local evaluation time backwards (22), with the auxiliaries *have* and *will* the
past and its mirror image (26), (29) and *be* a transmitter (24); tensed verbs are tenseless
and their morphology is licensed by the feature a semantic tense transmits to the variable it
binds (33). Frame adverbials combine by predicate modification and interact scopally with the
perfect auxiliary (43), and a quantified adverbial must be restricted to the past (44), (45).
Against [partee-1973]'s referential Past (47) with a perfective operator (50), the indefinite
Past with a contextual domain restriction (53) gives the same truth conditions for the stove
sentence (54) and, unlike the referential one, lets negation and quantifiers scope over tense
(58), (61); the restriction also keeps the event of a future perfect after the speech time
(57). In relative clauses the tense is an obligatorily bound temporal pronoun, whence the
simultaneous and the deictic readings of a present under *will* (66), (67). Under attitudes
the anaphoric analysis makes Mary at five believe that five is six (77), so, after
[lewis-1979-attitudes], the complement is a property of times and belief quantifies over
world–time pairs (78), of which Hintikka's propositional belief is the time-independent case
(74). Before- and after-clauses take the earliest time of the clause (91) after
[beaver-condoravdi-2003], from which [anscombe-1964]'s asymmetric universal *before* and
existential *after* follow.

## Implementation notes

Times form a linear order, the interval structure entering only through a parameter for the
subinterval relation where the perfective and *on* need it. Feature transmission and the
tense-deletion rule of [ogihara-1989] are described, not formalized; the extended-now perfect,
the progressive and the type-driven syntax of PRO movement are not formalized. The paper's
examples are the rows of `Data.Examples.VonStechow2009`.

## References

* [von-stechow-2009]
* [partee-1973]
* [lewis-1979-attitudes]
* [ogihara-1989]
* [beaver-condoravdi-2003]
* [anscombe-1964]
-/

@[expose] public section

namespace VonStechow2009

open Semantics

variable {T : Type*} {s t : T} {P Q : T → Prop}

/-! ### Tenses and auxiliaries (§5) -/

section Tenses

variable [LinearOrder T]

/-- The semantic Past (22b) and the auxiliary *have* (26): some time before the local
evaluation time satisfies the predicate. -/
def past (t : T) (P : T → Prop) : Prop := ∃ t', t' < t ∧ P t'

/-- The auxiliary *will* (29), the mirror image of *have*. -/
def future (t : T) (P : T → Prop) : Prop := ∃ t', t < t' ∧ P t'

/-- The temporal auxiliary *be* (24) passes the evaluation time on. -/
def be (t : T) (P : T → Prop) : Prop := P t

/-- The Past is the past cell of `Tense` quantified existentially. -/
theorem past_iff_cell : past t P ↔ ∃ t', compare t' t ∈ ⟦Tense.past⟧ ∧ P t' := by
  simp only [past, Tense.compare_mem_past]

/-- The pluperfect (27), *John had called*: a past time before a past time. -/
theorem pluperfect_iff : past s (λ t₁ => past t₁ P) ↔ ∃ t₁, t₁ < s ∧ ∃ t₂, t₂ < t₁ ∧ P t₂ :=
  Iff.rfl

end Tenses

/-! ### Temporal adverbials (§7) -/

/-- (43): *Mary had left at six* is ambiguous between modification of the past reference time
and of the event time; with the leaving at five and six a past time, the first reading holds
and the second fails. -/
theorem exists_referenceTime_ne_eventTime :
    ∃ (s six : ℕ) (leave : ℕ → Prop),
      past s (λ t => t = six ∧ past t leave) ∧
        ¬ past s (λ t => past t (λ t' => t' = six ∧ leave t')) :=
  ⟨10, 6, (· = 5), ⟨6, by omega, rfl, 5, by omega, rfl⟩, by
    rintro ⟨t, -, t', -, rfl, h⟩
    exact absurd h (by decide)⟩

section Quantified

variable [LinearOrder T] (onDay : T → T → Prop) (sunday work : T → Prop)

/-- Reading (44a), the adverbial quantifier under the Past, entails a past time on every Sunday. -/
theorem exists_on_of_quantifier_narrow (h : past s (λ t => ∀ t', sunday t' → onDay t t' ∧ work t)) :
    ∃ t, ∀ t', sunday t' → onDay t t' :=
  match h with | ⟨t, _, h⟩ => ⟨t, λ t' ht' => (h t' ht').1⟩

/-- Reading (44b), the quantifier over the Past, entails that every Sunday contains a time
before the speech time. -/
theorem forall_exists_of_quantifier_wide
    (h : ∀ t', sunday t' → past s (λ t => onDay t t' ∧ work t)) :
    ∀ t', sunday t' → ∃ t, t < s ∧ onDay t t' :=
  λ t' ht' => match h t' ht' with | ⟨t, hts, h⟩ => ⟨t, hts, h.1⟩

/-- (45): the wanted reading restricts the Sundays to the past; it follows from (44b) but not
conversely, a future Sunday being a counterexample. -/
theorem restricted_of_quantifier_wide (h : ∀ t', sunday t' → past s (λ t => onDay t t' ∧ work t)) :
    ∀ t', sunday t' ∧ t' < s → past s (λ t => onDay t t' ∧ work t) :=
  λ t' ht' => h t' ht'.1

theorem exists_restricted_not_quantifier_wide :
    ∃ (s : ℕ) (onDay : ℕ → ℕ → Prop) (sunday work : ℕ → Prop),
      (∀ t', sunday t' ∧ t' < s → past s (λ t => onDay t t' ∧ work t)) ∧
        ¬ ∀ t', sunday t' → past s (λ t => onDay t t' ∧ work t) :=
  ⟨1, Eq, (· = 2), λ _ => True, λ t' ht' => absurd ht' (by omega),
    λ h => match h 2 rfl with | ⟨_, ht, _, _⟩ => by omega⟩

end Quantified

/-! ### Referential and indefinite Past (§§8–9) -/

section Partee

variable [LinearOrder T] (sub : T → T → Prop) (C : T → Prop)

/-- The referential Past (47): the argument time is presupposed to precede the speech time. -/
def refPast (s t : T) : Prop := t < s

/-- The Perfective (50): the event time is a subinterval of the reference time. -/
def pf (t : T) (P : T → Prop) : Prop := ∃ t', sub t' t ∧ P t'

/-- The contextually restricted Past (53). -/
def pastC (t : T) (P : T → Prop) : Prop := ∃ t', C t' ∧ t' < t ∧ P t'

/-- Without a restriction the restricted Past is the Past. -/
theorem pastC_true : pastC (λ _ => True) t P ↔ past t P := by
  simp only [pastC, past, true_and]

/-- (52) and (54): negation over the referential Past with the Perfective, and negation over
the Past restricted to the subintervals of the time the speaker has in mind, are the same
truth condition once the subintervals of a past time are past. -/
theorem not_pastC_sub_iff_not_pf {t₅ : T} (hsub : ∀ t', sub t' t₅ → t' < s) :
    ¬ pastC (sub · t₅) s P ↔ ¬ pf sub t₅ P := by
  simp only [pastC, pf, not_exists, not_and]
  exact ⟨λ h t' ht' => h t' ht' (hsub t' ht'), λ h t' ht' _ => h t' ht'⟩

/-- (56), (57): with the content of the superordinate future added to its restriction, the
event of a future perfect lies after the speech time. -/
theorem lt_of_future_pastC {atSix : T → Prop}
    (h : future s (λ t => atSix t ∧ pastC (s < ·) t P)) : ∃ t', s < t' ∧ P t' :=
  match h with | ⟨_, _, _, t', hs, _, hP⟩ => ⟨t', hs, hP⟩

end Partee

/-! ### Scope interactions (§10) -/

section Scope

variable [LinearOrder T] {X : Type*} (boot : X → Prop) (polish : X → T → Prop)

/-- (61): a quantifier over the Past follows from the Past over the quantifier. -/
theorem forall_past_of_past_forall (h : past s (λ t => ∀ x, boot x → polish x t)) :
    ∀ x, boot x → past s (polish x) :=
  λ x hx => match h with | ⟨t, hts, h⟩ => ⟨t, hts, h x hx⟩

/-- The converse fails: the boots are polished at different past times. -/
theorem exists_forall_past_not_past_forall :
    ∃ (s : ℕ) (boot : Bool → Prop) (polish : Bool → ℕ → Prop),
      (∀ x, boot x → past s (polish x)) ∧ ¬ past s (λ t => ∀ x, boot x → polish x t) :=
  ⟨5, λ _ => True, λ b t => t = if b then 1 else 2,
    λ b _ => ⟨if b then 1 else 2, by cases b <;> decide, rfl⟩,
    λ ⟨t, _, h⟩ => by have := h true trivial; have := h false trivial; simp_all⟩

end Scope

/-! ### Tense in relative clauses (§11.1) -/

section Relative

variable [LinearOrder T] {X : Type*} (fish : X → Prop) (alive : X → T → Prop) (buy : X → T → Prop)

/-- (66), the simultaneous reading of (62): the fish is alive at the buying time, the
relative-clause pronoun bound by *will*. -/
def simultaneous (s : T) : Prop := future s (λ t => ∃ x, fish x ∧ alive x t ∧ buy x t)

/-- (67), the deictic reading: the pronoun bound by the matrix Present. -/
def deictic (s : T) : Prop := future s (λ t => ∃ x, fish x ∧ alive x s ∧ buy x t)

/-- The two readings are independent. -/
theorem simultaneous_deictic_independent :
    ∃ (s : ℕ) (fish : Unit → Prop) (alive buy : Unit → ℕ → Prop),
      simultaneous fish alive buy s ∧ ¬ deictic fish alive buy s :=
  ⟨0, λ _ => True, λ _ t => t = 1, λ _ t => t = 1, ⟨1, by omega, (), trivial, rfl, rfl⟩,
    λ ⟨_, _, _, _, h, _⟩ => by simp at h⟩

end Relative

/-! ### Tense under attitudes (§11.2) -/

section Attitudes

variable {W : Type*}

/-- Hintikka's belief (74): the complement is a proposition, true throughout the doxastic
alternatives. -/
def believeH (dox : W → T → Set W) (p : W → Prop) (w : W) (t : T) : Prop :=
  ∀ w' ∈ dox w t, p w'

/-- (77): on the anaphoric analysis the complement of *at five Mary thought it was six* is
the proposition that the matrix time is six, which the matrix time makes empty. -/
theorem anaphoric_content_empty {five six t₁ : T} (h₁ : t₁ = five) (hne : five ≠ six) :
    ∀ w : W, ¬ (λ _ : W => t₁ = six) w :=
  λ _ h => hne (h₁ ▸ h)

/-- Lewis's belief (78): the complement is a property of times, and the doxastic alternatives
are world–time pairs. -/
def believeL (dox : W → T → Set (W × T)) (P : W → T → Prop) (w : W) (t : T) : Prop :=
  ∀ p ∈ dox w t, P p.1 p.2

/-- (79): Mary locates herself at six, whatever the actual time. -/
theorem believeL_time {dox : W → T → Set (W × T)} {w : W} {t six : T} :
    believeL dox (λ _ t' => t' = six) w t ↔ ∀ p ∈ dox w t, p.2 = six :=
  Iff.rfl

/-- A time-independent complement is Hintikka's belief over the world projection of the
alternatives (74). -/
theorem believeL_const_iff {dox : W → T → Set (W × T)} {p : W → Prop} {w : W} {t : T} :
    believeL dox (λ w' _ => p w') w t ↔ believeH (λ w t => Prod.fst '' dox w t) p w t := by
  simp only [believeL, believeH, Set.forall_mem_image]

end Attitudes

section Complement

variable {W : Type*} [LinearOrder T]

/-- The complement tenses of (81): the tenseless PRO, or a Past over it, the shifted reading
(80). -/
inductive ComplementTense
  | pro
  | pastPro

/-- The property of times a complement denotes. -/
def ComplementTense.denote (Q : W → T → Prop) : ComplementTense → W → T → Prop
  | .pro => Q
  | .pastPro => λ w t => past t (Q w)

end Complement

/-! ### Before- and after-clauses (§11.3) -/

section Before

variable [LinearOrder T] {S : Set T} {m : T}

/-- *Before* the earliest time of the clause (91) is *before* every time of it, Anscombe's
universal *before*. -/
theorem lt_isLeast_iff (hm : IsLeast S m) : t < m ↔ ∀ t' ∈ S, t < t' :=
  ⟨λ h _ ht' => h.trans_le (hm.2 ht'), λ h => h m hm.1⟩

/-- *After* the earliest time is *after* some time of the clause, Anscombe's existential
*after*. -/
theorem isLeast_lt_iff (hm : IsLeast S m) : m < t ↔ ∃ t' ∈ S, t' < t :=
  ⟨λ h => ⟨m, hm.1, h⟩, λ ⟨_, ht', h⟩ => (hm.2 ht').trans_lt h⟩

end Before

end VonStechow2009
