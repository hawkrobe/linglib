import Linglib.Semantics.Tense.Embedding
import Linglib.Fragments.Japanese.TemporalConnectives
import Linglib.Data.Examples.ArreguiKusumoto1998
import Mathlib.Tactic.DeriveFintype

/-!
# Arregui & Kusumoto 1998: tense in temporal adjunct clauses

Japanese *mae* 'before' takes only a present-tense clause and *ato* 'after' only a past-tense
one, while English and Polish before- and after-clauses take the past. The relative-tense
account reads this off a consistency requirement: the adjunct tense orders the adjunct event
against the matrix event and must agree with the connective, unless a sequence-of-tense rule
deletes it. Polish has no such rule but patterns with English, and a Japanese *toki*
'when'-clause takes a past tense that the account forbids. The paper concludes that adjunct
tense is never in the semantic scope of the matrix tense. English and Polish adjuncts, and
Japanese when-clauses, are relative clauses over times: the relative pronoun abstracts over
a trace in the clause's time argument, the speech time sits in C, and the embedded tense is
absolute — hence the Geis ambiguity when the adjunct embeds a further clause. Japanese *mae*
and *ato* select TP directly, so their complements are unambiguous, and their tense
restrictions come from quantificational strength: the past tense is a Priorian operator that
closes its clause into a set of times, the present tense a variable awaiting a binder. *mae*
bears a binder index and must bind the present variable; *ato* bears none and needs the set of
times a past operator yields. The same contrast makes a present-tense when-clause
quantificational, bound by a covert adverb of quantification, and a past-tense one episodic.

## Main definitions

* `TP`, `Tense.tp`: a tensed clause as a set of times (past operator) or a proposition open
  in the tense variable (present); `TP.atSpeech` saturates it with the speech time.
* `before`, `after`, `Veridical`: the connective denotations and the veridicality contrast
  they predict for the English and Japanese fragment entries.
* `relativeClause`, `selectTP`: the two adjunct structures; `Structure.of` assigns them by
  language and connective, and `composes` says which tenses each admits.
* `relativeTense`: the rival consistency requirement, with the rows it mispredicts.

## References

* [arregui-kusumoto-1998]
* [ogihara-1989], [ogihara-1996] — the relative-tense account
* [geis-1970], [larson-1990] — temporal adjuncts as relative clauses
* [prior-1967], [partee-1973] — tense as operator, tense as variable
* [anscombe-1964], [ogihara-1995b] — the before/after veridicality contrast
* [heim-kratzer-1998] — predicate abstraction over the trace
-/

namespace ArreguiKusumoto1998

open Data.Examples English.TemporalExpressions Japanese.TemporalConnectives
open Tense (SOTParameter EmbeddedTenseReading availableReadings)

variable {Time : Type*}

/-! ### Tensed clauses and their types -/

/-- A tensed clause: a past-tense operator yields a set of times, a present-tense variable a
    proposition open in that variable. -/
inductive TP (Time : Type*)
  | times (X : Time → Prop)
  | free (P : Time → Prop)

/-- The semantic type of a tensed clause. -/
inductive Shape
  | times
  | free
  deriving DecidableEq

/-- The type of a tensed clause. -/
def TP.shape : TP Time → Shape
  | .times _ => .times
  | .free _ => .free

/-- The tenses the analysis distinguishes. -/
inductive Tense
  | past
  | present
  deriving DecidableEq, Fintype

/-- The type a tense gives its clause. -/
def Tense.shape : Tense → Shape
  | .past => .times
  | .present => .free

/-- The speech time in C saturates a set of times; an unbound present variable is indexical. -/
def TP.atSpeech : TP Time → Time → Prop
  | .times X, s => X s
  | .free P, s => P s

/-- The clause types a binder index admits. -/
def Shape.selected (binder : Bool) : Shape → Bool
  | .free => binder
  | .times => !binder

/-- A connective selecting TP: with a binder index it abstracts over the present variable,
    without one it takes the set of times a past operator yields. The other two combinations
    are uninterpretable — vacuous binding, or a truth value where a set of times is needed. -/
def selectTP : Bool → TP Time → Option (Time → Prop)
  | true, .free P => some P
  | false, .times X => some X
  | _, _ => none

theorem selectTP_isSome (binder : Bool) (tp : TP Time) :
    (selectTP binder tp).isSome = tp.shape.selected binder := by
  cases binder <;> cases tp <;> rfl

variable [LinearOrder Time]

/-! ### Tense as operator or variable -/

/-- The Priorian past operator closes the clause into the set of times some `P`-time precedes;
    the present tense leaves `P` open in its variable. -/
def Tense.tp : Tense → (Time → Prop) → TP Time
  | .past, P => .times λ t => ∃ t' < t, P t'
  | .present, P => .free P

@[simp] theorem Tense.shape_tp (τ : Tense) (P : Time → Prop) : (τ.tp P).shape = τ.shape := by
  cases τ <;> rfl

/-- A root present-tense sentence holds at the speech time. -/
theorem root_present (P : Time → Prop) (s : Time) : (Tense.present.tp P).atSpeech s ↔ P s :=
  Iff.rfl

/-- A root past-tense sentence holds at some time before the speech time. -/
theorem root_past (P : Time → Prop) (s : Time) :
    (Tense.past.tp P).atSpeech s ↔ ∃ t < s, P t :=
  Iff.rfl

/-! ### Before and after -/

/-- *before*: the times preceding every `X`-time. -/
def before (X : Time → Prop) (t : Time) : Prop := ∀ t', X t' → t < t'

/-- *after*: the times some `X`-time precedes. -/
def after (X : Time → Prop) (t : Time) : Prop := ∃ t', t' < t ∧ X t'

/-- A connective is veridical when its clause holds only if the complement has a time. -/
def Veridical (C : (Time → Prop) → Time → Prop) : Prop := ∀ X t, C X t → ∃ t', X t'

theorem veridical_after : Veridical (after (Time := Time)) := λ _ _ ⟨t', _, h⟩ => ⟨t', h⟩

theorem not_veridical_before (t : Time) : ¬ Veridical (before (Time := Time)) :=
  λ h => (h (λ _ => False) t λ _ h => h.elim).elim λ _ h => h

/-- The connective denotation of a fragment entry's order, where the paper gives one. -/
def denotation : TemporalOrder → Option ((Time → Prop) → Time → Prop)
  | .before => some before
  | .after => some after
  | _ => none

/-- The fragments' veridicality field is the veridicality of the denotation. -/
theorem complementVeridical_iff (t : Time) :
    ∀ e ∈ [before_, after_, mae, ato], ∀ C ∈ denotation (Time := Time) e.order,
      (e.complementVeridical = true ↔ Veridical C) := by
  simp [before_, after_, mae, ato, denotation, veridical_after, not_veridical_before t]

/-! ### Relative-clause adjuncts -/

/-- A relative-clause adjunct: the relative pronoun abstracts over a trace in the clause's
    time argument, and the speech time in C saturates the tensed clause. -/
def relativeClause (τ : Tense) (P : Time → Prop) (s tj : Time) : Prop :=
  (τ.tp λ t => P t ∧ t = tj).atSpeech s

/-- A past-tensed relative clause denotes the past `P`-times, ordered against the speech time
    alone. -/
theorem relativeClause_past (P : Time → Prop) (s t : Time) :
    relativeClause .past P s t ↔ t < s ∧ P t := by
  simp [relativeClause, Tense.tp, TP.atSpeech]

/-- An indexical present in a relative clause denotes the speech time, if `P` holds there. -/
theorem relativeClause_present (P : Time → Prop) (s t : Time) :
    relativeClause .present P s t ↔ P s ∧ s = t :=
  Iff.rfl

/-- A past-tensed matrix clause `Q` modified by an adjunct `X`: the adjunct intersects the VP
    and the matrix past locates the result before the speech time `s`. -/
def modified (Q X : Time → Prop) (s : Time) : Prop := ∃ t < s, Q t ∧ X t

/-- *Satoshi left after Junko came*: both events are past, and the connective alone orders
    them. -/
theorem after_relativeClause (Q P : Time → Prop) (s : Time) :
    modified Q (after (relativeClause .past P s)) s ↔
      ∃ t < s, Q t ∧ ∃ t', t' < t ∧ t' < s ∧ P t' := by
  simp [modified, after, relativeClause_past]

/-- *Satoshi left before Junko came*: the leaving precedes every past coming. -/
theorem before_relativeClause (Q P : Time → Prop) (s : Time) :
    modified Q (before (relativeClause .past P s)) s ↔
      ∃ t < s, Q t ∧ ∀ t', t' < s → P t' → t < t' := by
  simp [modified, before, relativeClause_past]

/-- *Junko was in her room when Satoshi came*, past tense: an episode at a past time. -/
theorem when_past (Q P : Time → Prop) (s : Time) :
    modified Q (relativeClause .past P s) s ↔ ∃ t < s, Q t ∧ t < s ∧ P t := by
  simp [modified, relativeClause_past]

/-- An indexical present in a when-clause contradicts a past matrix: the adjunct time is the
    speech time, which the matrix event precedes. -/
theorem when_present_indexical (Q P : Time → Prop) (s : Time) :
    ¬ modified Q (relativeClause .present P s) s := by
  rintro ⟨t, ht, -, -, rfl⟩
  exact lt_irrefl _ ht

/-- The present variable bound by a covert adverb of quantification: over some past interval,
    every `P`-time is a `Q`-time. -/
def whenever (P Q : Time → Prop) (s : Time) : Prop :=
  ∃ I : Set Time, (∀ t ∈ I, t < s) ∧ ∀ t ∈ I, P t → Q t

/-- The readings of a when-clause. -/
inductive WhenReading
  | episodic
  | habitual
  deriving DecidableEq

/-- A closed past clause yields an episodic reading; an open present variable, whose
    indexical construal is contradictory under a past matrix, is bound by an adverb of
    quantification. -/
def WhenReading.of : Shape → WhenReading
  | .times => .episodic
  | .free => .habitual

/-- The truth conditions of each reading, for a when-clause `P` modifying a past `Q`. -/
def WhenReading.denotation : WhenReading → (Time → Prop) → (Time → Prop) → Time → Prop
  | .episodic, P, Q, s => modified Q (relativeClause .past P s) s
  | .habitual, P, Q, s => whenever P Q s

/-! ### Connectives selecting TP -/

/-- The past operator inside an after-clause is absorbed by *after*. -/
theorem after_past [DenselyOrdered Time] (P : Time → Prop) (t : Time) :
    after (λ t => ∃ t' < t, P t') t ↔ after P t := by
  constructor
  · rintro ⟨t', ht', t'', ht'', h⟩
    exact ⟨t'', ht''.trans ht', h⟩
  · rintro ⟨t', ht', h⟩
    obtain ⟨u, hu, hu'⟩ := exists_between ht'
    exact ⟨u, hu', t', hu, h⟩

/-- *ato* takes the set of times its past-tensed complement denotes, and *after* absorbs the
    past operator. -/
theorem after_selectTP [DenselyOrdered Time] (P : Time → Prop) :
    ∀ X ∈ selectTP false (Tense.past.tp P), after X = after P := by
  simp only [selectTP, Tense.tp, Option.mem_def, Option.some.injEq, forall_eq']
  exact funext λ t => propext (after_past P t)

/-- *Satoshi left after Junko came* in Japanese: the coming precedes the leaving, with no
    relation to the speech time. -/
theorem modified_after (Q P : Time → Prop) (s : Time) :
    modified Q (after P) s ↔ ∃ t < s, Q t ∧ ∃ t', t' < t ∧ P t' :=
  Iff.rfl

/-- *mae* binds the present variable of its complement. -/
theorem before_selectTP (P : Time → Prop) :
    ∀ X ∈ selectTP true (Tense.present.tp P), X = P := by
  simp [selectTP, Tense.tp]

/-- *Satoshi left before Junko came* in Japanese: the leaving precedes every coming, past or
    not. -/
theorem modified_before (Q P : Time → Prop) (s : Time) :
    modified Q (before P) s ↔ ∃ t < s, Q t ∧ ∀ t', P t' → t < t' :=
  Iff.rfl

/-! ### Languages and structures -/

/-- The languages compared. -/
inductive Language
  | english
  | polish
  | japanese
  deriving DecidableEq

/-- English has the sequence-of-tense rule; Polish and Japanese do not. -/
def Language.sot : Language → SOTParameter
  | .english => .relative
  | _ => .absolute

/-- The temporal connectives compared. -/
inductive Connective
  | before
  | after
  | when
  deriving DecidableEq, Fintype

/-- *mae* 'before' is lexically specified with a binder index; *ato* 'after' is not. -/
def Connective.binder : Connective → Bool
  | .before => true
  | _ => false

/-- The structure of a temporal adjunct. -/
inductive Structure
  | relativeClause
  | selectTP
  deriving DecidableEq

/-- English and Polish adjuncts and Japanese *toki*-clauses are relative clauses; Japanese
    *mae* and *ato* select TP. -/
def Structure.of : Language → Connective → Structure
  | .japanese, .before | .japanese, .after => .selectTP
  | _, _ => .relativeClause

/-- Geis readings of an adjunct containing `n` clauses: a relative pronoun can be extracted
    from any of them; a connective selecting TP fixes the highest. -/
def Structure.readings : Structure → ℕ → ℕ
  | .relativeClause, n => n
  | .selectTP, _ => 1

/-- Whether a tensed adjunct is interpretable: a relative clause composes with either tense,
    a connective selecting TP only with the clause type its binder index admits. -/
def composes (l : Language) (c : Connective) (τ : Tense) : Bool :=
  match Structure.of l c with
  | .relativeClause => true
  | .selectTP => τ.shape.selected c.binder

/-! ### The relative-tense account -/

/-- The ordering a tense imposes on the adjunct event against the matrix event under the
    relative-tense account: past before it, the future-oriented present after it. -/
def Tense.relation : Tense → Ordering
  | .past => .lt
  | .present => .gt

/-- The ordering a connective imposes on the adjunct event against the matrix event. -/
def Connective.relation : Connective → Ordering
  | .before => .gt
  | .after => .lt
  | .when => .eq

/-- The relative-tense account: the adjunct tense takes the matrix event time as reference
    time and must agree with the connective, unless a sequence-of-tense rule deletes it. -/
def relativeTense (sot : SOTParameter) (c : Connective) (τ : Tense) : Bool :=
  sot = .relative || τ.relation = c.relation

/-- On *mae* and *ato* the two accounts agree. -/
theorem relativeTense_eq_composes :
    ∀ (c : Connective) (τ : Tense), Structure.of .japanese c = .selectTP →
      relativeTense .absolute c τ = composes .japanese c τ := by
  decide

/-! ### The paper's examples -/

/-- The language of a row. -/
def language? (r : LinguisticExample) : Option Language :=
  match r.language with
  | "stan1293" => some .english
  | "poli1260" => some .polish
  | "nucl1643" => some .japanese
  | _ => none

/-- The connective of a row's adjunct clause. -/
def connective? (r : LinguisticExample) : Option Connective :=
  match r.feature? "clause" with
  | some "before" => some .before
  | some "after" => some .after
  | some "when" => some .when
  | _ => none

/-- The tense of a row's embedded clause. -/
def tense? (r : LinguisticExample) : Option Tense :=
  match r.feature? "embeddedTense" with
  | some "past" => some .past
  | some "present" => some .present
  | _ => none

/-- How many clauses a row's adjunct contains, where the paper builds one on top of another. -/
def clauses? (r : LinguisticExample) : Option ℕ :=
  match r.feature? "embeddedClauses" with
  | some "2" => some 2
  | _ => none

/-- A row's readings as complement readings. -/
def complementReadings (r : LinguisticExample) : List EmbeddedTenseReading :=
  r.readings.filterMap λ x =>
    match x.1 with
    | "shifted" => some .shifted
    | "simultaneous" => some .simultaneous
    | _ => none

/-- A row's readings as when-clause readings. -/
def whenReadings (r : LinguisticExample) : List WhenReading :=
  r.readings.filterMap λ x =>
    match x.1 with
    | "episodic" => some .episodic
    | "habitual" => some .habitual
    | _ => none

/-- A past-under-past complement has the readings the language's sequence-of-tense
    parameter licenses; a present-under-past complement is simultaneous. -/
theorem rows_complement :
    ∀ r ∈ Examples.all, r.feature? "clause" = some "complement" →
      ∀ l ∈ language? r, ∀ τ ∈ tense? r,
        (complementReadings r).Perm
          (match τ with
            | .past => availableReadings l.sot
            | .present => [.simultaneous]) := by
  decide

/-- A past-tensed adjunct is acceptable exactly when it composes: always in a relative
    clause, and under *ato* but not *mae*. -/
theorem rows_past :
    ∀ r ∈ Examples.all, ∀ l ∈ language? r, ∀ c ∈ connective? r, tense? r = some .past →
      (r.judgment = .acceptable ↔ composes l c .past = true) := by
  decide

/-- Japanese adjuncts are acceptable exactly when their tense composes with the connective:
    *mae* with the present, *ato* with the past, *toki* with either. -/
theorem rows_japanese :
    ∀ r ∈ Examples.all, language? r = some .japanese →
      ∀ c ∈ connective? r, ∀ τ ∈ tense? r,
        (r.judgment = .acceptable ↔ composes .japanese c τ = true) := by
  decide

/-- An adjunct built over a further clause has as many readings as its structure provides:
    two for a relative clause, one when the connective selects TP. -/
theorem rows_readings :
    ∀ r ∈ Examples.all, ∀ n ∈ clauses? r, ∀ l ∈ language? r, ∀ c ∈ connective? r,
      (r.readings.filter (·.2 = .acceptable)).length = (Structure.of l c).readings n := by
  decide

/-- A Japanese when-clause is episodic with the past tense and habitual with the present. -/
theorem rows_when :
    ∀ r ∈ Examples.all, connective? r = some .when → ∀ τ ∈ tense? r,
      ∀ w ∈ whenReadings r, w = WhenReading.of τ.shape := by
  decide

/-- The relative-tense account forbids a past tense in a Japanese when-clause and in a Polish
    before-clause, both of which the paper finds acceptable. -/
theorem rows_relativeTense :
    ∀ r ∈ Examples.all, r.source.paperLabel ∈ ["(8)", "(11a)"] →
      ∀ l ∈ language? r, ∀ c ∈ connective? r, ∀ τ ∈ tense? r,
        r.judgment = .acceptable ∧ relativeTense l.sot c τ = false := by
  decide

end ArreguiKusumoto1998
