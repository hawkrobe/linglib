import Linglib.Studies.Anscombe1964
import Linglib.Studies.BeaverCondoravdi2003
import Linglib.Core.Order.AllenRelation
import Linglib.Semantics.Tense.RunTimes
import Linglib.Data.Examples.OgiharaSteinertThrelkeld2024

/-!
# Ogihara and Steinert-Threlkeld (2024): Limitations of a Modal Analysis of Before and After

This file formalizes the argument of [ogihara-steinert-threlkeld-2024] against the
branching-time analysis of *before* in [beaver-condoravdi-2003] and the eventuality-based
revision the paper proposes in its place. *After* is veridical and *before* is not: *he left
before she arrived* is compatible with her never arriving, as the paper's examples record
(`after_rows_veridical`, `before_rows_nonveridical`). Over event predicates the asymmetry is
quantificational, *after* being existential over both events and *before* universal over
the complement, so it holds vacuously when no complement event exists
(`eventAfter`, `eventBefore`, `before_nonveridicality_derived`), and whole-run-time
precedence is strictly stronger than the point-wise relation of [anscombe-1964]
(`not_eventBefore_of_anscombe`). The paper's second section shows that alternatives
branching only after the main-clause time cannot place a complement whose temporal window
closes at or before that time, as in the baseball season ending before Ohtani's tenth win,
the year ending before its first snow, and July 1999 ending before Nostradamus's prophecy
comes true (`bc_cannot_place_bounded_complement`, the three counterexamples). The fourth
section replaces world–time equivalence with an equivalence relative to an interval and an
eventuality whose counterpart co-occurs with it (`equivIE`, `altIE`, `eventContinuation`),
which contains the earlier alternatives (`histAlt_subset_altIE_trivial`), and states the
revamped truth conditions for *before* as three cases, veridical, false, and modal
(`OST.before`, `beforeCase_modal_nonveridical`, `mozart_is_case_iii`).

## Implementation notes

The paper's third section draws a parallel between the modal case of *before* and the
English progressive under the imperfective paradox; the parallel is not formalized here,
the substrate's subinterval lemmas stating the aspectual side on their own. The truth
conditions of the fourth section are, in the paper's words, very weak and in need of
strengthening by contextual and pragmatic factors; the fifth section's remaining problems
for the revamped proposal, the non-committal readings that contextual plausibility governs,
are recorded in the example rows only.

## References

* [ogihara-steinert-threlkeld-2024]
* [beaver-condoravdi-2003]
* [anscombe-1964]
* [heinamaki-1974]
* [landman-1992]
-/

namespace OgiharaSteinertThrelkeld2024

open Data.Examples
open OgiharaSteinertThrelkeld2024.Examples
open Tense Anscombe1964 BeaverCondoravdi2003

/-- The connective a row tests. -/
def connective (e : LinguisticExample) : Option String := e.feature? "connective"

/-- A row records that the sentence entails its complement clause. -/
def ComplementEntailed (e : LinguisticExample) : Prop :=
  e.feature? "complement_entailed" = some "true"

instance : DecidablePred ComplementEntailed := λ _ => inferInstanceAs (Decidable (_ = _))

/-- Every *after* sentence in the paper's data entails its complement. -/
theorem after_rows_veridical :
    ∀ e ∈ Examples.all, connective e = some "after" → ComplementEntailed e := by
  decide

/-- No *before* sentence in the paper's data entails its complement. -/
theorem before_rows_nonveridical :
    ∀ e ∈ Examples.all, connective e = some "before" → ¬ ComplementEntailed e := by
  decide

/-! The connectives over event predicates: *after* is doubly existential — both events
exist and the complement's run-time wholly precedes the main event's — while *before* is
existential over the main clause and universal over the complement, so it is vacuously
satisfied when no complement event exists. The precedence is Allen's `precedes` atom. -/

variable {T : Type*} [LinearOrder T]

/-- *P after Q*: some `P`-event whose run-time some `Q`-event's run-time wholly precedes. -/
def eventAfter (P Q : Event T → Prop) : Prop :=
  ∃ e₁ e₂ : Event T, P e₁ ∧ Q e₂ ∧ e₂.τ.precedes e₁.τ

/-- *P before Q*: some `P`-event whose run-time wholly precedes every `Q`-event's. -/
def eventBefore (P Q : Event T → Prop) : Prop :=
  ∃ e₁ : Event T, P e₁ ∧ ∀ e₂ : Event T, Q e₂ → e₁.τ.precedes e₂.τ

theorem eventAfter_iff_allen (P Q : Event T → Prop) :
    eventAfter P Q ↔ ∃ e₁ e₂ : Event T, P e₁ ∧ Q e₂ ∧
      AllenRelation.holdsIn AllenRelation.precedesSet e₂.τ e₁.τ := by
  simp only [eventAfter, NonemptyInterval.precedes_iff_allen]

theorem eventBefore_iff_allen (P Q : Event T → Prop) :
    eventBefore P Q ↔ ∃ e₁ : Event T, P e₁ ∧ ∀ e₂ : Event T, Q e₂ →
      AllenRelation.holdsIn AllenRelation.precedesSet e₁.τ e₂.τ := by
  simp only [eventBefore, NonemptyInterval.precedes_iff_allen]

/-- *After*'s veridicality follows from its double existential. -/
theorem after_veridicality_derived {P Q : Event T → Prop} (h : eventAfter P Q) :
    ∃ e : Event T, Q e :=
  let ⟨_, e₂, _, hq, _⟩ := h; ⟨e₂, hq⟩

/-- *Before*'s non-veridicality follows from its universal: any `P`-event with an empty `Q`
satisfies it. -/
theorem before_nonveridicality_derived :
    ∃ (P Q : Event ℤ → Prop), eventBefore P Q ∧ ¬ ∃ e : Event ℤ, Q e :=
  ⟨λ e => e = ⟨⟨⟨0, 1⟩, by decide⟩, .action⟩, λ _ => False,
    ⟨⟨⟨⟨0, 1⟩, by decide⟩, .action⟩, rfl, λ _ h => h.elim⟩, λ ⟨_, h⟩ => h⟩

/-- Both connectives commit to the main clause. -/
theorem eventBefore_veridical_main {P Q : Event T → Prop} (h : eventBefore P Q) :
    ∃ e : Event T, P e :=
  let ⟨e₁, hp, _⟩ := h; ⟨e₁, hp⟩

/-- The event-level *after* projects to [anscombe-1964]'s on run-time denotations. -/
theorem anscombe_after_of_eventAfter {P Q : Event T → Prop} (h : eventAfter P Q) :
    Anscombe.after (eventDenotation P) (eventDenotation Q) := by
  obtain ⟨e₁, e₂, hp, hq, hprec⟩ := h
  refine ⟨e₁.τ.fst, ?_, e₂.τ.snd, ?_, hprec⟩
  · rw [timeTrace_eventDenotation]; exact ⟨e₁, hp, le_rfl, e₁.τ.fst_le_snd⟩
  · rw [timeTrace_eventDenotation]; exact ⟨e₂, hq, e₂.τ.fst_le_snd, le_rfl⟩

/-- The event-level *before* projects to [anscombe-1964]'s quantificational one. -/
theorem anscombe_before_of_eventBefore {P Q : Event T → Prop} (h : eventBefore P Q) :
    Anscombe.beforeEver (eventDenotation P) (eventDenotation Q) := by
  obtain ⟨e₁, hp, hall⟩ := h
  refine ⟨e₁.τ.snd, ?_, λ t' ht' => ?_⟩
  · rw [timeTrace_eventDenotation]; exact ⟨e₁, hp, e₁.τ.fst_le_snd, le_rfl⟩
  · rw [timeTrace_eventDenotation] at ht'
    obtain ⟨e₂, hq, ht'_lo, _⟩ := ht'
    exact (hall e₂ hq).trans_le ht'_lo

/-- The projection is strict: [anscombe-1964]'s point-wise *before* allows the main run-time
to reach into the complement's, which whole-run-time precedence forbids. -/
theorem not_eventBefore_of_anscombe :
    ¬ ∀ (P Q : Event ℤ → Prop),
      Anscombe.beforeEver (eventDenotation P) (eventDenotation Q) → eventBefore P Q := by
  intro h
  let eP : Event ℤ := ⟨⟨⟨1, 5⟩, by decide⟩, .action⟩
  let eQ : Event ℤ := ⟨⟨⟨3, 8⟩, by decide⟩, .action⟩
  have hansc : Anscombe.beforeEver (eventDenotation (· = eP)) (eventDenotation (· = eQ)) := by
    refine ⟨1, ?_, ?_⟩
    · rw [timeTrace_eventDenotation]
      exact ⟨eP, rfl, by simp [Event.τ, eP], by simp [Event.τ, eP]⟩
    · intro t' ht'
      rw [timeTrace_eventDenotation] at ht'
      obtain ⟨e, rfl, hlo, _⟩ := ht'
      simp only [Event.τ, eQ] at hlo; omega
  obtain ⟨e₁, rfl, hall⟩ := h _ _ hansc
  have := hall eQ rfl
  simp [NonemptyInterval.precedes, Event.τ, eP, eQ] at this

/-- Scenario: "He left₁ after she arrived₀" with punctual events.
    - leaving event at time 1
    - arriving event at time 0
    the paper predicts: after(leave, arrive) holds (τ(arrive) ≺ τ(leave)). -/
theorem scenario_after_punctual :
    let leave : Event ℤ := ⟨⟨⟨1, 1⟩, le_refl _⟩, .action⟩
    let arrive : Event ℤ := ⟨⟨⟨0, 0⟩, le_refl _⟩, .action⟩
    eventAfter (· = leave) (· = arrive) := by
  refine ⟨⟨⟨⟨1, 1⟩, le_refl _⟩, .action⟩, ⟨⟨⟨0, 0⟩, le_refl _⟩, .action⟩, rfl, rfl, ?_⟩
  simp [NonemptyInterval.precedes, Event.τ]

/-- Scenario: "He left₁ before she arrived₃" with punctual events.
    - leaving event at time 1
    - arriving event at time 3
    the paper predicts: before(leave, arrive) holds (τ(leave) ≺ τ(arrive)). -/
theorem scenario_before_punctual :
    let leave : Event ℤ := ⟨⟨⟨1, 1⟩, le_refl _⟩, .action⟩
    let arrive : Event ℤ := ⟨⟨⟨3, 3⟩, le_refl _⟩, .action⟩
    eventBefore (· = leave) (· = arrive) := by
  refine ⟨⟨⟨⟨1, 1⟩, le_refl _⟩, .action⟩, rfl, ?_⟩
  intro e₂ rfl
  simp [NonemptyInterval.precedes, Event.τ]

/-- Scenario: "The bomb exploded₅ before anyone defused it" (nobody defused it).
    the paper predicts: before(explode, defuse) holds vacuously (no defuse-events). -/
theorem scenario_before_counterfactual :
    let explode : Event ℤ := ⟨⟨⟨5, 5⟩, le_refl _⟩, .action⟩
    eventBefore (· = explode) (λ _ => False) := by
  exact ⟨⟨⟨⟨5, 5⟩, le_refl _⟩, .action⟩, rfl, λ _ h => h.elim⟩

/-- The punctual after-scenario projects correctly through eventDenotation:
    OST.after implies Anscombe.after on the projected interval sets. -/
theorem scenario_after_projects :
    let leave : Event ℤ := ⟨⟨⟨1, 1⟩, le_refl _⟩, .action⟩
    let arrive : Event ℤ := ⟨⟨⟨0, 0⟩, le_refl _⟩, .action⟩
    Anscombe.after (eventDenotation (· = leave)) (eventDenotation (· = arrive)) :=
  anscombe_after_of_eventAfter scenario_after_punctual

/-- The punctual before-scenario projects correctly through eventDenotation. -/
theorem scenario_before_projects :
    let leave : Event ℤ := ⟨⟨⟨1, 1⟩, le_refl _⟩, .action⟩
    let arrive : Event ℤ := ⟨⟨⟨3, 3⟩, le_refl _⟩, .action⟩
    Anscombe.beforeEver (eventDenotation (· = leave)) (eventDenotation (· = arrive)) :=
  anscombe_before_of_eventBefore scenario_before_punctual

/-- A counterexample to B&C's branching-time analysis.
    In each case, the complement eventuality is temporally bounded to an
    interval that ends at or before the A-time. B&C's `alt(w,t)` branches
    only *after* t, so it cannot place the complement in an alternative
    world at a time after the A-time.

    The `boundedBefore` field captures the formal crux: the complement's
    temporal bound ends at or before the A-time. -/
structure BCCounterexampleDatum where
  /-- The example sentence -/
  sentence : String
  /-- The A-clause time (e.g., end of MLB season, end of 2020) -/
  aTime : ℤ
  /-- Upper bound of the complement's temporal window -/
  complementUpperBound : ℤ
  /-- The complement is temporally bounded before the A-time -/
  boundedBefore : complementUpperBound ≤ aTime
  /-- Which B&C reading is involved? -/
  reading : BeforeReading

/-- B&C's `before` requires `earliestAlt` to find a B-instantiation in
    some alternative world. When B is temporally bounded to `[lo, hi]`
    with `hi ≤ tA`, and `alt(w,tA)` only contains worlds that agree with
    w up to `tA`, B cannot be instantiated *after* `tA` in any alternative.

    This is the formal content of the paper's §5.1 critique: B&C's forward-
    branching architecture cannot handle complements whose temporal bound
    falls before the A-time. -/
theorem bc_cannot_place_bounded_complement
    {W : Type*} (alt : HistoricalAlternatives W ℤ)
    (B : Set (W × ℤ)) (w : W) (tA hi : ℤ)
    (hBound : hi ≤ tA)
    (_hBounded : ∀ w' t, (w', t) ∈ B → t ≤ hi)
    (hNoFuture : ∀ w' ∈ alt ⟨w, tA⟩, ∀ t, (w', t) ∈ B → t ≤ hi) :
    ∀ te ∈ instTimes (alt ⟨w, tA⟩) B, te ≤ tA := by
  intro te ⟨w', _, hw'B⟩
  exact le_trans (hNoFuture w' ‹_› te hw'B) hBound

/-- (20a) "Unfortunately, the 2021 MLB season will be over before Shohei Ohtani
    earns his 10th win of the season." (Uttered in the middle of September 2021.)
    The A-time is the end of the 2021 MLB season (October 3, 2021 = day 276).
    The complement (Ohtani's 10th win) can only occur during the season
    (before day 276). ([ogihara-steinert-threlkeld-2024], §5.1, ex. 20a) -/
def ost_counterexample_ohtani : BCCounterexampleDatum where
  sentence := ost2024_ohtani.primaryText
  aTime := 276
  complementUpperBound := 275
  boundedBefore := by omega
  reading := .counterfactual

/-- (20b) "2020 might come to an end before it snows for the first time this year."
    (Uttered on Christmas Day in 2020.) The expression *this year* refers back
    to 2020. Since the first snow of 2020 can only occur in 2020, the modal
    proposal that posits a fictitious snow event after the end of 2020 does not
    work. ([ogihara-steinert-threlkeld-2024], §5.1, ex. 20b) -/
def ost_counterexample_snow : BCCounterexampleDatum where
  sentence := ost2024_snow.primaryText
  aTime := 366
  complementUpperBound := 366
  boundedBefore := le_refl _
  reading := .nonCommittal

/-- (20c) "July 1999 will come to an end before Nostradamus' prophecy about the
    end of the world comes true." (Uttered a few minutes before the end of July
    1999. Assumes Michel de Nostradamus predicted that in July 1999, a great King
    of terror would come from the sky and destroy the world.) The prophecy can
    only come true if the world is destroyed in July 1999 — it cannot come true
    after the end of July 1999. ([ogihara-steinert-threlkeld-2024], §5.1, ex. 20c) -/
def ost_counterexample_nostradamus : BCCounterexampleDatum where
  sentence := ost2024_nostradamus.primaryText
  aTime := 31
  complementUpperBound := 31
  boundedBefore := le_refl _
  reading := .counterfactual

/-! ### The event-relative equivalence and alternatives (defs 17–18)

The paper's positive proposal replaces [beaver-condoravdi-2003]'s world–time
equivalence with one relative to an interval `I` and an eventuality `e`:
alternative worlds must contain a counterpart of `e` that co-occurs with it up
to `I`, and be identical at all earlier times. -/

section EventRelative

variable {W T : Type*} [LinearOrder T]

/-- Counterpart relation on eventualities across worlds (fn. 18): counterpart
eventualities share essential properties such as starting time and thematic
participants. -/
abbrev Counterpart (W T : Type*) := W → T → W → T → Prop

/-- Event-relative equivalence ≃_{I,e₁} (def 17): (i) a counterpart of `e₁`
exists in `w₂`; (ii) the two co-occur throughout [START(e₁), START(I)); (iii)
the worlds are identical at all earlier times. -/
def equivIE (counterpart : Counterpart W T)
    (coOccur : W → T → W → T → T → T → Prop)
    (agree : T → W → W → Prop)
    (w₁ w₂ : W) (startI : T) (e₁_start : T) : Prop :=
  counterpart w₁ e₁_start w₂ e₁_start ∧
  coOccur w₁ e₁_start w₂ e₁_start e₁_start startI ∧
  (∀ t', t' < e₁_start → agree t' w₁ w₂)

/-- Event-relative alternatives alt(w, I, e) (def 18a). -/
def altIE (counterpart : Counterpart W T)
    (coOccur : W → T → W → T → T → T → Prop)
    (agree : T → W → W → Prop)
    (w : W) (startI : T) (e_start : T) : Set W :=
  { w' | equivIE counterpart coOccur agree w w' startI e_start }

/-- Event continuation (def 18b): keep only the alternatives in which the
counterpart eventuality develops beyond `I`. -/
def eventContinuation (alt : Set W) (continues : W → Prop) : Set W :=
  { w' ∈ alt | continues w' }

/-- Downward closure (def 18c): equivalence at `I` implies equivalence at any
earlier `I'`. -/
theorem equivIE_downward_closed (counterpart : Counterpart W T)
    (coOccur : W → T → W → T → T → T → Prop)
    (coOccur_mono : ∀ w₁ e₁ w₂ e₂ s₁ s₂ s₂',
      s₂' ≤ s₂ → coOccur w₁ e₁ w₂ e₂ s₁ s₂ → coOccur w₁ e₁ w₂ e₂ s₁ s₂')
    (agree : T → W → W → Prop)
    (w₁ w₂ : W) (startI startI' : T) (e_start : T)
    (hle : startI' ≤ startI)
    (h : equivIE counterpart coOccur agree w₁ w₂ startI e_start) :
    equivIE counterpart coOccur agree w₁ w₂ startI' e_start :=
  ⟨h.1, coOccur_mono w₁ e_start w₂ e_start e_start startI startI' hle h.2.1, h.2.2⟩

/-- With trivial counterpart and co-occurrence, ≃_{I,e} is agreement at all
earlier times — the per-world-pair content of B&C's initial branch point
condition. -/
theorem equivIE_trivial_iff_agree (agree : T → W → W → Prop)
    (w₁ w₂ : W) (startI e_start : T) :
    equivIE (λ _ _ _ _ => True) (λ _ _ _ _ _ _ => True) agree w₁ w₂ startI e_start ↔
    (∀ t', t' < e_start → agree t' w₁ w₂) := by
  simp [equivIE]

/-- Any B&C alternative set obeying the initial branch point condition lands
inside the trivial event-relative alternatives: the O&ST equivalence
generalizes B&C's. -/
theorem histAlt_subset_altIE_trivial (alt : HistoricalAlternatives W T)
    (agree : T → W → W → Prop)
    (hIBP : BeaverCondoravdi2003.initialBranchPoint alt agree)
    (w : W) (t : T) :
    alt ⟨w, t⟩ ⊆ altIE (λ _ _ _ _ => True) (λ _ _ _ _ _ _ => True) agree w t t := by
  intro w' hw'
  rw [altIE, Set.mem_ofPred_eq, equivIE_trivial_iff_agree]
  exact hIBP w t w' hw'

end EventRelative

/-! The paper's central formal contribution: revamped truth conditions for
    *before* that incorporate eventuality-relative alternatives (def 18) and
    a CAUSE relation. Three cases for ⟦A before B⟧ evaluated at ⟨w₀, I₀, e₀⟩:

    **(i) Definitely true (veridical)**: A holds at ⟨w₀,I₀,e₀⟩ AND B already
    holds at some later interval I₂ > I₀ in w₀. The complement already
    occurred after A — straightforwardly true.

    **(ii) Definitely false**: A holds at ⟨w₀,I₀,e₀⟩ AND B already holds at
    some interval I₂ ≤ I₀ in w₀. The complement already occurred before/at
    A — so A is NOT before B.

    **(iii) Modal case (anti-veridical / non-committal)**: A holds at
    ⟨w₀,I₀,e₀⟩ and I₀ precedes the earliest I₁ such that ∃ eventuality e₁
    ongoing at I₀ in w₀, ∃ world w₁ ∈ alt(w₀,I₀,e₁), ∃ e₂ counterpart of
    e₁ in w₁, the continuation of e₂ CAUSES an eventuality e₃ with
    ⟨w₁,I₁,e₃⟩ ∈ ⟦B⟧.

    The authors note these truth conditions are "very weak and need to be
    strengthened by some contextual and pragmatic factors." -/

section Def19

variable {W T E : Type*} [LinearOrder T]

/-- Two intervals abut: the first ends where the second begins (no gap). -/
def abuts (I₀ I₁ : NonemptyInterval T) : Prop :=
  I₀.snd = I₁.fst

/-- An eventuality e₁ "holds throughout" an interval that abuts I₀:
    e₁'s runtime extends from before I₀ through to (at least) I₀'s start. -/
def holdsAtAbutting (runtime : E → NonemptyInterval T) (e₁ : E)
    (I₀ : NonemptyInterval T) : Prop :=
  (runtime e₁).fst ≤ I₀.fst ∧ I₀.fst ≤ (runtime e₁).snd

/-- Denotation type for the paper's truth conditions: sets of
    world–interval–eventuality triples. -/
abbrev SitDenot (W T E : Type*) [LinearOrder T] := Set (W × NonemptyInterval T × E)

/-- **Case (i)**: ⟦A before B⟧ = 1 when the complement B already holds
    at some interval after I₀ in the actual world w₀. -/
def beforeCase_veridical
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧ ∃ I₂ : NonemptyInterval T, I₀.snd < I₂.fst ∧
    ∃ e₄ : E, (w₀, I₂, e₄) ∈ B

/-- **Case (ii)**: ⟦A before B⟧ = 0 when the complement B already holds
    at some interval at or before I₀ in the actual world w₀. -/
def beforeCase_false
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧ ∃ I₂ : NonemptyInterval T, I₂.snd ≤ I₀.fst ∧
    ∃ e₅ : E, (w₀, I₂, e₅) ∈ B

/-- **Case (iii)**: The modal case. ⟦A before B⟧ = 1 when A holds at ⟨w₀,I₀,e₀⟩
    and I₀ precedes the earliest I₁ such that:
    - there is an eventuality e₁ in w₀ whose runtime abuts I₀,
    - there is an alternative world w₁ ∈ alt(w₀, I₀, e₁),
    - in w₁, the counterpart e₂ of e₁ continues and CAUSES an eventuality e₃,
    - ⟨w₁, I₁, e₃⟩ ∈ ⟦B⟧. -/
def beforeCase_modal
    (A B : SitDenot W T E)
    (runtime : E → NonemptyInterval T)
    (alt : W → NonemptyInterval T → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧
  ∃ I₁ : NonemptyInterval T,
    I₀.snd < I₁.fst ∧  -- I₀ precedes I₁
    ∃ e₁ : E,
      holdsAtAbutting runtime e₁ I₀ ∧  -- e₁ ongoing at I₀
      ∃ w₁ ∈ alt w₀ I₀ e₁,  -- alternative world
        ∃ e₂ : E,
          counterpart w₀ e₁ w₁ e₂ ∧  -- e₂ is counterpart of e₁
          ∃ e₃ : E,
            cause w₁ e₂ e₃ ∧  -- continuation of e₂ CAUSES e₃
            (w₁, I₁, e₃) ∈ B  -- B holds at ⟨w₁, I₁, e₃⟩

/-- **the paper's revamped *before*** (def 19): the disjunction of the three cases.
    Evaluated at ⟨w₀, I₀, e₀⟩, "A before B" is true iff either:
    - (i) B already occurred after I₀ (veridical), or
    - (iii) The modal case via alt(w₀,I₀,e₁) + CAUSE holds,
    AND case (ii) does not hold (B did not already occur before I₀). -/
def OST.before
    (A B : SitDenot W T E)
    (runtime : E → NonemptyInterval T)
    (alt : W → NonemptyInterval T → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  ¬beforeCase_false A B w₀ I₀ e₀ ∧
  (beforeCase_veridical A B w₀ I₀ e₀ ∨
   beforeCase_modal A B runtime alt cause counterpart w₀ I₀ e₀)

/-- Case (i) is veridical: when the complement has already occurred (after I₀),
    the complement is instantiated in the actual world. -/
theorem beforeCase_veridical_entails_complement
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) :
    beforeCase_veridical A B w₀ I₀ e₀ → ∃ I e, (w₀, I, e) ∈ B := by
  rintro ⟨_, I₂, _, e₄, hB⟩
  exact ⟨I₂, e₄, hB⟩

/-- Case (iii) is non-veridical: the complement need not be instantiated in
    w₀ — it may only exist in an alternative world w₁.

    Scenario: w₀ = false (actual), w₁ = true (alternative).
    A = {(false, [0,0], ())} — main clause holds only in w₀.
    B = {(true, [2,2], ())} — complement holds only in w₁.
    The modal case holds because alt gives w₁, with trivial cause/counterpart.
    But B has no witness in w₀. -/
theorem beforeCase_modal_nonveridical :
    ∃ (A B : SitDenot Bool ℤ Unit)
      (runtime : Unit → NonemptyInterval ℤ)
      (alt : Bool → NonemptyInterval ℤ → Unit → Set Bool)
      (cause : Bool → Unit → Unit → Prop)
      (counterpart : Bool → Unit → Bool → Unit → Prop)
      (w₀ : Bool) (I₀ : NonemptyInterval ℤ) (e₀ : Unit),
    beforeCase_modal A B runtime alt cause counterpart w₀ I₀ e₀ ∧
    ¬∃ I e, (w₀, I, e) ∈ B := by
  refine ⟨{(false, ⟨⟨0, 0⟩, le_refl _⟩, ())},
          {(true, ⟨⟨2, 2⟩, le_refl _⟩, ())},
          λ _ => ⟨⟨-1, 0⟩, by omega⟩,
          λ _ _ _ => {true},
          λ _ _ _ => True,      -- cause : W → E → E → Prop
          λ _ _ _ _ => True,    -- counterpart : W → E → W → E → Prop
          false, ⟨⟨0, 0⟩, le_refl _⟩, (), ?_, ?_⟩
  · refine ⟨rfl, ⟨⟨2, 2⟩, le_refl _⟩, ?_, (), ⟨?_, true, rfl, (),
      ⟨trivial, (), trivial, rfl⟩⟩⟩
    · show (0 : ℤ) < 2; omega
    · exact ⟨by show (-1 : ℤ) ≤ 0; omega, by show (0 : ℤ) ≤ 0; omega⟩
  · rintro ⟨I, e, hB⟩
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hB
    exact absurd hB.1 Bool.false_ne_true

/-- Cases (i) and (ii) are mutually exclusive when the complement occurs at
    a single interval: it cannot be both before and after I₀. -/
theorem cases_i_ii_exclusive
    (I₀ I_B : NonemptyInterval T)
    (hAfter : I₀.snd < I_B.fst)
    (hBefore : I_B.snd ≤ I₀.fst) :
    False := by
  have : I_B.snd < I_B.fst := lt_of_le_of_lt hBefore (lt_of_le_of_lt I₀.fst_le_snd hAfter)
  exact absurd this (not_lt.mpr I_B.fst_le_snd)

/-- The Mozart scenario: "Mozart died before he finished the Requiem."
    This is the anti-veridical reading (case iii). Mozart's death (e₀) is at
    I₀. In some alternative world w₁, Mozart's composing (e₁, ongoing at I₀)
    has a counterpart e₂ whose continuation CAUSES a finishing event e₃ at I₁.
    B ("finishing the Requiem") holds at ⟨w₁, I₁, e₃⟩ but NOT in w₀. -/
theorem mozart_is_case_iii
    {W E : Type*}
    (A B : SitDenot W ℤ E)
    (runtime : E → NonemptyInterval ℤ)
    (alt : W → NonemptyInterval ℤ → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : NonemptyInterval ℤ) (e₀ : E)
    (hNoFinish : ¬∃ I e, (w₀, I, e) ∈ B)
    (hModal : beforeCase_modal A B runtime alt cause counterpart w₀ I₀ e₀) :
    OST.before A B runtime alt cause counterpart w₀ I₀ e₀ := by
  refine ⟨?_, Or.inr hModal⟩
  intro ⟨_, I₂, _, e₅, hB⟩
  exact hNoFinish ⟨I₂, e₅, hB⟩

end Def19

end OgiharaSteinertThrelkeld2024
