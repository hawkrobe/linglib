import Linglib.Semantics.Tense.GramTense

/-!
# Compositional Tense Operators
[mendes-2025] [partee-1973]

Semantic operators for grammatical tense (PAST, PRES, FUT), in two styles:
Reichenbach-style (tense relates R to P on a frame, `applyTense`) and
situation-semantic ([mendes-2025]: operators constrain the temporal
coordinate of a situation argument). Both are driven by the shared
temporal-relation kernel (`precedes`/`coincides`/`follows`), which is also
the source of truth for the dynamic counterparts in `Tense/Dynamic.lean`.
Following [partee-1973], tenses are pronoun-like: they retrieve temporal
reference points rather than quantify over all times.
-/

namespace Tense

open Core (WorldTimeIndex)



/--
Type of tense operators.

A tense operator takes:
- A temporal predicate P : (s, s') → Prop
- Two situations: the "now" situation s and evaluation situation s'
- Returns whether P holds with the tense constraint
-/
abbrev TenseOp (W Time : Type*) := SitProp W Time → WorldTimeIndex W Time → WorldTimeIndex W Time → Prop

/-! ### Temporal-relation kernel -/

/-!
The temporal constraint of each tense, factored out as a pure relation
on `WorldTimeIndex` pairs and shared with the dynamic-context-update
counterparts in `Tense/Dynamic.lean` via `dynRelation`. This is the
Heim-Kratzer "tense as relation between times" intuition isolated from
the propositional payload, so that a single relation kernel (`precedes`/
`coincides`/`follows`) is the source of truth for both static `PAST`/
`PRES`/`FUT` (Compositional, this file) and their dynamic eliminative-
update counterparts (`Tense/Dynamic.lean`). Trichotomy and pairwise
exclusion proved at this layer propagate to both static and dynamic
operators by definitional unfolding.
-/

/-- Event time precedes reference time. The temporal kernel of `PAST`
and `dynPAST`. Reducible so `decide` and `rw` see through to the
underlying `<` on `.time`. -/
abbrev precedes {W Time : Type*} [LT Time]
    (s₁ s₂ : WorldTimeIndex W Time) : Prop :=
  s₁.time < s₂.time

/-- Event time coincides with reference time. The temporal kernel of
`PRES` and `dynPRES`. -/
abbrev coincides {W Time : Type*}
    (s₁ s₂ : WorldTimeIndex W Time) : Prop :=
  s₁.time = s₂.time

/-- Event time follows reference time. The temporal kernel of `FUT`
and `dynFUT`. -/
abbrev follows {W Time : Type*} [LT Time]
    (s₁ s₂ : WorldTimeIndex W Time) : Prop :=
  s₁.time > s₂.time

/-- The three temporal relations partition any pair of situations on a
linear order. Used downstream by `temporal_partition` (in
`Tense/Dynamic.lean`) and by static analyses that need exhaustive case
analysis on tense. -/
theorem precedes_or_coincides_or_follows {W Time : Type*} [LinearOrder Time]
    (s₁ s₂ : WorldTimeIndex W Time) :
    precedes s₁ s₂ ∨ coincides s₁ s₂ ∨ follows s₁ s₂ :=
  lt_trichotomy s₁.time s₂.time

/-- `precedes` and `follows` are mutually exclusive on any preorder. -/
theorem not_precedes_and_follows {W Time : Type*} [Preorder Time]
    (s₁ s₂ : WorldTimeIndex W Time) :
    ¬ (precedes s₁ s₂ ∧ follows s₁ s₂) :=
  fun ⟨h₁, h₂⟩ => lt_asymm h₁ h₂

/-- `precedes` and `coincides` are mutually exclusive on any preorder. -/
theorem not_precedes_and_coincides {W Time : Type*} [Preorder Time]
    (s₁ s₂ : WorldTimeIndex W Time) :
    ¬ (precedes s₁ s₂ ∧ coincides s₁ s₂) :=
  fun ⟨h₁, h₂⟩ =>
    have h₁' : s₁.time < s₂.time := h₁
    have h₂' : s₁.time = s₂.time := h₂
    lt_irrefl _ (h₂' ▸ h₁')

/-- `coincides` and `follows` are mutually exclusive on any preorder. -/
theorem not_coincides_and_follows {W Time : Type*} [Preorder Time]
    (s₁ s₂ : WorldTimeIndex W Time) :
    ¬ (coincides s₁ s₂ ∧ follows s₁ s₂) :=
  fun ⟨h₁, h₂⟩ =>
    have h₁' : s₁.time = s₂.time := h₁
    have h₂' : s₂.time < s₁.time := h₂
    lt_irrefl _ (h₁' ▸ h₂')

/--
PAST operator ([mendes-2025] style)

⟦PAST⟧ = λP.λs.λs'. τ(s) < τ(s') ∧ P(s)

The PAST operator:
1. Requires the event situation s to precede reference situation s'
2. Evaluates P at the past situation s

Defined via the `precedes` kernel (above) so the temporal constraint is
shared with `dynPAST` in `Tense/Dynamic.lean`.
-/
def PAST {W Time : Type*} [LT Time] : TenseOp W Time :=
  λ P s s' => precedes s s' ∧ P s

/--
PRES operator ([mendes-2025] style)

⟦PRES⟧ = λP.λs.λs'. τ(s) = τ(s') ∧ P(s)

The PRESENT operator:
1. Requires the event situation s to be contemporaneous with s'
2. Evaluates P at situation s

Defined via the `coincides` kernel.
-/
def PRES {W Time : Type*} : TenseOp W Time :=
  λ P s s' => coincides s s' ∧ P s

/--
FUT operator ([mendes-2025] style)

⟦FUT⟧ = λP.λs.λs'. τ(s) > τ(s') ∧ P(s)

The FUTURE operator:
1. Requires the event situation s to follow reference situation s'
2. Evaluates P at the future situation s

Defined via the `follows` kernel.
-/
def FUT {W Time : Type*} [LT Time] : TenseOp W Time :=
  λ P s s' => follows s s' ∧ P s


/-
For simpler analyses, tense can modify a predicate relative to a fixed
speech time, without threading through two situations.

These are the "traditional" tense operators.
-/

/--
Simple PAST: Event time precedes speech time.

⟦PAST⟧ₛᵢₘₚₗₑ = λP.λt.λt_s. t < t_s ∧ P(t)
-/
def pastSimple {Time : Type*} [LT Time] (P : Time → Prop) (eventTime speechTime : Time) : Prop :=
  eventTime < speechTime ∧ P eventTime

/--
Simple PRESENT: Event time equals speech time.
-/
def presSimple {Time : Type*} (P : Time → Prop) (eventTime speechTime : Time) : Prop :=
  eventTime = speechTime ∧ P eventTime

/--
Simple FUTURE: Event time follows speech time.
-/
def futSimple {Time : Type*} [LT Time] (P : Time → Prop) (eventTime speechTime : Time) : Prop :=
  eventTime > speechTime ∧ P eventTime


/--
Apply a tense to a Reichenbach frame, constraining R relative to P.
Tense locates reference time relative to perspective time,
not speech time. In root clauses P = S, so this reduces to the standard
Reichenbach analysis. In SOT languages, embedded P shifts to the matrix
event time, making the embedded tense relative.
-/
def applyTense {Time : Type*} [LinearOrder Time] (t : GramTense) (f : ReichenbachFrame Time) : Prop :=
  match t with
  | .past => f.referenceTime < f.perspectiveTime
  | .present => f.referenceTime = f.perspectiveTime
  | .future => f.referenceTime > f.perspectiveTime
  | .nonpast => f.referenceTime ≥ f.perspectiveTime

instance {Time : Type*} [LinearOrder Time] (t : GramTense) (f : ReichenbachFrame Time) :
    Decidable (applyTense t f) :=
  match t with
  | .past => inferInstanceAs (Decidable (_ < _))
  | .present => inferInstanceAs (Decidable (_ = _))
  | .future => inferInstanceAs (Decidable (_ > _))
  | .nonpast => inferInstanceAs (Decidable (_ ≥ _))


/-! ### applyTense ↔ GramTense.constrains Bridge -/

/-- `applyTense` is the Reichenbach-frame projection of `GramTense.constrains`:
    applying a tense to a frame is equivalent to the tense's temporal constraint
    on the frame's R and P. -/
theorem applyTense_eq_constrains {Time : Type*} [LinearOrder Time]
    (t : GramTense) (f : ReichenbachFrame Time) :
    applyTense t f ↔ t.constrains f.referenceTime f.perspectiveTime := by
  cases t <;> rfl


/--
PAST requires temporal precedence.
-/
theorem past_requires_precedence {W Time : Type*} [LT Time]
    (P : SitProp W Time) (s s' : WorldTimeIndex W Time) :
    PAST P s s' → s.time < s'.time := by
  intro ⟨h, _⟩
  exact h

/--
FUT requires temporal succession.
-/
theorem fut_requires_succession {W Time : Type*} [LT Time]
    (P : SitProp W Time) (s s' : WorldTimeIndex W Time) :
    FUT P s s' → s.time > s'.time := by
  intro ⟨h, _⟩
  exact h

/--
PRES requires contemporaneity.
-/
theorem pres_requires_contemporaneity {W Time : Type*}
    (P : SitProp W Time) (s s' : WorldTimeIndex W Time) :
    PRES P s s' → s.time = s'.time := by
  intro ⟨h, _⟩
  exact h

/--
Tense preserves the predicate.

If TENSE(P)(s, s'), then P(s).
-/
theorem past_preserves_pred {W Time : Type*} [LT Time]
    (P : SitProp W Time) (s s' : WorldTimeIndex W Time) :
    PAST P s s' → P s := by
  intro ⟨_, h⟩
  exact h

theorem pres_preserves_pred {W Time : Type*}
    (P : SitProp W Time) (s s' : WorldTimeIndex W Time) :
    PRES P s s' → P s := by
  intro ⟨_, h⟩
  exact h

theorem fut_preserves_pred {W Time : Type*} [LT Time]
    (P : SitProp W Time) (s s' : WorldTimeIndex W Time) :
    FUT P s s' → P s := by
  intro ⟨_, h⟩
  exact h


section Examples

/-- Example predicate: "rain at situation s" -/
def raining (W : Type*) : SitProp W ℤ := λ _s => True  -- placeholder

/-- "It rained" is true iff there's a past situation where it rained -/
example : PAST (raining Unit) ⟨(), -1⟩ ⟨(), 0⟩ := by
  constructor
  · -- -1 < 0
    decide
  · -- raining holds (trivially true)
    trivial

/-- "It will rain" is true iff there's a future situation where it rains -/
example : FUT (raining Unit) ⟨(), 1⟩ ⟨(), 0⟩ := by
  constructor
  · -- 1 > 0
    decide
  · trivial

end Examples

end Tense
