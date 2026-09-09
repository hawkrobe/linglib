import Linglib.Semantics.Aspect.Basic
import Linglib.Studies.Karttunen1974
import Linglib.Fragments.English.TemporalExpressions
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Greek.StandardModern.TemporalConnectives
import Linglib.Fragments.Icelandic.TemporalConnectives
import Linglib.Fragments.Dutch.TemporalConnectives
import Linglib.Data.Examples.Giannakidou2002

/-!
# Giannakidou (2002): UNTIL, Aspect, and Negation

This file formalizes [giannakidou-2002]'s argument for [karttunen-1974]'s two *until*s against
the one-*until* analysis on which negation is an aspectual stativizer ([mittwoch-1977],
[de-swart-1996]). Durative UNTIL asks its description to hold at every subinterval of an
interval ending at the until time (`durativeUntil`), which a homogeneous description supplies
(`durativeUntil_iff_of_homogeneous`) and a perfective description of a single event cannot
(`not_durativeUntil_prfv`): the imperfective is homogeneous (`impf_homogeneous`), so Greek, which
marks aspect overtly, lets *mexri* combine with imperfectives and not with negated perfectives,
where the scalar polarity item *para monon* stands in. Under negation the two analyses part ways:
the wide-scope reading is durative UNTIL of the state of not-P-ing and holds when nothing P-like
ever happens (`wideScope_of_forall_not`), whereas the eventive UNTIL entails the event
(`eventiveUntil_actualization`) and is Karttunen's *not until* together with the actualization his
presupposition supplies (`eventiveUntil_iff`). *Before* shares the scale but not the event
(`eventiveUntil_not_before`, `not_before_of_forall_not`).

The rows are the paper's Greek, English, Icelandic and Dutch sentences. `Predicted` derives each
judgment from the fragment entry of its connective, the homogeneity its aspect or eventuality
affords, and the licensing its polarity requires; the wide-scope reading, which preposing and a
continuation denying the event diagnose, needs an imperfective or perfect form, which the English
simple past is not. The stativity diagnostics of the paper's fifth section follow from the same
homogeneity criterion with negation playing no role (`diagnostics_predicted`).

## Implementation notes

* Descriptions are the aspect substrate's interval predicates; events carry a run time and a
  perfective description places it within the reference interval, an imperfective one strictly
  around it. The until interval is required to be nondegenerate, which is what excludes a single
  event from satisfying the durative condition at both its endpoints.
* Which connectives are durative and which punctual is read off the fragments' `order` and
  `forcesPunctual`; English *until* gets its eventive use from the polarity-item fragment. That
  *para monon*, *fyrr en* and English *until* need an antiveridical licenser while Dutch *pas* is
  a positive polarity item is the paper's classification and is recorded here, not in the
  fragments.
* The oddity of *Nancy didn't get married until she died* and of its Greek counterpart, which the
  actualization entailment explains, is pragmatic and is left in prose.

## References

* [giannakidou-2002]
* [karttunen-1974]
* [mittwoch-1977]
* [de-swart-1996]
-/

namespace Giannakidou2002

open Aspect Tense Karttunen1974 Heinamaki1974 Data.Examples

variable {W T : Type*} [LinearOrder T]

/-! ### Durative UNTIL and homogeneity -/

/-- A description of intervals is homogeneous when it holds at every subinterval of an interval
it holds at. -/
def Homogeneous (p : IntervalPred W T) : Prop :=
  ∀ w, ∀ i j : NonemptyInterval T, j ≤ i → p w i → p w j

theorem impf_homogeneous (P : W → Event T → Prop) : Homogeneous (IMPF P) :=
  λ _ _ _ hji ⟨e, hlt, he⟩ => ⟨e, lt_of_le_of_lt hji hlt, he⟩

theorem unbounded_homogeneous (P : W → Event T → Prop) : Homogeneous (UNBOUNDED P) :=
  λ _ _ _ hji ⟨e, hle, he⟩ => ⟨e, hji.trans hle, he⟩

/-- Durative UNTIL: the description holds at every subinterval of a nondegenerate interval ending
at the until time. -/
def durativeUntil (p : IntervalPred W T) (w : W) (t' : T) : Prop :=
  ∃ i : NonemptyInterval T, i.fst < i.snd ∧ i.snd = t' ∧ ∀ j ≤ i, p w j

/-- A homogeneous description need only hold at the until interval itself. -/
theorem durativeUntil_iff_of_homogeneous {p : IntervalPred W T} (hp : Homogeneous p) (w : W)
    (t' : T) :
    durativeUntil p w t' ↔ ∃ i : NonemptyInterval T, i.fst < i.snd ∧ i.snd = t' ∧ p w i :=
  ⟨λ ⟨i, hi, ht, h⟩ => ⟨i, hi, ht, h i le_rfl⟩,
    λ ⟨i, hi, ht, h⟩ => ⟨i, hi, ht, λ j hj => hp w i j hj h⟩⟩

/-- A perfective description of a single event is incompatible with durative UNTIL: an
achievement or accomplishment cannot lie within both endpoints of the until interval. -/
theorem not_durativeUntil_prfv {P : W → Event T → Prop} {w : W}
    (hP : ∀ e e', P w e → P w e' → e = e') (t' : T) : ¬ durativeUntil (PRFV P) w t' := by
  rintro ⟨i, hi, -, h⟩
  obtain ⟨e₁, h₁, he₁⟩ :=
    h (NonemptyInterval.pure i.fst) (NonemptyInterval.le_def.mpr ⟨le_rfl, i.fst_le_snd⟩)
  obtain ⟨e₂, h₂, he₂⟩ :=
    h (NonemptyInterval.pure i.snd) (NonemptyInterval.le_def.mpr ⟨i.fst_le_snd, le_rfl⟩)
  obtain rfl := hP e₁ e₂ he₁ he₂
  exact absurd ((NonemptyInterval.le_def.mp h₂).1.trans
    (e₁.τ.fst_le_snd.trans (NonemptyInterval.le_def.mp h₁).2)) (not_le.mpr hi)

/-! ### Negation: wide scope, narrow scope and the eventive UNTIL -/

/-- The state of not-P-ing that a stativizing negation would deliver: no P-event overlaps the
interval. -/
def notState (P : W → Event T → Prop) : IntervalPred W T :=
  λ w i => ∀ e, P w e → ∀ a ∈ e.τ, a ∉ i

theorem notState_homogeneous (P : W → Event T → Prop) : Homogeneous (notState P) :=
  λ _ _ _ hji h e he a ha haj => h e he a ha (NonemptyInterval.coe_subset_coe.mpr hji haj)

/-- Mittwoch's wide-scope reading: durative UNTIL of the state of not-P-ing. -/
def wideScope (P : W → Event T → Prop) (w : W) (t' : T) : Prop := durativeUntil (notState P) w t'

/-- External negation: the durative UNTIL claim denied. -/
def narrowScope (p : IntervalPred W T) (w : W) (t' : T) : Prop := ¬ durativeUntil p w t'

/-- Karttunen's eventive UNTIL, scalar: a P-event at the until time and none starting earlier. -/
def eventiveUntil (P : W → Event T → Prop) (w : W) (t : T) : Prop :=
  (∃ e, P w e ∧ t ∈ e.τ) ∧ ∀ e, P w e → t ≤ e.τ.fst

theorem eventiveUntil_actualization {P : W → Event T → Prop} {w : W} {t : T}
    (h : eventiveUntil P w t) : ∃ e, P w e :=
  let ⟨⟨e, he, _⟩, _⟩ := h; ⟨e, he⟩

/-- The wide-scope reading holds when nothing P-like ever happens: it carries no actualization. -/
theorem wideScope_of_forall_not {P : W → Event T → Prop} {w : W} (hP : ∀ e, ¬ P w e) {t t' : T}
    (h : t < t') : wideScope P w t' :=
  ⟨⟨(t, t'), h.le⟩, h, rfl, λ _ _ e he => absurd he (hP e)⟩

/-- The run times of a description's events at a world. -/
def runTimes (P : W → Event T → Prop) (w : W) : RunTimes T := {i | ∃ e, P w e ∧ e.τ = i}

/-- Eventive UNTIL is Karttunen's *not until* together with the actualization his presupposition
supplies. -/
theorem eventiveUntil_iff (P : W → Event T → Prop) (w : W) (t : T) :
    eventiveUntil P w t ↔ notUntil (runTimes P w) {NonemptyInterval.pure t} ∧
      when_ (runTimes P w) {NonemptyInterval.pure t} := by
  constructor
  · rintro ⟨⟨e, he, ht⟩, hall⟩
    refine ⟨(notUntil_iff _ _).mpr λ s ⟨_, ⟨e', he', rfl⟩, hs⟩ =>
      ⟨t, ⟨_, rfl, NonemptyInterval.mem_pure_self t⟩,
        (hall e' he').trans (NonemptyInterval.mem_def.mp hs).1⟩,
      t, ⟨e.τ, ⟨e, he, rfl⟩, ht⟩, ⟨_, rfl, NonemptyInterval.mem_pure_self t⟩⟩
  · rintro ⟨hnu, s, ⟨_, ⟨e, he, rfl⟩, hs⟩, j, hj, hsj⟩
    obtain rfl := Set.mem_singleton_iff.mp hj
    rw [NonemptyInterval.mem_pure] at hsj
    subst hsj
    refine ⟨⟨e, he, hs⟩, λ e' he' => ?_⟩
    obtain ⟨t', ⟨j, hj, ht'⟩, hle⟩ := (notUntil_iff _ _).mp hnu e'.τ.fst
      ⟨e'.τ, ⟨e', he', rfl⟩, NonemptyInterval.mem_def.mpr ⟨le_rfl, e'.τ.fst_le_snd⟩⟩
    obtain rfl := Set.mem_singleton_iff.mp hj
    rw [NonemptyInterval.mem_pure] at ht'
    exact ht' ▸ hle

/-- Eventive UNTIL entails *not before*, one direction of Karttunen's equivalence. -/
theorem eventiveUntil_not_before {P : W → Event T → Prop} {w : W} {t : T}
    (h : eventiveUntil P w t) : ¬ before (runTimes P w) t :=
  λ ⟨_, ⟨_, ⟨e, he, rfl⟩, hs⟩, hlt⟩ =>
    absurd ((h.2 e he).trans (NonemptyInterval.mem_def.mp hs).1) (not_le.mpr hlt)

/-- *Not before* carries no actualization: it holds when nothing P-like ever happens. -/
theorem not_before_of_forall_not {P : W → Event T → Prop} {w : W} (hP : ∀ e, ¬ P w e) (t : T) :
    ¬ before (runTimes P w) t :=
  λ ⟨_, ⟨_, ⟨e, he, _⟩, _⟩, _⟩ => hP e he

/-! ### The paper's sentences -/

/-- The UNTIL words and *before* of the paper's four languages. -/
inductive Connective
  | until | mexri | paraMonon | prin | til | fyrrEn | tot | pas
  deriving DecidableEq, Repr

/-- The fragment entry of each connective. -/
def Connective.entry : Connective → English.TemporalExpressions.TemporalExprEntry
  | .until => English.TemporalExpressions.until_
  | .mexri => Greek.StandardModern.TemporalConnectives.mexri
  | .paraMonon => Greek.StandardModern.TemporalConnectives.paraMonon
  | .prin => Greek.StandardModern.TemporalConnectives.prin
  | .til => Icelandic.TemporalConnectives.flangaTil
  | .fyrrEn => Icelandic.TemporalConnectives.fyrrEn
  | .tot => Dutch.TemporalConnectives.tot
  | .pas => Dutch.TemporalConnectives.pas

/-- The polarity item a connective doubles as: English *until* in its eventive use. -/
def Connective.polarityItem : Connective → Option Polarity.Item
  | .until => some English.PolarityItems.until_
  | _ => none

/-- The paper's polarity classification of the eventive UNTIL words. -/
inductive Polarity
  | npi | ppi | neutral
  deriving DecidableEq, Repr

def Connective.polarity : Connective → Polarity
  | .until | .paraMonon | .fyrrEn => .npi
  | .pas => .ppi
  | .mexri | .prin | .til | .tot => .neutral

/-- Durative UNTIL: an *until*-ordered entry that does not force a punctual reading. -/
abbrev Connective.Durative (c : Connective) : Prop :=
  c.entry.order = .until_ ∧ c.entry.forcesPunctual = false

/-- Eventive UNTIL: a punctual entry, or an *until* with a polarity-item use. -/
abbrev Connective.Eventive (c : Connective) : Prop :=
  c.entry.forcesPunctual = true ∨ c.polarityItem.isSome = true

abbrev Connective.Before (c : Connective) : Prop := c.entry.order = .before

/-- The viewpoint of the main clause. -/
inductive AspectForm
  | imperfective | perfective | progressive | perfect | simplePast
  deriving DecidableEq, Repr

/-- States and activities against achievements and accomplishments. -/
inductive Eventuality
  | stative | eventive
  deriving DecidableEq, Repr

/-- What the sentence puts the connective under. -/
inductive Licenser
  | none | negation | without | nonveridical
  deriving DecidableEq, Repr

/-- Negation and *without*, the antiveridical licensers. -/
abbrev Licenser.Antiveridical (l : Licenser) : Prop := l = .negation ∨ l = .without

/-- What the sentence tests: acceptability, preposing of the UNTIL phrase, or a continuation
denying the event. -/
inductive Test
  | plain | preposed | noEventContinuation
  deriving DecidableEq, Repr

structure Row where
  connective : Connective
  aspect : AspectForm
  eventuality : Eventuality
  licenser : Licenser
  test : Test
  acceptable : Bool
  deriving DecidableEq, Repr

/-- A homogeneous main clause: an imperfective, progressive or perfect form, or a stative. -/
abbrev Homog (a : AspectForm) (e : Eventuality) : Prop :=
  a = .imperfective ∨ a = .progressive ∨ a = .perfect ∨ e = .stative

/-- The forms that admit the wide-scope reading: the imperfective and the perfect. -/
abbrev WideScopeForm (a : AspectForm) : Prop := a = .imperfective ∨ a = .perfect

/-- The licensing a connective's polarity demands. -/
abbrev Licensed (c : Connective) (l : Licenser) : Prop :=
  (c.polarity = .npi → l.Antiveridical) ∧ (c.polarity = .ppi → l = .none)

/-- The judgment the two-*until* analysis predicts. -/
def Predicted (r : Row) : Prop :=
  (r.test = .plain → (r.connective.Durative ∧ Homog r.aspect r.eventuality) ∨
    (r.connective.Eventive ∧ Licensed r.connective r.licenser) ∨ r.connective.Before) ∧
  (r.test = .preposed → r.connective.Durative ∧ WideScopeForm r.aspect) ∧
  (r.test = .noEventContinuation →
    (r.connective.Durative ∧ WideScopeForm r.aspect) ∨ r.connective.Before)

instance : DecidablePred Predicted := λ _ => by unfold Predicted; infer_instance

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let connective ← ex.parse? "connective" [("until", Connective.until), ("mexri", .mexri),
    ("paraMonon", .paraMonon), ("prin", .prin), ("til", .til), ("fyrrEn", .fyrrEn), ("tot", .tot),
    ("pas", .pas)]
  let aspect ← ex.parse? "aspect" [("imperfective", AspectForm.imperfective),
    ("perfective", .perfective), ("progressive", .progressive), ("perfect", .perfect),
    ("simplePast", .simplePast)]
  let eventuality ← ex.parse? "eventuality" [("stative", Eventuality.stative),
    ("eventive", .eventive)]
  let licenser ← ex.parse? "licenser" [("none", Licenser.none), ("negation", .negation),
    ("without", .without), ("nonveridical", .nonveridical)]
  let test ← ex.parse? "test" [("plain", Test.plain), ("preposed", .preposed),
    ("noEventContinuation", .noEventContinuation)]
  pure ⟨connective, aspect, eventuality, licenser, test, ex.judgment == .acceptable⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Every judgment on the UNTIL sentences follows from the connective's fragment entry, the
homogeneity of the main clause and the licensing of the polarity item. -/
theorem rows_predicted : ∀ r ∈ rows, (r.acceptable = true ↔ Predicted r) := by
  decide

/-- The stativity diagnostics of the fifth section. -/
inductive Diagnostic
  | howLong | while | forAdverbial | imperative
  deriving DecidableEq, Repr

structure DiagnosticRow where
  diagnostic : Diagnostic
  aspect : AspectForm
  eventuality : Eventuality
  licenser : Licenser
  acceptable : Bool
  deriving DecidableEq, Repr

def DiagnosticRow.ofExample (ex : LinguisticExample) : Option DiagnosticRow := do
  let diagnostic ← ex.parse? "diagnostic" [("howLong", Diagnostic.howLong), ("while", .while),
    ("forAdverbial", .forAdverbial), ("imperative", .imperative)]
  let aspect ← ex.parse? "aspect" [("imperfective", AspectForm.imperfective),
    ("perfective", .perfective), ("progressive", .progressive), ("perfect", .perfect),
    ("simplePast", .simplePast)]
  let eventuality ← ex.parse? "eventuality" [("stative", Eventuality.stative),
    ("eventive", .eventive)]
  let licenser ← ex.parse? "licenser" [("none", Licenser.none), ("negation", .negation),
    ("without", .without), ("nonveridical", .nonveridical)]
  pure ⟨diagnostic, aspect, eventuality, licenser, ex.judgment == .acceptable⟩

def diagnostics : List DiagnosticRow := Examples.all.filterMap DiagnosticRow.ofExample

/-- The stative diagnostics accept a homogeneous clause and the imperative rejects one, with
negation playing no role: negation is no stativizer. -/
theorem diagnostics_predicted : ∀ r ∈ diagnostics, (r.acceptable = true ↔
    ((r.diagnostic = .imperative → ¬ Homog r.aspect r.eventuality) ∧
      (r.diagnostic ≠ .imperative → Homog r.aspect r.eventuality))) := by
  decide

end Giannakidou2002
