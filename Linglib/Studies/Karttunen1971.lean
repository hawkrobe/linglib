import Linglib.Semantics.Causation.VerbClass
import Linglib.Semantics.Presupposition.Basic

/-!
# Karttunen (1971): implicative verbs

[karttunen-1971] identifies a class of complement-taking verbs — *manage*, *remember*,
*bother*, *dare*, *happen*, … (his (2)) — whose assertion commits the speaker to the
complement and whose negation commits the speaker to its negation, and analyzes such a
sentence as a presupposition–proposition pair: the proposition `v(S)` is what is asserted,
negated, or questioned, and the presupposition says what condition `v(S)` is for the
complement `S`. Schema (37) makes `v(S)` necessary and sufficient for `S` (*manage*); (41)
necessary and sufficient for `¬S` (*fail*, *forget*); (54) necessary only (*be able*, *be
possible*); (59) sufficient only (*force*, *cause*); non-implicatives (*hope*, *want*,
*try*) carry no such presupposition and are plain `PartialProp.ofProp`. `Condition` is the
presupposed condition, `Schema` pairs it with the polarity of the complement, and
`Schema.sentence` is the presupposition–proposition pair as a `PartialProp`. The paper's
entailment facts follow: an affirmative assertion entails the (polarity-adjusted)
complement when the condition is sufficient (`holds_imp`), a negated one entails its
negation when the condition is necessary (`neg_holds_imp`), double negation cancels, his
(13) (`manage_neg_neg_holds_imp`), and the one-way cells and the non-implicatives leave the
other direction open (`force_neg_not_entails`, `beAble_not_entails`,
`ofProp_not_entails`).
-/

namespace Karttunen1971

open Semantics.Presupposition (PartialProp)

/-- The condition `v(S)` is presupposed to be for the complement. -/
inductive Condition where
  /-- (59): *force*, *cause*, *make*. -/
  | sufficient
  /-- (54): *be able*, *be possible*. -/
  | necessary
  /-- (37) and (41): *manage*, *fail*. -/
  | necessaryAndSufficient
  deriving DecidableEq, Repr

namespace Condition

/-- The presupposition: `v` stands in the condition to `S`. -/
def presup : Condition → Prop → Prop → Prop
  | .sufficient, v, S => v → S
  | .necessary, v, S => S → v
  | .necessaryAndSufficient, v, S => v ↔ S

/-- The condition is at least sufficient. -/
def IsSufficient : Condition → Prop
  | .necessary => False
  | _ => True

/-- The condition is at least necessary. -/
def IsNecessary : Condition → Prop
  | .sufficient => False
  | _ => True

variable {v S : Prop}

theorem presup_imp : ∀ {c : Condition}, c.IsSufficient → c.presup v S → v → S
  | .sufficient, _, h => h
  | .necessaryAndSufficient, _, h => h.1

theorem presup_imp_rev : ∀ {c : Condition}, c.IsNecessary → c.presup v S → S → v
  | .necessary, _, h => h
  | .necessaryAndSufficient, _, h => h.2

end Condition

/-- The presupposition–proposition schema of an implicative verb: the condition `v(S)` is
presupposed to be, and whether the complement in question is `S` (*manage*) or `¬S`
(*fail*). -/
structure Schema where
  condition : Condition
  polarity : Implicative
  deriving DecidableEq, Repr

namespace Schema

/-- (37): *manage*, *remember*, *bother*. -/
def manage : Schema := ⟨.necessaryAndSufficient, .positive⟩

/-- (41): *fail*, *forget*, *neglect*. -/
def fail : Schema := ⟨.necessaryAndSufficient, .negative⟩

/-- (59): *force*, *cause*, *make*. -/
def force : Schema := ⟨.sufficient, .positive⟩

/-- (59) for the negated complement: *prevent*. -/
def prevent : Schema := ⟨.sufficient, .negative⟩

/-- (54): *be able*, *be possible*. -/
def beAble : Schema := ⟨.necessary, .positive⟩

variable (k : Schema)

/-- The two-way implicatives of (37) and (41). -/
def TwoWay : Prop := k.condition = .necessaryAndSufficient

instance : Decidable k.TwoWay := inferInstanceAs (Decidable (_ = _))

/-- The complement the schema speaks of: `S` or `¬S` by polarity. -/
def implied (S : Prop) : Prop :=
  match k.polarity with
  | .positive => S
  | .negative => ¬ S

variable {W : Type*} (v S : W → Prop) (w : W)

/-- The sentence `v(S)`: the schema's presupposition, and `v` as the proposition. -/
def sentence : PartialProp W := ⟨fun w => k.condition.presup (v w) (k.implied (S w)), v⟩

/-- An affirmative assertion commits the speaker to the complement when `v(S)` is
presupposed sufficient. -/
theorem holds_imp (h : k.condition.IsSufficient) (hs : (k.sentence v S).holds w) :
    k.implied (S w) :=
  Condition.presup_imp h hs.1 hs.2

/-- A negated assertion commits the speaker to the negation of the complement when `v(S)`
is presupposed necessary. -/
theorem neg_holds_imp (h : k.condition.IsNecessary)
    (hs : (PartialProp.neg (k.sentence v S)).holds w) : ¬ k.implied (S w) :=
  fun hS => hs.2 (Condition.presup_imp_rev h hs.1 hS)

/-- Double negation cancels, (13): `John didn't remember not to lock his door` commits the
speaker to `John locked his door`. -/
theorem manage_neg_neg_holds_imp
    (hs : (PartialProp.neg (manage.sentence v fun w => ¬ S w)).holds w) : S w :=
  not_not.mp (neg_holds_imp manage v _ w trivial hs)

/-- (58): `John didn't force Mary to stay home` leaves open whether she stayed. -/
theorem force_neg_not_entails :
    ∃ (v S : Unit → Prop), (PartialProp.neg (force.sentence v S)).holds () ∧ S () :=
  ⟨fun _ => False, fun _ => True, ⟨fun _ => trivial, id⟩, trivial⟩

/-- (55): `John was able to come` leaves open whether he came. -/
theorem beAble_not_entails :
    ∃ (v S : Unit → Prop), (beAble.sentence v S).holds () ∧ ¬ S () :=
  ⟨fun _ => True, fun _ => False, ⟨fun h => h.elim, trivial⟩, id⟩

end Schema

/-- (5): a non-implicative, which has no presupposition, commits the speaker to nothing
about its complement in either polarity. -/
theorem ofProp_not_entails :
    (∃ (v S : Unit → Prop), (PartialProp.ofProp v).holds () ∧ ¬ S ()) ∧
      ∃ (v S : Unit → Prop), (PartialProp.neg (PartialProp.ofProp v)).holds () ∧ S () :=
  ⟨⟨fun _ => True, fun _ => False, ⟨trivial, trivial⟩, id⟩,
   ⟨fun _ => False, fun _ => True, ⟨trivial, id⟩, trivial⟩⟩

end Karttunen1971
