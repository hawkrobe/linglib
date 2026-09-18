import Linglib.Semantics.Tense.Embedding
import Linglib.Data.Examples.Sharvit2003

/-!
# Sharvit (2003): Embedded Tense and Universal Grammar

This file formalizes the squib's typological argument. Under the Deletion Theory of
[ogihara-1996] and [von-stechow-1995], sequence of tense is a parameter: an SOT language deletes
an embedded tense under agreement with a c-commanding attitude tense, and the deleted tense is a
bound zero tense, the relative now of [heim-1994-comments], so past under past has a nonpast
reading beside its anteriority reading (`Tense.availableReadings`). A second parameter, matrix
indexicality after [schlenker-1999], is whether the present-tense morpheme must refer to the
utterance time in present-under-past sentences or may be interpreted as a bound variable. The
two cross to the typology (11): English deletes and has an indexical present, Hebrew neither
deletes nor has an indexical present, Modern Greek deletes and has a bindable present, and the
fourth type, no deletion and an indexical present, is unattested (`Language`). In such a language
*Mary is pregnant* could not be reported under an attitude verb at all. The Embeddability
Principle (13) is the principle of Universal Grammar that every well-formed matrix LF has a
content-matching λ0-abstract embeddable under an attitude verb; a language meets it by providing
a source of zero tense, a deleted tense or a bound present (`ZeroTense`, `Language.Provides`),
which is exactly what type 4 lacks (`embeddabilityPrinciple_iff`).

The readings follow from the tense-pronoun substrate. A bound present resolves to the attitude's
now, the nonpast reading of (5) and (12a) (`boundPresent_nonpast`); an indexical present
resolves to the utterance time, which a past attitude's now cannot match, so (3) keeps only the
double access reading (`indexicalPresent_no_nonpast`), and an interval too short to span the two
years of (4b) cannot give it (`not_doubleAccess_of_short`). The LF (7) of the nonpast reading of
(1), three λ0-abstracts rebinding one zero tense, denotes (10) under the entries (8) and (9)
(`lf7_iff`). The typology predicts the availability of the nonpast reading across the paper's
examples (1)–(6) and (12) (`nonpast_rows`).

## Implementation notes

* The semantic half of the Embeddability Principle (15), matching in content, is met by the
  λ0-abstract of the matrix LF itself; the principle's force is syntactic, that the language can
  spell out the abstract's free zero tense, and that is what `EmbeddabilityPrinciple` states.
* The classification of English, Hebrew and Modern Greek is the paper's and lives in the study,
  not in the Fragments. The person-domain extension of the principle and free indirect discourse
  (§3) are argued informally and are not formalized.

## References

* [sharvit-2003]
* [ogihara-1996]
* [von-stechow-1995]
* [heim-1994-comments]
* [schlenker-1999]
* [abusch-1997]
-/

namespace Sharvit2003

open Semantics

open Tense Data.Examples

variable {T : Type*}

/-! ### The typology (11) -/

/-- Whether a language's present-tense morpheme is a matrix indexical, obligatorily referring
to the utterance time in present-under-past sentences, or may be interpreted as a bound
variable. -/
inductive PresentTense
  | matrixIndexical | bindable
  deriving DecidableEq, Repr

/-- A language type of the Deletion Theory (11): the SOT rule, which deletes a tense under
agreement and interprets it as a bound zero tense, and the indexicality of the present. -/
structure Language where
  sot : SOTParameter
  present : PresentTense
  deriving DecidableEq, Repr

/-- Type 1, English: the SOT rule and a matrix-indexical present. -/
def english : Language := ⟨.relative, .matrixIndexical⟩

/-- Type 2, Hebrew: no SOT rule and a bindable present. -/
def hebrew : Language := ⟨.absolute, .bindable⟩

/-- Type 3, Modern Greek: the SOT rule and a bindable present. -/
def greek : Language := ⟨.relative, .bindable⟩

/-- Type 4, unattested: no SOT rule and a matrix-indexical present. -/
def type4 : Language := ⟨.absolute, .matrixIndexical⟩

/-! ### Zero tense and the Embeddability Principle -/

/-- The sources of a bound zero tense in a complement clause: a tense deleted under agreement
by the SOT rule, or a present morpheme interpreted as a bound variable. -/
inductive ZeroTense
  | deleted | boundPresent
  deriving DecidableEq, Repr, Fintype

/-- A language provides a source of zero tense: deletion needs the SOT rule, and a bound
present needs a present morpheme that is not a matrix indexical. -/
def Language.Provides (L : Language) : ZeroTense → Prop
  | .deleted => L.sot = .relative
  | .boundPresent => L.present = .bindable

instance (L : Language) : DecidablePred L.Provides
  | .deleted => inferInstanceAs (Decidable (L.sot = .relative))
  | .boundPresent => inferInstanceAs (Decidable (L.present = .bindable))

/-- The Embeddability Principle (13) as a condition on a language: some source of zero tense
is available, so that every well-formed matrix LF has a content-matching λ0-abstract that can
be embedded under an attitude verb carrying past or present. -/
def EmbeddabilityPrinciple (L : Language) : Prop := ∃ z, L.Provides z

instance (L : Language) : Decidable (EmbeddabilityPrinciple L) :=
  inferInstanceAs (Decidable (∃ z, L.Provides z))

/-- Exactly type 4 violates the Embeddability Principle. -/
theorem embeddabilityPrinciple_iff (L : Language) :
    EmbeddabilityPrinciple L ↔ L ≠ type4 := by
  obtain ⟨s, p⟩ := L
  cases s <;> cases p <;> decide

/-- English embeds *Mary is pregnant* by deleting a tense, Hebrew by binding its present, and
Modern Greek either way. -/
theorem attested_types :
    english.Provides .deleted ∧ hebrew.Provides .boundPresent ∧
      greek.Provides .deleted ∧ greek.Provides .boundPresent := by
  decide

/-! ### The readings

The nonpast reading of past under past is the simultaneous reading of a deleted tense; the
nonpast reading of present under past is the binding of the present morpheme. -/

/-- The morpheme embedded under the past attitude verb. -/
inductive Embedded
  | past | present
  deriving DecidableEq, Repr

/-- The nonpast reading is available for an embedded past exactly when the SOT rule licenses
the simultaneous reading (`Tense.availableReadings`), and for an embedded present exactly when
the present can be bound. -/
def NonpastAvailable (L : Language) : Embedded → Prop
  | .past => .simultaneous ∈ availableReadings L.sot
  | .present => L.Provides .boundPresent

instance (L : Language) : DecidablePred (NonpastAvailable L)
  | .past => inferInstanceAs (Decidable (_ ∈ _))
  | .present => inferInstanceAs (Decidable (L.Provides .boundPresent))

/-- The simultaneous reading of a deleted tense is available exactly in languages with the SOT
rule: the two parameters of the typology are the two sources of zero tense. -/
theorem nonpastAvailable_past_iff (L : Language) :
    NonpastAvailable L .past ↔ L.Provides .deleted := by
  obtain ⟨s, p⟩ := L
  cases s <;> cases p <;> decide

/-- The present morpheme of a complement clause as a tense pronoun: variable `n` under the
present constraint, in the mode the language admits, evaluated at the attitude's now, slot
`e`. -/
def embeddedPresent (n e : ℕ) (mode : ReferentialMode) : TensePronoun :=
  ⟨n, ⟦Tense.present⟧, mode, e⟩

/-- A bindable present bound by the attitude verb resolves to the attitude's now, so it is
present relative to the embedded perspective: the nonpast reading of (5) and (12a). -/
theorem boundPresent_nonpast (n e : ℕ) (g : TemporalAssignment T) (speech now event : T) :
    ((embeddedPresent n e .bound).toFrame (updateTemporal g n now) speech now event).isPresent :=
  TensePronoun.bound_present_simultaneous _ _ _ _ _
    (TensePronoun.bound_resolve_eq_binder _ g now) rfl

/-- A matrix-indexical present under a past attitude verb refers to the utterance time, which
the attitude's earlier now cannot match, so the present constraint fails relative to the
embedded perspective: (3) has no nonpast reading, only the double access reading. -/
theorem indexicalPresent_no_nonpast [LinearOrder T] (tp : TensePronoun)
    (hPres : tp.constraint = ⟦Tense.present⟧) {resolved speech now : T}
    (hSpeech : tp.presupposition resolved speech) (hlt : now < speech) :
    ¬ tp.presupposition resolved now := by
  obtain rfl := TensePronoun.indexical_present_at_speech tp resolved speech hPres hSpeech
  simp [TensePronoun.presupposition, hPres, hlt.ne']

/-- The double access reading of (4b) needs the pregnancy interval to contain both the finding
out and the utterance time; an interval too short to span the two years between them cannot,
hence the oddity. -/
theorem not_doubleAccess_of_short [Sub T] [Preorder T] {I : Set T} {b u : T}
    (h : ∀ x ∈ I, ∀ y ∈ I, y - x < u - b) : ¬ DoubleAccess I b u :=
  λ ⟨hb, hu⟩ => lt_irrefl _ (h b hb u hu)

/-! ### The nonpast reading of (1) under the Deletion Theory -/

/-- The entry (8) for *decide* and *tell*: the complement holds at every time compatible with
what the holder decides or tells at `t`. -/
def attitude (compatible : T → Set T) (p : T → Prop) (t : T) : Prop :=
  ∀ t' ∈ compatible t, p t'

/-- The entry (9) for *will*: the complement holds at some later time. -/
def will [LT T] (p : T → Prop) (t : T) : Prop := ∃ t', t < t' ∧ p t'

/-- The LF (7) of the nonpast reading of (1): the matrix past locates the deciding before the
utterance time, slot `0` of the assignment, and each complement is a λ0-abstract that rebinds
the zero tense read by the deleted past on *will*, the base-generated zero tense on *tell* and
the deleted past on *miss*. -/
def lf7 [LT T] (decides tells : T → Set T) (miss : T → Prop) (g : TemporalAssignment T) :
    Prop :=
  ∃ t, t < interpTense 0 g ∧
    attitude decides
      (temporalLambdaAbs 0 (λ g₁ =>
        will
          (temporalLambdaAbs 0 (λ g₂ =>
            attitude tells (temporalLambdaAbs 0 (λ g₃ => miss (interpTense 0 g₃)) g₂)
              (interpTense 0 g₂)) g₁)
          (interpTense 0 g₁)) g) t

/-- The interpretation (10): for every time compatible with what John decides at some time
before the utterance time there is a later time at which he tells his mother, and he misses
her at every time compatible with that telling. -/
theorem lf7_iff [LT T] (decides tells : T → Set T) (miss : T → Prop)
    (g : TemporalAssignment T) :
    lf7 decides tells miss g ↔
      ∃ t, t < g 0 ∧ ∀ t' ∈ decides t, ∃ t'', t' < t'' ∧ ∀ t''' ∈ tells t'', miss t''' := by
  simp only [lf7, attitude, will, temporalLambdaAbs, interpTense, Function.update_self]

/-! ### The paper's examples -/

/-- A row of the paper's data: the language, the embedded morpheme, and whether the nonpast
reading is available. -/
structure Row where
  language : Language
  embedded : Embedded
  nonpast : Bool
  deriving DecidableEq, Repr

/-- Read a row off an example's paper features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let language ← match e.paperFeatures.lookup "language" with
    | some "english" => some english
    | some "hebrew" => some hebrew
    | some "greek" => some greek
    | _ => none
  let embedded ← match e.paperFeatures.lookup "embedded" with
    | some "past" => some .past
    | some "present" => some .present
    | _ => none
  let nonpast ← match e.paperFeatures.lookup "nonpast" with
    | some "yes" => some true
    | some "no" => some false
    | _ => none
  pure ⟨language, embedded, nonpast⟩

/-- The rows of (1)–(6) and (12). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Every example carries the three features. -/
theorem rows_complete : ∀ e ∈ Examples.all, (Row.ofExample e).isSome = true := by decide

/-- The typology (11) predicts the paper's judgments: the nonpast reading is available exactly
where the language provides a zero tense for the embedded morpheme. -/
theorem nonpast_rows :
    ∀ r ∈ rows, r.nonpast = true ↔ NonpastAvailable r.language r.embedded := by
  decide

end Sharvit2003
