module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Studies.BeaverCondoravdi2003
public import Linglib.Semantics.Tense.Embedding

/-!
# Sharvit (2014): On the universal principles of tense embedding

Sharvit makes the distinction between pronominal tenses, after Partee, and quantificational
ones, after Prior, the source of cross-linguistic variation in *before*-clauses and attitude
reports. Under Beaver and Condoravdi's semantics of *before*, a quantificational past in a
*before*-clause makes the definedness condition of EARLIEST fail, while a pronominal past does
not. With the sequence-of-tense rule and the shiftability of the present this yields a typology
of languages and three universal predictions, checked here on English, Polish and Japanese.

## Main definitions

* `quantificationalPast`: the quantificational past.
* `pronominalLookup`: the pronominal past.
* `Shiftability`: the shiftability of the present tense.
* `LanguageTenseProfile`: a language's three tense parameters.

## Main results

* `ipf_quantificationalPast`: a quantificational past in a *before*-clause fails EARLIEST.
* `pastUnderBefore_wellFormed_iff`: a past is well-formed under *before* iff it is pronominal.
* `eq99a_pres_under_past_before_implies_shiftable`: the first universal prediction.
* `eq99b_before_and_embedded_pshift_imply_simultaneous`: the second universal prediction.
* `eq99c_before_and_no_simultaneous_imply_no_bare_pshift`: the third universal prediction.

## Implementation notes

* The typology covers English, Polish and Japanese. Modern Greek and the two Spanish varieties
  need a mood parameter, and one of them a mixed past-present lexical type the profile cannot
  represent; tenseless languages are outside the no-tenseless assumption.
* Japanese's quantificational past follows Ogihara, against relative-tense alternatives, and
  Polish's semi-shiftable present follows Sharvit, against Grønn and von Stechow's appeal to
  Aktionsart.

## References

* [sharvit-2014]
* [ogihara-sharvit-2012]
* [sharvit-2003]
* [beaver-condoravdi-2003]
* [partee-1973]
* [ogihara-1996]
-/

@[expose] public section

namespace Sharvit2014

open Semantics


/-- The `EARLIEST` presupposition of `before^{B&C}` holds of the body `p` when the set of
`C`-times at which `p` holds has a least element. -/
def hasEarliest {T : Type*} [LinearOrder T] (C : Set T) (p : T → Prop) : Prop :=
  ∃ t, IsLeast {t' | t' ∈ C ∧ p t'} t

/-- [beaver-condoravdi-2003]'s `earliest` is defined exactly when the `EARLIEST`
    presupposition holds of the instantiation times, with trivial restrictor. -/
theorem earliestAlt_nonempty_iff_hasEarliest {W T : Type*} [LinearOrder T]
    (alt : HistoricalAlternatives W T) (B : Set (W × T)) (w : W) (t : T) :
    (BeaverCondoravdi2003.earliestAlt alt B w t).Nonempty ↔
      hasEarliest Set.univ (· ∈ BeaverCondoravdi2003.instTimes (alt ⟨w, t⟩) B) := by
  unfold hasEarliest
  simp only [Set.Nonempty, BeaverCondoravdi2003.earliestAlt, Set.mem_ofPred_eq, Set.mem_univ,
    true_and, Set.ofPred_mem_eq]

/-! ### The two lexical types of tense ((30)) -/

/-- A tense is of one of Sharvit's two semantic types, (30) on p. 274, pronominal or
quantificational. -/
inductive LexicalType
  /-- A pronominal tense is an element of `D_i`, the two-indexed `past_{j,k}`. -/
  | pronominal
  /-- A quantificational tense is a Priorean operator over predicates of times. -/
  | quantificational
  deriving DecidableEq, Repr

/-- The quantificational past, (30b), is the generalized quantifier `some` over the contextual
restrictor `K` with the scope "precedes `t` and satisfies `p`". -/
def quantificationalPast {T : Type*} [LT T]
    (K : Set T) (p : T → Prop) (t : T) : Prop :=
  Quantifier.GQ.some (· ∈ K) (fun t' => t' < t ∧ p t')

/-- When the body of `before^{B&C}` is the quantificational past and the restrictor `C` is
dense with `K ⊆ C`, the `EARLIEST` presupposition fails, since by density any witness lifts to
a smaller one, (27) on p. 272. -/
theorem ipf_quantificationalPast {T : Type*} [LinearOrder T]
    {C K : Set T}
    (hK : K ⊆ C)
    (hC_dense : ∀ a b, a ∈ C → b ∈ C → a < b → ∃ c ∈ C, a < c ∧ c < b)
    (q : T → Prop) :
    ¬ hasEarliest C (quantificationalPast K q) := by
  rintro ⟨t_min, ⟨ht_min_C, t_q, ht_q_K, ht_q_lt, hq_t_q⟩, hmin⟩
  obtain ⟨t_mid, ht_mid_C, ht_q_lt_mid, ht_mid_lt_min⟩ :=
    hC_dense t_q t_min (hK ht_q_K) ht_min_C ht_q_lt
  exact absurd (hmin ⟨ht_mid_C, t_q, ht_q_K, ht_q_lt_mid, hq_t_q⟩)
    (not_le.mpr ht_mid_lt_min)

/-- `triggersIPFInBefore l` says whether a tense of type `l` triggers IPF in a *before*-clause;
quantificational tenses do and pronominal ones do not. -/
def triggersIPFInBefore : LexicalType → Bool
  | .quantificational => true
  | .pronominal       => false

/-- A past tense is well-formed under `before^{B&C}` iff its type does not trigger IPF, that is,
iff it is pronominal, (27) on p. 272. -/
@[simp] theorem pastUnderBefore_wellFormed_iff (τ : LexicalType) :
    triggersIPFInBefore τ = false ↔ τ = .pronominal := by
  cases τ <;> simp [triggersIPFInBefore]

/-! ### The pronominal past ((30a))

The pronominal-past lookup and its grounding in the codebase's canonical
tense pronoun: `pronominalLookup` is the presupposition-gated referent of a
past-constraint `TensePronoun`, so [sharvit-2014]'s (30a) and
[partee-1973]'s tense-pronoun carrier coincide
(`pronominalLookup_eq_some_iff_tensePronoun`). -/

/-- The pronominal past `[[past_{j,k}]]^g`, (30a), with evaluation index `j` and referential index
`k`, is defined iff `g k < g j`, and then denotes `g k`. -/
def pronominalLookup {T : Type*} [LT T] [DecidableLT T]
    (g : ℕ → T) (j k : ℕ) : Option T :=
  if g k < g j then some (g k) else none

/-- The pronominal past denotes the referential index when defined. -/
@[simp]
theorem pronominalLookup_eq_some_iff {T : Type*} [LT T]
    [DecidableLT T] (g : ℕ → T) (j k : ℕ) (t : T) :
    pronominalLookup g j k = some t ↔ g k < g j ∧ g k = t := by
  unfold pronominalLookup; split <;> simp_all

/-- The pronominal past is undefined exactly when the constraint fails. -/
@[simp]
theorem pronominalLookup_eq_none_iff {T : Type*} [LT T]
    [DecidableLT T] (g : ℕ → T) (j k : ℕ) :
    pronominalLookup g j k = none ↔ ¬ g k < g j := by
  unfold pronominalLookup; split <;> simp_all

/-- The pronominal past (30a) is defined with value `t` iff the past `TensePronoun` with
referential index `k` and evaluation index `j` satisfies its presupposition and resolves to
`t`, for any binding mode. -/
theorem pronominalLookup_eq_some_iff_tensePronoun {T : Type*} [LinearOrder T]
    (g : Tense.TemporalAssignment T) (j k : ℕ) (t : T)
    (mode : Tense.ReferentialMode) :
    pronominalLookup g j k = some t ↔
      (Tense.TensePronoun.mk k ⟦Tense.past⟧ mode j).fullPresupposition g ∧
      (Tense.TensePronoun.mk k ⟦Tense.past⟧ mode j).resolve g = t := by
  simp only [Tense.TensePronoun.fullPresupposition, Tense.TensePronoun.resolve,
    Tense.TensePronoun.evalTime, Tense.interpTense, Tense.compare_mem_past]
  exact pronominalLookup_eq_some_iff g j k t

/-! ### The parameter space ((98)) -/

/-- The shiftability of the present tense, (71) and (78) on pp. 288–291, is full in Japanese,
partial in Polish, whose present is bindable but not by the binder of its referential index, and
absent in English. -/
inductive Shiftability
  /-- The present is free and cannot be bound, as in English. -/
  | nonShiftable
  /-- The present is bindable, but not by the binder of its referential index, as in Polish. -/
  | semiShiftable
  /-- The present is freely bindable, as in Japanese. -/
  | fullyShiftable
  deriving DecidableEq, Repr

/-- A language's tense profile, (98) on p. 300, records whether it has the SOT rule, the
shiftability of its present, and the type of its past, of which there is at most one. -/
structure LanguageTenseProfile where
  /-- Whether the language has the SOT rule, deleting an agreeing embedded tense. -/
  hasSOT : Bool
  /-- The shiftability of the present tense. -/
  presentShiftability : Shiftability
  /-- The type of the past tense, or `none` for a tenseless language. -/
  pastLexicalType : Option LexicalType
  deriving DecidableEq, Repr

namespace LanguageTenseProfile

/-- A language has tenses when its past has a type. -/
def hasTenses (L : LanguageTenseProfile) : Bool := L.pastLexicalType.isSome

/-- A language's past is pronominal. -/
def isPronominal (L : LanguageTenseProfile) : Bool := L.pastLexicalType == some .pronominal

/-- A language's past is quantificational. -/
def isQuantificational (L : LanguageTenseProfile) : Bool :=
  L.pastLexicalType == some .quantificational

/-- A language's present is shiftable when it can be bound at all, which suffices to host a
"now"-thought in attitudes. -/
def hasShiftablePresent (L : LanguageTenseProfile) : Bool :=
  L.presentShiftability != .nonShiftable

/-- A language's present is fully shiftable when it is freely bindable, the condition for a
well-formed present-under-past *before*-clause, (78) on p. 291. -/
def hasFullyShiftablePresent (L : LanguageTenseProfile) : Bool :=
  L.presentShiftability == .fullyShiftable

/-! ### Derived empirical predicates

These are not independent stipulations: the *before*-well-formedness predicate routes through the
IPF dispatch `triggersIPFInBefore`, and deletion of a past under an agreeing past applies just in
case the language has the SOT rule. -/

/-- PAST-under-PAST in *before* is well-formed iff the past does not trigger IPF. -/
def wellFormedPastUnderPastBefore (L : LanguageTenseProfile) : Bool :=
  match L.pastLexicalType with
  | some τ => !triggersIPFInBefore τ
  | none   => false

/-- PRES-under-PAST in *before* is well-formed iff the present is fully shiftable, the Stump
effect, which rules out English and Polish, (78) on p. 291. -/
def wellFormedPresentUnderPastBefore (L : LanguageTenseProfile) : Bool :=
  L.hasFullyShiftablePresent

/-- The simultaneous reading of past-under-past in attitude reports, (59b) on p. 284, needs a
pronominal past and the SOT rule; Japanese's present-tense simultaneous reading is a different
mechanism. -/
def simultaneousAttitudeReading (L : LanguageTenseProfile) : Bool :=
  L.isPronominal && L.hasSOT

/-- A bare *before*-clause is p-shiftable, its past referring to a future time, when the past is
quantificational, (51) on p. 281. -/
def pShiftabilityBare (L : LanguageTenseProfile) : Bool := L.isQuantificational

/-- An embedded *before*-clause is p-shiftable under a matrix attitude verb when the past is
quantificational or the SOT rule deletes the matrix past, (66)–(68) on p. 287, for many
speakers. -/
def pShiftabilityEmbedded (L : LanguageTenseProfile) : Bool :=
  L.isQuantificational || (L.isPronominal && L.hasSOT)

/-- A language respects the Embeddability Principle, restated on p. 299, when it has some
mechanism for embedding a "now"-thought, the SOT rule, a shiftable present, or a quantificational
past. -/
def respectsEmbeddability (L : LanguageTenseProfile) : Bool :=
  L.hasSOT || L.hasShiftablePresent || L.isQuantificational

/-- A pronominal past is not quantificational. -/
theorem isQuantificational_eq_false_of_isPronominal (L : LanguageTenseProfile) :
    L.isPronominal = true → L.isQuantificational = false := by
  intro h
  have : L.pastLexicalType = some .pronominal := by
    simpa [isPronominal] using h
  simp [isQuantificational, this]

/-- Past-under-past in *before* is well-formed iff the past is pronominal. -/
theorem wellFormedPastUnderPastBefore_iff_pronominal (L : LanguageTenseProfile) :
    L.wellFormedPastUnderPastBefore = true ↔ L.isPronominal = true := by
  cases hτ : L.pastLexicalType with
  | none => simp [wellFormedPastUnderPastBefore, isPronominal, hτ]
  | some τ => cases τ <;> simp [wellFormedPastUnderPastBefore, isPronominal, triggersIPFInBefore, hτ]

end LanguageTenseProfile

/-! ### Attested language types ((98), p. 300) -/

/-- English, type 6 of (98), has the SOT rule, a non-shiftable present and a pronominal past. -/
def english : LanguageTenseProfile where
  hasSOT := true
  presentShiftability := .nonShiftable
  pastLexicalType := some .pronominal

/-- Polish, type 10 of (98), has no SOT rule, a semi-shiftable present and a pronominal past, so
its present-under-past *before*-clauses are ill-formed as in English. -/
def polish : LanguageTenseProfile where
  hasSOT := false
  presentShiftability := .semiShiftable
  pastLexicalType := some .pronominal

/-- Japanese, type 11 of (98), has no SOT rule, a fully shiftable present and a quantificational
past. -/
def japanese : LanguageTenseProfile where
  hasSOT := false
  presentShiftability := .fullyShiftable
  pastLexicalType := some .quantificational

/-- `attestedTypes` lists the attested language types of Sharvit's table (98). -/
def attestedTypes : List LanguageTenseProfile := [english, polish, japanese]

/-! ### Structural constraints (§6.1) -/

/-- Every attested language has tenses. -/
theorem all_attested_have_tenses : ∀ L ∈ attestedTypes, L.hasTenses = true := by decide

/-- Every attested language respects the Embeddability Principle. -/
theorem all_attested_respect_embeddability :
    ∀ L ∈ attestedTypes, L.respectsEmbeddability = true := by decide

/-! ### Cross-linguistic predictions ((99), p. 301)

Stated and proved over *all* profiles, not the three attested rows: each prediction follows
structurally from the parameter definitions and the substrate grounding. -/

/-- A well-formed present-under-past in *before* implies a shiftable present, (99a). -/
theorem eq99a_pres_under_past_before_implies_shiftable (L : LanguageTenseProfile) :
    L.wellFormedPresentUnderPastBefore = true → L.hasShiftablePresent = true := by
  cases hs : L.presentShiftability <;>
    simp [LanguageTenseProfile.wellFormedPresentUnderPastBefore,
      LanguageTenseProfile.hasFullyShiftablePresent, LanguageTenseProfile.hasShiftablePresent, hs]

/-- A well-formed PAST-under-PAST in *before* with embedded p-shiftability implies a simultaneous
reading of past-under-past in attitudes, (99b). -/
theorem eq99b_before_and_embedded_pshift_imply_simultaneous (L : LanguageTenseProfile) :
    L.wellFormedPastUnderPastBefore = true → L.pShiftabilityEmbedded = true →
      L.simultaneousAttitudeReading = true := by
  intro hwf hemb
  have hpron : L.isPronominal = true :=
    (LanguageTenseProfile.wellFormedPastUnderPastBefore_iff_pronominal L).mp hwf
  have hquant : L.isQuantificational = false :=
    LanguageTenseProfile.isQuantificational_eq_false_of_isPronominal L hpron
  simp only [LanguageTenseProfile.pShiftabilityEmbedded, hquant, hpron, Bool.false_or,
    Bool.true_and] at hemb
  simp only [LanguageTenseProfile.simultaneousAttitudeReading, hpron, Bool.true_and]
  exact hemb

/-- A well-formed PAST-under-PAST in *before* without a simultaneous reading implies that bare
past-under-past *before* is not p-shiftable, (99c). The consequent already follows from
well-formedness, so the second antecedent is idle in this encoding. -/
theorem eq99c_before_and_no_simultaneous_imply_no_bare_pshift (L : LanguageTenseProfile) :
    L.wellFormedPastUnderPastBefore = true → L.simultaneousAttitudeReading = false →
      L.pShiftabilityBare = false := by
  intro hwf _hNoSim
  have hpron : L.isPronominal = true :=
    (LanguageTenseProfile.wellFormedPastUnderPastBefore_iff_pronominal L).mp hwf
  exact LanguageTenseProfile.isQuantificational_eq_false_of_isPronominal L hpron

/-! ### Substrate connection: IPF and quantificational past

The `wellFormedPastUnderPastBefore` predicate is grounded in the [beaver-condoravdi-2003] IPF
result formalized via `hasEarliest`; the two theorems below consume that
grounding via `wellFormedPastUnderPastBefore_iff_pronominal`. -/

/-- In a language with a quantificational past, such as Japanese, past-under-past in *before* is
ill-formed. -/
theorem quant_past_languages_fail_before (L : LanguageTenseProfile) :
    L.isQuantificational = true → L.wellFormedPastUnderPastBefore = false := by
  intro h
  have : L.pastLexicalType = some .quantificational := by
    simpa [LanguageTenseProfile.isQuantificational] using h
  simp [LanguageTenseProfile.wellFormedPastUnderPastBefore, this, triggersIPFInBefore]

/-- In English and Polish, whose past is pronominal, past-under-past in *before* is
well-formed. -/
theorem pronominal_past_languages_pass_before (L : LanguageTenseProfile) :
    L.isPronominal = true → L.wellFormedPastUnderPastBefore = true :=
  fun h => (LanguageTenseProfile.wellFormedPastUnderPastBefore_iff_pronominal L).mpr h

/-! ### Per-language payload

The central typological contrast — and a regression guard on the three-valued shiftability: a
binary `shiftablePresent` would wrongly make Polish's present-under-past in *before* well-formed. -/

example : japanese.pShiftabilityBare = true := rfl
example : english.pShiftabilityBare = false := rfl
example : polish.wellFormedPresentUnderPastBefore = false := rfl
example : japanese.wellFormedPresentUnderPastBefore = true := rfl

/-! ### The simultaneous reading

The Sharvit ↔ [klecha-2016] comparison (same simultaneous-reading prediction, different
mechanisms) lives in the later paper's study file, `Studies/Klecha2016.lean §F1`. -/

/-- In English the SOT rule and the pronominal past yield the simultaneous reading of
past-under-past in attitudes. -/
theorem english_predicts_simultaneous : english.simultaneousAttitudeReading = true := rfl

end Sharvit2014
