import Linglib.Data.Examples.Egressy2026
import Linglib.Fragments.Hungarian.Predicates
import Linglib.Semantics.Tense.Embedding
import Linglib.Syntax.Minimalist.Probe.Profile

/-!
# Egressy (2026): Size-Sensitive Sequence of Tense in Hungarian

This file formalizes [egressy-2026]'s account of a split among Hungarian past-under-past
clauses: a non-speech-reporting clause (perception, dreaming, thought, belief, a reason adjunct)
has the simultaneous reading, like an English complement, while a speech-reporting clause, one
encoding the content of a verbal or other sign, is backshifted only, like a Japanese one. The
split is clause-internal, since one verb embeds either type. Non-speech-reporting clauses are
bare TPs and speech-reporting clauses SayPs with Say > Foc > T, Hungarian having no CP; the
Sequence of Tense Rule of [ogihara-1996] deletes an embedded PAST under Agree with a matrix
PAST, and that Agree obeys the Williams Cycle of [williams-2003]: a dependency headed at T cannot
search a projection above T in the functional sequence. It therefore crosses a TP and is blocked
by a SayP, just as focus movement to Spec,FocP escapes a TP but not a SayP and raising to Spec,TP
crosses a TP but not a CP. The Williams Cycle in Agree is derived from size-dependent adjunction:
an embedded clause adjoins to the matrix projection of its own size, so only a clause no larger
than TP lies inside a projection of the matrix PAST. The same derivation gives the
multiple-embedding data, where only structurally adjacent clauses interact, and locates the
size-insensitive Sequence of Tense of English in its CP complements sitting inside the VP.

## Implementation notes

* Clause size is `Minimalist.ComplementSize` on the shared functional sequence `fValue`, where
  `Cat.Say` sits at Say > Foc > T. The Williams Cycle (26) and its version for Agree (35) are one
  relation, `WilliamsCycle x y`, between the head of a dependency and the crossed projection.
* Readings are `Tense.EmbeddedTenseReading`. The two clause types realize the two values of
  [ogihara-sharvit-2012]'s language-wide `Tense.SOTParameter` clause-internally, so `readings`
  is `Tense.availableReadings` at the clause-internal parameter, and a chain of embeddings is
  read pairwise by `profile`.
* The examples are `Data.Examples.Egressy2026`. A row's clause type is its `clauseType`
  feature, its matrix verb the `Hungarian.Predicates` entry named by its `matrixVerb` feature,
  and direct perception, which the paper says removes the backshifted reading pragmatically, its
  `directPerception` feature.
* Footnote 9 allows the complement of *mond* to be an XP with Say > Foc > X > T, which movement
  to Spec,FocP escapes but Agree from T does not; the shared sequence has no such head, so those
  complements are SayPs here.

## References

* [egressy-2026]
* [egressy-2025]
* [williams-2003]
* [keine-2019]
* [keine-2020]
* [ogihara-1996]
* [ogihara-sharvit-2012]
* [sharvit-2020]
* [kiss-2023]
* [abusch-1988]
* [heim-1994-comments]
-/

namespace Egressy2026

open Minimalist Tense Data.Examples Hungarian.Predicates Egressy2026.Examples

/-! ### The two clause types and their size (§2, §3.1) -/

/-- Whether an embedded clause encodes the content of a verbal or other sign (§2.2): a property
of the clause, not of the matrix predicate, which may embed either type. -/
inductive ClauseType
  | nonSpeechReporting
  | speechReporting
  deriving DecidableEq, Repr, Fintype

/-- (21)–(22): a non-speech-reporting clause is a bare TP, a speech-reporting clause a SayP. -/
def ClauseType.size : ClauseType → ComplementSize
  | .nonSpeechReporting => .tP
  | .speechReporting => .sayP

/-- Speech-reporting clauses are the larger ones (§3.1). -/
theorem size_nonSpeech_lt_speech :
    ClauseType.nonSpeechReporting.size.fLevel < ClauseType.speechReporting.size.fLevel := by
  decide

/-! ### The Williams Cycle (26) and the Williams Cycle in Agree (35) -/

/-- A dependency headed at `x`, movement to Spec,XP or Agree from X or XP, may cross or search
a projection of `y` unless Y is above X in the functional sequence. -/
def WilliamsCycle (x y : Cat) : Prop := fValue y ≤ fValue x

instance (x y : Cat) : Decidable (WilliamsCycle x y) := inferInstanceAs (Decidable (_ ≤ _))

/-- A projection of the dependency's own category is crossed. -/
theorem WilliamsCycle.refl (x : Cat) : WilliamsCycle x x := le_rfl

/-- Upward entailment: whatever a projection blocks, every higher projection blocks. -/
theorem WilliamsCycle.of_le {x y y' : Cat} (h : fValue y' ≤ fValue y) (hxy : WilliamsCycle x y) :
    WilliamsCycle x y' :=
  h.trans hxy

/-- (24)–(25), [egressy-2025]: focus and wh-movement to Spec,FocP escape a TP. -/
theorem focus_crosses_TP : WilliamsCycle .Foc .T := by decide

/-- (24)–(25): movement to Spec,FocP cannot leave a SayP, whose Say is above Foc. -/
theorem focus_blocked_by_SayP : ¬ WilliamsCycle .Foc .Say := by decide

/-- (27): raising to Spec,TP crosses a TP. -/
theorem raising_crosses_TP : WilliamsCycle .T .T := WilliamsCycle.refl _

/-- (28), the ban on hyperraising: raising to Spec,TP cannot cross a CP. -/
theorem raising_blocked_by_CP : ¬ WilliamsCycle .T .C := by decide

/-- The complement size crossed in a raising row. -/
def crossed? (e : LinguisticExample) : Option ComplementSize :=
  e.parse? "crossed" [("tP", .tP), ("cP", .cP)]

/-- The raising rows are judged exactly as the Williams Cycle predicts. -/
theorem raising_rows : ∀ e ∈ [ex_27, ex_28], ∀ cs ∈ crossed? e,
    e.judgment = .acceptable ↔ WilliamsCycle .T cs.highestHead := by
  decide

/-- (23): evaluative adverbs such as *sajnos* sit in the Say layer above foci, so a clause hosts
one iff it is at least a SayP. -/
def HostsEvaluativeAdverb (cs : ComplementSize) : Prop := fValue .Say ≤ cs.fLevel

instance (cs : ComplementSize) : Decidable (HostsEvaluativeAdverb cs) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The complements of *mond*, *hall* and *gondol* in (23) host *sajnos*; the TP complement of
*álmodik* cannot. -/
theorem hostsEvaluativeAdverb_iff (ct : ClauseType) :
    HostsEvaluativeAdverb ct.size ↔ ct = .speechReporting := by
  cases ct <;> decide

/-! ### The Sequence of Tense Rule (31) and size-dependent adjunction (41) -/

/-- Where an embedded clause attaches (§4): by (41) to the matrix projection of its own size, as
in Hungarian, or inside the matrix VP as the sister of V, as in English, where (41) does not
hold. -/
inductive Attachment
  | sizeDependent
  | vpInternal
  deriving DecidableEq

/-- The functional-sequence level of the matrix projection an embedded clause attaches to. -/
def Attachment.level : Attachment → ComplementSize → ℕ
  | .sizeDependent, cs => cs.fLevel
  | .vpInternal, _ => fValue .V

/-- The Sequence of Tense Rule (31) can delete an embedded PAST iff the embedded T is contained
in a projection of the matrix PAST T, that is, iff the clause attaches no higher than TP. -/
def SOTRule.Applicable (a : Attachment) (cs : ComplementSize) : Prop := a.level cs ≤ fValue .T

instance (a : Attachment) (cs : ComplementSize) : Decidable (SOTRule.Applicable a cs) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- §3.3 and §4: under size-dependent adjunction the Sequence of Tense Rule obeys the Williams
Cycle in Agree, reaching the embedded PAST exactly where the cycle lets T search the clause. -/
theorem applicable_sizeDependent_iff (cs : ComplementSize) :
    SOTRule.Applicable .sizeDependent cs ↔ WilliamsCycle .T cs.highestHead :=
  Iff.rfl

/-- §4: with the embedded clause inside the VP the rule ignores size. English CP complements
are deleted under Agree although the Williams Cycle would keep T out of a CP, which is why
English Sequence of Tense is size-insensitive. -/
theorem applicable_vpInternal_cP :
    SOTRule.Applicable .vpInternal .cP ∧ ¬ WilliamsCycle .T .C := by
  decide

/-! ### Readings: the language-wide parameter realized clause-internally (§1, §2.4) -/

/-- The value of [ogihara-sharvit-2012]'s Sequence of Tense parameter for one embedded clause:
`relative` (English) where the rule can apply, `absolute` (Japanese) where it cannot. -/
def sotParameter (a : Attachment) (cs : ComplementSize) : SOTParameter :=
  if SOTRule.Applicable a cs then .relative else .absolute

/-- The readings of a past clause under a past matrix: backshift is the default, the
simultaneous reading arises only through the rule. -/
def readings (a : Attachment) (cs : ComplementSize) : List EmbeddedTenseReading :=
  availableReadings (sotParameter a cs)

/-- A non-speech-reporting clause is an English complement. -/
theorem sotParameter_nonSpeech :
    sotParameter .sizeDependent ClauseType.nonSpeechReporting.size = .relative := by
  decide

/-- A speech-reporting clause is a Japanese complement. -/
theorem sotParameter_speech :
    sotParameter .sizeDependent ClauseType.speechReporting.size = .absolute := by
  decide

/-- The core asymmetry (§2.4): the simultaneous reading is available exactly in
non-speech-reporting clauses. -/
theorem simultaneous_iff (ct : ClauseType) :
    EmbeddedTenseReading.simultaneous ∈ readings .sizeDependent ct.size ↔
      ct = .nonSpeechReporting := by
  cases ct <;> decide

/-- The grammar always leaves the backshifted reading; only pragmatics removes it. -/
theorem shifted_mem (a : Attachment) (cs : ComplementSize) :
    EmbeddedTenseReading.shifted ∈ readings a cs := by
  unfold readings sotParameter
  split <;> simp [availableReadings]

/-- (19): an English past-under-past complement has the simultaneous reading. -/
theorem english_simultaneous :
    EmbeddedTenseReading.simultaneous ∈ readings .vpInternal .cP := by
  decide

/-! ### Direct perception (§2.1) -/

/-- One can only perceive directly what happens now: the readings the paper reports are the
grammatical ones, narrowed to the simultaneous reading under direct perception. -/
def observed (direct : Prop) [Decidable direct] (rs : List EmbeddedTenseReading) :
    List EmbeddedTenseReading :=
  if direct then rs.filter (· = .simultaneous) else rs

/-- Pragmatics only removes readings. -/
theorem observed_subset (direct : Prop) [Decidable direct] (rs : List EmbeddedTenseReading) :
    observed direct rs ⊆ rs := by
  unfold observed
  split
  · exact List.filter_subset_self _
  · exact List.Subset.refl _

/-! ### The data (§2) -/

/-- The clause types as recorded in the rows. -/
def clauseTypeTable : List (String × ClauseType) :=
  [("nonSpeechReporting", .nonSpeechReporting), ("speechReporting", .speechReporting)]

/-- The clause type of a single-embedding row. -/
def clauseType? (e : LinguisticExample) : Option ClauseType :=
  e.parse? "clauseType" clauseTypeTable

/-- Whether a row's feature `key` records direct perception. -/
def DirectPerceptionAt (e : LinguisticExample) (key : String) : Prop :=
  e.feature? key = some "yes"

instance (e : LinguisticExample) (key : String) : Decidable (DirectPerceptionAt e key) :=
  inferInstanceAs (Decidable (_ = _))

/-- The readings as named in the rows. -/
def readingTable : List (String × EmbeddedTenseReading) :=
  [("simultaneous", .simultaneous), ("backshifted", .shifted)]

/-- A row's reported readings at embedding level `lvl` agree with a predicted reading set when
each named reading is judged acceptable exactly if predicted. -/
def Agrees (e : LinguisticExample) (lvl : String) (rs : List EmbeddedTenseReading) : Prop :=
  ∀ r ∈ e.readings, ∀ x ∈ readingTable, r.1 = lvl ++ x.1 → (r.2 = .acceptable ↔ x.2 ∈ rs)

instance (e : LinguisticExample) (lvl : String) (rs : List EmbeddedTenseReading) :
    Decidable (Agrees e lvl rs) :=
  inferInstanceAs (Decidable (∀ r ∈ e.readings, ∀ x ∈ readingTable, _ → _))

/-- The predicted readings of a single-embedding Hungarian row: the grammar at its clause
type, narrowed by direct perception. -/
def predicted (e : LinguisticExample) (ct : ClauseType) : List EmbeddedTenseReading :=
  observed (DirectPerceptionAt e "directPerception") (readings .sizeDependent ct.size)

/-- The single-embedding rows of §2.1–2.2: object, subject and adjunct clauses of both types. -/
def singleRows : List LinguisticExample :=
  [ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_11a, ex_11b, ex_11c, ex_12, ex_13, ex_14]

/-- Every single-embedding row is predicted: the simultaneous reading exactly in
non-speech-reporting clauses, and backshift wherever direct perception does not exclude it. -/
theorem singleRows_predicted :
    ∀ e ∈ singleRows, ∀ ct : ClauseType, clauseType? e = some ct →
      Agrees e "" (predicted e ct) := by
  decide

/-- The fragment entry named by a row's `matrixVerb` feature. -/
def matrixVerb? (e : LinguisticExample) : Option HungarianVerbEntry :=
  e.parse? "matrixVerb" [("lát", lat), ("hall", hall), ("álmodik", almodik), ("gondol", gondol),
    ("aggaszt", aggaszt), ("mond", mond), ("rikolt", rikolt), ("morog", morog)]

/-- §2.2: the clause type is a property of the clause, not of the matrix verb. *hall* 'hear'
embeds a non-speech-reporting clause in (5) and the speech-reporting content of a report in
(13), and *morog* 'growl' a non-speech-reporting reason adjunct in (9) and the speech-reporting
content of the growl in (11): no assignment of clause types to verbs fits the rows. -/
theorem clauseType_not_of_verb :
    ¬ ∃ f : HungarianVerbEntry → ClauseType, ∀ e ∈ [ex_5, ex_13, ex_9, ex_11c],
      ∀ v ct, matrixVerb? e = some v → clauseType? e = some ct → f v = ct := by
  rintro ⟨f, hf⟩
  have h5 := hf ex_5 (by simp) hall .nonSpeechReporting rfl rfl
  have h13 := hf ex_13 (by simp) hall .speechReporting rfl rfl
  exact absurd (h5.symm.trans h13) (by decide)

/-! ### Multiple embedding (§2.3, §4) -/

/-- An embedded clause: its morphological tense and its size. -/
structure Clause where
  /-- The clause's tense as a comparison cell, `Tense.past` or `Tense.future`. -/
  tense : Finset Ordering
  /-- The clause's size. -/
  size : ComplementSize

/-- The readings of an embedded clause against the clause immediately containing it. A past
clause under a past clause is read by the rule; a past clause under any other tense is
backshifted only, since the rule needs an agreeing PAST above; a non-past clause has no
past-under-past reading. -/
def linkReadings (a : Attachment) (matrix : Finset Ordering) (c : Clause) :
    List EmbeddedTenseReading :=
  if c.tense = past then (if matrix = past then readings a c.size else [.shifted]) else []

/-- The readings at each level of a chain of embedded clauses under a matrix tense, matrix first.
Each clause is read against the clause immediately containing it: by (41) every clause attaches
at its own size, so a SayP is never inside a TP of any higher clause while a TP is inside the TP
of the clause containing it, and only structurally adjacent clauses interact (§2.3, §4). -/
def profile (a : Attachment) : Finset Ordering → List Clause → List (List EmbeddedTenseReading)
  | _, [] => []
  | m, c :: rest => linkReadings a m c :: profile a c.tense rest

/-- The chain of a two-level Hungarian row, from its two clause-type features. -/
def chain (ct₁ ct₂ : ClauseType) : List Clause := [⟨past, ct₁.size⟩, ⟨past, ct₂.size⟩]

/-- (16): shout > see > be. The speech-reporting intermediate clause is backshifted; the
non-speech-reporting deepest clause is simultaneous with it. -/
theorem ex16_profile :
    profile .sizeDependent past (chain .speechReporting .nonSpeechReporting) =
      [[.shifted], [.shifted, .simultaneous]] := by
  decide

/-- (17): hear > shout > be, the mirror image of (16): only adjacent clauses interact, and a
speech-reporting clause is backshifted whatever contains it. -/
theorem ex17_profile :
    profile .sizeDependent past (chain .nonSpeechReporting .speechReporting) =
      [[.shifted, .simultaneous], [.shifted]] := by
  decide

/-- The two-level rows (10), (15), (16) and (17) are predicted level by level, direct perception
narrowing the level of the perceiving clause. -/
theorem doubleRows_predicted : ∀ e ∈ [ex_10, ex_15, ex_16, ex_17], ∀ ct₁ ct₂ : ClauseType,
    e.parse? "intermediateClauseType" clauseTypeTable = some ct₁ →
    e.parse? "deepestClauseType" clauseTypeTable = some ct₂ →
      Agrees e "intermediate " (observed (DirectPerceptionAt e "intermediateDirectPerception")
          ((profile .sizeDependent past (chain ct₁ ct₂)).getD 0 [])) ∧
        Agrees e "deepest " (observed (DirectPerceptionAt e "deepestDirectPerception")
          ((profile .sizeDependent past (chain ct₁ ct₂)).getD 1 [])) := by
  decide

/-- (18), [ogihara-1996]: English past under *will* under past. The deepest past has no
simultaneous reading, the tense immediately above it being a future rather than an agreeing
past, although English complements attach inside the VP and are otherwise deleted freely. -/
theorem ex18_profile :
    profile .vpInternal past [⟨future, .cP⟩, ⟨past, .cP⟩] = [[], [.shifted]] := by
  decide

theorem ex18_predicted : Agrees ex_18 "deepest " [.shifted] := by decide

/-! ### Rival mechanisms (§3.3, §4) -/

/-- De re res-movement of the embedded PAST ([abusch-1988], [heim-1994-comments]) targets an
A-position inside the matrix VP. A res-movement obeying the Williams Cycle could not leave even
a TP, since T is above V, so it could not derive the simultaneous reading of non-speech-reporting
clauses; deriving them requires a movement free of the locality every other Hungarian
dependency obeys, whereas Agree from T (`raising_crosses_TP`) derives them within it. -/
theorem resMovement_blocked_by_TP : ¬ WilliamsCycle .V .T := by decide

/-- Sequence of Tense as a probe of [keine-2020]: a probe on T whose horizon is Say. -/
def sotProbe : Probe.Profile := ⟨.T, some .Say⟩

/-- The horizon account agrees with the Williams Cycle on the two Hungarian clause types. -/
theorem sotProbe_clauseTypes :
    sotProbe.transparentToLabel [.V, .v, .T] = true ∧
      sotProbe.transparentToLabel [.V, .v, .T, .Foc, .Say] = false := by
  decide

/-- §4: the horizon account is the less restrictive of the two. A clause whose highest head lies
strictly between T and Say, such as a FocP, is transparent to the probe yet beyond the reach of
T under the Williams Cycle, the pattern footnote 9 needs for the complements of *mond*. -/
theorem horizon_admits_FocP :
    sotProbe.transparentToLabel [.V, .v, .T, .Foc] = true ∧ ¬ WilliamsCycle .T .Foc := by
  decide

end Egressy2026
