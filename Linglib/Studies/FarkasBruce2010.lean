import Linglib.Data.Examples.FarkasBruce2010
import Linglib.Discourse.Commitment.Table
import Linglib.Discourse.Role

/-!
# Farkas and Bruce (2010): On Reacting to Assertions and Polar Questions

This file formalizes [farkas-bruce-2010]'s account of why reactions to assertions and to polar
questions overlap only in part. The context structure is `Commitment.Table`: the participants'
discourse commitments, the common ground, and the Table, whose items project the common
grounds that would settle them. A default assertion commits its author, places the declarative
on the Table and projects confirmation alone (9); a default polar question places the
interrogative on the Table and projects both resolutions (12). So an assertion leaves the
common ground as it was, unlike [stalnaker-1978]'s update (`Table.commonGround_assert`,
`assert_not_narrowing`);
the two moves differ in whether the author is committed and in whether the projected set is
inquisitive (`projectedSet_assert`, `projectedSet_polarQuestion`), and agree in deciding the
sentence radical in every projected common ground (`Table.mem_of_mem_projectedSet_assert`,
`Table.mem_or_compl_mem_of_mem_projectedSet_polarQuestion`). Confirmation (16) followed by the
common-ground increase `M'` (17) settles an assertion (`shared_assert_confirm`,
`isStable_settle_assert`, `mem_commonGround_settle`); a total denial (22) leaves nothing
consistent projected and the conversation in crisis (21, `Table.inCrisis_assert_assert_compl`), from
which agreeing to disagree (23) recovers with the commitments intact
(`not_inCrisis_agreeToDisagree`,
  `discourseCommitments_agreeToDisagree`). A reverse answer to a polar question
(28) is no crisis (`not_inCrisis_polarQuestion_assert_compl`), a confirming answer (24)
projects the single common ground with the answer (`projectedSet_polarQuestion_assert`), and
the questioner's confirmation of it settles the question (`isStable_settle_polarQuestion`).

§4.3 and §5 classify responding assertions by two features: the relative polarity [same] or
[reverse] of the response to the sentence radical on the Table (31) and the absolute polarity
[+] or [−] of the asserted sentence. `Sentence` is a radical with its polarity and
`Confirming`/`Reversing` the move types (26) and (29) on sentences; the same [reverse] response
is a denial after an assertion and a reverse answer after a question
(`inCrisis_reversing_assert`, `not_inCrisis_reversing_polarQuestion`). `rows` are the
responding assertions of (4), (5) and (35)–(50) in English, Romanian, French and German, with
`Row.relative` and `Row.absolute` read off the polarities of the exchange: `yes_same_or_pos`
and `no_reverse_or_neg` are the double duty of the English particles, `da_pos` and `nu_neg`
the Romanian absolute particles, `ba_reverse`, `ba_denial` and `ba_not_reverse_answer_neg`
the distribution of *ba* (only in [reverse] responses; possible in a denial; impossible in a
[reverse, −] answer to a question), and `si_doch_reverse_pos` the French and German particles
for the marked combination [reverse, +].

## Implementation notes

* The Table records the issue a sentence raises, not its syntactic object, so a negative polar
  question raises the same issue as its positive counterpart (15), `Question.polar_compl`, and
  the relative polarity of a response is computed from the sentences of the exchange rather
  than read off the Table.
* `M'` is `Table.settle`, which strips the shared proposition from the individual
  commitment lists as (17) prescribes; the projected set is derived from the Table rather than
  stored, as the paper notes it can be.
* Rows record the polarities of the initiating and responding sentences; since a responding
  assertion shares its radical with the initiating sentence, [same] is agreement of polarity
  and [reverse] its reversal (`Reversing.iff_ne_negative`).

## TODO

* (5) accepts a bare *nu* denial of a positive assertion that (42) stars, so §5.2's claim that
  *ba* is required in a [reverse, −] denial is left as the weaker `ba_denial`.
* Example and section numbers follow the 2009 preprint; UNVERIFIED against the numbering of
  the journal version.

## References

* [farkas-bruce-2010]
* [stalnaker-1978]
-/

namespace FarkasBruce2010

open Commitment Filter Data.Examples

variable {W : Type*} (K : Table Discourse.Role W) (p : Set W)

/-- Total denial (22): the speaker asserts `p` and the addressee asserts its negation. -/
abbrev denial : Table Discourse.Role W := (K.assert .speaker p).assert .addressee pᶜ

/-! ### Default assertions and default polar questions -/

/-- A world can survive the assertion of `p` without satisfying `p`, since only the projected set
moves; `Commitment.Table` is not a `HasAssertion` instance under its own `assert`. -/
theorem assert_not_narrowing :
    ∃ (K : Table Discourse.Role Bool) (p : Set Bool) (w : Bool),
      w ∈ HasCommonGround.contextSet (K.assert .speaker p) ∧ w ∉ p :=
  ⟨.empty, {true}, false, by simp [HasCommonGround.contextSet], Bool.false_ne_true⟩

/-- (8): from a stable context an assertion projects the single common ground with `p`, a
categorical bias towards confirmation. -/
theorem projectedSet_assert (a : Discourse.Role) (hK : K.IsStable) (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥) :
    (K.assert a p).projectedSet = {K.commonGround ⊓ 𝓟 p} := by
  rw [Table.projectedSet_assert, Table.projectedSet_of_isStable hK,
    Table.project_singleton_ofSet hp]

/-- (11): from a stable context a polar question projects both resolutions, an inquisitive
context. -/
theorem projectedSet_polarQuestion (hK : K.IsStable) (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥)
    (hnp : K.commonGround ⊓ 𝓟 pᶜ ≠ ⊥) :
    (K.polarQuestion p).projectedSet = {K.commonGround ⊓ 𝓟 p, K.commonGround ⊓ 𝓟 pᶜ} := by
  rw [Table.projectedSet_polarQuestion, Table.projectedSet_of_isStable hK,
    Table.project_singleton_polar hp hnp]

/-! ### Confirmation, denial, and agreeing to disagree -/

/-- (16): after the addressee confirms, the asserted proposition is on every commitment
list. -/
theorem shared_assert_confirm : ((K.assert .speaker p).commit .addressee p).Shared p := by
  intro a
  cases a
  · rw [Table.discourseCommitments_commit_of_ne (by decide)]
    exact Table.mem_discourseCommitments_assert _ _ _
  · exact Table.mem_discourseCommitments_commit_self _ _ _ _ _

/-- (17): the shared proposition enters the common ground. -/
theorem mem_commonGround_settle :
    p ∈ (K.settle p).commonGround := mem_inf_of_right (mem_principal_self p)

/-- (17): the settled assertion is popped, and from a stable context the Table is empty
again. -/
theorem isStable_settle_assert (hK : K.IsStable) :
    (((K.assert .speaker p).commit .addressee p).settle p).IsStable := by
  rw [Table.settle_commit_self, Table.settle_assert_self]
  exact Table.isStable_settle_of_isStable p hK

/-- (23): agreeing to disagree removes the contradictory pair from the Table, and with a
consistent common ground the crisis is over. -/
theorem not_inCrisis_agreeToDisagree (hK : K.IsStable) (hcg : K.commonGround ≠ ⊥) :
    ¬ (denial K p).agreeToDisagree.InCrisis := by
  rw [Table.inCrisis_agreeToDisagree_assert_assert, Table.inCrisis_iff,
    Table.projectedSet_of_isStable hK]
  exact fun h ↦ hcg (h _ rfl)

/-- (23): each participant stays committed to what they asserted. -/
theorem discourseCommitments_agreeToDisagree :
    p ∈ (denial K p).agreeToDisagree.discourseCommitments .speaker ∧
      pᶜ ∈ (denial K p).agreeToDisagree.discourseCommitments .addressee := by
  rw [Table.discourseCommitments_agreeToDisagree,
    Table.discourseCommitments_assert_of_ne (by decide)]
  exact ⟨Table.mem_discourseCommitments_assert _ _ _, Table.mem_discourseCommitments_assert _ _ _⟩

/-! ### Reacting to a polar question -/

/-- A resolving answer to a polar question projects the single common ground with the answer:
the projected resolution inconsistent with it is discarded. -/
theorem projectedSet_polarQuestion_assert (hK : K.IsStable) (b : Discourse.Role) {q : Set W}
    (hq : q ∈ ({p, pᶜ} : Set (Set W))) (hc : K.commonGround ⊓ 𝓟 q ≠ ⊥) :
    ((K.polarQuestion p).assert b q).projectedSet = {K.commonGround ⊓ 𝓟 q} := by
  rw [Table.projectedSet_assert, Table.projectedSet_polarQuestion,
    Table.projectedSet_of_isStable hK]
  ext f
  simp only [Table.mem_project, Question.alt_ofSet, Set.mem_singleton_iff, exists_eq_left]
  constructor
  · rintro ⟨⟨_, ⟨⟨r, hr, rfl⟩, -⟩, rfl⟩, hf⟩
    rcases (Question.alt_polar_iff p r).1 hr with ⟨-, rfl⟩ | ⟨-, -, rfl | rfl⟩
    · rw [principal_univ, inf_top_eq]
    · rcases hq with rfl | rfl
      · rw [inf_assoc, inf_idem]
      · exact absurd (by simp [inf_assoc, inf_principal]) hf
    · rcases hq with rfl | rfl
      · exact absurd (by simp [inf_assoc, inf_principal]) hf
      · rw [inf_assoc, inf_idem]
  · rintro rfl
    refine ⟨⟨K.commonGround ⊓ 𝓟 q, ⟨⟨q, ?_, rfl⟩, hc⟩, by rw [inf_assoc, inf_idem]⟩, hc⟩
    rcases hq with rfl | rfl
    · by_cases hu : q = Set.univ
      · exact (Question.alt_polar_iff _ _).2 (Or.inl ⟨Or.inr hu, hu⟩)
      · exact (Question.alt_polar_iff _ _).2
          (Or.inr ⟨fun e ↦ hc (by simp [e]), hu, Or.inl rfl⟩)
    · by_cases he : p = ∅
      · exact (Question.alt_polar_iff _ _).2 (Or.inl ⟨Or.inl he, by simp [he]⟩)
      · exact (Question.alt_polar_iff _ _).2
          (Or.inr ⟨he, fun e ↦ hc (by simp [e]), Or.inr rfl⟩)

/-- (27): a reverse answer is no crisis, since the question projected both resolutions. -/
theorem not_inCrisis_polarQuestion_assert_compl (hK : K.IsStable) (b : Discourse.Role)
    (hnp : K.commonGround ⊓ 𝓟 pᶜ ≠ ⊥) : ¬ ((K.polarQuestion p).assert b pᶜ).InCrisis := by
  rw [Table.inCrisis_iff, projectedSet_polarQuestion_assert K p hK b (Or.inr rfl) hnp]
  exact fun h ↦ hnp (h _ rfl)

/-- (24) then (16): the questioner's confirmation of the answer settles the question. -/
theorem isStable_settle_polarQuestion (hK : K.IsStable) :
    ((((K.polarQuestion p).assert .addressee p).commit .speaker p).settle p).IsStable := by
  rw [Table.settle_commit_self, Table.settle_assert_self,
    Table.settle_polarQuestion_self]
  exact Table.isStable_settle_of_isStable p hK

/-! ### Responding assertions and polarity features -/

/-- A sentence radical with its polarity: `S` or `¬S`. -/
structure Sentence (W : Type*) where
  radical : Set W
  negative : Bool

/-- The proposition a sentence denotes. -/
def Sentence.prop (s : Sentence W) : Set W := if s.negative then s.radicalᶜ else s.radical

/-- (26): a response confirms when it commits to the proposition of the sentence on the Table. -/
def Confirming (s t : Sentence W) : Prop := t.prop = s.prop

/-- (29): a response reverses when it commits to the complement of that proposition. -/
def Reversing (s t : Sentence W) : Prop := t.prop = s.propᶜ

/-- With a shared radical, reversing is reversing the polarity. -/
theorem Reversing.iff_ne_negative [Nonempty W] {s t : Sentence W} (h : t.radical = s.radical) :
    Reversing s t ↔ t.negative ≠ s.negative := by
  unfold Reversing Sentence.prop
  rw [h]
  cases s.negative <;> cases t.negative <;> simp

/-- With a shared radical, confirming is matching the polarity. -/
theorem Confirming.iff_eq_negative [Nonempty W] {s t : Sentence W} (h : t.radical = s.radical) :
    Confirming s t ↔ t.negative = s.negative := by
  unfold Confirming Sentence.prop
  rw [h]
  cases s.negative <;> cases t.negative <;> simp

/-- A [reverse] response to an assertion is a denial: the conversation is in crisis. -/
theorem inCrisis_reversing_assert {s t : Sentence W} (h : Reversing s t) (a b : Discourse.Role) :
    ((K.assert a s.prop).assert b t.prop).InCrisis := by
  rw [h]
  exact K.inCrisis_assert_assert_compl a s.prop b

/-- The same [reverse] response to the polar question is a reverse answer: no crisis. -/
theorem not_inCrisis_reversing_polarQuestion {s t : Sentence W} (h : Reversing s t)
    (hK : K.IsStable) (b : Discourse.Role) (hc : K.commonGround ⊓ 𝓟 s.propᶜ ≠ ⊥) :
    ¬ ((K.polarQuestion s.prop).assert b t.prop).InCrisis := by
  rw [h]
  exact not_inCrisis_polarQuestion_assert_compl K s.prop hK b hc

/-- The initiating move of a responding assertion. -/
inductive Reaction
  | assertion
  | question
  deriving DecidableEq, Repr

/-- The relative polarity features (31). -/
inductive Relative
  | same
  | reverse
  deriving DecidableEq, Repr

/-- The absolute polarity features. -/
inductive Absolute
  | pos
  | neg
  deriving DecidableEq, Repr

/-- The polarity particles of the paper's examples. -/
inductive Particle
  | yes | no | da | nu | ba | si | doch
  deriving DecidableEq, Repr

inductive Language
  | english | romanian | french | german
  deriving DecidableEq, Repr

/-- A responding assertion of the paper's examples: the initiating move, the polarities of the
initiating and responding sentences, the particles, and the judgment. -/
structure Row where
  language : Language
  reaction : Reaction
  inputNegative : Bool
  responseNegative : Bool
  particles : List Particle
  judgment : Data.Examples.Judgment
  deriving DecidableEq, Repr

/-- [same] or [reverse], from the polarities of the shared radical. -/
def Row.relative (r : Row) : Relative :=
  if r.inputNegative = r.responseNegative then .same else .reverse

/-- [+] or [−]. -/
def Row.absolute (r : Row) : Absolute := if r.responseNegative then .neg else .pos

def languageTable : List (String × Language) :=
  [("stan1293", .english), ("roma1327", .romanian), ("stan1290", .french), ("stan1295", .german)]

def reactionTable : List (String × Reaction) := [("assertion", .assertion), ("question", .question)]

def polarityTable : List (String × Bool) := [("positive", false), ("negative", true)]

def particleTable : List (String × Particle) :=
  [("yes", .yes), ("no", .no), ("da", .da), ("nu", .nu), ("ba", .ba), ("si", .si),
    ("doch", .doch)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let language ← List.lookup ex.language languageTable
  let reaction ← ex.parse? "reaction" reactionTable
  let inputNegative ← ex.parse? "input" polarityTable
  let responseNegative ← ex.parse? "response" polarityTable
  let particle ← ex.parse? "particle" particleTable
  let particles := particle :: (ex.parse? "particle2" particleTable).toList
  pure ⟨language, reaction, inputNegative, responseNegative, particles, ex.judgment⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- English *yes* marks [same] or [+]. -/
theorem yes_same_or_pos :
    ∀ r ∈ rows, r.judgment = .acceptable → .yes ∈ r.particles →
      r.relative = .same ∨ r.absolute = .pos := by
  decide

/-- English *no* marks [reverse] or [−]. -/
theorem no_reverse_or_neg :
    ∀ r ∈ rows, r.judgment = .acceptable → .no ∈ r.particles →
      r.relative = .reverse ∨ r.absolute = .neg := by
  decide

/-- Romanian *da* is an absolute particle: [+]. -/
theorem da_pos : ∀ r ∈ rows, r.judgment = .acceptable → .da ∈ r.particles → r.absolute = .pos := by
  decide

/-- Romanian *nu* is an absolute particle: [−]. -/
theorem nu_neg : ∀ r ∈ rows, r.judgment = .acceptable → .nu ∈ r.particles → r.absolute = .neg := by
  decide

/-- Romanian *ba* signals [reverse]. -/
theorem ba_reverse :
    ∀ r ∈ rows, r.judgment = .acceptable → .ba ∈ r.particles → r.relative = .reverse := by
  decide

/-- *ba* is possible in every denial. -/
theorem ba_denial :
    ∀ r ∈ rows, r.language = .romanian → r.reaction = .assertion → r.relative = .reverse →
      .ba ∈ r.particles → r.judgment = .acceptable := by
  decide

/-- In a [reverse, −] answer to a question, *ba* is impossible and its absence acceptable. -/
theorem ba_not_reverse_answer_neg :
    ∀ r ∈ rows, r.language = .romanian → r.reaction = .question → r.relative = .reverse →
      r.absolute = .neg → (r.judgment = .acceptable ↔ .ba ∉ r.particles) := by
  decide

/-- French *si* and German *doch* mark the marked combination [reverse, +], after assertions
and questions alike. -/
theorem si_doch_reverse_pos :
    ∀ r ∈ rows, .si ∈ r.particles ∨ .doch ∈ r.particles →
      r.relative = .reverse ∧ r.absolute = .pos ∧ r.judgment = .acceptable := by
  decide

end FarkasBruce2010
