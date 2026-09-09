import Linglib.Data.Examples.FarkasBruce2010
import Linglib.Discourse.Commitment.Table
import Linglib.Discourse.Roles

/-!
# Farkas and Bruce (2010): On Reacting to Assertions and Polar Questions

This file formalizes [farkas-bruce-2010]'s account of why reactions to assertions and to polar
questions overlap only in part. The context structure is `Commitment.Table`: the participants'
discourse commitments, the common ground, and the Table, whose items project the common
grounds that would settle them. A default assertion commits its author, places the declarative
on the Table and projects confirmation alone (9); a default polar question places the
interrogative on the Table and projects both resolutions (12). So an assertion leaves the
common ground as it was, against [stalnaker-1978] (`assert_cg`, `assert_not_narrowing`); the
two moves differ in whether the author is committed and in whether the projected set is
inquisitive (`projectedSet_assert`, `projectedSet_polarQuestion`), and agree in deciding the
sentence radical in every projected common ground (`mem_of_mem_projectedSet_assert`,
`mem_or_compl_mem_of_mem_projectedSet_polarQuestion`). Confirmation (16) followed by the
common-ground increase `M'` (17) settles an assertion (`shared_assert_confirm`,
`isStable_increaseCG_assert`, `mem_cg_increaseCG`); a total denial (22) leaves nothing
consistent projected and the conversation in crisis (21, `inCrisis_assert_compl`), from
which agreeing to disagree (23) recovers with the commitments intact
(`not_inCrisis_agreeToDisagree`, `dc_agreeToDisagree`). A reverse answer to a polar question
(28) is no crisis (`not_inCrisis_polarQuestion_assert_compl`), a confirming answer (24)
projects the single common ground with the answer (`projectedSet_polarQuestion_assert`), and
the questioner's confirmation of it settles the question (`isStable_increaseCG_polarQuestion`).

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

* The Table records an item's sentential feature and denotation, not its syntactic object, so
  a negative polar question has the same effect as its positive counterpart (15), and the
  relative polarity of a response is computed from the sentences of the exchange rather than
  read off the Table.
* `M'` is `Table.increaseCG`, which strips the shared proposition from the individual
  commitment lists as (17) prescribes; the projected set is derived from the Table rather than
  stored, as the paper notes it can be.
* Rows record the polarities of the initiating and responding sentences; since a responding
  assertion shares its radical with the initiating sentence, [same] is agreement of polarity
  and [reverse] its reversal (`Reversing.iff_ne_negative`).

## TODO

* (5) accepts a bare *nu* denial of a positive assertion that (42) stars, so §5.2's claim that
  *ba* is required in a [reverse, −] denial is left as the weaker `ba_denial`.

## References

* [farkas-bruce-2010]
* [stalnaker-1978]
* [gunlogson-2001]
* [karttunen-1977]
-/

namespace FarkasBruce2010

open Commitment Filter Data.Examples

variable {W : Type*} (K : Table Discourse.Role W) (p : Set W)

/-! ### Default assertions and default polar questions -/

/-- Assertion proposes: the common ground is exactly as before (9). -/
theorem assert_cg : (K.assert .speaker p).cg = K.cg := rfl

/-- A world can survive the assertion of `p` without satisfying `p`, since only the projected set
moves; `Commitment.Table` is not a `HasAssertion` instance under its own `assert`. -/
theorem assert_not_narrowing :
    ∃ (K : Table Discourse.Role Bool) (p : Set Bool) (w : Bool),
      w ∈ (K.assert .speaker p).contextSet ∧ w ∉ p :=
  ⟨.empty, {true}, false, by simp [Table.contextSet, Table.assert, Table.push, Table.commit],
    Bool.false_ne_true⟩

/-- Every projected common ground decides one of the propositions added. -/
theorem exists_mem_of_mem_project {ps : Set (Filter W)} {P : Set (Set W)} {f : Filter W}
    (h : f ∈ Table.project ps P) : ∃ q ∈ P, q ∈ f := by
  obtain ⟨_, -, q, hq, rfl, -⟩ := h
  exact ⟨q, hq, mem_inf_of_right (mem_principal_self q)⟩

/-- The asserted proposition holds in every projected common ground. -/
theorem mem_of_mem_projectedSet_assert (a : Discourse.Role) {f : Filter W}
    (h : f ∈ (K.assert a p).projectedSet) : p ∈ f := by
  obtain ⟨q, hq, hf⟩ := exists_mem_of_mem_project h
  exact Set.mem_singleton_iff.1 hq ▸ hf

/-- The sentence radical of a polar question is decided in every projected common ground. -/
theorem mem_or_compl_mem_of_mem_projectedSet_polarQuestion {f : Filter W}
    (h : f ∈ (K.polarQuestion p).projectedSet) : p ∈ f ∨ pᶜ ∈ f := by
  obtain ⟨q, hq, hf⟩ := exists_mem_of_mem_project h
  rcases hq with rfl | rfl
  · exact Or.inl hf
  · exact Or.inr hf

/-- (8): from a stable context an assertion projects the single common ground with `p`, a
categorical bias towards confirmation. -/
theorem projectedSet_assert (a : Discourse.Role) (hK : K.IsStable) (hp : K.cg ⊓ 𝓟 p ≠ ⊥) :
    (K.assert a p).projectedSet = {K.cg ⊓ 𝓟 p} := by
  rw [Table.projectedSet_assert, Table.projectedSet_of_isStable _ hK]
  ext f
  simp only [Table.project, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq]
  exact ⟨λ h => h.1, λ h => ⟨h, h ▸ hp⟩⟩

/-- (11): from a stable context a polar question projects both resolutions, an inquisitive
context. -/
theorem projectedSet_polarQuestion (hK : K.IsStable) (hp : K.cg ⊓ 𝓟 p ≠ ⊥)
    (hnp : K.cg ⊓ 𝓟 pᶜ ≠ ⊥) :
    (K.polarQuestion p).projectedSet = {K.cg ⊓ 𝓟 p, K.cg ⊓ 𝓟 pᶜ} := by
  rw [Table.projectedSet_polarQuestion, Table.projectedSet_of_isStable _ hK]
  ext f
  simp only [Table.project, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨q, rfl | rfl, rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨p, Or.inl rfl, rfl, hp⟩
    · exact ⟨pᶜ, Or.inr rfl, rfl, hnp⟩

/-! ### Confirmation, denial, and agreeing to disagree -/

/-- (16): after the addressee confirms, the asserted proposition is on every commitment
list. -/
theorem shared_assert_confirm : ((K.assert .speaker p).confirm .addressee p).Shared p := by
  intro a
  cases a
  · rw [Table.confirm, Table.dc_commit_of_ne _ _ _ _ _ (by decide)]
    exact Table.mem_dc_assert _ _ _
  · exact Table.mem_dc_commit_self _ _ _ _ _

/-- (17): the shared proposition enters the common ground. -/
theorem mem_cg_increaseCG : p ∈ (K.increaseCG p).cg := mem_inf_of_right (mem_principal_self p)

open scoped Classical in
/-- (17): the settled assertion is popped, and from a stable context the Table is empty
again. -/
theorem isStable_increaseCG_assert (hK : K.IsStable) :
    (((K.assert .speaker p).confirm .addressee p).increaseCG p).IsStable := by
  have hp : ∃ q ∈ ({p} : Set (Set W)), q ∈ K.cg ⊓ 𝓟 p :=
    ⟨p, rfl, mem_inf_of_right (mem_principal_self p)⟩
  simp only [Table.IsStable, Table.increaseCG, Table.confirm, Table.commit_stack,
    Table.assert_stack, Table.commit_cg, Table.assert_cg, show K.stack = [] from hK,
    List.dropWhile_cons, decide_eq_true hp, ite_true, List.dropWhile_nil]

/-- A denied assertion leaves the conversation in crisis (21). -/
theorem inCrisis_assert_compl : ((K.assert .speaker p).assert .addressee pᶜ).InCrisis :=
  K.inCrisis_assert_compl .speaker p .addressee

/-- (23): agreeing to disagree removes the contradictory pair from the Table, and with a
consistent common ground the crisis is over. -/
theorem not_inCrisis_agreeToDisagree (hK : K.IsStable) (hcg : K.cg ≠ ⊥) :
    ¬ (((K.assert .speaker p).assert .addressee pᶜ).agreeToDisagree p).InCrisis := by
  have hs : (((K.assert .speaker p).assert .addressee pᶜ).agreeToDisagree p).IsStable := by
    simp only [Table.IsStable, Table.agreeToDisagree, Table.assert_stack, show K.stack = [] from hK]
    rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_neg (by simp), List.filter_nil]
  rintro (h | h)
  · exact hcg h
  · rw [Table.projectedSet_of_isStable _ hs] at h
    exact hcg (h _ rfl)

/-- (23): each participant stays committed to what they asserted. -/
theorem dc_agreeToDisagree :
    p ∈ (((K.assert .speaker p).assert .addressee pᶜ).agreeToDisagree p).dc .speaker ∧
      pᶜ ∈ (((K.assert .speaker p).assert .addressee pᶜ).agreeToDisagree p).dc .addressee := by
  refine ⟨?_, Table.mem_dc_assert _ _ _⟩
  show p ∈ ((K.assert .speaker p).assert .addressee pᶜ).dc .speaker
  rw [Table.assert, Table.dc_push, Table.dc_commit_of_ne _ _ _ _ _ (by decide)]
  exact Table.mem_dc_assert _ _ _

/-! ### Reacting to a polar question -/

/-- A resolving answer to a polar question projects the single common ground with the answer:
the projected resolution inconsistent with it is discarded. -/
theorem projectedSet_polarQuestion_assert (hK : K.IsStable) (b : Discourse.Role) {q : Set W}
    (hq : q ∈ ({p, pᶜ} : Set (Set W))) (hc : K.cg ⊓ 𝓟 q ≠ ⊥) :
    ((K.polarQuestion p).assert b q).projectedSet = {K.cg ⊓ 𝓟 q} := by
  rw [Table.projectedSet_assert, Table.projectedSet_polarQuestion,
    Table.projectedSet_of_isStable _ hK]
  ext f
  simp only [Table.project, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl, -⟩, rfl, hf⟩
    rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;>
      first
      | rw [inf_assoc, inf_idem]
      | exact absurd (by simp [inf_assoc, inf_principal]) hf
  · rintro rfl
    exact ⟨K.cg ⊓ 𝓟 q, ⟨q, hq, rfl, hc⟩, by rw [inf_assoc, inf_idem], hc⟩

/-- (27): a reverse answer is no crisis, since the question projected both resolutions. -/
theorem not_inCrisis_polarQuestion_assert_compl (hK : K.IsStable) (b : Discourse.Role)
    (hnp : K.cg ⊓ 𝓟 pᶜ ≠ ⊥) : ¬ ((K.polarQuestion p).assert b pᶜ).InCrisis := by
  rintro (h | h)
  · exact hnp (by rw [show ((K.polarQuestion p).assert b pᶜ).cg = K.cg from rfl] at h; simp [h])
  · rw [projectedSet_polarQuestion_assert K p hK b (Or.inr rfl) hnp] at h
    exact hnp (h _ rfl)

open scoped Classical in
/-- (24) then (16): the questioner's confirmation of the answer settles the question. -/
theorem isStable_increaseCG_polarQuestion (hK : K.IsStable) :
    ((((K.polarQuestion p).assert .addressee p).confirm .speaker p).increaseCG p).IsStable := by
  have hp : ∃ q ∈ ({p} : Set (Set W)), q ∈ K.cg ⊓ 𝓟 p :=
    ⟨p, rfl, mem_inf_of_right (mem_principal_self p)⟩
  have hq : ∃ q ∈ ({p, pᶜ} : Set (Set W)), q ∈ K.cg ⊓ 𝓟 p :=
    ⟨p, Or.inl rfl, mem_inf_of_right (mem_principal_self p)⟩
  simp only [Table.IsStable, Table.increaseCG, Table.confirm, Table.commit_stack,
    Table.assert_stack, Table.polarQuestion_stack, Table.commit_cg, Table.assert_cg,
    Table.polarQuestion_cg, show K.stack = [] from hK, List.dropWhile_cons, decide_eq_true hp,
    decide_eq_true hq, ite_true, List.dropWhile_nil]

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
  exact K.inCrisis_assert_compl a s.prop b

/-- The same [reverse] response to the polar question is a reverse answer: no crisis. -/
theorem not_inCrisis_reversing_polarQuestion {s t : Sentence W} (h : Reversing s t)
    (hK : K.IsStable) (b : Discourse.Role) (hc : K.cg ⊓ 𝓟 s.propᶜ ≠ ⊥) :
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
  judgment : Features.Judgment
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
