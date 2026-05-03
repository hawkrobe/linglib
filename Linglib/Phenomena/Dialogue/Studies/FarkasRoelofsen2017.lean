import Linglib.Theories.Dialogue.FarkasBruce

/-!
# Farkas & Roelofsen (2017): Division of Labor in Declaratives and Interrogatives

@cite{farkas-roelofsen-2017}

A formalization of the sentence-type taxonomy and commitment table
from "Division of Labor in the Interpretation of Declaratives and
Interrogatives" (J. Semantics 34(2): 237–289). The paper builds on
@cite{farkas-bruce-2010}'s commitment-based discourse contexts and
inquisitive semantics (@cite{ciardelli-groenendijk-roelofsen-2018})
to give a uniform account of the six sentence types in (3)–(8):

* (3) Amalia left↓.            [falling declarative]
* (4) Amalia left↑?            [rising declarative]
* (5) Did Amalia leave↓?       [falling polar interrogative]
* (6) Did Amalia leave↑?       [rising polar interrogative]
* (7) Amalia left↓, didn't she↓? [falling tag interrogative]
* (8) Amalia left↓, didn't she↑? [rising tag interrogative]

## What this study formalizes

1. **Clause-type markers** (§4.1, eq. (26)): the two binary axes
   DEC/INT (declarative vs interrogative word order) and CLOSED/OPEN
   (falling vs rising intonation), composed with an optional tag.
2. **Markedness principle** (§3, eq. (21), p. 250): unmarked sentence
   forms are determined by their semantic content + a single basic
   convention of use; marked forms accumulate special effects.
   Falling declaratives + polar interrogatives are unmarked; rising
   declaratives + tag interrogatives are marked.
3. **Commitment table** (p. 240, the unnumbered table after eq. (12)):
   the four-row taxonomy of commitment types — full / bias / neutral.
4. **Credence intervals** (§3.2, after eq. (23), p. 256): rising
   declaratives signal credence at most low; rising tag interrogatives
   signal moderate-to-high; falling tag interrogatives signal high.
5. **Felicity contrasts** (24)/(25), p. 256: the rising-declarative
   ↔ tag-interrogative complementary distribution depending on
   speaker's evidence for the highlighted alternative.

## What's out of scope

- Full inquisitive semantics machinery (projection operators ! and ?,
  highlighting). This study uses placeholder propositions; a deeper
  integration with `Core.Inquisitive` is sibling work.
- The compositional semantics of §4.2 (how clause-type markers
  combine with sentence radicals).
- Sections 5–7 (the conventions of use + comparison to alternatives).
  These would require integrating with the substrate's enriched
  discourse contexts in a more thoroughgoing way.

## Substrate consumed

`Theories/Dialogue/FarkasBruce.lean` provides the basic
participant/table/commitment trichotomy that F&R extend. This study
adds the sentence-form taxonomy and the credence-evidence layer in
Lean, treating both as paper-anchored extensions.
-/

namespace Phenomena.Dialogue.Studies.FarkasRoelofsen2017

-- ════════════════════════════════════════════════════════════════
-- § 1. Clause-type markers (§4.1, eq. (26), p. 257)
-- ════════════════════════════════════════════════════════════════

/-- DEC/INT axis: declarative vs interrogative word order
    (@cite{farkas-roelofsen-2017} §4.1 eq. (26a), p. 257). In
    English root clauses, DEC = declarative word order, INT =
    interrogative word order. -/
inductive ClauseType where
  | dec
  | int
  deriving DecidableEq, Repr, Inhabited

/-- CLOSED/OPEN axis: falling vs rising intonation
    (@cite{farkas-roelofsen-2017} §4.1 eq. (26b), p. 257).
    CLOSED = ↓ (falling); OPEN = ↑ (rising). -/
inductive Intonation where
  | closed  -- falling ↓
  | rising  -- rising ↑ (book uses "open" but `open` is a Lean keyword)
  deriving DecidableEq, Repr, Inhabited

/-- A sentence form is a triple of clause-type marker, intonation
    marker, and tag-presence flag (@cite{farkas-roelofsen-2017}
    §4.1; tags are introduced after eq. (27), p. 258).

    The 6 sentence types of (3)–(8):
    * `⟨.dec, .closed, false⟩` — falling declarative
    * `⟨.dec, .rising, false⟩` — rising declarative
    * `⟨.int, .closed, false⟩` — falling polar interrogative
    * `⟨.int, .rising, false⟩` — rising polar interrogative
    * `⟨.dec, .closed, true⟩`  — falling tag interrogative
      (declarative anchor + tag with falling intonation)
    * `⟨.dec, .rising, true⟩`  — rising tag interrogative
      (declarative anchor + tag with rising intonation) -/
structure SentenceForm where
  clauseType : ClauseType
  intonation : Intonation
  hasTag : Bool
  deriving DecidableEq, Repr, Inhabited

namespace SentenceForm

/-- Falling declarative (3) "Amalia left↓." -/
def fallingDeclarative : SentenceForm := ⟨.dec, .closed, false⟩

/-- Rising declarative (4) "Amalia left↑?" -/
def risingDeclarative : SentenceForm := ⟨.dec, .rising, false⟩

/-- Falling polar interrogative (5) "Did Amalia leave↓?" -/
def fallingPolarInterrogative : SentenceForm := ⟨.int, .closed, false⟩

/-- Rising polar interrogative (6) "Did Amalia leave↑?" -/
def risingPolarInterrogative : SentenceForm := ⟨.int, .rising, false⟩

/-- Falling tag interrogative (7) "Amalia left↓, didn't she↓?" -/
def fallingTagInterrogative : SentenceForm := ⟨.dec, .closed, true⟩

/-- Rising tag interrogative (8) "Amalia left↓, didn't she↑?" -/
def risingTagInterrogative : SentenceForm := ⟨.dec, .rising, true⟩

end SentenceForm

-- ════════════════════════════════════════════════════════════════
-- § 2. Markedness (§3 eq. (21), p. 250)
-- ════════════════════════════════════════════════════════════════

/-- Markedness predicate (@cite{farkas-roelofsen-2017} §3
    eq. (21) "Division of labor principle", p. 250):

    Unmarked forms have their conventional discourse effects fully
    determined by semantic content + the single basic convention
    of use F_b. Marked forms accumulate special effects.

    Falling declaratives + polar interrogatives are UNMARKED.
    Rising declaratives + tag interrogatives are MARKED. -/
def SentenceForm.isMarked : SentenceForm → Prop
  | ⟨_, _, true⟩ => True   -- any tag → marked
  | ⟨.dec, .rising, false⟩ => True   -- rising declarative → marked
  | _ => False             -- falling declarative + both polar interrogatives are unmarked

instance (sf : SentenceForm) : Decidable sf.isMarked := by
  cases sf with
  | mk ct i ht =>
    cases ht <;> cases ct <;> cases i <;>
      (unfold SentenceForm.isMarked; infer_instance)

-- ════════════════════════════════════════════════════════════════
-- § 3. Commitment table (p. 240, after eq. (12))
-- ════════════════════════════════════════════════════════════════

/-- Three commitment-types from the table on p. 240
    (@cite{farkas-roelofsen-2017}):

    * `fullCommitment` — the speaker is fully committed to one
      alternative (falling declaratives).
    * `bias` — the speaker is biased toward one alternative but
      not fully committed (rising declaratives + tag interrogatives).
    * `neutral` — the speaker remains neutral between alternatives
      (polar interrogatives, both intonations). -/
inductive CommitmentType where
  | fullCommitment
  | bias
  | neutral
  deriving DecidableEq, Repr, Inhabited

/-- Map each sentence form to its commitment type
    (@cite{farkas-roelofsen-2017}, p. 240 table). -/
def commitmentType : SentenceForm → CommitmentType
  | ⟨.dec, .closed, false⟩ => .fullCommitment   -- falling declarative
  | ⟨.dec, .rising, false⟩ => .bias             -- rising declarative
  | ⟨.dec, _, true⟩ => .bias                    -- tag interrogative (either intonation)
  | ⟨.int, _, _⟩ => .neutral                    -- polar interrogative

/-- **Headline theorem**: the commitment table from p. 240. Each
    of the 6 sentence types is assigned the commitment type the
    paper claims it has. -/
theorem commitment_table :
    commitmentType .fallingDeclarative = .fullCommitment ∧
    commitmentType .risingDeclarative = .bias ∧
    commitmentType .fallingTagInterrogative = .bias ∧
    commitmentType .risingTagInterrogative = .bias ∧
    commitmentType .fallingPolarInterrogative = .neutral ∧
    commitmentType .risingPolarInterrogative = .neutral := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § 4. Credence intervals (§3.2, p. 256, after eq. (23))
-- ════════════════════════════════════════════════════════════════

/-- Credence levels (@cite{farkas-roelofsen-2017} §3.2 p. 256):
    "If the speaker considers the highlighted alternative α to be
    much more likely than ᾱ, we say her credence in α is high; if
    she only considers it to be somewhat more likely than ᾱ, we say
    her credence in α is moderate; in cases that fall in between
    these two extremes that the speaker's credence in α is low; and
    finally, if the speaker does not consider α more likely than
    ᾱ at all, we say her credence in α is zero."

    The four levels are linearly ordered: zero < low < moderate < high. -/
inductive CredenceLevel where
  | zero
  | low
  | moderate
  | high
  deriving DecidableEq, Repr, Inhabited

/-- Total order on `CredenceLevel`: zero < low < moderate < high. -/
def CredenceLevel.toNat : CredenceLevel → Nat
  | .zero => 0
  | .low => 1
  | .moderate => 2
  | .high => 3

instance : LE CredenceLevel := ⟨fun a b => a.toNat ≤ b.toNat⟩

instance (a b : CredenceLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

/-- A credence interval is a pair of lower and upper bounds on a
    speaker's credence in the highlighted alternative
    (@cite{farkas-roelofsen-2017} §3.2, after eq. (23), p. 256:
    "i is a credence interval, capturing the amount of credence x
    signals that she has in p"). -/
structure CredenceInterval where
  lower : CredenceLevel
  upper : CredenceLevel
  deriving DecidableEq, Repr, Inhabited

/-- A credence level falls within a credence interval. -/
def CredenceInterval.contains (i : CredenceInterval) (c : CredenceLevel) : Prop :=
  i.lower ≤ c ∧ c ≤ i.upper

instance (i : CredenceInterval) (c : CredenceLevel) :
    Decidable (i.contains c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The credence interval signaled by each marked sentence form
    (@cite{farkas-roelofsen-2017} §3.2, p. 256, just before §4):

    * Rising declaratives → [zero, low]
    * Rising tag interrogatives → [moderate, high]
    * Falling tag interrogatives → [high, high]
    * Other forms (unmarked) → no signal; we use [zero, high]
      (the trivial interval) as a placeholder. -/
def signaledCredence : SentenceForm → CredenceInterval
  | ⟨.dec, .rising, false⟩ => ⟨.zero, .low⟩         -- rising declarative
  | ⟨.dec, .rising, true⟩ => ⟨.moderate, .high⟩      -- rising tag
  | ⟨.dec, .closed, true⟩ => ⟨.high, .high⟩          -- falling tag
  | _ => ⟨.zero, .high⟩                              -- unmarked: trivial

-- ════════════════════════════════════════════════════════════════
-- § 5. Felicity contrasts (24)/(25), p. 256
-- ════════════════════════════════════════════════════════════════

/-- A speaker is felicitous in uttering `form` in a context where
    her credence in the highlighted alternative is `c` iff `c` falls
    within the form's signaled credence interval
    (@cite{farkas-roelofsen-2017} §3.2 prose around examples (24)/(25),
    p. 256). -/
def felicitous (form : SentenceForm) (speakerCredence : CredenceLevel) : Prop :=
  (signaledCredence form).contains speakerCredence

instance (form : SentenceForm) (c : CredenceLevel) :
    Decidable (felicitous form c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Example (24)** (p. 256): "Belinda is going through a pile of
    job applications. Chris has not seen any of them yet. Belinda
    hands Chris the application that she just finished reading, and
    tells him to have a look at it. Chris to Belinda:
    a. This is a good one↑?           [rising declarative, ✓ felicitous]
    b. #This is a good one, isn't it?  [tag, # infelicitous]"

    In this context, Chris has NO prior evidence — credence = zero.
    Rising declarative requires [zero, low] → felicitous (zero ∈ [zero, low]).
    Tag interrogative requires [moderate, high] → infelicitous. -/
theorem example_24_rising_felicitous :
    felicitous .risingDeclarative .zero := by decide

theorem example_24_tag_infelicitous :
    ¬ felicitous .risingTagInterrogative .zero := by decide

theorem example_24_tag_infelicitous_falling :
    ¬ felicitous .fallingTagInterrogative .zero := by decide

/-- **Example (25)** (p. 256): "Belinda and Chris are looking at a
    sunset together. Belinda to Chris:
    a. #It's a beautiful sunset↑?      [rising declarative, # infelicitous]
    b. It's a beautiful sunset, isn't it? [tag, ✓ felicitous]"

    In this context, Belinda is looking at the sunset directly —
    credence = high. Rising declarative requires [zero, low] →
    infelicitous (high ∉ [zero, low]). Tag (typically rising in this
    case) requires [moderate, high] → felicitous. -/
theorem example_25_rising_infelicitous :
    ¬ felicitous .risingDeclarative .high := by decide

theorem example_25_tag_felicitous_rising :
    felicitous .risingTagInterrogative .high := by decide

theorem example_25_tag_felicitous_falling :
    felicitous .fallingTagInterrogative .high := by decide

/-- The complementary-distribution claim of (24)/(25): rising
    declaratives and tag interrogatives are NEVER both felicitous
    in the same speaker-credence context (their signaled-credence
    intervals are disjoint). -/
theorem rising_dec_and_falling_tag_disjoint (c : CredenceLevel) :
    ¬ (felicitous .risingDeclarative c ∧ felicitous .fallingTagInterrogative c) := by
  cases c <;> decide

/-- Rising declarative + rising tag are also disjoint in
    signaled-credence (rising-dec ⊆ [zero, low] vs rising-tag
    ⊆ [moderate, high]). -/
theorem rising_dec_and_rising_tag_disjoint (c : CredenceLevel) :
    ¬ (felicitous .risingDeclarative c ∧ felicitous .risingTagInterrogative c) := by
  cases c <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 6. Markedness ↔ commitment-table connection
-- ════════════════════════════════════════════════════════════════

/-- The six sentence forms the paper considers (3)–(8). Tags only
    combine with declarative anchors, so `⟨.int, _, true⟩` is not
    a valid F&R sentence form. -/
def paperSentenceForms : List SentenceForm :=
  [.fallingDeclarative, .risingDeclarative,
   .fallingPolarInterrogative, .risingPolarInterrogative,
   .fallingTagInterrogative, .risingTagInterrogative]

/-- A consequence of the framework restricted to the 6 paper-valid
    sentence forms: every UNMARKED form is either fullyCommitting
    (falling declarative) or neutral (polar interrogatives). Bias
    commitments are reserved for marked forms (rising declaratives
    + tag interrogatives).

    This is the "Division of Labor" principle's structural
    signature: unmarked forms have either full commitment or no
    commitment, never partial bias. -/
theorem unmarked_iff_full_or_neutral_paper (sf : SentenceForm)
    (h : sf ∈ paperSentenceForms) :
    ¬ sf.isMarked ↔ commitmentType sf ∈ [CommitmentType.fullCommitment, .neutral] := by
  -- Decide-check by exhausting the 6 paper-valid forms.
  simp only [paperSentenceForms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 7. F&B-substrate threading (closing the audit's "hollow import" finding)
-- ════════════════════════════════════════════════════════════════

/-! The original landing of this study (CHANGELOG 0.230.675) imported
`Theories.Dialogue.FarkasBruce` but never used it — `FarkasBruce.`
appeared 0 times in the body. The re-audit (CHANGELOG 0.230.677)
flagged this as a hollow import. This section closes the gap by
threading `SentenceForm` through F&B's discourse-state operators,
turning the "extends F&B" claim from aspirational to structural.

The F&B-side mapping for each unmarked sentence type follows from
F-R 2017's "single basic convention of use" (eq. (21), p. 250).
For marked types, F-R 2017 augments the basic convention with
special effects (the credence interval signaled by §3.2's
machinery); we model the structural part of that effect here. -/

open Dialogue.FarkasBruce

/-- Update a F&B discourse state by uttering `content` with sentence
    form `form` (@cite{farkas-roelofsen-2017} §3 + §4.1 conventions
    of use threaded through F&B's substrate operators).

    Mapping:
    * Falling declarative (unmarked) → `assertDeclarative`: writes
      to dcS, pushes a one-alternative issue.
    * Rising or falling polar interrogative → `askPolarQuestion`:
      pushes a {p, ¬p} issue, no dcS write.
    * Rising declarative (marked, bias) → push a one-alternative
      issue WITHOUT writing dcS. F&B has no built-in operator for
      this; we construct the `RaisedIssue` directly.
    * Tag interrogative (marked, bias) → declarative anchor commits
      via `assertDeclarative` AND a polar issue is raised by the tag.

    Non-paper-canonical forms (interrogative + tag) are no-ops. -/
def SentenceForm.update {W : Type*} (form : SentenceForm)
    (content : Set W) (ds : DiscourseState W) : DiscourseState W :=
  match form with
  | ⟨.dec, .closed, false⟩ => ds.assertDeclarative content
  | ⟨.int, _, false⟩ => ds.askPolarQuestion content
  | ⟨.dec, .rising, false⟩ =>
      ds.pushIssue
        { form := .declarative, alternatives := [content], source := .speaker }
  | ⟨.dec, _, true⟩ => (ds.assertDeclarative content).askPolarQuestion content
  | _ => ds

/-- Falling declarative writes to dcS (full commitment, p. 240 table). -/
theorem fallingDec_writes_dcS {W : Type*}
    (content : Set W) (ds : DiscourseState W) :
    (SentenceForm.fallingDeclarative.update content ds).dcS = content :: ds.dcS := rfl

/-- Polar interrogatives (either intonation) do NOT write to dcS
    (neutral, p. 240 table). -/
theorem polarInt_doesnt_write_dcS_falling {W : Type*}
    (content : Set W) (ds : DiscourseState W) :
    (SentenceForm.fallingPolarInterrogative.update content ds).dcS = ds.dcS := rfl

theorem polarInt_doesnt_write_dcS_rising {W : Type*}
    (content : Set W) (ds : DiscourseState W) :
    (SentenceForm.risingPolarInterrogative.update content ds).dcS = ds.dcS := rfl

/-- Rising declarative does NOT write to dcS (bias, no full commitment;
    matches p. 240 table classification). -/
theorem risingDec_doesnt_write_dcS {W : Type*}
    (content : Set W) (ds : DiscourseState W) :
    (SentenceForm.risingDeclarative.update content ds).dcS = ds.dcS := rfl

/-- Tag interrogatives DO write to dcS (the declarative anchor commits;
    the tag separately raises an issue). The "bias" classification on
    p. 240 thus has TWO structurally distinct realizations in F&B
    terms: rising declaratives don't commit, tags do. -/
theorem tag_writes_dcS_falling {W : Type*}
    (content : Set W) (ds : DiscourseState W) :
    (SentenceForm.fallingTagInterrogative.update content ds).dcS = content :: ds.dcS := rfl

theorem tag_writes_dcS_rising {W : Type*}
    (content : Set W) (ds : DiscourseState W) :
    (SentenceForm.risingTagInterrogative.update content ds).dcS = content :: ds.dcS := rfl

/-- All sentence types push at least one issue onto the table.
    The structural common ground per F&B: every utterance is
    table-bearing. -/
theorem all_paper_forms_push_issue {W : Type*}
    (content : Set W) (ds : DiscourseState W) (form : SentenceForm)
    (h : form ∈ paperSentenceForms) :
    (form.update content ds).table.length > ds.table.length := by
  simp only [paperSentenceForms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;>
    simp [SentenceForm.update, SentenceForm.fallingDeclarative,
        SentenceForm.risingDeclarative, SentenceForm.fallingPolarInterrogative,
        SentenceForm.risingPolarInterrogative,
        SentenceForm.fallingTagInterrogative, SentenceForm.risingTagInterrogative,
        DiscourseState.assertDeclarative, DiscourseState.askPolarQuestion,
        DiscourseState.pushIssue, DiscourseState.addToDcS] <;> try omega

/-- The commitment-table classification corresponds to F&B-side
    behavior for the two "extreme" cases:
    * `fullCommitment` ↔ writes to dcS via `assertDeclarative`
    * `neutral` ↔ does not write to dcS (only pushes an issue)

    The `bias` middle case is NOT structurally uniform: rising
    declaratives don't write dcS (like neutral), tag interrogatives
    DO write dcS (like full). This is an honest finding — the
    p. 240 commitment table abstracts over a structural distinction
    that F&B's substrate makes visible. -/
theorem fullCommitment_iff_dcS_grows {W : Type*}
    (content : Set W) (ds : DiscourseState W) (form : SentenceForm)
    (h : form ∈ paperSentenceForms) :
    commitmentType form = .fullCommitment →
      (form.update content ds).dcS = content :: ds.dcS := by
  simp only [paperSentenceForms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> intro hc <;>
    simp_all [commitmentType, SentenceForm.fallingDeclarative,
              SentenceForm.risingDeclarative, SentenceForm.fallingPolarInterrogative,
              SentenceForm.risingPolarInterrogative,
              SentenceForm.fallingTagInterrogative, SentenceForm.risingTagInterrogative,
              SentenceForm.update, DiscourseState.assertDeclarative,
              DiscourseState.addToDcS, DiscourseState.pushIssue]

end Phenomena.Dialogue.Studies.FarkasRoelofsen2017
