import Linglib.Theories.Semantics.Quotation.Demonstration
import Linglib.Theories.Pragmatics.Assertion.QuotationFBOntology
import Linglib.Fragments.English.Predicates.Verbal

/-!
# @cite{rudin-2025b}: Embedded Intonation and Quotative Complements

Rudin, Deniz (2025/2026). "Embedded Intonation and Quotative Complements
to Verbs of Speech." Linguistic Inquiry, early access. doi:10.1162/ling.a.554.

## Empirical Generalizations

The paper's central observation: verbs of speech systematically split on
whether they accept rising-declarative ("quotative") complements:

| Verb         | "p"  | "p?" | "p" loud | "p" whisp | *that p* | *that wh / Q* |
|--------------|------|------|----------|-----------|----------|--------------|
| say          | ✓    | ✓    | ✓        | ✓         | ✓        | ✗            |
| assert       | ✓    | ✗    | ✓        | ✓         | ✓        | ✗            |
| yell         | ✓    | ✓    | ✓        | ✗         | ✓        | ✗            |
| whisper      | ✓    | ✓    | ✗        | ✓         | ✓        | ✗            |
| ask          | ✗    | ✓    | ✗        | ✗         | ✗        | ✓            |

## Architecture: One Definition, Not Three

Following mathlib practice, this file has **no** parallel formalizations.

- `Felicitous M V c` is the single, model-parameterized definition of
  felicity: a complement is felicitous with a verb predicate iff there
  exists a witness (event + performance/proposition) with the right
  ontological properties.
- `IsRudinModel M` is a class with 30 fields, one per cell. This is
  *the* statement of @cite{rudin-2025b}'s empirical claim — any model
  is tested against it.
- `rudinModel` is the concrete `SpeechVerbs ℕ Bool (FBPerformance Bool)
  (fbOntology Bool)` instantiation — Farkas-Bruce-grounded, with verb
  predicates defined as the postulate RHS so the meaning postulates
  hold by `rfl`.
- `instance : IsRudinModel rudinModel` discharges the 30 cells from
  the postulates + FB ontology axioms.

There is no separate `empirical : Verb → Complement → Felicity`
function and no separate `predicted` decision function. The empirical
matrix and its derivation are the same proposition.
-/

namespace Phenomena.Quotation.Studies.Rudin2025LI

open Semantics.Quotation.Demonstration
open Pragmatics.Assertion.QuotationFBOntology
open Semantics.Dynamic.State
open Semantics.Events

-- ════════════════════════════════════════════════════
-- § 1. Empirical Taxonomy
-- ════════════════════════════════════════════════════

/-- Verbs of speech examined by @cite{rudin-2025b}. -/
inductive Verb
  | say | assert | yell | whisper | ask
  deriving DecidableEq, Repr, Inhabited

/-- Complement types in the Rudin matrix. -/
inductive Complement
  | quoteDecl       -- "Aaron likes apples" (declarative quotation)
  | quoteRising     -- "Aaron likes apples?" (rising declarative)
  | quoteLoud       -- shouted/loud declarative quotation
  | quoteWhispered  -- whispered declarative quotation
  | thatProp        -- *that p* with propositional p
  | thatQuestion    -- *that wh-/Q* with question denotation
  deriving DecidableEq, Repr, Inhabited

/-- Selector: map a `Verb` enum to the corresponding model predicate. -/
def Verb.toPred {Time SemObj Perf : Type*} [LE Time] {Ω : PerformanceOntology Perf}
    (M : SpeechVerbs Time SemObj Perf Ω) : Verb → (Ev Time → Prop)
  | .say => M.SAY
  | .assert => M.ASSERT
  | .yell => M.YELL
  | .whisper => M.WHISPER
  | .ask => M.ASK

-- ════════════════════════════════════════════════════
-- § 2. Felicitous: the SINGLE definition
-- ════════════════════════════════════════════════════

/-- A complement is *felicitous* with a verb predicate in a given
    model iff there exists a witness — an event-and-performance pair
    (for quotative complements) or an event-and-content pair (for
    *that*-clauses) — satisfying the ontological constraints encoded
    by the complement type.

    Quotative complements constrain the REENACTed performance:
    `quoteDecl` requires a committing linguistic performance,
    `quoteRising` a rising declarative, `quoteLoud`/`quoteWhispered`
    a committing performance with the marked volume.

    Propositional complements constrain the CONTENT denotation:
    `thatProp` requires propositional content, `thatQuestion` requires
    question content.

    Verb-class felicity is then *derived*: a verb's postulates impose
    constraints on REENACTed performances (or CONTENT denotations);
    if those constraints conflict with the complement's, no witness
    exists and the cell is infelicitous. -/
def Felicitous {Time SemObj Perf : Type*} [LE Time] {Ω : PerformanceOntology Perf}
    (M : SpeechVerbs Time SemObj Perf Ω) (V : Ev Time → Prop) :
    Complement → Prop
  | .quoteDecl =>
      ∃ e u, V e ∧ M.REENACT e u ∧ Ω.LINGMAT u ∧ Ω.Commits u
  | .quoteRising =>
      ∃ e u, V e ∧ M.REENACT e u ∧ Ω.RisingDecl u
  | .quoteLoud =>
      ∃ e u, V e ∧ M.REENACT e u ∧ Ω.LINGMAT u ∧ Ω.Commits u ∧ Ω.Loud u
  | .quoteWhispered =>
      ∃ e u, V e ∧ M.REENACT e u ∧ Ω.LINGMAT u ∧ Ω.Commits u ∧ Ω.Whispered u
  | .thatProp =>
      ∃ e p, V e ∧ M.CONTENT e p ∧ M.isProposition p
  | .thatQuestion =>
      ∃ e q, V e ∧ M.CONTENT e q ∧ M.isQuestion q

-- ════════════════════════════════════════════════════
-- § 3. IsRudinModel — the empirical claim as a class
-- ════════════════════════════════════════════════════

/-- A `SpeechVerbs` model satisfies @cite{rudin-2025b}'s empirical
    claims about English speech verbs. The 30 fields are exactly the
    cells of the verb × complement felicity matrix.

    This class IS the empirical claim. There is no separate `empirical`
    function whose values must be reconciled with model predictions —
    a model satisfies these facts or it does not. -/
class IsRudinModel {Time SemObj Perf : Type*} [LE Time]
    {Ω : PerformanceOntology Perf} (M : SpeechVerbs Time SemObj Perf Ω) :
    Prop where
  -- say (5 felicitous, 1 infelicitous)
  say_quoteDecl       : Felicitous M M.SAY .quoteDecl
  say_quoteRising     : Felicitous M M.SAY .quoteRising
  say_quoteLoud       : Felicitous M M.SAY .quoteLoud
  say_quoteWhispered  : Felicitous M M.SAY .quoteWhispered
  say_thatProp        : Felicitous M M.SAY .thatProp
  say_thatQuestion    : ¬ Felicitous M M.SAY .thatQuestion
  -- assert (4 felicitous, 2 infelicitous)
  assert_quoteDecl       : Felicitous M M.ASSERT .quoteDecl
  assert_quoteRising     : ¬ Felicitous M M.ASSERT .quoteRising
  assert_quoteLoud       : Felicitous M M.ASSERT .quoteLoud
  assert_quoteWhispered  : Felicitous M M.ASSERT .quoteWhispered
  assert_thatProp        : Felicitous M M.ASSERT .thatProp
  assert_thatQuestion    : ¬ Felicitous M M.ASSERT .thatQuestion
  -- yell (4 felicitous, 2 infelicitous)
  yell_quoteDecl       : Felicitous M M.YELL .quoteDecl
  yell_quoteRising     : Felicitous M M.YELL .quoteRising
  yell_quoteLoud       : Felicitous M M.YELL .quoteLoud
  yell_quoteWhispered  : ¬ Felicitous M M.YELL .quoteWhispered
  yell_thatProp        : Felicitous M M.YELL .thatProp
  yell_thatQuestion    : ¬ Felicitous M M.YELL .thatQuestion
  -- whisper (4 felicitous, 2 infelicitous)
  whisper_quoteDecl       : Felicitous M M.WHISPER .quoteDecl
  whisper_quoteRising     : Felicitous M M.WHISPER .quoteRising
  whisper_quoteLoud       : ¬ Felicitous M M.WHISPER .quoteLoud
  whisper_quoteWhispered  : Felicitous M M.WHISPER .quoteWhispered
  whisper_thatProp        : Felicitous M M.WHISPER .thatProp
  whisper_thatQuestion    : ¬ Felicitous M M.WHISPER .thatQuestion
  -- ask (2 felicitous, 4 infelicitous)
  ask_quoteDecl       : ¬ Felicitous M M.ASK .quoteDecl
  ask_quoteRising     : Felicitous M M.ASK .quoteRising
  ask_quoteLoud       : ¬ Felicitous M M.ASK .quoteLoud
  ask_quoteWhispered  : ¬ Felicitous M M.ASK .quoteWhispered
  ask_thatProp        : ¬ Felicitous M M.ASK .thatProp
  ask_thatQuestion    : Felicitous M M.ASK .thatQuestion

-- ════════════════════════════════════════════════════
-- § 4. Concrete Model: rudinModel
-- ════════════════════════════════════════════════════

/-! We now build a concrete `SpeechVerbs` model over `FBPerformance Bool`
with `fbOntology` as its performance ontology, and show it satisfies
`IsRudinModel`. The model uses ℕ as the time type and Bool as the
semantic-object type (true ↦ proposition, false ↦ question).

Verb predicates are defined as the postulate RHS, so the meaning
postulates hold by `rfl`. The discriminator for verb classes is
`runtime.start` (0 = SAY, 1 = ASSERT, 2 = YELL, 3 = WHISPER, 4 = ASK).
`REENACT` and `CONTENT` are defined per verb class to give the right
witnesses and exclusions. -/

/-- A canonical event for each verb class, indexed by `runtime.start`. -/
def E (n : ℕ) : Ev ℕ := ⟨⟨n, n, le_refl _⟩, .action⟩

/-- The REENACT relation: per verb-class events have different REENACT
    targets, chosen so the postulates' universal quantifiers reduce to
    obvious tautologies (e.g., for SAY events, REENACT only relates to
    LINGMAT performances, so SAY's postulate `∀u, REENACT → LINGMAT`
    is vacuously true). -/
def rudinReenact (e : Ev ℕ) (u : FBPerformance Bool) : Prop :=
  match e.runtime.start with
  | 0 => (fbOntology Bool).LINGMAT u                              -- say
  | 1 => (fbOntology Bool).LINGMAT u ∧ (fbOntology Bool).Commits u  -- assert
  | 2 => (fbOntology Bool).LINGMAT u ∧ (fbOntology Bool).Loud u     -- yell
  | 3 => (fbOntology Bool).LINGMAT u ∧ (fbOntology Bool).Whispered u-- whisper
  | 4 => (fbOntology Bool).RESP u                                  -- ask
  | _ => False

/-- The CONTENT relation: SAY-class events take propositional (true)
    content; ASK-class events take question (false) content; other
    events have no propositional content. -/
def rudinContent (e : Ev ℕ) (b : Bool) : Prop :=
  match e.runtime.start with
  | 0 | 1 | 2 | 3 => b = true
  | 4 => b = false
  | _ => False

/-- Verb predicates: defined as the postulate RHS so the iff-axioms
    hold by `rfl`. -/
def rudinSay     (e : Ev ℕ) : Prop :=
  ∀ u, rudinReenact e u → (fbOntology Bool).LINGMAT u
def rudinAssert  (e : Ev ℕ) : Prop :=
  rudinSay e ∧ ∀ u, rudinReenact e u → (fbOntology Bool).Commits u
def rudinAsk     (e : Ev ℕ) : Prop :=
  ∀ u, rudinReenact e u → (fbOntology Bool).RESP u
def rudinYell    (e : Ev ℕ) : Prop :=
  rudinSay e ∧ ∀ u, rudinReenact e u → (fbOntology Bool).Loud u
def rudinWhisper (e : Ev ℕ) : Prop :=
  rudinSay e ∧ ∀ u, rudinReenact e u → (fbOntology Bool).Whispered u

/-- A non-LINGMAT RESP performance: a non-linguistic, non-rising
    interrogative (e.g., a wordless interrogative gesture). Its
    update is `askPolarQuestion`, which pushes an issue without
    committing. Used to falsify `SAY` for ASK-class events. -/
def respNonLingmat : FBPerformance Bool :=
  { form := .interrogative, content := fun _ => true,
    lingmat := false, volume := .neutral, rising := false }

theorem respNonLingmat_resp : (fbOntology Bool).RESP respNonLingmat := by
  refine ⟨?_, ?_⟩
  · -- RaisesIssue
    show (respNonLingmat.update DiscourseState.empty).table ≠ []
    intro h; cases h
  · -- ¬ Commits
    show ¬ (respNonLingmat.content ∈ (respNonLingmat.update DiscourseState.empty).dcS)
    intro h
    exact List.not_mem_nil h

theorem respNonLingmat_not_lingmat : ¬ (fbOntology Bool).LINGMAT respNonLingmat := by
  intro h
  cases h with
  | inl h => cases h
  | inr h => cases h

/-! ### Witness performances

Concrete `FBPerformance` witnesses with named property proofs. Each
witness pins down the exact field configuration that makes a particular
cell of the matrix felicitous, and is referenced both in `rudinModel`'s
postulate proofs and in the `IsRudinModel` instance discharge. -/

/-- A neutral committing declarative performance. -/
def committingDecl : FBPerformance Bool :=
  { form := .declarative, content := fun _ => true,
    lingmat := true, volume := .neutral, rising := false }

theorem committingDecl_lingmat : (fbOntology Bool).LINGMAT committingDecl :=
  Or.inl rfl

theorem committingDecl_commits : (fbOntology Bool).Commits committingDecl := by
  show committingDecl.content ∈ (committingDecl.update DiscourseState.empty).dcS
  simp [FBPerformance.update, DiscourseState.assertDeclarative,
        DiscourseState.addToDcS, DiscourseState.pushIssue,
        DiscourseState.empty, committingDecl]

/-- A loud committing declarative performance. -/
def committingLoud : FBPerformance Bool :=
  { form := .declarative, content := fun _ => true,
    lingmat := true, volume := .loud, rising := false }

theorem committingLoud_lingmat : (fbOntology Bool).LINGMAT committingLoud :=
  Or.inl rfl

theorem committingLoud_loud : (fbOntology Bool).Loud committingLoud := rfl

theorem committingLoud_commits : (fbOntology Bool).Commits committingLoud := by
  show committingLoud.content ∈ (committingLoud.update DiscourseState.empty).dcS
  simp [FBPerformance.update, DiscourseState.assertDeclarative,
        DiscourseState.addToDcS, DiscourseState.pushIssue,
        DiscourseState.empty, committingLoud]

/-- A whispered committing declarative performance. -/
def committingWhispered : FBPerformance Bool :=
  { form := .declarative, content := fun _ => true,
    lingmat := true, volume := .whispered, rising := false }

theorem committingWhispered_lingmat : (fbOntology Bool).LINGMAT committingWhispered :=
  Or.inl rfl

theorem committingWhispered_whispered :
    (fbOntology Bool).Whispered committingWhispered := rfl

theorem committingWhispered_commits :
    (fbOntology Bool).Commits committingWhispered := by
  show committingWhispered.content ∈
       (committingWhispered.update DiscourseState.empty).dcS
  simp [FBPerformance.update, DiscourseState.assertDeclarative,
        DiscourseState.addToDcS, DiscourseState.pushIssue,
        DiscourseState.empty, committingWhispered]

/-- A rising-declarative performance (RESP, not committing). -/
def risingDecl : FBPerformance Bool :=
  { form := .declarative, content := fun _ => true,
    lingmat := true, volume := .neutral, rising := true }

theorem risingDecl_rd : (fbOntology Bool).RisingDecl risingDecl := ⟨rfl, rfl⟩

theorem risingDecl_resp : (fbOntology Bool).RESP risingDecl :=
  (fbOntology Bool).rd_is_resp _ ⟨rfl, rfl⟩

/-- A loud rising-declarative performance. -/
def risingLoud : FBPerformance Bool :=
  { form := .declarative, content := fun _ => true,
    lingmat := true, volume := .loud, rising := true }

theorem risingLoud_rd : (fbOntology Bool).RisingDecl risingLoud := ⟨rfl, rfl⟩

theorem risingLoud_lingmat : (fbOntology Bool).LINGMAT risingLoud := Or.inr rfl

theorem risingLoud_loud : (fbOntology Bool).Loud risingLoud := rfl

/-- A whispered rising-declarative performance. -/
def risingWhispered : FBPerformance Bool :=
  { form := .declarative, content := fun _ => true,
    lingmat := true, volume := .whispered, rising := true }

theorem risingWhispered_rd : (fbOntology Bool).RisingDecl risingWhispered :=
  ⟨rfl, rfl⟩

theorem risingWhispered_whispered :
    (fbOntology Bool).Whispered risingWhispered := rfl

/-- The Rudin model: a concrete `SpeechVerbs` instantiation over
    `FBPerformance Bool` with `fbOntology` as its performance ontology.
    Each meaning postulate holds by `rfl` since the verb predicates
    are defined as the postulate RHS. -/
def rudinModel : SpeechVerbs ℕ Bool (FBPerformance Bool) (fbOntology Bool) where
  SAY := rudinSay
  ASSERT := rudinAssert
  ASK := rudinAsk
  YELL := rudinYell
  WHISPER := rudinWhisper
  CONTENT := rudinContent
  REENACT := rudinReenact
  isProposition b := b = true
  isQuestion b := b = false
  say_iff_lingmat _ := Iff.rfl
  ask_iff_resp _ := Iff.rfl
  assert_iff_say_and_commits _ := Iff.rfl
  yell_iff_say_and_loud _ := Iff.rfl
  whisper_iff_say_and_whispered _ := Iff.rfl
  content_say_propositional := by
    intro e p hsay hcont
    -- For e.runtime.start ∈ {0,1,2,3}, rudinContent e p = (p = true)
    -- For e.runtime.start = 4, rudinContent e p = (p = false), but then
    --   hsay forces False via respNonLingmat (RESP but not LINGMAT)
    -- For e.runtime.start ≥ 5, rudinContent e p = False, contradiction
    show p = true
    unfold rudinContent at hcont
    unfold rudinSay rudinReenact at hsay
    match h : e.runtime.start with
    | 0 => rw [h] at hcont; exact hcont
    | 1 => rw [h] at hcont; exact hcont
    | 2 => rw [h] at hcont; exact hcont
    | 3 => rw [h] at hcont; exact hcont
    | 4 =>
      -- ASK-class event: hsay says ∀u, RESP u → LINGMAT u
      -- but respNonLingmat is RESP and not LINGMAT — contradiction
      exfalso
      rw [h] at hsay
      exact respNonLingmat_not_lingmat (hsay respNonLingmat respNonLingmat_resp)
    | n + 5 =>
      rw [h] at hcont
      exact hcont.elim
  content_ask_question := by
    intro e q hask hcont
    show q = false
    unfold rudinContent at hcont
    unfold rudinAsk rudinReenact at hask
    match h : e.runtime.start with
    | 0 =>
      -- SAY-class: hask says ∀u, LINGMAT u → RESP u. False (committing
      -- LINGMAT performance is not RESP). Use a committing decl.
      exfalso
      rw [h] at hask
      have hcommit : (fbOntology Bool).Commits committingDecl := committingDecl_commits
      have hlingmat : (fbOntology Bool).LINGMAT committingDecl := committingDecl_lingmat
      exact (hask committingDecl hlingmat).2 hcommit
    | 1 =>
      exfalso
      rw [h] at hask
      have h1 : (fbOntology Bool).LINGMAT committingDecl ∧
                (fbOntology Bool).Commits committingDecl :=
        ⟨committingDecl_lingmat, committingDecl_commits⟩
      exact (hask committingDecl h1).2 committingDecl_commits
    | 2 =>
      exfalso
      rw [h] at hask
      have h1 : (fbOntology Bool).LINGMAT committingLoud ∧
                (fbOntology Bool).Loud committingLoud :=
        ⟨committingLoud_lingmat, committingLoud_loud⟩
      exact (hask committingLoud h1).2 committingLoud_commits
    | 3 =>
      exfalso
      rw [h] at hask
      have h1 : (fbOntology Bool).LINGMAT committingWhispered ∧
                (fbOntology Bool).Whispered committingWhispered :=
        ⟨committingWhispered_lingmat, committingWhispered_whispered⟩
      exact (hask committingWhispered h1).2 committingWhispered_commits
    | 4 => rw [h] at hcont; exact hcont
    | n + 5 => rw [h] at hcont; exact hcont.elim
  prop_not_question := by
    intro p hp hq
    show False
    rw [hp] at hq
    cases hq

-- ════════════════════════════════════════════════════
-- § 5. The IsRudinModel instance
-- ════════════════════════════════════════════════════

/-- All 30 cells of @cite{rudin-2025b}'s empirical matrix are derived
    from the FB-grounded model + the SpeechVerbs postulates. -/
instance : IsRudinModel rudinModel := by
  refine
    { -- ─── say ───
      say_quoteDecl := ?_, say_quoteRising := ?_, say_quoteLoud := ?_,
      say_quoteWhispered := ?_, say_thatProp := ?_, say_thatQuestion := ?_,
      -- ─── assert ───
      assert_quoteDecl := ?_, assert_quoteRising := ?_, assert_quoteLoud := ?_,
      assert_quoteWhispered := ?_, assert_thatProp := ?_, assert_thatQuestion := ?_,
      -- ─── yell ───
      yell_quoteDecl := ?_, yell_quoteRising := ?_, yell_quoteLoud := ?_,
      yell_quoteWhispered := ?_, yell_thatProp := ?_, yell_thatQuestion := ?_,
      -- ─── whisper ───
      whisper_quoteDecl := ?_, whisper_quoteRising := ?_, whisper_quoteLoud := ?_,
      whisper_quoteWhispered := ?_, whisper_thatProp := ?_,
      whisper_thatQuestion := ?_,
      -- ─── ask ───
      ask_quoteDecl := ?_, ask_quoteRising := ?_, ask_quoteLoud := ?_,
      ask_quoteWhispered := ?_, ask_thatProp := ?_, ask_thatQuestion := ?_ }
  -- say_quoteDecl
  · exact ⟨E 0, committingDecl, fun _ h => h, committingDecl_lingmat,
           committingDecl_lingmat, committingDecl_commits⟩
  -- say_quoteRising
  · refine ⟨E 0, risingDecl, fun _ h => h, ?_, risingDecl_rd⟩
    exact (Or.inl rfl)
  -- say_quoteLoud
  · refine ⟨E 0, committingLoud, fun _ h => h, committingLoud_lingmat,
            committingLoud_lingmat, committingLoud_commits, committingLoud_loud⟩
  -- say_quoteWhispered
  · refine ⟨E 0, committingWhispered, fun _ h => h, committingWhispered_lingmat,
            committingWhispered_lingmat, committingWhispered_commits,
            committingWhispered_whispered⟩
  -- say_thatProp
  · exact ⟨E 0, true, fun _ h => h, rfl, rfl⟩
  -- say_thatQuestion
  · rintro ⟨e, q, hsay, hcont, hq⟩
    have : q = true := rudinModel.content_say_propositional e q hsay hcont
    rw [this] at hq
    cases hq
  -- assert_quoteDecl
  · refine ⟨E 1, committingDecl, ?_, ⟨committingDecl_lingmat, committingDecl_commits⟩,
            committingDecl_lingmat, committingDecl_commits⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- assert_quoteRising
  · rintro ⟨e, u, ⟨_, hcom⟩, hreen, hrd⟩
    exact (fbOntology Bool).rd_not_commits u hrd (hcom u hreen)
  -- assert_quoteLoud
  · refine ⟨E 1, committingLoud, ?_, ⟨committingLoud_lingmat, committingLoud_commits⟩,
            committingLoud_lingmat, committingLoud_commits, committingLoud_loud⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- assert_quoteWhispered
  · refine ⟨E 1, committingWhispered, ?_,
            ⟨committingWhispered_lingmat, committingWhispered_commits⟩,
            committingWhispered_lingmat, committingWhispered_commits,
            committingWhispered_whispered⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- assert_thatProp
  · refine ⟨E 1, true, ?_, rfl, rfl⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- assert_thatQuestion
  · rintro ⟨e, q, hass, hcont, hq⟩
    have hsay : rudinModel.SAY e := hass.1
    have : q = true := rudinModel.content_say_propositional e q hsay hcont
    rw [this] at hq
    cases hq
  -- yell_quoteDecl
  · refine ⟨E 2, committingLoud, ?_, ⟨committingLoud_lingmat, committingLoud_loud⟩,
            committingLoud_lingmat, committingLoud_commits⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- yell_quoteRising
  · refine ⟨E 2, risingLoud, ?_, ⟨risingLoud_lingmat, risingLoud_loud⟩, risingLoud_rd⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- yell_quoteLoud
  · refine ⟨E 2, committingLoud, ?_, ⟨committingLoud_lingmat, committingLoud_loud⟩,
            committingLoud_lingmat, committingLoud_commits, committingLoud_loud⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- yell_quoteWhispered
  · rintro ⟨e, u, ⟨_, hloud⟩, hreen, _, _, hwh⟩
    exact (fbOntology Bool).loud_not_whispered u (hloud u hreen) hwh
  -- yell_thatProp
  · refine ⟨E 2, true, ?_, rfl, rfl⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- yell_thatQuestion
  · rintro ⟨e, q, hyell, hcont, hq⟩
    have hsay : rudinModel.SAY e := hyell.1
    have : q = true := rudinModel.content_say_propositional e q hsay hcont
    rw [this] at hq
    cases hq
  -- whisper_quoteDecl
  · refine ⟨E 3, committingWhispered, ?_,
            ⟨committingWhispered_lingmat, committingWhispered_whispered⟩,
            committingWhispered_lingmat, committingWhispered_commits⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- whisper_quoteRising
  · refine ⟨E 3, risingWhispered, ?_,
            ⟨Or.inr rfl, risingWhispered_whispered⟩, risingWhispered_rd⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- whisper_quoteLoud
  · rintro ⟨e, u, ⟨_, hwh⟩, hreen, _, _, hloud⟩
    exact (fbOntology Bool).loud_not_whispered u hloud (hwh u hreen)
  -- whisper_quoteWhispered
  · refine ⟨E 3, committingWhispered, ?_,
            ⟨committingWhispered_lingmat, committingWhispered_whispered⟩,
            committingWhispered_lingmat, committingWhispered_commits,
            committingWhispered_whispered⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- whisper_thatProp
  · refine ⟨E 3, true, ?_, rfl, rfl⟩
    refine ⟨fun u h => h.1, fun u h => h.2⟩
  -- whisper_thatQuestion
  · rintro ⟨e, q, hwhis, hcont, hq⟩
    have hsay : rudinModel.SAY e := hwhis.1
    have : q = true := rudinModel.content_say_propositional e q hsay hcont
    rw [this] at hq
    cases hq
  -- ask_quoteDecl
  · rintro ⟨e, u, hask, hreen, _, hcom⟩
    exact ((rudinModel.ask_iff_resp e).mp hask u hreen).2 hcom
  -- ask_quoteRising
  · refine ⟨E 4, risingDecl, ?_, risingDecl_resp, risingDecl_rd⟩
    intro u h; exact h
  -- ask_quoteLoud
  · rintro ⟨e, u, hask, hreen, _, hcom, _⟩
    exact ((rudinModel.ask_iff_resp e).mp hask u hreen).2 hcom
  -- ask_quoteWhispered
  · rintro ⟨e, u, hask, hreen, _, hcom, _⟩
    exact ((rudinModel.ask_iff_resp e).mp hask u hreen).2 hcom
  -- ask_thatProp
  · rintro ⟨e, q, hask, hcont, hp⟩
    have hq : rudinModel.isQuestion q :=
      rudinModel.content_ask_question e q hask hcont
    exact rudinModel.prop_not_question q hp hq
  -- ask_thatQuestion
  · refine ⟨E 4, false, ?_, rfl, rfl⟩
    intro u h; exact h

-- ════════════════════════════════════════════════════
-- § 6. Fragment Verb Bridge
-- ════════════════════════════════════════════════════

/-- Classify an English `VerbEntry` into the Rudin verb taxonomy.
    Returns `none` for verbs that don't fall into the matrix (e.g.,
    *tell* requires a recipient; *think* is not a speech act).

    Reads directly off Fragment fields — `speechActVerb`,
    `takesQuestionBase`, `levinClass`, and surface `form` — so the
    classification stays in sync with Fragment edits. -/
def fromEnglishVerb (v : Fragments.English.Predicates.Verbal.VerbEntry) :
    Option Verb :=
  if !v.speechActVerb then none
  else if v.takesQuestionBase then some .ask
  else match v.levinClass with
    | some .say => some .say
    | some .mannerOfSpeaking =>
      match v.form with
      | "yell" | "shout" | "scream" | "shriek" => some .yell
      | "whisper" | "murmur" | "mumble" | "mutter" => some .whisper
      | _ => none
    | _ => none

/-! ### Per-entry classification witnesses

These `example`s pin individual Fragment verbs to the Rudin taxonomy.
Renaming or reclassifying any of these verbs in the Fragment will
break exactly the relevant witness, surfacing the inconsistency. -/

example : fromEnglishVerb Fragments.English.Predicates.Verbal.say     = some .say     := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.claim   = some .say     := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.whisper = some .whisper := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.murmur  = some .whisper := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.mumble  = some .whisper := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.mutter  = some .whisper := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.yell    = some .yell    := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.shout   = some .yell    := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.scream  = some .yell    := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.shriek  = some .yell    := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.ask     = some .ask     := rfl

/-! ### Negative cases — verbs outside the Rudin matrix -/

example : fromEnglishVerb Fragments.English.Predicates.Verbal.tell   = none := rfl
example : fromEnglishVerb Fragments.English.Predicates.Verbal.wonder = none := rfl

end Phenomena.Quotation.Studies.Rudin2025LI
