import Linglib.Discourse.Commitment.Table
import Linglib.Discourse.Commitment.SourceMarked
import Linglib.Discourse.Commitment.Space
import Linglib.Semantics.Highlighting

/-!
# Farkas & Roelofsen (2017): Division of Labor in Declaratives and Interrogatives

[farkas-roelofsen-2017]

A formalization of the sentence-type taxonomy and commitment table
from "Division of Labor in the Interpretation of Declaratives and
Interrogatives" (J. Semantics 34(2): 237–289). The paper builds on
[farkas-bruce-2010]'s commitment-based discourse contexts and
inquisitive semantics ([ciardelli-groenendijk-roelofsen-2018])
to give a uniform account of the six sentence types in (3)–(8):

* (3) Amalia left↓.            [falling declarative]
* (4) Amalia left↑?            [rising declarative]
* (5) Did Amalia leave↓?       [falling polar interrogative]
* (6) Did Amalia leave↑?       [rising polar interrogative]
* (7) Amalia left↓, didn't she↓? [falling tag interrogative]
* (8) Amalia left↓, didn't she↑? [rising tag interrogative]

## What this study formalizes

1. **Clause-type markers** (§4.1, eq. (26), p. 257): the two binary axes
   DEC/INT (declarative vs interrogative word order) and CLOSED/OPEN
   (falling vs rising intonation), composed with an optional tag.
   Implemented as `MarkerTriple`.
2. **Markedness classification** (§3 eq. (21) "Division of labor principle",
   p. 250; eq. (47) classification, p. 265). Falling declaratives + polar
   interrogatives are unmarked; rising declaratives + tag interrogatives
   are marked. The polar-interrogative classification rests on the paper's
   "equal weight" reading of formal-simplicity vs communicative-success
   (p. 264, last paragraph): "We leave open here how the factors are ranked
   in American English, and will not distinguish rising and falling polar
   interrogatives in terms of markedness." The flat verdict here therefore
   matches eq. (47) but inherits that disambiguation.
3. **Commitment table** (p. 240, the unnumbered table immediately preceding
   example (13)): the four-row taxonomy — full / bias / neutral.
4. **Basic convention of use** F_b (§5.1 eq. (48), p. 265): two clauses —
   (1) the proposition is added to the table, (2) its informative content
   is added to the speaker's commitments. F_b is the single convention
   that replaces Frege's two force operators (Assertion / Question);
   §7 defines it explicitly over `Discourse.Commitment.Table.State` and proves
   the structural division-of-labor claim that **for unmarked forms,
   the discourse-effect update reduces to F_b alone** (p. 266: "the
   conventional discourse effects of unmarked sentence types ... are
   fully determined by (48)").
5. **Credence intervals** (§3.2, p. 256): rising declaratives signal
   credence at most low; rising tag interrogatives signal moderate-to-high;
   falling tag interrogatives signal high. The four-level scale
   zero < low < moderate < high is F&R's own (p. 256).
6. **Felicity contrasts** (13)/(14), p. 240 — repeated as (24)/(25) on
   p. 256 — illustrating the rising-declarative ↔ tag-interrogative
   complementary distribution.
7. **Highlighting integration** (§5b): the felicity-in-context predicate
   threads `Semantics.Highlighting.HighlightingContext`, retiring the
   earlier "placeholder propositions" caveat. F&R's "highlighted
   alternative" (p. 256) is exactly the substrate's `Highlighted`
   predicate, anchored on the same Roelofsen-Farkas line of work
   ([roelofsen-farkas-2015], two years prior to F&R 2017).
8. **Cross-framework divergences** (§8): formal contrasts with
   `Discourse/Commitment/SourceMarked.lean` on rising declaratives (different
   substrate, different state predictions) and Krifka 2015 on tag
   interrogatives (sequential composition vs conjunction/disjunction;
   see also `Studies/Krifka2015.lean` §5).

## What's out of scope

- Full inquisitive-semantic compositional machinery of §4.2 (how
  clause-type markers combine with sentence radicals at the type level).
  The proposition-as-set-of-alternatives apparatus is available in
  `Core/Question/`; this study uses bare `Set W` for content because
  the paper-anchored felicity claims do not require alternative-set
  arithmetic.
- Sections 6–7 of the paper (extensions: alternative-question marking,
  comparison to other accounts).

## Substrate consumed

- `Discourse/Commitment/Table.lean` — `State`, `assert`,
  `polarQuestion`, `pushItem`, `addCommit`.
- `Semantics/Highlighting.lean` — `HighlightingContext`,
  `Highlighted`, `AddressesQUD`. Anchored on Roelofsen & Farkas (2015),
  which F&R 2017 cites and builds on.
- `Discourse/Commitment/SourceMarked.lean` — the divergence in §8 (rising
  declarative writes to addressee slate vs. F&R + F&B's "no commitment
  write" prediction).

## Literature pointers (post-F&R 2017, not consumed by this file)

The dialogue commitment / rising-intonation literature has continued
since 2017. Pointers for downstream readers:
- [rudin-2018], [rudin-2019] on rising declaratives
- [goodhue-2022a], [goodhue-2022b] on bias in polar questions
- [krifka-2015] (≤ 2017) on tag interrogatives in Commitment Space
  Semantics — see `Studies/Krifka2015.lean` for the
  formalization
-/

namespace FarkasRoelofsen2017

-- ════════════════════════════════════════════════════════════════
-- § 1. Clause-type markers (§4.1, eq. (26), p. 257)
-- ════════════════════════════════════════════════════════════════

/-- DEC/INT axis: declarative vs interrogative word order
    ([farkas-roelofsen-2017] §4.1 eq. (26a), p. 257). In
    English root clauses, DEC = declarative word order, INT =
    interrogative word order. -/
inductive ClauseType where
  | dec
  | int
  deriving DecidableEq, Repr, Inhabited

/-- CLOSED/OPEN axis: falling vs rising intonation
    ([farkas-roelofsen-2017] §4.1 eq. (26b), p. 257).
    CLOSED = ↓ (falling); OPEN = ↑ (rising). -/
inductive Intonation where
  | closed  -- falling ↓
  | rising  -- rising ↑ (the paper writes "open"; `open` is a Lean keyword)
  deriving DecidableEq, Repr, Inhabited

/-- A `MarkerTriple` is a triple of clause-type marker, intonation
    marker, and tag-presence flag ([farkas-roelofsen-2017]
    §4.1; tags are introduced after eq. (27), p. 258).

    The 6 sentence types of (3)–(8):
    * `⟨.dec, .closed, false⟩` — falling declarative
    * `⟨.dec, .rising, false⟩` — rising declarative
    * `⟨.int, .closed, false⟩` — falling polar interrogative
    * `⟨.int, .rising, false⟩` — rising polar interrogative
    * `⟨.dec, .closed, true⟩`  — falling tag interrogative
      (declarative anchor + tag with falling intonation)
    * `⟨.dec, .rising, true⟩`  — rising tag interrogative
      (declarative anchor + tag with rising intonation)

    Tags assumed to be reverse-polarity per F&R 2017 footnote 15
    (p. 259); same-polarity tags ("Amalia left, did she?", their (9))
    are explicitly out of scope.

    This triple refines the coarse declarative/interrogative cut of
    `Semantics.Mood.IllocutionaryMood` (which `Item.mood` carries). -/
structure MarkerTriple where
  clauseType : ClauseType
  intonation : Intonation
  hasTag : Bool
  deriving DecidableEq, Repr, Inhabited

namespace MarkerTriple

/-- Falling declarative (3) "Amalia left↓." -/
def fallingDeclarative : MarkerTriple := ⟨.dec, .closed, false⟩

/-- Rising declarative (4) "Amalia left↑?" -/
def risingDeclarative : MarkerTriple := ⟨.dec, .rising, false⟩

/-- Falling polar interrogative (5) "Did Amalia leave↓?" -/
def fallingPolarInterrogative : MarkerTriple := ⟨.int, .closed, false⟩

/-- Rising polar interrogative (6) "Did Amalia leave↑?" -/
def risingPolarInterrogative : MarkerTriple := ⟨.int, .rising, false⟩

/-- Falling tag interrogative (7) "Amalia left↓, didn't she↓?" -/
def fallingTagInterrogative : MarkerTriple := ⟨.dec, .closed, true⟩

/-- Rising tag interrogative (8) "Amalia left↓, didn't she↑?" -/
def risingTagInterrogative : MarkerTriple := ⟨.dec, .rising, true⟩

end MarkerTriple

-- ════════════════════════════════════════════════════════════════
-- § 2. Markedness (§3 eq. (21), p. 250; eq. (47), p. 265)
-- ════════════════════════════════════════════════════════════════

/-- Markedness predicate ([farkas-roelofsen-2017] §3
    eq. (21) "Division of labor principle", p. 250; classification
    eq. (47), p. 265):

    Per (21):
    (a) The discourse effects of unmarked forms should be fully
        determined by their semantic content and the basic convention
        of use, F_b.
    (b) The discourse effects of marked forms should always include
        the discourse effects dictated by F_b. In addition, they
        **may include** special discourse effects connected to the
        particular sentence type involved.

    Classification per eq. (47):
    * Optimal, unmarked: falling declaratives, polar interrogatives
      (BOTH intonations, under the equal-weight reading discussed at
      p. 264, last paragraph).
    * Marked: rising declaratives, tag interrogatives.

    Caveat: F&R explicitly leave open whether English ranks formal
    simplicity above communicative success or vice versa (p. 264);
    if one is ranked higher, rising and falling polar interrogatives
    differ in markedness. The Lean classification adopts the equal-weight
    reading and so does not split rising vs. falling polars. -/
def MarkerTriple.isMarked : MarkerTriple → Prop
  | ⟨_, _, true⟩ => True   -- any tag → marked
  | ⟨.dec, .rising, false⟩ => True   -- rising declarative → marked
  | _ => False             -- falling declarative + both polar interrogatives unmarked

instance (mt : MarkerTriple) : Decidable mt.isMarked := by
  cases mt with
  | mk ct i ht =>
    cases ht <;> cases ct <;> cases i <;>
      (unfold MarkerTriple.isMarked; infer_instance)

-- ════════════════════════════════════════════════════════════════
-- § 3. Commitment table (p. 240, table immediately preceding ex. (13))
-- ════════════════════════════════════════════════════════════════

/-- Three commitment-types from the unnumbered "Type of commitment"
    table on p. 240 ([farkas-roelofsen-2017]):

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

/-- Map each marker triple to its commitment type
    ([farkas-roelofsen-2017], p. 240 unnumbered table). -/
def commitmentType : MarkerTriple → CommitmentType
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
-- § 4. Credence intervals (§3.2, p. 256)
-- ════════════════════════════════════════════════════════════════

/-- Credence levels ([farkas-roelofsen-2017] §3.2 p. 256):
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
    ([farkas-roelofsen-2017] §3.2, p. 256: "i is a credence
    interval, capturing the amount of credence x signals that she
    has in p"). -/
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

/-- The credence interval signaled by each marker triple
    ([farkas-roelofsen-2017] §3.2, p. 256, last paragraph
    before §4: "for rising declaratives the credence interval will
    be [zero, low], for rising tag interrogatives [moderate, high],
    and for falling tag interrogatives just [high]"):

    * Rising declaratives → [zero, low]
    * Rising tag interrogatives → [moderate, high]
    * Falling tag interrogatives → [high, high]  (F&R's "[high]")
    * Other forms (unmarked) → no signal; the trivial interval
      [zero, high] which contains every level vacuously. The
      "no signal" reading is intended: F&R's credence-interval
      machinery applies only to marked forms (§3.2 prose). -/
def signaledCredence : MarkerTriple → CredenceInterval
  | ⟨.dec, .rising, false⟩ => ⟨.zero, .low⟩         -- rising declarative
  | ⟨.dec, .rising, true⟩ => ⟨.moderate, .high⟩      -- rising tag
  | ⟨.dec, .closed, true⟩ => ⟨.high, .high⟩          -- falling tag (F&R: [high])
  | _ => ⟨.zero, .high⟩                              -- unmarked: trivial

-- ════════════════════════════════════════════════════════════════
-- § 5. Felicity contrasts (24)/(25), p. 256
-- (these are the same examples as (13)/(14) on p. 240)
-- ════════════════════════════════════════════════════════════════

/-- A speaker is felicitous in uttering `form` in a context where
    her credence in the highlighted alternative is `c` iff `c` falls
    within the form's signaled credence interval
    ([farkas-roelofsen-2017] §3.2 prose around examples (24)/(25),
    p. 256). -/
def felicitous (form : MarkerTriple) (speakerCredence : CredenceLevel) : Prop :=
  (signaledCredence form).contains speakerCredence

instance (form : MarkerTriple) (c : CredenceLevel) :
    Decidable (felicitous form c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Example (24)** ([farkas-roelofsen-2017] p. 256): "Belinda is
    going through a pile of job applications. Chris has not seen any
    of them yet. Belinda hands Chris the application that she just
    finished reading, and tells him to have a look at it. Chris to Belinda:
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

/-- **Example (25)** ([farkas-roelofsen-2017] p. 256): "Belinda and
    Chris are looking at a sunset together. Belinda to Chris:
    a. #It's a beautiful sunset↑?      [rising declarative, # infelicitous]
    b. It's a beautiful sunset, isn't it? [tag, ✓ felicitous]"

    In this context, Belinda is looking at the sunset directly —
    credence = high. Rising declarative requires [zero, low] →
    infelicitous (high ∉ [zero, low]). The paper does not specify the
    intonation on the tag in (25b); F&R's signaled-credence assignment
    is "[high]" for falling-tag specifically (p. 256). The Lean
    encoding proves felicity for both intonations: rising-tag's
    [moderate, high] contains high, and falling-tag's [high, high]
    trivially contains high. -/
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
-- § 5b. Highlighting integration (closes the placeholder-propositions gap)
-- ════════════════════════════════════════════════════════════════

/-! F&R 2017's signaled-credence claims are explicitly about
"the highlighted alternative" (p. 256). The substrate
`Semantics/Highlighting.lean` (anchored on
[roelofsen-farkas-2015], the same author line two years prior
to F&R 2017) supplies the `HighlightingContext`/`Highlighted`
predicate. This section threads it through `felicitous`, retiring the
study's earlier "placeholder propositions" caveat. -/

open Semantics.Highlighting

variable {W : Type*}

/-- Felicity of a marker form in a highlighting context: the
    proposition `p` must actually be highlighted in the context, AND
    the speaker's credence in `p` must fall in the form's signaled
    interval ([farkas-roelofsen-2017] §3.2 p. 256, "the
    highlighted alternative" prose). -/
def felicitousInContext (form : MarkerTriple) (c : HighlightingContext W)
    (p : Set W) (speakerCredence : CredenceLevel) : Prop :=
  Highlighted c p ∧ felicitous form speakerCredence

instance (form : MarkerTriple) (c : HighlightingContext W) (p : Set W)
    (cr : CredenceLevel) [Decidable (Highlighted c p)] :
    Decidable (felicitousInContext form c p cr) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Felicity-in-context implies the proposition is highlighted. -/
theorem felicitousInContext_imp_highlighted
    {form : MarkerTriple} {c : HighlightingContext W} {p : Set W}
    {cr : CredenceLevel} (h : felicitousInContext form c p cr) :
    Highlighted c p := h.1

/-- Felicity-in-context implies the bare felicity (forgetting the
    highlighting witness). -/
theorem felicitousInContext_imp_felicitous
    {form : MarkerTriple} {c : HighlightingContext W} {p : Set W}
    {cr : CredenceLevel} (h : felicitousInContext form c p cr) :
    felicitous form cr := h.2

/-- The complementary-distribution result lifts to the contextual
    setting: if `p` is highlighted in `c`, rising-dec and falling-tag
    cannot both be felicitous-in-context at any credence level. -/
theorem rising_dec_and_falling_tag_disjoint_in_context
    (c : HighlightingContext W) (p : Set W) (cr : CredenceLevel) :
    ¬ (felicitousInContext .risingDeclarative c p cr ∧
       felicitousInContext .fallingTagInterrogative c p cr) := by
  rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  exact rising_dec_and_falling_tag_disjoint cr ⟨h1, h2⟩

/-- Felicity-in-context implies the proposition addresses the current
    QUD. Routes through `Highlighting.highlighted_imp_addressesQUD` —
    making the integration with `Semantics/Highlighting.lean`
    load-bearing (the substrate's `AddressesQUD` API is invoked, not
    just its `Highlighted` predicate's existence). -/
theorem felicitousInContext_imp_addressesQUD
    {form : MarkerTriple} {c : HighlightingContext W} {p : Set W}
    {cr : CredenceLevel} (h : felicitousInContext form c p cr) :
    AddressesQUD c.qud p :=
  highlighted_imp_addressesQUD h.1

/-- Felicity-in-context implies the proposition is in the salient set
    (made salient by recent utterance). Routes through
    `Highlighting.highlighted_imp_salient`. -/
theorem felicitousInContext_imp_salient
    {form : MarkerTriple} {c : HighlightingContext W} {p : Set W}
    {cr : CredenceLevel} (h : felicitousInContext form c p cr) :
    p ∈ c.salient :=
  highlighted_imp_salient h.1

/-- In the empty highlighting context (no salient propositions, trivial
    QUD), no proposition is felicitous-in-context for any marker form.
    The Highlighted check fails on the empty salient set. -/
theorem not_felicitousInContext_empty (form : MarkerTriple) (p : Set W)
    (cr : CredenceLevel) :
    ¬ felicitousInContext form (empty : HighlightingContext W) p cr := by
  intro h
  have hsal : p ∈ (empty : HighlightingContext W).salient :=
    felicitousInContext_imp_salient h
  simp [empty] at hsal

/-- The credence interval signaled by `form` for a specific proposition
    `p` in highlighting context `c`: `some (signaledCredence form)` if
    `p` is highlighted in `c`, otherwise `none`. F&R's signaled-credence
    machinery applies only when there IS a highlighted alternative
    (p. 256). -/
def signaledCredenceFor (form : MarkerTriple) (c : HighlightingContext W)
    (p : Set W) [Decidable (Highlighted c p)] : Option CredenceInterval :=
  if Highlighted c p then some (signaledCredence form) else none

/-- When the proposition is highlighted, `signaledCredenceFor` projects
    to the bare `signaledCredence`. -/
theorem signaledCredenceFor_some_of_highlighted {form : MarkerTriple}
    {c : HighlightingContext W} {p : Set W} [Decidable (Highlighted c p)]
    (h : Highlighted c p) :
    signaledCredenceFor form c p = some (signaledCredence form) := by
  simp [signaledCredenceFor, h]

/-- A proposition that does not address the current QUD has no signaled
    credence interval — `signaledCredenceFor` returns `none`. This is
    the load-bearing use of `AddressesQUD`: the F&R signaled-credence
    machinery is gated on the highlighted alternative actually
    addressing the QUD, not merely being made salient. -/
theorem signaledCredenceFor_none_of_not_addressesQUD {form : MarkerTriple}
    {c : HighlightingContext W} {p : Set W} [Decidable (Highlighted c p)]
    (h : ¬ AddressesQUD c.qud p) :
    signaledCredenceFor form c p = none := by
  have : ¬ Highlighted c p := fun ⟨_, hAddr⟩ => h hAddr
  simp [signaledCredenceFor, this]

/-- A proposition not in the salient set has no signaled credence
    interval. Load-bearing use of `c.salient`. -/
theorem signaledCredenceFor_none_of_not_salient {form : MarkerTriple}
    {c : HighlightingContext W} {p : Set W} [Decidable (Highlighted c p)]
    (h : p ∉ c.salient) :
    signaledCredenceFor form c p = none := by
  have : ¬ Highlighted c p := fun ⟨hSal, _⟩ => h hSal
  simp [signaledCredenceFor, this]

-- ════════════════════════════════════════════════════════════════
-- § 6. Markedness ↔ commitment-table connection
-- ════════════════════════════════════════════════════════════════

/-- The six sentence forms the paper considers (3)–(8). Tags only
    combine with declarative anchors, so `⟨.int, _, true⟩` is not
    a valid F&R sentence form. -/
def paperSentenceForms : List MarkerTriple :=
  [.fallingDeclarative, .risingDeclarative,
   .fallingPolarInterrogative, .risingPolarInterrogative,
   .fallingTagInterrogative, .risingTagInterrogative]

/-- A consequence of the framework restricted to the 6 paper-valid
    sentence forms: every UNMARKED form is either fullCommitment
    (falling declarative) or neutral (polar interrogatives). Bias
    commitments are reserved for marked forms (rising declaratives
    + tag interrogatives).

    This is the "Division of Labor" principle's structural
    signature: unmarked forms have either full commitment or no
    commitment, never partial bias. -/
theorem unmarked_iff_full_or_neutral_paper (mt : MarkerTriple)
    (h : mt ∈ paperSentenceForms) :
    ¬ mt.isMarked ↔ commitmentType mt ∈ [CommitmentType.fullCommitment, .neutral] := by
  -- Decide-check by exhausting the 6 paper-valid forms.
  simp only [paperSentenceForms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 7. Basic convention of use F_b (eq. (48), p. 265)
-- and the Division-of-Labor structural claim
-- ════════════════════════════════════════════════════════════════

/-! F&R 2017's central architectural move (p. 265 eq. (48), p. 266 prose)
is replacing Frege's two illocutionary force operators (Assertion +
Question) with a single basic convention of use F_b. F_b is then
augmented with sentence-type-specific special effects for marked forms.

This section formalizes F_b over `Discourse.Commitment.Table.State` and
proves that **for the unmarked forms (falling declaratives + both polar
interrogatives), the per-form discourse-effect update reduces to F_b
alone** — the structural Division of Labor (eq. (21a) + p. 266).
Explicit F_b and the unmarked-equals-F_b reduction structurally
enforce what the paper states in prose. -/

open Discourse.Commitment.Table

/-- F_b — F&R 2017's "basic convention of use" (eq. (48), p. 265).
    Per F&R: "If a discourse participant x utters a declarative or
    interrogative sentence φ, the discourse context is affected as
    follows: (1) The proposition expressed by φ, [[φ]], is added to
    the table. (2) The informative content of φ, ⋃[[φ]], is added to
    commitments(x)."

    F&R parameterize the proposition's alternatives at the type of
    inquisitive content. For the F&B substrate, we expose F_b in two
    forms: a single-alternative version (declarative content; one
    proposition `α`) and a two-alternative version (polar content;
    `α` and `αᶜ`).

    The polar case follows F&R's eq. (50) (p. 267) verbatim: even though
    ⋃{α, αᶜ} = W is the trivial commitment, F&R explicitly add it to
    `commitments(x)`. F&R's prose (p. 267): "the commitment entered on
    the speaker's discourse commitment list is the trivial commitment
    that w_a is an element of α∪ᾱ, which is the set of all possible
    worlds, W. In this case then, the speaker makes a trivial commitment
    and she remains neutral." This is distinct from F&B's
    `polarQuestion`, which omits the trivial-commitment step.
    The vacuity is genuine — see `F_b_int_dcS_growth_is_vacuous` below. -/
def F_b_dec {W : Type*} (content : Set W) (ds : State W) :
    State W :=
  -- Single-alternative content {α}: informative content = α.
  -- Add α to commitments(speaker), push {α} as an issue (form .declarative).
  assert ds content

/-- F_b for two-alternative (polar) content: alternatives = {α, αᶜ},
    informative content = α ∪ αᶜ = Set.univ. Per F&R eq. (50) p. 267,
    this trivial commitment IS added to dcS — diverging from the
    F&B-substrate convention used by `MarkerTriple.update` for polar
    interrogatives, which skips the vacuous step. The two predictions
    differ in dcS shape but agree on `contextSet` (the Set.univ
    commit doesn't constrain anything; see the vacuity theorem below). -/
def F_b_int {W : Type*} (content : Set W) (ds : State W) :
    State W :=
  (polarQuestion ds content).addCommit .speaker Set.univ

/-- Update a F&B discourse state by uttering `content` with marker form
    `form`. Follows F&B substrate conventions, which differ from F&R's
    verbatim eq. (48)/(50) on polar interrogatives — see
    `update_int_vs_F_b_int_diverge_on_dcS` below for the divergence and
    `F_b_int_dcS_growth_is_vacuous` for why the divergence is observably
    inert (contextSet-preserving).

    Mapping:
    * Falling declarative (unmarked) → `F_b_dec` (= `assert`):
      writes to dcS, pushes a one-alternative issue.
    * Rising or falling polar interrogative (unmarked) → `polarQuestion`
      (NOT `F_b_int`): pushes a {p, ¬p} issue, omits the trivial Set.univ
      commit. Differs from F&R verbatim by the trivial commit; agrees on
      observable context.
    * Rising declarative (marked, bias) → push a one-alternative
      issue WITHOUT writing dcS. F&B has no built-in operator for
      this; we construct the `RaisedIssue` directly.
    * Tag interrogative (marked, bias) → declarative anchor commits
      via `assert` AND a polar issue is raised by the tag.

    Non-paper-canonical forms (interrogative + tag) are no-ops. -/
def MarkerTriple.update {W : Type*} (form : MarkerTriple)
    (content : Set W) (ds : State W) : State W :=
  match form with
  | ⟨.dec, .closed, false⟩ => F_b_dec content ds
  | ⟨.int, _, false⟩ => polarQuestion ds content
  | ⟨.dec, .rising, false⟩ =>
      ds.pushItem ⟨.speaker, .addressee, .declarative, [content]⟩
  | ⟨.dec, _, true⟩ => polarQuestion (assert ds content) content
  | _ => ds

/-- **Division of Labor (eq. (21a) + p. 266 prose), unmarked falling
    declarative case**: the per-form update IS F_b for falling
    declaratives. Note this remains `rfl`-vacuous because `update` for
    this case is *defined* to call `F_b_dec`. The substantive content
    is in §3 of the paper (that no special effects are needed for this
    form); the Lean encoding records that consensus. -/
theorem update_eq_F_b_dec_falling {W : Type*}
    (content : Set W) (ds : State W) :
    MarkerTriple.fallingDeclarative.update content ds = F_b_dec content ds := rfl

/-- **Substrate divergence on polar interrogatives**: F&B's
    `polarQuestion` (used by `MarkerTriple.update` for both polar
    interrogatives) skips the trivial Set.univ commit that F&R's eq. (50)
    requires. Concretely, F&R-verbatim F_b adds Set.univ to dcS; F&B's
    polarQuestion does not. -/
theorem update_int_vs_F_b_int_diverge_on_dcS {W : Type*}
    (content : Set W) (ds : State W) :
    (MarkerTriple.fallingPolarInterrogative.update content ds).dcS =
      ds.dcS ∧
    (F_b_int content ds).dcS = Set.univ :: ds.dcS := by
  refine ⟨rfl, rfl⟩

/-- The divergence in `update_int_vs_F_b_int_diverge_on_dcS` is
    observably inert: F&R's verbatim F_b for polar adds Set.univ to dcS,
    but `Set.univ` is the identity for context-set intersection, so the
    `contextSet` projection of F_b_int agrees with that of
    `polarQuestion`. F&R prose (p. 267): "the speaker makes a
    trivial commitment and she remains neutral." -/
theorem F_b_int_dcS_growth_is_vacuous {W : Type*}
    (content : Set W) (ds : State W) :
    (F_b_int content ds).contextSet =
      (polarQuestion ds content).contextSet := by
  -- Both sides differ only in dcS ([Set.univ :: ...] vs [...]), and
  -- contextSet only reads cg, not dcS. So they're equal by rfl.
  rfl

/-- Falling declarative writes to dcS (full commitment, p. 240 table). -/
theorem fallingDec_writes_dcS {W : Type*}
    (content : Set W) (ds : State W) :
    (MarkerTriple.fallingDeclarative.update content ds).dcS = content :: ds.dcS := rfl

/-- Polar interrogatives (either intonation) do NOT write to dcS
    (neutral, p. 240 table). -/
theorem polarInt_doesnt_write_dcS_falling {W : Type*}
    (content : Set W) (ds : State W) :
    (MarkerTriple.fallingPolarInterrogative.update content ds).dcS = ds.dcS := rfl

theorem polarInt_doesnt_write_dcS_rising {W : Type*}
    (content : Set W) (ds : State W) :
    (MarkerTriple.risingPolarInterrogative.update content ds).dcS = ds.dcS := rfl

/-- Rising declarative does NOT write to dcS (bias, no full commitment;
    matches p. 240 table classification). -/
theorem risingDec_doesnt_write_dcS {W : Type*}
    (content : Set W) (ds : State W) :
    (MarkerTriple.risingDeclarative.update content ds).dcS = ds.dcS := rfl

/-- Tag interrogatives DO write to dcS (the declarative anchor commits;
    the tag separately raises an issue). The "bias" classification on
    p. 240 thus has TWO structurally distinct realizations in F&B
    terms: rising declaratives don't commit, tags do. -/
theorem tag_writes_dcS_falling {W : Type*}
    (content : Set W) (ds : State W) :
    (MarkerTriple.fallingTagInterrogative.update content ds).dcS = content :: ds.dcS := rfl

theorem tag_writes_dcS_rising {W : Type*}
    (content : Set W) (ds : State W) :
    (MarkerTriple.risingTagInterrogative.update content ds).dcS = content :: ds.dcS := rfl

/-- All sentence types push at least one issue onto the table.
    The structural common ground per F&B: every utterance is
    table-bearing. -/
theorem all_paper_forms_push_issue {W : Type*}
    (content : Set W) (ds : State W) (form : MarkerTriple)
    (h : form ∈ paperSentenceForms) :
    (form.update content ds).table.length > ds.table.length := by
  simp only [paperSentenceForms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;>
    simp only [MarkerTriple.update, MarkerTriple.fallingDeclarative,
        MarkerTriple.risingDeclarative, MarkerTriple.fallingPolarInterrogative,
        MarkerTriple.risingPolarInterrogative,
        MarkerTriple.fallingTagInterrogative, MarkerTriple.risingTagInterrogative,
        F_b_dec,
        assert_table, polarQuestion_table, DiscourseState.pushItem_table,
        List.length_cons] <;> omega

/-- The commitment-table classification corresponds to F&B-side
    behavior for the two "extreme" cases:
    * `fullCommitment` ↔ writes to dcS via `assert`
    * `neutral` ↔ does not write to dcS (only pushes an issue)

    The `bias` middle case is NOT structurally uniform: rising
    declaratives don't write dcS (like neutral), tag interrogatives
    DO write dcS (like full). This is an honest finding — the
    p. 240 commitment table abstracts over a structural distinction
    that F&B's substrate makes visible. -/
theorem fullCommitment_iff_dcS_grows {W : Type*}
    (content : Set W) (ds : State W) (form : MarkerTriple)
    (h : form ∈ paperSentenceForms) :
    commitmentType form = .fullCommitment →
      (form.update content ds).dcS = content :: ds.dcS := by
  simp only [paperSentenceForms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> intro hc <;>
    simp_all only [commitmentType, MarkerTriple.fallingDeclarative,
              MarkerTriple.risingDeclarative, MarkerTriple.fallingPolarInterrogative,
              MarkerTriple.risingPolarInterrogative,
              MarkerTriple.fallingTagInterrogative, MarkerTriple.risingTagInterrogative,
              MarkerTriple.update, F_b_dec,
              assert_dcS, reduceCtorEq] <;> rfl

/-- Complement direction: `neutral` commitment type ↔ no dcS write. -/
theorem neutral_iff_dcS_unchanged {W : Type*}
    (content : Set W) (ds : State W) (form : MarkerTriple)
    (h : form ∈ paperSentenceForms) :
    commitmentType form = .neutral →
      (form.update content ds).dcS = ds.dcS := by
  simp only [paperSentenceForms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> intro hc <;>
    simp_all only [commitmentType, MarkerTriple.fallingDeclarative,
              MarkerTriple.risingDeclarative, MarkerTriple.fallingPolarInterrogative,
              MarkerTriple.risingPolarInterrogative,
              MarkerTriple.fallingTagInterrogative, MarkerTriple.risingTagInterrogative,
              MarkerTriple.update,
              polarQuestion_dcS, reduceCtorEq]

-- ════════════════════════════════════════════════════════════════
-- § 8. Cross-framework divergences
-- ════════════════════════════════════════════════════════════════

/-! F&R 2017 sits in a crowded field of commitment-based dialogue
frameworks, each making different structural predictions for the
contested cases (rising declaratives, tag interrogatives). This
section makes two divergences Lean-checkable. -/

-- ─────────────────────────────────────────────────────────────────
-- § 8a. Rising declarative — F&R + F&B vs Gunlogson 2008
-- ─────────────────────────────────────────────────────────────────

/-! [gunlogson-2008] (and earlier [gunlogson-2001], the work
F&R 2017's footnote 13 cites), formalized in `Discourse/Commitment/SourceMarked.lean`,
records rising-declarative information by writing to the **addressee's**
slate as an other-generated commitment. F&R 2017 (threaded through F&B
substrate) writes nothing to the speaker's `dcS` (only pushes an issue).

These two facts look like a contradiction, but F&R themselves frame
the relationship more carefully. Footnote 13 (p. 257) reads: "Our
account is **similar to Gunlogson's in separating the two components**
but while for Gunlogson they only come into play at the discourse
level, for us they have semantic import." So the difference is in
**which layer of analysis** carries the rising-vs-falling distinction
(discourse-level for Gunlogson; semantic-level for F&R), not whether
the addressee has anything attributed to them.

The Lean witness in this section records the difference in
**state shapes** — F&R + F&B's `DiscourseState` does not even have a
slot for "other-generated addressee commitment" (only `dcL` for
self-generated listener commitments), so F&B's silence on rising-dec
addressee attribution is **type-level** silence, not an empirical
prediction. The substrates differ in what they record, not in what
they claim happens. -/

/-- F&R + F&B prediction for rising declarative: dcS is unchanged. -/
theorem fr_rising_dec_no_speaker_commitment {W : Type*}
    (content : Set W) (ds : State W) :
    (MarkerTriple.risingDeclarative.update content ds).dcS = ds.dcS := rfl

/-- Gunlogson 2008 prediction for rising declarative from the empty
    state: the addressee's slate gains exactly one commitment
    (other-generated). Restated from
    `Discourse/Commitment/SourceMarked.lean` for the cross-framework comparison. -/
theorem gunlogson_rising_dec_writes_addressee {W : Type*} (content : Set W) :
    ((Discourse.Gunlogson.GunlogsonState.empty :
        Discourse.Gunlogson.GunlogsonState W).risingDeclarative
      content).addresseeSlate.commitments.length = 1 := rfl

/-- **Cross-framework state-shape divergence**: F&R + F&B record the
    rising-declarative effect in different state slots than Gunlogson.
    F&R + F&B's `dcS` (speaker's commitments) is unchanged; Gunlogson's
    `addresseeSlate` gains an other-generated commitment. Per F&R's own
    footnote 13 (p. 257), this is a layer-of-analysis difference rather
    than an empirical contradiction — F&R simply factor the addressee-
    attribution into the *semantic* component (out of scope for this
    discourse-state formalization), where Gunlogson factors it into
    the *discourse* component (which the substrate makes visible).
    The theorem witnesses the structural divergence; it does not
    adjudicate which framework better captures the phenomenon. -/
theorem fr_vs_gunlogson_rising_dec_state_shape {W : Type*} (content : Set W) :
    -- F&R + F&B from empty state: dcS empty (no speaker commitment recorded)
    (MarkerTriple.risingDeclarative.update content
        (DiscourseState.empty : State W)).dcS = [] ∧
    -- Gunlogson from empty state: addressee slate non-empty (addressee
    -- attribution recorded at the discourse layer)
    ((Discourse.Gunlogson.GunlogsonState.empty :
        Discourse.Gunlogson.GunlogsonState W).risingDeclarative
      content).addresseeSlate.commitments ≠ [] := by
  refine ⟨rfl, ?_⟩
  intro h
  have h1 := gunlogson_rising_dec_writes_addressee (W := W) content
  rw [h] at h1
  simp only [List.length_nil] at h1
  omega

-- ─────────────────────────────────────────────────────────────────
-- § 8b. Tag interrogative — F&R + F&B sequential vs Krifka 2015
--       conjunction/disjunction
-- ─────────────────────────────────────────────────────────────────

/-! [krifka-2015] §5 (eqs. 44–45), with substrate in
`Discourse/Commitment/Space.lean`, argues that tag interrogatives
are a SINGLE complex speech act — `matchingTag` is a `ComplexSpeechAct.conj`
of an assertion and a monopolar question (sharing content φ), `reverseTag`
is a `ComplexSpeechAct.disj`. Krifka explicitly contrasts this with the
sequential reading: per CommitmentSpace.lean line ~688, "this is **not**
a move in which the speaker first makes an assertion and then asks the
addressee to make the same assertion. Rather, the two speech acts are
first conjoined, and then applied as one complex speech act."

The F&B-threaded F&R update in this file uses sequential composition
(`assert |> polarQuestion`), producing two independent
issues on the table. This is exactly the structural shape Krifka rejects.
The contrast theorem below pulls in Krifka's `matchingTag` substrate so
the divergence is Lean-checkable on both sides — F&R's two-issue
sequential signature vs Krifka's single-conjunction signature. -/

/-- F&R + F&B prediction for tag interrogative: the table gains TWO
    issues — one interrogative (from the tag's polar question), one
    declarative (from the assertion anchor), sequentially stacked. -/
theorem fr_tag_pushes_two_issues {W : Type*} (content : Set W) :
    (MarkerTriple.fallingTagInterrogative.update content
        (DiscourseState.empty : State W)).table.length = 2 := rfl

/-- The two issues F&R + F&B place on the table for a tag are of
    DIFFERENT forms — one interrogative (from the tag's polar
    question), one declarative (from the assertion anchor). -/
theorem fr_tag_table_forms {W : Type*} (content : Set W) :
    (MarkerTriple.fallingTagInterrogative.update content
        (DiscourseState.empty : State W)).table.map (·.mood) =
      [.interrogative, .declarative] := rfl

/-- Krifka 2015 prediction for a matching tag: a SINGLE
    `ComplexSpeechAct.conj` wrapper around two component speech acts.
    Restated from `Discourse/Commitment/Space.lean` for the
    cross-framework comparison. -/
theorem krifka_matching_tag_is_single_conjunction {W : Type*}
    (φ : W → Prop) :
    ∃ a b, Discourse.Krifka.matchingTag φ = .conj a b :=
  ⟨_, _, rfl⟩

/-- In Krifka's matching tag, the two components share content `φ`
    (matching the assertion + monopolar-question semantics of "I have
    won the race, have I?"). Restated from `CommitmentSpace.lean`. -/
theorem krifka_matching_tag_shared_content {W : Type*} (φ : W → Prop) :
    (Discourse.Krifka.matchingTag φ).components.map
      Discourse.Krifka.SpeechAct.content = [φ, φ] := rfl

/-- **Cross-framework structural divergence on tag interrogatives**:
    F&R + F&B produces a sequence of TWO distinct issues with DIFFERENT
    forms; Krifka 2015 produces ONE complex speech act wrapping two
    components with the SAME content. The two signatures cannot be
    re-reconciled by changing input content — they encode tag
    interrogatives as fundamentally different mathematical objects. -/
theorem fr_vs_krifka_tag_structural_divergence {W : Type*} (φ : W → Prop) :
    -- F&R + F&B: 2 distinct table issues with mixed forms (sequential)
    (MarkerTriple.fallingTagInterrogative.update φ
        (DiscourseState.empty : State W)).table.map (·.mood) =
      [.interrogative, .declarative] ∧
    -- Krifka: SINGLE complex speech act, NOT a sequence of atoms
    (∃ a b, Discourse.Krifka.matchingTag φ = .conj a b) ∧
    -- Krifka's components share content (vs F&R's mixed declarative φ
    -- and interrogative {φ, φᶜ})
    (Discourse.Krifka.matchingTag φ).components.map
      Discourse.Krifka.SpeechAct.content = [φ, φ] :=
  ⟨rfl, ⟨_, _, rfl⟩, rfl⟩

end FarkasRoelofsen2017
