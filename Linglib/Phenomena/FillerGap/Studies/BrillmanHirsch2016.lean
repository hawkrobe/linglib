import Linglib.Theories.Syntax.Minimalism.Core.Position

/-!
# Brillman & Hirsch (2016) @cite{brillman-hirsch-2016}

An anti-locality account of English subject/non-subject asymmetries.
Proceedings of CLS 50, 73–87.

## The Claim

A single constraint — **Spec-to-Spec Anti-Locality (SSAL)** — unifies
three English subject/non-subject asymmetries:

1. **That-trace effects**: `*Who does Bill think that _ saw John?`
2. **Tough-constructions**: `*Anneke is tough _ to see Ian`
3. **Matrix subject wh-questions**: no *do*-support, no parasitic gaps

In each case, the subject must move from Spec,TP to Spec,CP, but CP
immediately dominates TP — the movement is too local. Objects, starting
lower (complement of V), are never in a specifier, so SSAL never
applies to them.

## Connection to @cite{erlewine-2016} and Kaqchikel

The constraint is `specToSpecAntiLocality` from Position.lean — the
same predicate that drives Agent Focus in Kaqchikel. The blocking
theorem here (`subject_blocked_by_ssal`) delegates to
`pivot_blocked_by_anti_locality`, making the cross-linguistic identity
structural rather than asserted.

## Obviation Strategies

SSAL is a conditional: it blocks movement only when (a) the mover is
in Spec,XP AND (b) YP immediately dominates XP. Each of the following
strategies falsifies one hypothesis, vacuously satisfying SSAL:

1. **Intervening projection**: AdvP between TP and CP breaks immediate
   dominance — falsifies (b). Formalized: `ssal_vacuous_no_immediate_dominance`.
2. **Movement from lower**: Subject starts below Spec,TP (e.g., *there*
   fills Spec,TP) — falsifies (a). Formalized: `ssal_vacuous_not_in_spec`.
3. **No embedded spec-CP**: Absent *that* → no CP layer or no stop at
   embedded spec-CP — movement never enters the [Spec,TP → Spec,CP] config.
4. **In situ**: Subject *wh* stays in Spec,TP (matrix questions).

-/

namespace Phenomena.FillerGap.Studies.BrillmanHirsch2016

open Minimalism

-- ============================================================================
-- § 1: Data Types
-- ============================================================================

/-- Which argument position the gap is in. -/
inductive GapPosition where
  | subject
  | object
  deriving DecidableEq, BEq, Repr

/-- Grammaticality judgment. -/
inductive Judgment where
  | grammatical
  | ungrammatical
  /-- Degraded but improved over the fully ungrammatical baseline
      (e.g., parasitic gaps in GDPs, paper §4 ex. 29a). -/
  | marginal
  /-- Structurally ambiguous between two derivations
      (e.g., TC/GDP, paper §4.1 ex. 30). -/
  | ambiguous
  deriving DecidableEq, BEq, Repr

/-- An extraction datum: a sentence with a filler-gap dependency. -/
structure ExtractionDatum where
  sentence : String
  gap : GapPosition
  judgment : Judgment
  description : String := ""
  deriving Repr

-- ============================================================================
-- § 2: That-Trace Effects (Paper §3)
-- ============================================================================

/-! ### Baseline asymmetry

Subject extraction across *that* violates SSAL: the subject in Spec,TP
must move to the embedded Spec,CP, but CP immediately dominates TP.
Object extraction starts from complement of V — not a specifier — so
SSAL never applies (see `ssal_vacuous_not_in_spec`). -/

/-- (12a) Subject extraction across *that* — SSAL violation. -/
def thatTrace_subj : ExtractionDatum :=
  { sentence := "*Who does Bill think that _ saw John?"
    gap := .subject, judgment := .ungrammatical
    description := "Spec,TP → Spec,CP crosses only TP — too local" }

/-- (12b) Object extraction across *that* — no SSAL issue. -/
def thatTrace_obj : ExtractionDatum :=
  { sentence := "Who does Bill think that John saw _?"
    gap := .object, judgment := .grammatical
    description := "Object starts in Comp,VP — not spec-to-spec" }

/-! ### Neutralization 1: Intervening AdvP (anti-that-trace, §3.2.1)

A speaker-oriented adverb structurally between TP and CP breaks
immediate dominance. CP no longer immediately contains TP, so SSAL's
second hypothesis fails. Crucially, manner adverbs (which attach low,
inside vP) do NOT rescue: they don't break TP–CP adjacency. -/

/-- (15a) Baseline that-trace — no intervener. -/
def antiThatTrace_baseline : ExtractionDatum :=
  { sentence := "*Who does John think that _ served as president?"
    gap := .subject, judgment := .ungrammatical
    description := "No intervener — SSAL blocks" }

/-- (15b) *For all intents and purposes* between TP and CP rescues. -/
def antiThatTrace_advp : ExtractionDatum :=
  { sentence := "Who does John think that for all intents and purposes _ served as president?"
    gap := .subject, judgment := .grammatical
    description := "AdvP breaks TP–CP adjacency" }

/-- (16b) Speaker-oriented *fortunately* (high attachment) rescues. -/
def antiThatTrace_fortunately : ExtractionDatum :=
  { sentence := "Who did John say that fortunately _ ran to the store?"
    gap := .subject, judgment := .grammatical
    description := "High adverb between TP and CP" }

/-- (16c) Manner adverb *quickly* (low attachment) does NOT rescue.
    *Quickly* is a manner adverb attaching low (inside vP, below TP),
    so TP and CP remain structurally adjacent despite the linear
    intervention. -/
def antiThatTrace_quickly : ExtractionDatum :=
  { sentence := "*Who did John say that quickly _ ran to the store?"
    gap := .subject, judgment := .ungrammatical
    description := "Low adverb inside vP — TP–CP still adjacent" }

/-! ### Neutralization 2: Movement from lower (§3.2.2)

Expletive *there* fills Spec,TP. The associate DP remains low (e.g.,
inside PredP). Extraction thus starts below Spec,TP, crossing enough
structure. This parallels Kaqchikel AF, where the agent extracts from
Spec,vP directly to Spec,CP (@cite{erlewine-2016}). -/

/-- (17a) Subject extraction from Spec,TP — blocked. -/
def there_baseline : ExtractionDatum :=
  { sentence := "*How many horses does John think that _ are in the barn?"
    gap := .subject, judgment := .ungrammatical
    description := "Subject in Spec,TP — SSAL violation" }

/-- (17b) *There* in Spec,TP; subject extracts from lower — rescued. -/
def there_insertion : ExtractionDatum :=
  { sentence := "How many horses does John think that there are _ in the barn?"
    gap := .subject, judgment := .grammatical
    description := "Subject extracts from below Spec,TP" }

/-! ### Neutralization 3: No embedded spec-CP (§3.2.3)

Without overt *that*, the embedded clause may lack a CP layer
(Doherty 1997), or the subject may skip embedded spec-CP because C
lacks overt exponence and linearization doesn't force the stop
(Erlewine, building on Fox & Pesetsky 2005). Either way, no short
spec-TP → spec-CP step occurs. -/

/-- (18) Null *that* — subject extraction is grammatical. -/
def null_that : ExtractionDatum :=
  { sentence := "Who does Bill think _ saw John?"
    gap := .subject, judgment := .grammatical
    description := "No 'that' — no intermediate spec-CP step" }

-- ============================================================================
-- § 3: Tough-Constructions and GDPs (Paper §4)
-- ============================================================================

/-! ### Infinitival subject extraction: anti-locality, not case

The traditional case-based account (@cite{chomsky-1981}) attributes
the ban on infinitival subject extraction to case: the subject of an
infinitive is not in a case position, so it cannot be extracted.

The paper argues this is insufficient. Example (21) is the key datum:
even with case-assigning *for*, subject extraction is still blocked.
Anti-locality accounts for both (20a) and (21): the derivation
involves spec-TP → spec-CP in the embedded clause, violating SSAL. -/

/-- (20a) Subject of infinitive resists extraction. -/
def inf_subj : ExtractionDatum :=
  { sentence := "*Who is it possible _ to see Mary?"
    gap := .subject, judgment := .ungrammatical
    description := "OP in Spec,TP → Spec,CP violates SSAL" }

/-- (20b) Object of infinitive extracts freely. -/
def inf_obj : ExtractionDatum :=
  { sentence := "Who is it possible for Mary to see _?"
    gap := .object, judgment := .grammatical
    description := "Object starts in Comp,VP — not spec-to-spec" }

/-- (21) Case-assigning *for* does NOT rescue subject extraction.
    Under the case account, *for* should save (20a) by providing case.
    It does not. Under anti-locality, (21) is blocked for the same
    reason as (20a): spec-TP → spec-CP violates SSAL regardless of
    whether the embedded C assigns case. -/
def inf_subj_for : ExtractionDatum :=
  { sentence := "*Who is it possible for _ to see Mary?"
    gap := .subject, judgment := .ungrammatical
    description := "Case-assigning 'for' doesn't help — SSAL still blocks" }

/-! ### Tough-constructions (TCs)

In TCs, a null operator Ā-moves from the embedded infinitival clause
to spec-CP. Subject gap TCs are blocked because the operator in
spec-TP must move to spec-CP — violating SSAL. -/

/-- (23a) Subject gap TC. -/
def tc_subj : ExtractionDatum :=
  { sentence := "*Anneke is tough _ to talk to Ian"
    gap := .subject, judgment := .ungrammatical
    description := "Subject TC — OP: Spec,TP → Spec,CP violates SSAL" }

/-- (23b) Object gap TC. -/
def tc_obj : ExtractionDatum :=
  { sentence := "Ian is tough for Anneke to talk to _"
    gap := .object, judgment := .grammatical
    description := "Object TC — OP from Comp,VP" }

/-! ### Gapped degree phrases (GDPs)

GDPs (Nissenbaum & Schwarz 2011) project a DegP between AP and CP.
The null operator moves to spec-DegP, not spec-CP. For subject gaps,
the step from spec-TP to spec-DegP crosses both TP and CP (DegP does
NOT immediately dominate TP), satisfying SSAL.

Evidence that GDPs involve genuine Ā-movement (not control): they
license parasitic gaps, unlike control constructions (29a vs 29b). -/

/-- (24a) Subject GDP with *too* — grammatical. -/
def gdp_subj : ExtractionDatum :=
  { sentence := "Anneke is too smart _ to talk to Ian"
    gap := .subject, judgment := .grammatical
    description := "DegP above CP — Spec,TP → Spec,DegP crosses CP" }

/-- (24b) Object GDP with *too* — grammatical. -/
def gdp_obj : ExtractionDatum :=
  { sentence := "Ian is too smart for Anneke to talk to _"
    gap := .object, judgment := .grammatical
    description := "Object GDP — OP from Comp,VP" }

/-- (29a) GDP licenses parasitic gap (marginal but clearly improved
    over the control baseline in 29b and the unlicensed baseline
    in 29c). This is evidence that the null operator in GDPs
    undergoes genuine Ā-movement. -/
def gdp_parasitic_gap : ExtractionDatum :=
  { sentence := "?This student is too young _ to take the bar exam [without us talking to pg]"
    gap := .subject, judgment := .marginal
    description := "GDP Ā-movement licenses parasitic gap (degraded)" }

/-- (29b) Control construction does NOT license parasitic gap. -/
def control_no_parasitic_gap : ExtractionDatum :=
  { sentence := "*This student is eager PRO to take the bar exam [without us talking to pg]"
    gap := .subject, judgment := .ungrammatical
    description := "Control (no Ā-movement) — pg not licensed" }

/-- (29c) Baseline: unlicensed parasitic gap. -/
def pg_baseline : ExtractionDatum :=
  { sentence := "*This student took the bar exam [without us talking to pg]"
    gap := .subject, judgment := .ungrammatical
    description := "No Ā-movement at all — pg not licensed" }

/-! ### TC/GDP structural contrast (§4.1)

The paper's key diagnostic: the SAME surface string (with *enough*)
is ambiguous between a TC reading and a GDP reading. In the TC
structure, DegP adjoins to AP — the OP moves to spec-CP. In the GDP
structure, DegP takes CP as complement — the OP moves to spec-DegP.

For object gaps, both structures converge (no SSAL issue either way).
For subject gaps, only the GDP structure is available: the TC
structure requires spec-TP → spec-CP (SSAL violation). -/

/-- (30) Object gap with *tough enough* — ambiguous between TC reading
    ("it's difficult") and GDP reading ("Anneke herself is tough"). -/
def tough_enough_ambig : ExtractionDatum :=
  { sentence := "Anneke is tough enough for Ian to talk to _"
    gap := .object, judgment := .ambiguous
    description := "TC/GDP structural ambiguity — DegP attachment varies" }

/-- (33a) Subject gap with *tough enough* — only GDP reading available.
    The TC structure would require OP to move from spec-TP to spec-CP
    (SSAL violation). The GDP structure has OP move from spec-TP to
    spec-DegP, crossing CP — SSAL satisfied.

    The monoambiguity of (33a) vs the ambiguity of (30) is the
    signature of anti-locality. -/
def tough_enough_subj_gdp_only : ExtractionDatum :=
  { sentence := "Ian is tough enough _ to talk to Anneke"
    gap := .subject, judgment := .grammatical
    description := "Only GDP reading — TC reading blocked by SSAL" }

-- ============================================================================
-- § 4: Matrix Subject Wh-Questions (Paper §5)
-- ============================================================================

/-! ### Subject wh stays in situ

If subject *wh* movement from Spec,TP to Spec,CP would violate SSAL,
the grammar leaves *wh* in situ. This predicts three surface
properties of subject questions:

- **No do-support**: T-to-C (triggered by wh-movement to Spec,CP) does
  not occur, so *do* is not inserted.
- **No parasitic gaps**: Ā-movement is required to license parasitic
  gaps; in-situ *wh* provides no Ā-chain.
- **Weaker wh-island effects**: subject relatives are not wh-islands
  because *who* never occupies Spec,CP. -/

/-- (36a) Subject question — no *do*-support. -/
def subj_wh : ExtractionDatum :=
  { sentence := "Who saw John?"
    gap := .subject, judgment := .grammatical
    description := "Subject wh in situ — no T-to-C, no do-support" }

/-- (36b) Subject question with *do*-support — ungrammatical on the
    non-emphatic reading. If subject *wh* cannot move to Spec,CP,
    T-to-C movement is not triggered and *do* is not inserted. -/
def subj_wh_do_blocked : ExtractionDatum :=
  { sentence := "*Who did _ see John?"
    gap := .subject, judgment := .ungrammatical
    description := "No wh-movement → no T-to-C → no do-support" }

/-- (37b) Object question — *do*-support required. -/
def obj_wh : ExtractionDatum :=
  { sentence := "Who did John see _?"
    gap := .object, judgment := .grammatical
    description := "Object wh moves to Spec,CP → T-to-C → do-support" }

/-- (38a) Subject question does NOT license parasitic gap. -/
def subj_wh_no_pg : ExtractionDatum :=
  { sentence := "*Who _ hired Mary without us talking to pg?"
    gap := .subject, judgment := .ungrammatical
    description := "No Ā-movement → no parasitic gap licensing" }

/-- (38b) Object question licenses parasitic gap. -/
def obj_wh_pg : ExtractionDatum :=
  { sentence := "Who did Mary hire _ without talking to pg?"
    gap := .object, judgment := .grammatical
    description := "Ā-movement to Spec,CP → parasitic gap licensed" }

/-! ### Wh-island contrast (§5, ex. 39–40)

If subject *who* stays in situ, a subject relative clause is not a
wh-island (no *who* in Spec,CP to block further extraction). A
non-subject relative, where *who* does move to Spec,CP, creates a
wh-island as expected. -/

/-- (39b) Extraction from a subject relative — grammatical.
    The subject relative *who wanted to record that song* is not a
    wh-island because *who* is in situ (in Spec,TP, not Spec,CP). -/
def subj_rel_no_island : ExtractionDatum :=
  { sentence := "Isn't that the song which Paul and Stevie were the only ones [who wanted to record _]?"
    gap := .object, judgment := .grammatical
    description := "Subject relative — no wh-island (who in situ)" }

/-- (40b) Extraction from a non-subject relative — blocked.
    *Who* in the non-subject relative occupies Spec,CP (it moved from
    a lower position), creating a wh-island. -/
def nonsubj_rel_island : ExtractionDatum :=
  { sentence := "*Isn't that the song which Paul and Stevie were the only ones [who George would let _ record _]?"
    gap := .object, judgment := .ungrammatical
    description := "Non-subject relative — wh-island (who in Spec,CP)" }

/-! ### Neutralization: intervener enables subject wh-movement (§5.2)

When a projection intervenes between TP and CP, subject *wh* can
move to Spec,CP, triggering T-to-C and *do*-support. -/

/-- (42a) Subject *wh* with *do*-support — no intervener. Ungrammatical
    on the non-emphatic reading. -/
def subj_wh_do_baseline : ExtractionDatum :=
  { sentence := "*Who does _ serve as president?"
    gap := .subject, judgment := .ungrammatical
    description := "No intervener — subject wh can't move to Spec,CP" }

/-- (42b) AdvP between TP and CP — subject *wh* moves, *do*-support
    appears. Several informants report a non-emphatic reading of *do*
    is available, unlike in (42a). -/
def subj_wh_do_intervener : ExtractionDatum :=
  { sentence := "Who does for all intents and purposes _ serve as president?"
    gap := .subject, judgment := .grammatical
    description := "AdvP enables Spec,TP → Spec,CP + do-support" }

/-- (43) Adjunct between TP and CP — parasitic gap licensed.
    Longobardi (1985) observed this pattern. The position of *who* to
    the left of the adjunct indicates movement from Spec,TP to
    Spec,CP, and with Ā-movement, the parasitic gap is licensed. -/
def subj_wh_pg_rescued : ExtractionDatum :=
  { sentence := "Who without Mary talking to pg _ hired Jill nonetheless?"
    gap := .subject, judgment := .grammatical
    description := "Adjunct intervenes — Ā-movement + pg licensing" }

-- ============================================================================
-- § 5: SSAL Theorems
-- ============================================================================

/-! Every subject/non-subject asymmetry in this paper is an instance of
    `specToSpecAntiLocality` from Position.lean — the same constraint
    used for Kaqchikel Agent Focus (@cite{erlewine-2016}) and Toba Batak
    pivot blocking (@cite{erlewine-2018}).

    The blocking theorem delegates directly to `pivot_blocked_by_anti_locality`
    from Position.lean. The two vacuous-satisfaction lemmas formalize
    the paper's obviation strategies as falsifications of SSAL's antecedents. -/

/-- **Blocking**: Subject extraction from Spec,TP to Spec,CP is blocked
    when CP immediately dominates TP. Accounts for:
    - *that*-trace effects (§3, ex. 12a)
    - TC subject gap restriction (§4, ex. 23a)
    - Subject *wh*-in-situ (§5, ex. 36)
    - Infinitival subject extraction, including with *for* (§4, ex. 20a, 21)

    Delegates to `pivot_blocked_by_anti_locality` (Position.lean) — the
    English blocking theorem IS the Toba Batak/Kaqchikel blocking theorem,
    applied to a different language's clause structure. -/
theorem subject_blocked_by_ssal
    (events : List MergeEvent) (subj tP cP : SyntacticObject)
    (h_spec : isSpecIn events subj tP)
    (h_imm : immediatelyContains cP tP)
    (h_ssal : specToSpecAntiLocality events subj tP cP) :
    ¬movedToSpecOf events subj cP :=
  pivot_blocked_by_anti_locality events subj tP cP h_spec h_imm h_ssal

/-- **Obviation by intervening projection** (§3.2.1, §5.2): When a
    maximal projection (AdvP, adjunct) structurally intervenes between
    TP and CP, `immediatelyContains cP tP` is false and SSAL is
    vacuously satisfied. Subject extraction is then permitted.

    Accounts for:
    - Anti-*that*-trace with *fortunately* / *for all intents and purposes*
    - Subject *wh* with *do*-support when AdvP intervenes (42b)
    - Parasitic gap licensing when adjunct attaches between TP and CP (43)
    - GDP subject gaps: DegP between TP and the movement target (24a, 33a) -/
theorem ssal_vacuous_no_immediate_dominance
    (events : List MergeEvent) (subj tP cP : SyntacticObject)
    (h_not_imm : ¬immediatelyContains cP tP) :
    specToSpecAntiLocality events subj tP cP :=
  λ _ h_imm => absurd h_imm h_not_imm

/-- **Obviation by movement from lower** (§3.2.2): When the mover is
    not in Spec,TP, `isSpecIn` is false and SSAL is vacuously satisfied.

    This covers two cases:
    - **There-insertion**: expletive *there* fills Spec,TP; the subject
      remains low and extracts from below, crossing enough structure (17b).
    - **Object extraction** (all cases): objects originate in complement
      position (Comp,VP), never in a specifier. SSAL's first hypothesis
      is structurally impossible for them, which is why object extraction
      is uniformly grammatical across all three phenomena.

    Parallels Kaqchikel AF: the agent extracts from Spec,vP directly
    to Spec,CP, bypassing Spec,TP entirely (@cite{erlewine-2016}). -/
theorem ssal_vacuous_not_in_spec
    (events : List MergeEvent) (subj tP cP : SyntacticObject)
    (h_not_spec : ¬isSpecIn events subj tP) :
    specToSpecAntiLocality events subj tP cP :=
  λ h_spec _ => absurd h_spec h_not_spec

-- ============================================================================
-- § 6: TC/GDP Structural Contrast (Paper §4.1)
-- ============================================================================

/-! The paper's most distinctive contribution (§4.1, ex. 30–35): the
    TC/GDP structural contrast for subject gaps.

    In TCs, the null operator moves to **Spec,CP**. CP immediately
    dominates TP, so subject gaps violate SSAL.

    In GDPs, the null operator moves to **Spec,DegP**. DegP does NOT
    immediately dominate TP — CP intervenes — so SSAL is satisfied
    and subject gaps are grammatical.

    The formal difference reduces to whether the movement target
    immediately dominates TP. Both theorems below are applications of
    `pivot_blocked_by_anti_locality` and `ssal_vacuous_no_immediate_dominance`
    respectively. -/

/-- **TC subject gap blocked**: In the TC structure, the null operator
    targets Spec,CP. CP immediately dominates TP. SSAL blocks.
    This rules out the TC reading of (33a) and all of (23a). -/
theorem tc_subj_gap_blocked
    (events : List MergeEvent) (op tP cP : SyntacticObject)
    (h_spec : isSpecIn events op tP)
    (h_imm : immediatelyContains cP tP)
    (h_ssal : specToSpecAntiLocality events op tP cP) :
    ¬movedToSpecOf events op cP :=
  pivot_blocked_by_anti_locality events op tP cP h_spec h_imm h_ssal

/-- **GDP subject gap permitted**: In the GDP structure, the null operator
    targets Spec,DegP. DegP does NOT immediately dominate TP (CP
    intervenes: DegP ⊃ CP ⊃ TP). SSAL is vacuously satisfied.
    This licenses the GDP reading of (33a) and all of (24a). -/
theorem gdp_subj_gap_permitted
    (events : List MergeEvent) (op tP degP : SyntacticObject)
    (h_not_imm : ¬immediatelyContains degP tP) :
    specToSpecAntiLocality events op tP degP :=
  ssal_vacuous_no_immediate_dominance events op tP degP h_not_imm

-- ============================================================================
-- § 7: Cross-Linguistic Unification
-- ============================================================================

/-! The English subject/non-subject asymmetries, Kaqchikel Agent Focus,
    and Toba Batak pivot restriction all invoke the same structural
    configuration: a mover in Spec,XP and a target Spec,YP where YP
    immediately dominates XP.

    The differences lie entirely in repair strategies:

    | Language   | Phenomenon          | Repair                         |
    |------------|---------------------|--------------------------------|
    | Kaqchikel  | Agent Focus         | AF morphology (OT: SSAL>>XRef) |
    | English    | *that*-trace        | ungrammaticality (no repair)   |
    | English    | anti-*that*-trace   | intervening AdvP               |
    | English    | *there*-insertion   | extraction from lower          |
    | English    | null *that*         | no intermediate spec-CP        |
    | English    | subject *wh*        | in situ (no movement)          |
    | English    | GDP subject gap     | DegP between TP and target     |
    | Toba Batak | pivot restriction   | predicate fronting + licensing  |

    The identity is by construction: `subject_blocked_by_ssal`,
    `tc_subj_gap_blocked`, and `pivot_blocked_by_anti_locality`
    all delegate to `specToSpecAntiLocality`. -/

-- ============================================================================
-- § 8: Data Verification
-- ============================================================================

/-! Subject extraction is ungrammatical in all three baseline phenomena. -/

#guard thatTrace_subj.judgment == .ungrammatical
#guard thatTrace_obj.judgment == .grammatical

#guard tc_subj.judgment == .ungrammatical
#guard tc_obj.judgment == .grammatical

#guard subj_wh_no_pg.judgment == .ungrammatical
#guard obj_wh_pg.judgment == .grammatical

/-! Case-assigning *for* doesn't rescue infinitival subject extraction. -/

#guard inf_subj.judgment == .ungrammatical
#guard inf_subj_for.judgment == .ungrammatical
#guard inf_obj.judgment == .grammatical

/-! All four obviation strategies yield grammatical subject extraction. -/

#guard antiThatTrace_advp.judgment == .grammatical       -- intervening AdvP
#guard there_insertion.judgment == .grammatical           -- movement from lower
#guard null_that.judgment == .grammatical                 -- no embedded spec-CP
#guard subj_wh.judgment == .grammatical                   -- in situ

/-! High adverbs rescue; low adverbs do not. -/

#guard antiThatTrace_fortunately.judgment == .grammatical
#guard antiThatTrace_quickly.judgment == .ungrammatical

/-! GDPs rescue subject gaps that TCs block. -/

#guard gdp_subj.judgment == .grammatical
#guard tc_subj.judgment == .ungrammatical
#guard tough_enough_subj_gdp_only.judgment == .grammatical

/-! GDPs license parasitic gaps; control does not. -/

#guard gdp_parasitic_gap.judgment == .marginal
#guard control_no_parasitic_gap.judgment == .ungrammatical
#guard pg_baseline.judgment == .ungrammatical

/-! Subject questions: no do-support, no parasitic gaps, no wh-islands. -/

#guard subj_wh.judgment == .grammatical
#guard subj_wh_do_blocked.judgment == .ungrammatical
#guard subj_wh_no_pg.judgment == .ungrammatical
#guard subj_rel_no_island.judgment == .grammatical
#guard nonsubj_rel_island.judgment == .ungrammatical

/-! Intervener enables subject wh-movement + do-support + pg licensing. -/

#guard subj_wh_do_baseline.judgment == .ungrammatical
#guard subj_wh_do_intervener.judgment == .grammatical
#guard subj_wh_pg_rescued.judgment == .grammatical

end Phenomena.FillerGap.Studies.BrillmanHirsch2016
