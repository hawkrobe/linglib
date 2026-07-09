import Linglib.Fragments.Mayan.Kaqchikel.Focus
import Linglib.Syntax.Minimalist.Position
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Studies.CoonMateoPedroPreminger2014

/-!
# Erlewine 2016: Anti-Locality and Optimality in Kaqchikel Agent Focus
[erlewine-2016] [erlewine-2018]

[erlewine-2016] analyzes Kaqchikel Agent Focus as the optimal output
of a competition between derivations, ranked by three violable
constraints: **XRef-Participant** ≫ **Spec-to-Spec Anti-Locality
(SSAL)** ≫ **XRef** (cross-referencing). The core two-candidate
competition is decided by the SSAL ≫ XRef sub-ranking; top-ranked
XRef-Participant produces the participant exception below. The
fragment in `Fragments/Mayan/Kaqchikel/Focus.lean` carries the
typology-neutral extraction profile; this study file adds the
theory-laden OT machinery and verifies the paper's results.

## The Derivation ([erlewine-2016] §§4–5)

### Why the transitive derivation crashes

In a normal Kaqchikel transitive, the agent base-generates in Spec,vP
and is attracted to Spec,TP by the A-probe on T (receiving Set A
agreement). For Ā-extraction, the agent must then move from Spec,TP
to Spec,CP. But CP immediately dominates TP, so this step crosses no
intervening maximal projection — violating Spec-to-Spec Anti-Locality.

### Why AF is selected

The grammar generates a competing candidate — the AF structure — with
an intransitive-like v that does NOT introduce the agent in Spec,vP.
The agent extracts directly to Spec,CP without passing through Spec,TP,
so no SSAL violation occurs. But the agent never enters Spec,TP, so
the A-probe cannot establish Set A (ergative) agreement — violating
the lower-ranked XRef constraint.

The evaluation selects AF because SSAL ≫ XRef: avoiding the too-local
movement outranks maintaining cross-referencing agreement.

### Key insight: locality, not extraction per se

AF is triggered by the *locality of movement*, not by agent extraction
per se. Two signatures ([erlewine-2016] §§2.2, 3): intervening
preverbal material lengthens the subject's movement and obviates AF —
the full-agreement transitive resurfaces and AF becomes ungrammatical;
and long-distance subject extraction places AF on the *embedded* verb,
whose subject makes the too-local first step, while the matrix verb,
whose own subject has not moved, must stay transitive.

### Connection to Position.lean

The `specToSpecAntiLocality` predicate (Position.lean) formalizes
the constraint that blocks the transitive derivation: movement from
Spec,XP to Spec,YP is blocked when YP immediately dominates XP. In
Kaqchikel, XP = TP and YP = CP. SSAL traces to [abels-2003]'s
anti-locality theory, with refinements in [boskovic-1997] and
many subsequent papers; [erlewine-2016]'s contribution is the
specific application to Kichean AF as an OT-competing-candidate
analysis.

### Connection to Constraint

The OT tableau uses the lexicographic comparison from
`Phonology/OptimalityTheory/Tableau.lean`. The key result
`af_is_optimal` shows that AF beats the transitive under strict
ranking — and `satisfaction_ordering_incomparable` shows this requires
OT's lexicographic comparison, not satisfaction ordering's subset
inclusion.

## Anti-agreement

AF is an instance of a broader cross-linguistic pattern of
**anti-agreement**: when extraction forces a DP to skip an A-position
(to avoid SSAL), the agreement morphology associated with that
position is lost — Kaqchikel Set A under agent extraction, Trentino
Italian nominative under extraction, Karitiâna absolutive under
extraction. All derive from the same mechanism: SSAL forces skipping
an A-position, and agreement with the head at that position fails.

## Contrast with Toba Batak

Both Kaqchikel and Toba Batak have extraction restrictions derived
from anti-locality in predicate-fronting contexts, but the repair
strategies differ: Toba Batak restricts extraction to the pivot
position (structural restriction), while Kaqchikel repairs the
derivation via AF (alternation strategy). Both use
`specToSpecAntiLocality` from Position.lean.
-/

namespace Erlewine2016

open Kaqchikel Minimalist Minimalist.Voice
open Mayan (VerbForm)
open Constraints OptimalityTheory

/-! ### Competing derivations -/

/-- A candidate derivation for clause-local transitive agent extraction.
    The OT competition evaluates these: which structure best satisfies
    the ranked constraints? Both candidates share the same clausal spine
    (CP > TP > vP > VP); they differ in the v head and the agent's
    movement path. -/
inductive AFCandidate where
  /-- Normal transitive derivation: transitive v introduces agent in
      Spec,vP. A-probe on T attracts agent to Spec,TP (triggering Set A
      agreement). Subsequent Ā-extraction from Spec,TP to Spec,CP
      violates SSAL because CP immediately dominates TP. -/
  | transitiveExtraction
  /-- Agent Focus derivation: intransitive-like v, agent NOT in Spec,vP.
      Agent extracts directly to Spec,CP without passing through Spec,TP.
      No SSAL violation, but cross-referencing is incomplete: no Set A
      (ergative) agreement because the agent never enters Spec,TP. -/
  | agentFocusExtraction
  deriving DecidableEq, Repr

/-- The verb form that surfaces for each candidate. -/
def AFCandidate.verbForm : AFCandidate → VerbForm
  | .transitiveExtraction => .transitive
  | .agentFocusExtraction => .agentFocus

/-- Does this candidate violate Spec-to-Spec Anti-Locality (SSAL)?
    The transitive derivation does: the step Spec,TP → Spec,CP crosses
    no intervening maximal projection (CP immediately dominates TP). -/
def AFCandidate.violatesAntiLocality : AFCandidate → Bool
  | .transitiveExtraction => true
  | .agentFocusExtraction => false

/-- Does this candidate violate the XRef (cross-referencing) constraint?
    AF loses Set A agreement because the agent never enters Spec,TP
    where the A-probe resides. The transitive candidate maintains full
    cross-referencing (Set A + Set B). -/
def AFCandidate.violatesXRef : AFCandidate → Bool
  | .transitiveExtraction => false
  | .agentFocusExtraction => true

/-! ### The constraints and rankings -/

/-- Spec-to-Spec Anti-Locality: movement from Spec,XP to Spec,YP is
    banned when YP immediately dominates XP. Outranks XRef; outranked
    only by XRef-Participant. -/
def ssalConstraint : Constraint AFCandidate :=
  fun c => if c.violatesAntiLocality then 1 else 0

/-- XRef (cross-referencing, lowest-ranked): every argument DP must be
    cross-referenced by a pronominal morpheme on the verb (Set A for
    ergative, Set B for absolutive). -/
def xrefConstraint : Constraint AFCandidate :=
  fun c => if c.violatesXRef then 1 else 0

/-- XRef-Participant (top-ranked): every 1st/2nd-person argument must be
    cross-referenced. Parameterized by whether both arguments are
    participants: the AF candidate's single Set B slot can cross-reference
    only one of them, so AF incurs a violation exactly then; the
    full-agreement transitive never does. -/
def xrefPConstraint (bothParticipants : Bool) : Constraint AFCandidate
  | .agentFocusExtraction => if bothParticipants then 1 else 0
  | .transitiveExtraction => 0

/-- The core two-constraint competition for Kaqchikel AF: SSAL ≫ XRef.
    Decides the outcome whenever XRef-Participant is inactive (at most
    one participant argument) — see `fullRanking`. -/
def afRanking : List (Constraint AFCandidate) :=
  [ssalConstraint, xrefConstraint]

/-- The full Kaqchikel ranking ([erlewine-2016]'s (83)):
    XRef-Participant ≫ SSAL ≫ XRef. -/
def fullRanking (bothParticipants : Bool) : List (Constraint AFCandidate) :=
  [xrefPConstraint bothParticipants, ssalConstraint, xrefConstraint]

/-- The two candidates in the OT competition. -/
def afCandidates : List AFCandidate :=
  [.transitiveExtraction, .agentFocusExtraction]

/-! ### Anti-locality grounds the transitive crash -/

/-- The transitive candidate violates SSAL. The agent, having moved to
    Spec,TP via the A-probe, cannot continue to Spec,CP because CP
    immediately dominates TP — the movement is too local. -/
theorem transitive_crashes :
    AFCandidate.transitiveExtraction.violatesAntiLocality = true := rfl

/-- The AF candidate does NOT violate SSAL. The agent skips Spec,TP
    and extracts directly to Spec,CP, crossing enough structure to
    satisfy anti-locality. -/
theorem af_survives :
    AFCandidate.agentFocusExtraction.violatesAntiLocality = false := rfl

/-- The two candidates have different violation profiles: they disagree
    on at least one constraint. -/
theorem candidates_differ :
    ssalConstraint .transitiveExtraction ≠
      ssalConstraint .agentFocusExtraction ∨
    xrefConstraint .transitiveExtraction ≠
      xrefConstraint .agentFocusExtraction := by decide

/-! ### The evaluation selects AF -/

/-- AF is the unique optimal candidate. SSAL ≫ XRef means the derivation
    that avoids anti-locality wins, even though it loses Set A agreement.
    This is the central result of [erlewine-2016]. -/
theorem af_is_optimal :
    (Tableau.ofRanking afCandidates afRanking).optimal =
      {AFCandidate.agentFocusExtraction} := by
  decide

/-- The winning candidate surfaces with AF morphology: the AF suffix
    (*-ö* or *-n*), no Set A (ergative) agreement. -/
theorem af_morphology :
    AFCandidate.agentFocusExtraction.verbForm = .agentFocus ∧
    VerbForm.agentFocus.hasSetA = false ∧
    VerbForm.agentFocus.hasAFSuffix = true := ⟨rfl, rfl, rfl⟩

/-! ### Lexicographic vs satisfaction ordering -/

/-- Under componentwise ≤ (satisfaction ordering), neither candidate
    dominates: the transitive satisfies XRef but violates SSAL, while AF
    satisfies SSAL but violates XRef. Each satisfies a constraint the
    other violates — they are incomparable. OT's lexicographic ranking
    is what breaks the tie in favor of AF. -/
theorem satisfaction_ordering_incomparable :
    ¬(ssalConstraint .transitiveExtraction ≤
        ssalConstraint .agentFocusExtraction ∧
      xrefConstraint .transitiveExtraction ≤
        xrefConstraint .agentFocusExtraction) ∧
    ¬(ssalConstraint .agentFocusExtraction ≤
        ssalConstraint .transitiveExtraction ∧
      xrefConstraint .agentFocusExtraction ≤
        xrefConstraint .transitiveExtraction) := by
  decide

/-- The transitive candidate is lexicographically worse because it
    violates the HIGHER-ranked constraint (SSAL, position 0).
    AF violates only the lower-ranked constraint (XRef, position 1). -/
theorem transitive_worse_on_ssal :
    ssalConstraint .transitiveExtraction >
      ssalConstraint .agentFocusExtraction := by decide

/-! ### Anti-locality predicate grounding -/

/-- The transitive candidate's violation profile reflects
    `specToSpecAntiLocality` from Position.lean. The SSAL constraint
    assigns 1 violation to the transitive candidate and 0 to AF,
    grounding the OT violation count in the structural predicate. -/
theorem antilocality_grounded :
    ssalConstraint .transitiveExtraction = 1 ∧
    ssalConstraint .agentFocusExtraction = 0 :=
  ⟨rfl, rfl⟩

/-- AF wins because it has 0 violations of the highest-ranked constraint.
    The connection to `specToSpecAntiLocality`: the transitive derivation
    would require movement from Spec,TP to Spec,CP where CP immediately
    dominates TP — exactly what the predicate bans. AF avoids this
    by not placing the agent in Spec,TP at all. -/
theorem antilocality_drives_af :
    ssalConstraint .agentFocusExtraction = 0 ∧
    (Tableau.ofRanking afCandidates afRanking).optimal =
      {AFCandidate.agentFocusExtraction} :=
  ⟨rfl, af_is_optimal⟩

/-! ### SSAL-inactive contexts: where AF does not appear

Wherever the extractee's movement is not too short, SSAL assigns no
violations and XRef alone decides — the full-agreement transitive wins
and AF is ungrammatical. Three empirical cells share this violation
profile ([erlewine-2016] §§2.2, 3.1): patient extraction (the patient
starts in Comp,VP and never passes through Spec,TP), subject
extraction across intervening preverbal material (adverb obviation),
and the matrix clause of a long-distance extraction (the matrix
subject has not moved). Long-distance subject extraction is the two
halves side by side: the *embedded* clause is exactly the
`af_is_optimal` competition — the subject's first step, embedded
Spec,TP → Spec,CP, would be too short — so AF appears on the embedded
verb, while the matrix verb sits in an SSAL-inactive context and must
stay transitive. -/

/-- SSAL in a context where no candidate's movement is too short:
    vacuously satisfied by both candidates. -/
def ssalInactive : Constraint AFCandidate := fun _ => 0

/-- Without an anti-locality violation at stake, the full-agreement
    transitive is the unique winner — AF is ungrammatical wherever the
    subject's movement is not too short. Derives the extraction asymmetry
    (patient extraction never triggers AF), adverb obviation, and the
    transitive matrix verb under long-distance extraction. -/
theorem transitive_optimal_when_ssal_inactive :
    (Tableau.ofRanking afCandidates [ssalInactive, xrefConstraint]).optimal =
      {AFCandidate.transitiveExtraction} := by
  decide

/-! ### The participant exception (XRef-Participant) -/

/-- With at most one participant argument, XRef-Participant is inactive
    and the full ranking agrees with the core competition: AF wins. -/
theorem af_optimal_full_ranking :
    (Tableau.ofRanking afCandidates (fullRanking false)).optimal =
      {AFCandidate.agentFocusExtraction} := by
  decide

/-- When both arguments are 1st/2nd person, top-ranked XRef-Participant
    reverses the outcome: the full-agreement transitive appears even
    under subject extraction, because AF's single Set B slot would leave
    a participant argument un-cross-referenced ([erlewine-2016] §5.2). -/
theorem participant_exception :
    (Tableau.ofRanking afCandidates (fullRanking true)).optimal =
      {AFCandidate.transitiveExtraction} := by
  decide

/-! ### Reranking and the typology of Mayan AF

[erlewine-2016] §6.1 (his (84)): rerankings of the same three
constraints predict three attested language types. Kaqchikel and
Popti' instantiate XRef-Participant ≫ SSAL ≫ XRef (AF with the
participant exception; in Popti' the exception surfaces whenever the
extracted subject is a participant, since Popti's Set B strictly
targets the object). Akatek ranks SSAL above both cross-referencing
constraints: AF regardless of the arguments' φ-features. Languages
ranking XRef ≫ SSAL lack AF altogether — transitive subjects extract
with the full-agreement transitive, e.g. Ch'ol (his (93)–(94)):
grammatical extraction, not a gap. The two-candidate competition here
collapses his AF candidates (which differ in Set B target) into one. -/

/-- Akatek (SSAL ≫ {XRef-Participant, XRef}): AF wins regardless of the
    arguments' φ-features — no participant exception. -/
theorem akatek_af_regardless_of_participants (b : Bool) :
    (Tableau.ofRanking afCandidates
      [ssalConstraint, xrefPConstraint b, xrefConstraint]).optimal =
      {AFCandidate.agentFocusExtraction} := by
  cases b <;> decide

/-- A no-AF language (XRef ≫ SSAL): the full-agreement transitive wins,
    so transitive subjects extract without AF and without ill-formedness,
    at the cost of a low-ranked anti-locality violation — Ch'ol's
    pattern. -/
theorem no_af_language_transitive_wins :
    (Tableau.ofRanking afCandidates [xrefConstraint, ssalConstraint]).optimal =
      {AFCandidate.transitiveExtraction} := by
  decide

/-! ### Contrast with Q'anjob'al ([coon-mateo-pedro-preminger-2014])

Different Mayan languages circumvent syntactic ergativity through
different mechanisms. Q'anjob'al's AF Voice assigns case to the
object, freeing the phase-edge escape hatch
([coon-mateo-pedro-preminger-2014]); Kaqchikel's AF avoids the
too-local Spec,TP → Spec,CP step at the cost of Set A agreement
([erlewine-2016], for whom the case-based account is the principal
foil). Both share the underlying problem — agentive Voice is a phase
head trapping the subject — and the same surface effect, loss of
Set A. -/

open CoonMateoPedroPreminger2014 in
/-- Q'anjob'al AF Voice checks case; Kaqchikel's regular Voice does NOT.
    This is the core parametric difference: Q'anjob'al's AF is a
    case-assigning repair, while Kaqchikel's AF is a locality repair. -/
theorem af_mechanism_contrast :
    voiceAF.checksCase = true ∧
    kaqVoice.checksCase = false := ⟨rfl, rfl⟩

open CoonMateoPedroPreminger2014 in
/-- Both languages share the underlying problem: agentive Voice is a
    phase head, creating a locality boundary that traps the subject. -/
theorem shared_phase_problem :
    agentive.IsPhasal ∧ kaqVoice.IsPhasal := by decide

/-- Both Q'anjob'al and Kaqchikel are HIGH-ABS languages that mark
    transitive-subject extraction. -/
theorem both_have_extraction_asymmetries :
    Qanjobal.absPosition = .high ∧ Kaqchikel.absPosition = .high ∧
    Extraction.Marks Qanjobal.extractionMarkedPositions .subject ∧
    Extraction.Marks Kaqchikel.extractionMarkedPositions .subject :=
  ⟨rfl, rfl, by decide, by decide⟩

/-- Kaqchikel AF loses Set A agreement (the agent never enters Spec,TP).
    Q'anjob'al AF also loses Set A agreement.
    Same surface morphological effect, different underlying mechanism. -/
theorem both_af_lose_setA :
    Qanjobal.agentFocusForm.hasSetA = false ∧
    VerbForm.agentFocus.hasSetA = false := ⟨rfl, rfl⟩

/-! ### Extraction strategy -/

/-- Kaqchikel marks transitive-subject extraction with dedicated AF
    morphology (*-ö* or *-n*) — the same surface strategy-type as Mam's
    extraction marker, in contrast to Toba Batak's structural pivot
    restriction ([erlewine-2018]). Same underlying problem
    (anti-locality), different marking. -/
theorem strategy_is_af :
    extractionStrategy = .dedicatedMorpheme := rfl

end Erlewine2016
