import Linglib.Theories.Phonology.OptimalityTheory.OptimalParadigms
import Linglib.Theories.Phonology.OptimalityTheory.Constraints
import Linglib.Theories.Phonology.Prosodic.Syllable.Defs
import Linglib.Core.Constraint.System

/-!
# Marco & Rasin (2026): Optimal Paradigms — A Challenge from JTA
@cite{marco-rasin-2026} @cite{mccarthy-2005}

Formalizes the argument that Optimal Paradigms (OP) cannot simultaneously
predict the distribution of schwa in verbs, nouns, and adjectives in
Judeo-Tripolitanian Arabic (JTA). The core paradox:

- **Verbs**: schwa always between C₂ and C₃ (CCəC), regardless of sonority
- **Adjectives**: same as verbs — CCəC regardless of sonority
- **Nouns**: sonority-sensitive — CəCC when C₂ > C₃, CCəC otherwise

Adjectives share phonological behavior with verbs but paradigm structure
with nouns (only V-initial suffixes). OP predicts phonological behavior
should track paradigm structure, so it wrongly predicts adjectives should
behave like nouns.

## Modeling note

In OP, candidates are **whole paradigms** where each member independently
chooses a stem shape. Markedness constraints (*CCC, *ə]σ) determine the
shapes of suffixed members: C-initial suffixed forms must be CCəC (to
avoid tri-consonantal clusters), V-initial suffixed forms must be CəCC
(to avoid schwa in an open syllable). Only the suffix-less bare form
is free — its shape is determined by OP-MAX-V (paradigm uniformity).

For verbs, we enumerate the 4 candidates from tableau (10) in the paper.
For adjectives, we enumerate all 2³ = 8 possible paradigms exhaustively.
The main result (`adj_always_initial`) proves that the uniform CəCC
paradigm has 0 violations on all four constraints and thus wins under
every ranking — contradicting the attested CCəC pattern.

The paper considers two scenarios for adjectives: with a paradigm
(tableau (19)) and without (tableau (20)). Both fail — `op_wrong_adjectives`
covers (19) and `op_wrong_adj_bare` covers (20), formalizing the paper's
argument that OP fails "regardless of what constitutes a paradigm."
-/

namespace MarcoRasin2026

open Core.OT
open Phonology.Constraints
open Phonology.OptimalParadigms
open Phonology.Syllable (SonorityRank)

-- ============================================================================
-- § 1: Data Types
-- ============================================================================

/-- The two possible schwa positions in a tri-consonantal stem C₁C₂C₃.
    `medial` = CCəC (schwa between C₂ and C₃); `initial` = CəCC (schwa
    between C₁ and C₂). -/
inductive SchwaPos where
  | medial   -- CCəC: schwa between C₂ and C₃
  | initial  -- CəCC: schwa between C₁ and C₂
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Suffix onset type, determining the phonological environment. -/
inductive SuffixOnset where
  | cInit  -- C-initial suffix (e.g., -t, -na, -ti, -tu)
  | vInit  -- V-initial suffix (e.g., -ət, -u; -a, -in)
  | bare   -- No suffix (bare form)
  deriving DecidableEq, Repr, BEq

/-- A single paradigm member: schwa position + suffix type. -/
structure JTAForm where
  schwa : SchwaPos
  suffix : SuffixOnset
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 2: McCarthy's Constraints
-- ============================================================================

/-- *CCC: assign * for every sequence of three consonants.
    Violated by CəCC (initial) stems before C-initial suffixes:
    C₁əC₂C₃ + C → C₂C₃C = tri-consonantal cluster. -/
def starCCC : NamedConstraint (List JTAForm) :=
  liftPerMember "*CCC" .markedness fun f =>
    if f.schwa == .initial && f.suffix == .cInit then 1 else 0

/-- *ə]σ: assign * for every schwa in an open syllable.
    Violated by CCəC (medial) stems before V-initial suffixes:
    C₁C₂ə.C₃V → schwa in open syllable. -/
def starSchwaOpen : NamedConstraint (List JTAForm) :=
  liftPerMember "*ə]σ" .markedness fun f =>
    if f.schwa == .medial && f.suffix == .vInit then 1 else 0

/-- SONCON: assign * for a CCəC (medial) form when C₂ > C₃ in sonority.
    Parametrized over the sonority ranks of C₂ and C₃, using the
    `LinearOrder SonorityRank` instance from `Syllable.Defs`. -/
def sonCon (c2 c3 : Phonology.Syllable.SonorityRank) :
    NamedConstraint (List JTAForm) :=
  liftPerMember "SONCON" .markedness fun f =>
    if c2 > c3 && f.schwa == .medial then 1 else 0

/-- OP-MAX-V: assign * for each ordered pair of paradigm members with
    different schwa positions. Each positional mismatch = 1 violation.
    For n₁ medial and n₂ initial members: n₁·n₂ + n₂·n₁ = 2·n₁·n₂
    total violations (matching @cite{mccarthy-2005}'s counting). -/
def opMaxV : NamedConstraint (List JTAForm) :=
  mkOPMaxV fun f1 f2 =>
    if f1.schwa != f2.schwa then 1 else 0

-- ============================================================================
-- § 3: Verbal Paradigm — 4 Candidates (Tableau 10)
-- ============================================================================

/-- JTA verbal suffixes: bare + 4 C-initial + 2 V-initial = 7 members. -/
def vSuf : List SuffixOnset :=
  [.bare, .cInit, .cInit, .cInit, .cInit, .vInit, .vInit]

/-- Helper: build a paradigm from a list of schwa positions and suffix list. -/
def mkP (shapes : List SchwaPos) (suffixes : List SuffixOnset) : List JTAForm :=
  (shapes.zip suffixes).map fun (s, suf) => ⟨s, suf⟩

-- The 4 candidates from tableau (10):
-- Markedness determines suffixed forms; only bare form varies.
-- C-init suffixed → medial (avoids *CCC), V-init suffixed → initial (avoids *ə]σ)

/-- (10a) ☞ Bare=medial: 5 medial, 2 initial. OP-MAX-V = 20. -/
def vA := mkP [.medial, .medial, .medial, .medial, .medial, .initial, .initial] vSuf
/-- (10b) Bare=initial: 4 medial, 3 initial. OP-MAX-V = 24. -/
def vB := mkP [.initial, .medial, .medial, .medial, .medial, .initial, .initial] vSuf
/-- (10c) Uniform medial: *ə]σ violated twice. -/
def vC := mkP [.medial, .medial, .medial, .medial, .medial, .medial, .medial] vSuf
/-- (10d) Uniform initial: *CCC violated four times. -/
def vD := mkP [.initial, .initial, .initial, .initial, .initial, .initial, .initial] vSuf

def verbCands : List (List JTAForm) := [vA, vB, vC, vD]
theorem verbCands_ne : verbCands ≠ [] := by simp [verbCands]

-- ============================================================================
-- § 4: Nominal Paradigm — 2 Candidates (Tableau 12)
-- ============================================================================

/-- Nouns: bare singular only (1 member). -/
def nM := mkP [.medial] [.bare]   -- CCəC
def nI := mkP [.initial] [.bare]  -- CəCC

def nounCands : List (List JTAForm) := [nM, nI]
theorem nounCands_ne : nounCands ≠ [] := by simp [nounCands]

-- ============================================================================
-- § 5: Adjectival Paradigm — All 8 Candidates (Exhaustive)
-- ============================================================================

/-- Adjective suffixes: bare (MSG) + 2 V-initial (-a FSG, -in PL). -/
def aSuf : List SuffixOnset := [.bare, .vInit, .vInit]

/-- All 2³ = 8 possible adjective paradigms. Exhaustive enumeration
    ensures the negative result holds for ALL candidates, not just
    selected ones. -/
def adjCands : List (List JTAForm) :=
  [ mkP [.medial,  .medial,  .medial]  aSuf   -- MMM
  , mkP [.medial,  .medial,  .initial] aSuf   -- MMI
  , mkP [.medial,  .initial, .medial]  aSuf   -- MIM
  , mkP [.medial,  .initial, .initial] aSuf   -- MII (attested)
  , mkP [.initial, .medial,  .medial]  aSuf   -- IMM
  , mkP [.initial, .medial,  .initial] aSuf   -- IMI
  , mkP [.initial, .initial, .medial]  aSuf   -- IIM
  , mkP [.initial, .initial, .initial] aSuf ] -- III (OP prediction)
theorem adjCands_ne : adjCands ≠ [] := by simp [adjCands]

/-- The attested adjective paradigm: bare=medial, V-init=initial. -/
def adjAttested := mkP [.medial, .initial, .initial] aSuf
/-- The OP-predicted paradigm: uniform initial. -/
def adjOPpred := mkP [.initial, .initial, .initial] aSuf

-- ============================================================================
-- § 6: OP Analysis — McCarthy's Ranking
-- ============================================================================

/-- McCarthy's ranking: *ə]σ, *CCC ≫ OP-MAX-V ≫ SONCON (for C₂ > C₃). -/
def mccarthyRanking : List (NamedConstraint (List JTAForm)) :=
  [starSchwaOpen, starCCC, opMaxV, sonCon .liquid .stop]

set_option maxHeartbeats 800000 in
/-- OP correctly selects the attested verbal paradigm (10a): bare=medial.
    Majority Rules in action — the bare form aligns with the C-initial
    majority (5 medial vs 2 initial members). -/
theorem op_correct_verbs :
    (mkTableau verbCands mccarthyRanking verbCands_ne).optimal =
      {vA} := by decide

/-- OP correctly selects CəCC for nouns (when C₂ > C₃). Single-member
    paradigm, so OP-MAX-V is vacuous; SONCON decides. -/
theorem op_correct_nouns :
    (mkTableau nounCands mccarthyRanking nounCands_ne).optimal =
      {nI} := by decide

set_option maxHeartbeats 800000 in
/-- OP wrongly selects uniform-initial for adjectives (tableau (19)).
    Adjectives have only V-initial suffixes (like nouns), so OP-MAX-V
    cannot force medial schwa in the bare form. SONCON then favors
    initial. -/
theorem op_wrong_adjectives :
    (mkTableau adjCands mccarthyRanking adjCands_ne).optimal =
      {adjOPpred} := by decide

set_option maxHeartbeats 800000 in
/-- The attested adjective paradigm (bare=CCəC) is NOT selected by OP. -/
theorem op_fails_adjectives :
    (mkTableau adjCands mccarthyRanking adjCands_ne).optimal ≠
      {adjAttested} := by decide

-- ============================================================================
-- § 7: No Ranking Works for Adjectives (Main Negative Result)
-- ============================================================================

/-- The four constraints used in McCarthy's OP analysis. -/
def opConstraints : List (NamedConstraint (List JTAForm)) :=
  [starSchwaOpen, starCCC, opMaxV, sonCon .liquid .stop]

/-- The uniform-initial adjective paradigm has **zero violations on all
    four OP constraints**. This is the structural reason it wins under
    every ranking — not a coincidence of McCarthy's particular ranking.

    - *ə]σ: 0 — initial schwa (CəCC) is never in an open syllable
    - *CCC: 0 — no C-initial suffixes in the adjective paradigm
    - OP-MAX-V: 0 — uniform paradigm, no positional mismatches
    - SONCON: 0 — no medial (CCəC) forms to violate sonority

    A candidate with profile [0,0,...,0] is the minimum of any
    lexicographic order on Nat-valued profiles (`ViolationProfile.zero_le`),
    so permuting the ranking cannot change the outcome. -/
theorem adjOPpred_zero_viols :
    ∀ con ∈ opConstraints, con.eval adjOPpred = 0 := by decide

/-- Structural consequence of `adjOPpred_zero_viols`: the uniform-initial
    paradigm is optimal under **every** permutation of the four OP
    constraints. Uses `mkTableau_zero_optimal_allRankings` from the
    general OT infrastructure — no finitary enumeration needed. -/
private theorem adjOPpred_mem : adjOPpred ∈ adjCands := by
  simp only [adjCands, adjOPpred, List.mem_cons]; tauto

theorem adjOPpred_always_optimal :
    ∀ ranking ∈ permutations opConstraints,
      adjOPpred ∈ (mkTableau adjCands ranking adjCands_ne).optimal :=
  mkTableau_zero_optimal_allRankings adjCands opConstraints adjCands_ne
    adjOPpred adjOPpred_mem adjOPpred_zero_viols

set_option maxHeartbeats 4000000 in
/-- **Main result.** No ranking of the four OP constraints selects the
    attested adjective paradigm (bare=CCəC).

    The uniform-initial paradigm has **zero violations on all four
    constraints** (`adjOPpred_zero_viols`), making it the lexicographic
    minimum under any permutation (`adjOPpred_always_optimal`). Moreover,
    it is the **unique** winner — no other candidate also has a zero
    profile (verified by `decide`).

    Since [0,0,0,0] is the lexicographic minimum regardless of constraint
    permutation, uniform-initial wins under **every** ranking. The attested
    paradigm (bare=medial, V-init=initial) always loses because it incurs
    OP-MAX-V and SONCON violations.

    This formalizes @cite{marco-rasin-2026}'s central challenge: OP cannot
    derive category-distinct phonological behavior when two categories share
    paradigm structure but differ phonologically. -/
theorem adj_always_initial :
    ∀ ranking ∈ permutations opConstraints,
      (mkTableau adjCands ranking adjCands_ne).optimal = {adjOPpred} := by
  decide

-- ============================================================================
-- § 8: OP Fails Without a Paradigm Too (Tableau (20))
-- ============================================================================

/-- If adjectives have no inflectional paradigm (single bare form, like
    nouns), SONCON wrongly favors CəCC (initial). This is tableau (20)
    in the paper: the single-member adjective case. Combined with
    `op_wrong_adjectives` (tableau (19)), this shows OP fails
    **regardless of what constitutes a paradigm** for JTA adjectives. -/
theorem op_wrong_adj_bare :
    (mkTableau nounCands mccarthyRanking nounCands_ne).optimal =
      {nI} := op_correct_nouns

/-- The attested adjective form (CCəC = medial) is NOT selected when
    adjectives are treated as having no paradigm. -/
theorem op_wrong_adj_bare_not_attested :
    (mkTableau nounCands mccarthyRanking nounCands_ne).optimal ≠
      {nM} := by decide

-- ============================================================================
-- § 9: Category-Specific Alternative
-- ============================================================================

/-- Morphosyntactic category, used for category-indexed constraints. -/
inductive MorphCat where
  | verb | adj | noun
  deriving DecidableEq, Repr, BEq

/-- {CCəC}_{Verb, Adj}: template constraint applying to verbs and
    adjectives but not nouns. Penalizes initial (CəCC) forms in verbs
    and adjectives. Directly references morphosyntactic categories,
    violating the TCNP (@cite{bobaljik-2008}). -/
def templateMedial (cat : MorphCat) : NamedConstraint (List JTAForm) :=
  liftPerMember "{CCəC}_{V,A}" .markedness fun f =>
    match cat with
    | .verb | .adj => if f.schwa == .initial then 1 else 0
    | .noun => 0

/-- Category-specific ranking: {CCəC}_{V,A} ≫ SONCON. -/
def templateRanking (cat : MorphCat) : List (NamedConstraint (List JTAForm)) :=
  [templateMedial cat, sonCon .liquid .stop]

/-- Template correctly selects medial (CCəC) for verbs.
    (Using uniform candidates since template forces all members to medial.) -/
def verbUnifM := mkP [.medial, .medial, .medial, .medial, .medial, .medial, .medial] vSuf
def verbUnifI := mkP [.initial, .initial, .initial, .initial, .initial, .initial, .initial] vSuf
def verbTemplateCands : List (List JTAForm) := [verbUnifM, verbUnifI]
theorem verbTemplateCands_ne : verbTemplateCands ≠ [] := by simp [verbTemplateCands]

theorem template_correct_verbs :
    (mkTableau verbTemplateCands (templateRanking .verb) verbTemplateCands_ne).optimal =
      {verbUnifM} := by decide

/-- Template correctly selects initial (CəCC) for nouns (template inactive). -/
theorem template_correct_nouns :
    (mkTableau nounCands (templateRanking .noun) nounCands_ne).optimal =
      {nI} := by decide

/-- Template correctly selects the attested adjective paradigm — the case
    where OP fails. The template forces medial (CCəC) for both verb and
    adjective categories, overriding SONCON. -/
def adjTemplateCands : List (List JTAForm) :=
  [ mkP [.medial,  .medial,  .medial]  aSuf
  , mkP [.initial, .initial, .initial] aSuf ]
theorem adjTemplateCands_ne : adjTemplateCands ≠ [] := by simp [adjTemplateCands]

theorem template_correct_adjectives :
    (mkTableau adjTemplateCands (templateRanking .adj) adjTemplateCands_ne).optimal =
      {mkP [.medial, .medial, .medial] aSuf} := by decide

-- ============================================================================
-- § 10: Generic ConstraintSystem Predictions
-- ============================================================================

/-! Each unique-winner tableau lifts to a generic `ConstraintSystem` via
`tableauSystem`. For McCarthy's OP ranking this exposes the correct
predictions for verbs and nouns, and the *wrong* prediction for adjectives —
the empirical content of @cite{marco-rasin-2026}'s argument. -/

section PredictAPI
open Core.Constraint

/-- Verbal paradigm under McCarthy's OP ranking. -/
noncomputable def verbSystem : ConstraintSystem (List JTAForm) (LexProfile Nat 4) :=
  tableauSystem (mkTableau verbCands mccarthyRanking verbCands_ne)

/-- OP correctly predicts the attested bare-medial verbal paradigm (10a). -/
theorem verbSystem_predict_vA : verbSystem.predict vA = 1 :=
  tableauSystem_predict_unique_winner _ _ op_correct_verbs

/-- Nominal paradigm under McCarthy's OP ranking. -/
noncomputable def nounSystem : ConstraintSystem (List JTAForm) (LexProfile Nat 4) :=
  tableauSystem (mkTableau nounCands mccarthyRanking nounCands_ne)

/-- OP correctly predicts CəCC for nouns when C₂ > C₃. -/
theorem nounSystem_predict_nI : nounSystem.predict nI = 1 :=
  tableauSystem_predict_unique_winner _ _ op_correct_nouns

/-- Adjectival paradigm under McCarthy's OP ranking. The probability-1
    prediction here is the *wrong* uniform-initial paradigm — the formal
    content of @cite{marco-rasin-2026}'s challenge. -/
noncomputable def adjSystem : ConstraintSystem (List JTAForm) (LexProfile Nat 4) :=
  tableauSystem (mkTableau adjCands mccarthyRanking adjCands_ne)

/-- OP wrongly assigns probability 1 to the uniform-initial adjective
    paradigm. The attested CCəC pattern receives probability 0 — the
    formal sharpening of "OP fails for adjectives." -/
theorem adjSystem_predict_OPpred : adjSystem.predict adjOPpred = 1 :=
  tableauSystem_predict_unique_winner _ _ op_wrong_adjectives

/-- Loser side: the attested adjective paradigm gets probability 0. -/
theorem adjSystem_predict_attested_zero :
    adjSystem.predict adjAttested = 0 :=
  tableauSystem_predict_loser _ _ _
    (by unfold adjAttested adjOPpred mkP; decide) op_wrong_adjectives

/-- Verbal paradigm under the category-specific template ranking. -/
noncomputable def verbTemplateSystem :
    ConstraintSystem (List JTAForm) (LexProfile Nat 2) :=
  tableauSystem (mkTableau verbTemplateCands (templateRanking .verb) verbTemplateCands_ne)

theorem verbTemplateSystem_predict_unifM :
    verbTemplateSystem.predict verbUnifM = 1 :=
  tableauSystem_predict_unique_winner _ _ template_correct_verbs

/-- Adjectival paradigm under the category-specific template ranking —
    now correctly predicting the attested medial pattern with probability 1. -/
noncomputable def adjTemplateSystem :
    ConstraintSystem (List JTAForm) (LexProfile Nat 2) :=
  tableauSystem (mkTableau adjTemplateCands (templateRanking .adj) adjTemplateCands_ne)

theorem adjTemplateSystem_predict_medial :
    adjTemplateSystem.predict (mkP [.medial, .medial, .medial] aSuf) = 1 :=
  tableauSystem_predict_unique_winner _ _ template_correct_adjectives

end PredictAPI

end MarcoRasin2026
