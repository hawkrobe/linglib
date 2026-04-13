import Linglib.Theories.Syntax.Minimalism.Ellipsis.FormalMatching
import Linglib.Theories.Syntax.Minimalism.Core.Copula
import Linglib.Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2021
import Linglib.Phenomena.Ellipsis.Sluicing

/-!
# @cite{anand-hardt-mccloskey-2025} — The Domain of Formal Matching in Sluicing

@cite{anand-hardt-mccloskey-2025}

Anand, Hardt & McCloskey (2025) extend @cite{rudin-2019}'s proposal that
syntactic isomorphism in sluicing applies only to the **argument domain**
(the most inclusive ⟨e,t⟩ projection in the EP), not the entire elided clause.

## Core Contributions

1. **Small clause antecedents** (§2): perception verbs, causatives (*have*),
   adjectival SCs, absolute *with* — the antecedent can be just a small clause.
2. **Revised argument domain definition** (Def 4): cross-categorial — covers
   verbal vP, nominal nP, adjectival A, and adpositional P uniformly.
3. **Revised Syntactic Isomorphism Condition** (Def 6): isomorphism required
   only over heads within the argument domain, via head pair correspondence.
4. **Stranded prepositions** (§4): nonargument PPs are outside the argument
   domain → Chung's Generalization follows without stipulation.
5. **Copular pseudosluices** (§5): nominal antecedents with implicit copular
   elided clauses — predicted, not anomalous.

## Key Theoretical Claims

- The argument domain is the **most inclusive projection denoting ⟨e,t⟩**
  in the extended projection (Def 4). For full clauses this is vP; for
  small clauses it is the SC itself.
- The SIC requires **structural identity only within argument domains** (Def 6).
  Material outside the argument domain (T, Mod, C, nonargument PPs) may
  differ freely between antecedent and ellipsis site.
- This resolves the paradox of strict argument structure matching coexisting
  with rampant tense/modality/polarity mismatches.
-/

namespace Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2025

open Minimalism
open Minimalism.Ellipsis.FormalMatching
open Phenomena.Ellipsis.Sluicing

-- ============================================================================
-- § 1: Small Clause Antecedents (paper §2)
-- ============================================================================

/-- Antecedent types that license small clause sluicing.

    @cite{anand-hardt-mccloskey-2025} §2: the antecedent need not be
    a full clause — a small clause suffices. The embedding predicate
    (perception verb, causative, *with*) and its external argument are
    NOT part of the argument domain. -/
inductive SCAntecedentType where
  | perceptionVerb     -- (1a-c): "noticed [lights still on]", "see [me smiling]"
  | causativeHave      -- (3c): "have the students write"
  | causativeMake      -- (3b): "made employees contribute"
  | adjectivalConsider -- (3d): "considers early treatment appropriate"
  | absoluteWith       -- (3e): "with [the campaign on hold]"
  deriving DecidableEq, Repr

/-- Map SC antecedent types to their predicate category.
    Perception verb and causative complements are V-headed SCs;
    adjectival complements are A-headed; absolute *with* selects a
    P-headed SC (e.g., "the campaign on hold" — predicate *on hold*
    is a PP headed by the preposition *on*). -/
def SCAntecedentType.toSCPred : SCAntecedentType → SCPredCategory
  | .perceptionVerb     => .V
  | .causativeHave      => .V
  | .causativeMake      => .V
  | .adjectivalConsider => .A
  | .absoluteWith       => .P

/-- Small clause sluicing example from the paper. -/
structure SCSluicingDatum where
  sentence : String
  antecedent : String
  scAntecedent : String
  whPhrase : String
  elided : String
  antecedentType : SCAntecedentType
  grammatical : Bool := true
  corpusId : Option Nat := none
  deriving Repr

-- Perception verb SC sluicing (paper ex. 1a)

def perceptionSluice1a : SCSluicingDatum where
  sentence := "The bodies were discovered just before 1 a.m. when an employee noticed [lights still on] almost three hours after closing time and went inside to see why."
  antecedent := "an employee noticed [lights still on]"
  scAntecedent := "lights still on"
  whPhrase := "why"
  elided := "lights were still on"
  antecedentType := .perceptionVerb
  corpusId := some 72082

-- Perception verb SC sluicing (paper ex. 1b)

def perceptionSluice1b : SCSluicingDatum where
  sentence := "When you see me [smiling on the weekend], you'll know why."
  antecedent := "you see me [smiling on the weekend]"
  scAntecedent := "me smiling on the weekend"
  whPhrase := "why"
  elided := "I'm smiling"
  antecedentType := .perceptionVerb
  corpusId := some 96338

-- Causative have SC sluicing (paper ex. 3c)

def causativeHaveSluice : SCSluicingDatum where
  sentence := "I have the students write a series of literature reviews. How many is up to them, but each student has to have written at least 20,000 words by the end of the quarter."
  antecedent := "I have the students write a series of literature reviews"
  scAntecedent := "the students write a series of literature reviews"
  whPhrase := "how many"
  elided := "students MODAL write"
  antecedentType := .causativeHave

-- Absolute with SC sluicing (paper ex. 3e)

def absoluteWithSluice : SCSluicingDatum where
  sentence := "With the campaign on hold—and who knows for how long—Biden is left without any regular way to make his case to the electorate."
  antecedent := "the campaign on hold"
  scAntecedent := "the campaign on hold"
  whPhrase := "how long"
  elided := "the campaign will be on hold"
  antecedentType := .absoluteWith

-- ============================================================================
-- § 2: Cross-Categorial Argument Domain (paper §3, Def 4)
-- ============================================================================

/-- The argument domain is cross-categorial: the same definition (Def 4)
    applies uniformly to verbal, nominal, adjectival, and adpositional EPs.
    For full clauses/DPs, the boundary is at the first functional head (v/n);
    for SCs, the boundary is the lexical head itself. -/
theorem argdomain_uniformity :
    -- Full clause → vP
    argumentDomainCat .C = .v ∧
    -- Full DP → nP
    argumentDomainCat .D = .n ∧
    -- Verbal SC → V
    argumentDomainCat .V = .V ∧
    -- Adjectival SC → A
    argumentDomainCat .A = .A ∧
    -- Prepositional SC → P
    argumentDomainCat .P = .P ∧
    -- Nominal SC → N
    argumentDomainCat .N = .N := by decide

/-- SC argument domains are strictly smaller than full clause argument
    domains: at F0 vs F1. This means the SIC imposes fewer constraints
    on SC sluicing — only the lexical head pair must match. -/
theorem sc_strictly_smaller_than_clause :
    fValue (argumentDomainCat .V) < fValue (argumentDomainCat .C) ∧
    fValue (argumentDomainCat .A) < fValue (argumentDomainCat .C) ∧
    fValue (argumentDomainCat .P) < fValue (argumentDomainCat .C) ∧
    fValue (argumentDomainCat .N) < fValue (argumentDomainCat .C) := by decide

/-- Everything outside the argument domain — T, Mod, C, and their
    interpretive properties (tense, modality, polarity, force) — may
    differ freely between antecedent and ellipsis site. The SIC is
    agnostic to these categories. -/
theorem outside_argdomain_free :
    isInArgumentDomain .T .C = false ∧
    isInArgumentDomain .Mod .C = false ∧
    isInArgumentDomain .Neg .C = false ∧
    isInArgumentDomain .C .C = false ∧
    isInArgumentDomain .Fin .C = false := by decide

-- ============================================================================
-- § 3: Active–Passive Voice Mismatch Blocking (paper §3, ex. 10–11)
-- ============================================================================

-- The paper shows that voice mismatches are blocked even in its revised
-- framework: the light verb v is inside the argument domain, and
-- active v[agentive] ≠ passive v[nonThematic].

/-- Paper ex. (10)–(11): voice mismatches are blocked by the SIC.
    v[nonThematic] (unaccusative/passive) ≠ v[agentive] (transitive),
    and both are within the argument domain.

    Ex. (10): "*All the rules around here have changed, but I just
    can't work out who." — unaccusative antecedent, transitive ellipsis.

    Ex. (11a): "*It's important to establish when he was robbed and,
    more important, who." — passive antecedent, active ellipsis.

    Both reduce to the same structural mismatch: v[nonThematic] vs
    v[agentive] within the argument domain. -/
theorem voice_mismatch_blocked :
    structurallyIdentical passiveVP activeVP = false := by
  decide

-- ============================================================================
-- § 4: Stranded Prepositions — Chung's Generalization (paper §4)
-- ============================================================================

/-- Paper ex. (13a): stranded nonargument preposition with no antecedent source.

    "The board believes that a 'one-size-fits-all' approach to financial
    market regulation is inappropriate. ... what form [government regulation
    is necessary IN]."

    The stranded *in* marks a nonargument PP — merged above vP, outside
    the argument domain. The SIC does not require it to match. -/
def strandedPrepEx13a : SluicingDatum where
  sentence := "The board believes a one-size-fits-all approach to financial market regulation is inappropriate ... what form [government regulation is necessary IN]."
  antecedent := "government regulation is necessary"
  innerAntecedent := "a one-size-fits-all approach"
  whPhrase := "what form"
  elided := "government regulation is necessary in"
  grammatical := true
  source := "SCSS [138195]"

/-- Paper ex. (13b): stranded nonargument PP *on* with no antecedent source.

    "When the officer asked me about her, I remembered meeting her but
    I couldn't say what date [I MET her ON]."  -/
def strandedPrepEx13b : SluicingDatum where
  sentence := "When the officer asked me about her, I remembered meeting her but I couldn't say what date [I MET her ON]."
  antecedent := "I remembered meeting her"
  innerAntecedent := "her"
  whPhrase := "what date"
  elided := "I met her on"
  grammatical := true
  source := "SCSS [F38]"

/-- The SIC correctly licenses sluicing with stranded nonargument PPs:
    filtering removes the nonargument PP from the SIC check, and the
    remaining argument-domain head pairs match. -/
theorem stranded_nonadjunct_pp_licensed :
    let antecedentPairs : List HeadPair :=
      [⟨.v, .V, none, some .agentive, none⟩, ⟨.V, .D, none, none, none⟩]
    let ellipsisPairs : List HeadPair :=
      [⟨.v, .V, none, some .agentive, none⟩, ⟨.V, .D, none, none, none⟩,
       ⟨.P, .D, none, none, some false⟩]
    structurallyIdentical
      (filterArgumentPairs antecedentPairs)
      (filterArgumentPairs ellipsisPairs) = true := by
  decide

/-- Paper ex. (12): The argument/nonargument PP contrast.

    (12a) "They're furious but it's unclear who(m)" — OK (sprouted PP
    *at who(m)* not fully contained in ellipsis site after movement)
    (12b) "They're furious but it's unclear who at" — OK (pied-piped)
    (12c) "*They're furious but it's unclear who" — blocked: *at* is
    within the argument domain (selected by *furious*), has no
    antecedent source, and fails the SIC.

    This is the key contrast: (12a-b) work because the PP *at whom*
    is either not fully within the ellipsis site (12a) or is matched
    by pied-piping (12b). (12c) fails because the argument-marking
    preposition *at* is inside the argument domain and must match. -/
def argumentPPEx12c : SluicingDatum where
  sentence := "*They're furious but it's unclear who."
  antecedent := "they're furious"
  innerAntecedent := ""
  whPhrase := "who"
  elided := "they are furious at"
  grammatical := false
  source := "Anand, Hardt & McCloskey 2025 ex. 12c"

/-- Argument PP *at* (selected by *furious*) is within the argument
    domain and must match. Since it has no counterpart in the
    antecedent's argument domain, the SIC blocks (12c). -/
theorem argument_pp_blocks_sluicing :
    let antecedentPairs : List HeadPair :=
      [⟨.A, .D, none, none, none⟩]  -- A-headed SC: [furious]
    let ellipsisPairs : List HeadPair :=
      [⟨.A, .D, none, none, none⟩,
       ⟨.P, .D, none, none, some true⟩]  -- arg PP *at*
    -- Argument PP is NOT filtered out
    filterArgumentPairs ellipsisPairs = ellipsisPairs ∧
    -- So the SIC fails: 1 ≠ 2 head pairs
    structurallyIdentical
      (filterArgumentPairs antecedentPairs)
      (filterArgumentPairs ellipsisPairs) = false := by
  exact ⟨rfl, rfl⟩

/-- Contrast: paper ex. (15a-b) — sluicing fails completely when the
    argument domain itself has no match.

    "*He is very loyal, but I don't know who." — no vP in antecedent
    whose argument domain matches "who [he is loyal to]". -/
def failedSluiceEx15a : SluicingDatum where
  sentence := "*He is very loyal, but I don't know who."
  antecedent := "he is very loyal"
  innerAntecedent := ""
  whPhrase := "who"
  elided := "he is loyal to"
  grammatical := false
  source := "Anand, Hardt & McCloskey 2025 ex. 15a"

-- ============================================================================
-- § 5: Copular Pseudosluices (paper §5)
-- ============================================================================

/-- A copular pseudosluice: the antecedent is a nominal, and the elided
    clause is a copular clause whose argument domain is a small clause.

    @cite{anand-hardt-mccloskey-2025} §5: These are NOT anomalous.
    The antecedent nominal provides the SC subject; the elided clause
    is [TP T be [SC subject predicate]], whose argument domain is
    just the SC. The SC in the antecedent context (the bare nominal)
    matches the SC argument domain of the elided clause. -/
structure CopularPseudosluice where
  sentence : String
  nominalAntecedent : String
  whRemnant : String
  impliedCopularClause : String
  grammatical : Bool := true
  corpusId : Option Nat := none
  deriving Repr

-- Paper ex. (18a): nominal antecedent → copular pseudosluice

def copularEx18a : CopularPseudosluice where
  sentence := "Bradley said that he has not shut the door to [a presidential race], though he would not say when [that presidential race MODAL BE]."
  nominalAntecedent := "a presidential race"
  whRemnant := "when"
  impliedCopularClause := "that presidential race would be"
  corpusId := some 176498

-- Paper ex. (18b): nominal antecedent → copular pseudosluice

def copularEx18b : CopularPseudosluice where
  sentence := "The doctors anticipate [a full recovery] for me, but they really don't know when [that recovery MODAL BE]."
  nominalAntecedent := "a full recovery"
  whRemnant := "when"
  impliedCopularClause := "that recovery will be"
  corpusId := some 76117

-- Paper ex. (19a): existential copular pseudosluice

def copularEx19a : CopularPseudosluice where
  sentence := "[A cut] appears almost certain this year; the question is how soon [THERE MODAL BE a cut], and by how much [THERE MODAL BE a cut]."
  nominalAntecedent := "a cut"
  whRemnant := "how soon"
  impliedCopularClause := "there will be a cut"
  corpusId := some 15811

/-- The argument domain of a copular pseudosluice is an N-headed SC.
    *be* selects an SC complement; the SC predicate is nominal (N).
    This is smaller than a full clause's argument domain. -/
theorem copular_pseudosluice_argdomain :
    argumentDomainCat .N = .N := by decide

/-- The copula in a pseudosluice spells out as BE (not HAVE): the
    implicit clause has expletive/middle Voice (no external argument
    introducing transitive Voice), triggering the elsewhere VI rule.
    This connects to @cite{myler-2016}'s copula theory. -/
theorem pseudosluice_copula_is_be :
    copulaVI voiceMiddle = .be := rfl

/-- Copular pseudosluice SIC: the argument domain of the implicit
    copular clause is an N-headed SC. The SIC requires only that the
    head pair ⟨N, D⟩ matches between the elided SC and the antecedent
    nominal. A nominal antecedent trivially provides this. -/
theorem copular_pseudosluice_sic :
    let scPairs : List HeadPair := [⟨.N, .D, none, none, none⟩]
    structurallyIdentical scPairs scPairs = true :=
  single_pair_matches _

-- ============================================================================
-- § 6: Anti-PredP Argument (paper §5, ex. 22–24)
-- ============================================================================

/-- @cite{matushansky-2019} argues that small clauses lack a functional
    Pred head — the subject occupies the specifier of the predicate itself.
    The paper provides an indirect argument from ellipsis: if PredP existed,
    the SC node would be inside the argument domain, requiring a match in
    the antecedent. Since copular pseudosluices (18)–(19) are grammatical
    with nominal antecedents that have no SC node, either PredP does not
    exist (Matushansky) or the SIC checks only heads, not phrasal nodes.

    @cite{anand-hardt-mccloskey-2025} Def 6 resolves this by requiring
    identity only for **heads** in ℋ, not for all nodes. The SC node
    itself is excluded from the matching calculation. -/
theorem sic_checks_heads_not_nodes :
    -- A single head pair ⟨N, D⟩ is sufficient for copular pseudosluice
    -- licensing — no SC-level phrasal node needs matching
    structurallyIdentical [⟨.N, .D, none, none, none⟩] [⟨.N, .D, none, none, none⟩] = true :=
  single_pair_matches _

-- ============================================================================
-- § 7: Consistency with 2021 Corpus Data
-- ============================================================================

-- The revised SIC in @cite{anand-hardt-mccloskey-2025} makes the same
-- predictions as the original SIC for all full-clause sluicing. The new
-- contributions concern SC antecedents, stranded PPs, and copular
-- pseudosluices — cases that the original framework did not address.

/-- The 2025 SIC revision is consistent with the 2021 corpus findings:
    every dimension inside the argument domain has 0 corpus attestations
    of mismatches; every dimension outside has nonzero attestations.
    This imports and extends the bridge theorems from
    @cite{anand-hardt-mccloskey-2021}. -/
theorem consistent_with_2021_corpus :
    isInArgumentDomain .v .C = true ∧
    AnandHardtMcCloskey2021.MismatchDimension.corpusCount .argumentStructure = 0 ∧
    isInArgumentDomain .T .C = false ∧
    AnandHardtMcCloskey2021.MismatchDimension.corpusCount .tense > 0 ∧
    isInArgumentDomain .Mod .C = false ∧
    AnandHardtMcCloskey2021.MismatchDimension.corpusCount .modality > 0 :=
  ⟨by decide, rfl, by decide, by decide, by decide, by decide⟩

/-- The 2021 corpus found 17 cases of stranded prepositions with no
    antecedent source. @cite{anand-hardt-mccloskey-2025} §4 predicts this:
    nonargument PPs are outside the argument domain (P is at F0 but
    nonargument PPs merge above vP), so the SIC does not require matching.
    The prediction: filtering out nonargument PPs from both sides should
    make the remaining head pairs structurally identical. -/
theorem stranded_prep_prediction :
    -- Nonargument PP filtering removes unmatched stranded preps
    let withStrandedPrep : List HeadPair :=
      [⟨.v, .V, none, some .agentive, none⟩, ⟨.V, .D, none, none, none⟩,
       ⟨.P, .D, none, none, some false⟩]  -- nonarg PP
    -- Without filtering: mismatch (3 ≠ 2 head pairs)
    structurallyIdentical activeVP withStrandedPrep = false ∧
    -- With filtering: match (nonarg PP removed)
    structurallyIdentical
      (filterArgumentPairs activeVP)
      (filterArgumentPairs withStrandedPrep) = true := by
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Collected Data
-- ============================================================================

def scSluicingData : List SCSluicingDatum :=
  [perceptionSluice1a, perceptionSluice1b, causativeHaveSluice, absoluteWithSluice]

def copularPseudosluiceData : List CopularPseudosluice :=
  [copularEx18a, copularEx18b, copularEx19a]

end Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2025
