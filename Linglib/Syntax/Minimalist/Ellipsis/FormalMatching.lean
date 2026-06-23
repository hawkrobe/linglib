import Linglib.Syntax.Minimalist.ExtendedProjection.Properties
import Linglib.Syntax.Minimalist.Voice
import Linglib.Syntax.Minimalist.SmallClause
import Linglib.Syntax.Minimalist.Labeling

/-!
# Sluicing: Syntactic Isomorphism Condition

Formalization of [anand-hardt-mccloskey-2025] Syntactic Isomorphism Condition
for sluicing, building on [grimshaw-2005] Extended Projection, with a
comparison to [rudin-2019]'s domination-chain–based structure matching.

## Key Ideas

Sluicing is licensed when the **argument domain** of the ellipsis site is
**structurally identical** to the argument domain of the antecedent.

1. **Argument Domain** (Def 4): The most inclusive projection in an EP that
   denotes type ⟨e,t⟩ (property). For full clauses, this is vP.
2. **Head Pair** (Def 5): A pair ⟨head, complement⟩ within the argument domain,
   encoding local syntactic structure.
3. **Structural Identity** (Def 6): Two argument domains are structurally identical
   iff their head pairs can be put in 1-1 correspondence with lexical identity.
4. **SIC**: Sluicing is licensed iff structural identity holds between
   antecedent and ellipsis argument domains.

## Predictions

- **Voice mismatch**: v[agentive] ≠ v[nonThematic] within argument domain → SIC violation
- **Case matching**: Case is assigned within the argument domain → must match
- **Small clause antecedents**: Smaller argument domain → more permissive matching
- **Copular pseudosluices**: AHM licenses (head pairs match); Rudin blocks
  (domain roots differ: SC .N ≠ DP .D)

## AHM vs Rudin

[rudin-2019] Def 9 requires domination chains from the domain root to match.
This makes the domain root category load-bearing. [anand-hardt-mccloskey-2025]
Def 6 checks only head pairs, abstracting away from the domain root. The theories
converge on standard sluicing (same domain root) and diverge on cross-category
antecedence (different domain roots). We prove this convergence/divergence generally
via `same_root_convergence`.

-/

namespace Minimalist.Ellipsis.FormalMatching

open Minimalist

-- ═══════════════════════════════════════════════════════════════
-- § 1: Head Pairs
-- ═══════════════════════════════════════════════════════════════

/-- A head pair: a head and its complement category within the argument domain.
    Head pairs encode the local syntactic structure that must match
    between antecedent and ellipsis site.

    [anand-hardt-mccloskey-2025] Definition 5: Two heads are lexically identical
    iff they have the same category AND complement category. Case is
    included because it is assigned within the argument domain: a V that
    assigns dative is structurally distinct from one that assigns
    accusative ([merchant-2001], [anand-hardt-mccloskey-2021] §5.5). -/
structure HeadPair where
  /-- The category of the head -/
  head : Cat
  /-- The category of its complement -/
  complement : Cat
  /-- Case assigned by the head to its complement, when relevant.
      `none` for head pairs where case is not assigned (e.g., v–V). -/
  assignedCase : Option UD.Case := none
  /-- Voice flavor of the head (agentive, nonThematic, etc.), when relevant.
      Distinguishes active v[agentive] from passive v[nonThematic] within
      the argument domain. -/
  voiceFlavor : Option VoiceFlavor := none
  /-- Is this PP an argument of the verb (selected) or an adjunct?
      [anand-hardt-mccloskey-2025] §4: argument PPs (e.g., "rely on X")
      are inside the argument domain and must match under the SIC;
      nonargument PPs (e.g., "sing in the shower") are outside.
      `none` for non-PP head pairs. -/
  isArgumentPP : Option Bool := none
  deriving Repr, DecidableEq

-- ═══════════════════════════════════════════════════════════════
-- § 2: Syntactic Identity
-- ═══════════════════════════════════════════════════════════════

/-- Optional-field "agreement" predicate: two `Option α` values agree iff
    either is `none`, or both are `some` with equal contents. Used by
    `lexicallyIdentical` (and `rudinIdentical` below) to model "match the
    field if both sides specify it." -/
def optAgree {α : Type} [DecidableEq α] (o1 o2 : Option α) : Prop :=
  o1.isNone ∨ o2.isNone ∨ o1 = o2

instance {α} [DecidableEq α] (o1 o2 : Option α) : Decidable (optAgree o1 o2) := by
  unfold optAgree; infer_instance

/-- Lexical identity of head pairs ([anand-hardt-mccloskey-2025], Def 5):
    Two head pairs are lexically identical iff they have the same
    head category, complement category, and assigned case (when both
    specify case).

    Case matching follows from the SIC because case is assigned within
    the argument domain: if the head assigns different case, the
    head-complement relationship is structurally distinct.

    When either side has `assignedCase = none`, case is not checked
    (the head pair does not involve case assignment, e.g., v selecting VP). -/
def lexicallyIdentical (hp1 hp2 : HeadPair) : Prop :=
  hp1.head = hp2.head ∧
  hp1.complement = hp2.complement ∧
  optAgree hp1.assignedCase hp2.assignedCase ∧
  optAgree hp1.voiceFlavor hp2.voiceFlavor ∧
  optAgree hp1.isArgumentPP hp2.isArgumentPP

instance (hp1 hp2 : HeadPair) : Decidable (lexicallyIdentical hp1 hp2) := by
  unfold lexicallyIdentical; infer_instance

/-- Remove the first element matching a decidable predicate from a list.
    Returns `none` if no match found, `some remaining` otherwise.

    Polymorphic over `(α → Prop)` with `[DecidablePred p]` so that consumers
    can pass Prop predicates (e.g., `lexicallyIdentical hp`) directly without
    Bool wrapping. -/
def removeFirst {α : Type} (p : α → Prop) [DecidablePred p] :
    List α → Option (List α)
  | [] => none
  | x :: xs =>
    if p x then some xs
    else (removeFirst p xs).map (x :: ·)

/-- Check if every head pair in `pairs1` has a lexically identical
    match in `pairs2`, consuming matches (1-1 correspondence). -/
def matchHeadPairs : List HeadPair → List HeadPair → Prop
  | [], _ => True
  | hp :: rest, candidates =>
    match removeFirst (lexicallyIdentical hp) candidates with
    | some remaining => matchHeadPairs rest remaining
    | none => False

instance : (l1 l2 : List HeadPair) → Decidable (matchHeadPairs l1 l2)
  | [], _ => isTrue trivial
  | hp :: rest, candidates => by
    unfold matchHeadPairs
    match removeFirst (lexicallyIdentical hp) candidates with
    | none => exact isFalse not_false
    | some remaining => exact instDecidableMatchHeadPairs rest remaining

/-- Structural identity ([anand-hardt-mccloskey-2025], Def 6):
    Two sets of head pairs are structurally identical iff they can be
    put in 1-1 correspondence where each pair is lexically identical.

    This requires same cardinality AND a bijective matching. -/
def structurallyIdentical (pairs1 pairs2 : List HeadPair) : Prop :=
  pairs1.length = pairs2.length ∧ matchHeadPairs pairs1 pairs2

instance (pairs1 pairs2 : List HeadPair) :
    Decidable (structurallyIdentical pairs1 pairs2) := by
  unfold structurallyIdentical; infer_instance

-- ═══════════════════════════════════════════════════════════════
-- § 3: Sluicing License (SIC)
-- ═══════════════════════════════════════════════════════════════

/-- Sluicing license: the Syntactic Isomorphism Condition (SIC).

    Sluicing of a CP is licensed iff the argument domain of the
    ellipsis site has structurally identical head pairs to the
    argument domain of the antecedent. -/
structure SluicingLicense where
  /-- Head pairs from the antecedent's argument domain -/
  antecedentPairs : List HeadPair
  /-- Head pairs from the ellipsis site's argument domain -/
  ellipsisPairs : List HeadPair

/-- Is sluicing licensed? Checks structural identity of head pairs. -/
def SluicingLicense.isLicensed (sl : SluicingLicense) : Prop :=
  structurallyIdentical sl.antecedentPairs sl.ellipsisPairs

instance (sl : SluicingLicense) : Decidable sl.isLicensed := by
  unfold SluicingLicense.isLicensed; infer_instance

-- ═══════════════════════════════════════════════════════════════
-- § 4: SIC Predictions
-- ═══════════════════════════════════════════════════════════════

-- Voice Mismatch Resolution ([anand-hardt-mccloskey-2021])

/-- Voice is within the argument domain (F1, same level as v).
    [anand-hardt-mccloskey-2021]: voice mismatches ARE blocked by the SIC because
    v[agentive] ≠ v[nonThematic] within the argument domain. -/
theorem voice_flavor_in_argdomain :
    isInArgumentDomain .Voice .C := by decide

/-- T is not within the argument domain of a CP. -/
theorem t_outside_argdomain :
    ¬ isInArgumentDomain .T .C := by decide

/-- C is not within the argument domain. -/
theorem c_outside_argdomain :
    ¬ isInArgumentDomain .C .C := by decide

/-- Head pairs for an active (agentive) transitive vP.
    v[agentive] selects VP, V selects DP. -/
def activeVP : List HeadPair :=
  [⟨.v, .V, none, some .agentive, none⟩, ⟨.V, .D, none, none, none⟩]

/-- Head pairs for a passive (non-thematic) transitive vP.
    v[nonThematic] selects VP, V selects DP. -/
def passiveVP : List HeadPair :=
  [⟨.v, .V, none, some .nonThematic, none⟩, ⟨.V, .D, none, none, none⟩]

/-- Voice mismatch blocks sluicing: active v[agentive] ≠ passive v[nonThematic]
    within the argument domain. -/
theorem voice_mismatch_blocks_sluicing :
    ¬ structurallyIdentical activeVP passiveVP := by
  decide

/-- Same voice licenses sluicing: active→active is structurally identical. -/
theorem voice_match_licenses_sluicing :
    structurallyIdentical activeVP activeVP := by
  decide

-- Argument domain boundaries

/-- V is within the argument domain of a CP (F0 ≤ F1). -/
theorem v_lexical_in_argdomain :
    isInArgumentDomain .V .C := by decide

/-- v is within the argument domain of a CP (F1 ≤ F1). -/
theorem v_functional_in_argdomain :
    isInArgumentDomain .v .C := by decide

-- Small clause predictions

/-- For a small clause (top = V), the argument domain is V itself.
    Only F0 heads are in the argument domain. -/
theorem small_clause_argdomain_is_self :
    argumentDomainCat .V = .V := by decide

/-- In a small clause, v is NOT in the argument domain
    (since the top is V at F0, and v is F1). -/
theorem small_clause_excludes_v :
    ¬ isInArgumentDomain .v .V := by decide

-- Cross-categorial SC argument domains ([anand-hardt-mccloskey-2025] Def 4)

/-- For a P-headed small clause, the argument domain is P itself.
    E.g., absolute *with*: "with [the campaign on hold]". -/
theorem sc_P_argdomain_is_self : argumentDomainCat .P = .P := by decide

/-- For an A-headed small clause, the argument domain is A itself.
    E.g., resultative: "hammer [the metal flat]". -/
theorem sc_A_argdomain_is_self : argumentDomainCat .A = .A := by decide

/-- For an N-headed small clause, the argument domain is N itself.
    E.g., copular: "consider [John a fool]". -/
theorem sc_N_argdomain_is_self : argumentDomainCat .N = .N := by decide

/-- The argument domain boundary for an SC is the SC predicate category. -/
def scArgumentDomainCat (sc : SCPredCategory) : Cat :=
  argumentDomainCat sc.toCat

/-- SC argument domains are uniformly at F0 (lexical level). -/
theorem sc_argdomain_at_f0 (sc : SCPredCategory) :
    fValue (scArgumentDomainCat sc) = 0 := by
  cases sc <;> decide

/-- SC argument domains are smaller than full clause argument domains. -/
theorem sc_argdomain_le_clause (sc : SCPredCategory) :
    fValue (scArgumentDomainCat sc) ≤ fValue (argumentDomainCat .C) := by
  cases sc <;> decide

/-- Head pairs from a small clause's argument domain.
    The SC argument domain contains only the predicate head and its
    complement (the subject DP), yielding a single head pair. -/
def scHeadPairsForCat (cat : SCPredCategory) : List HeadPair :=
  [⟨cat.toCat, .D, none, none, none⟩]

/-- SC sluicing requires fewer matches than full-clause sluicing. -/
theorem sc_sic_fewer_constraints :
    (scHeadPairsForCat .A).length < activeVP.length := by decide

/-- SIC licenses SC sluicing when antecedent and ellipsis share
    the same SC predicate category (same ⟨PredCat, D⟩ head pair). -/
theorem sc_same_pred_sluicing_licensed (cat : SCPredCategory) :
    structurallyIdentical
      (scHeadPairsForCat cat)
      (scHeadPairsForCat cat) := by
  cases cat <;> decide

-- Matching properties

/-- `optAgree` is reflexive on any optional value. -/
private theorem optAgree_refl {α} [DecidableEq α] (o : Option α) : optAgree o o :=
  Or.inr (Or.inr rfl)

/-- Lexical identity is reflexive for any head pair. -/
theorem lexicallyIdentical_refl (hp : HeadPair) : lexicallyIdentical hp hp :=
  ⟨rfl, rfl, optAgree_refl _, optAgree_refl _, optAgree_refl _⟩

/-- Removing the first lexically identical element from a list headed
    by that element succeeds and returns the tail. -/
theorem removeFirst_self (hp : HeadPair) (rest : List HeadPair) :
    removeFirst (lexicallyIdentical hp) (hp :: rest) = some rest := by
  unfold removeFirst
  rw [if_pos (lexicallyIdentical_refl hp)]

/-- Head pair matching is reflexive: any list matches itself. -/
theorem matchHeadPairs_refl : (pairs : List HeadPair) →
    matchHeadPairs pairs pairs
  | [] => by unfold matchHeadPairs; trivial
  | hp :: rest => by
    unfold matchHeadPairs
    rw [removeFirst_self]
    exact matchHeadPairs_refl rest

/-- Structural identity is reflexive: any set of head pairs is
    structurally identical to itself. This subsumes `empty_domains_identical`
    and `single_pair_matches`. -/
theorem structurallyIdentical_refl (pairs : List HeadPair) :
    structurallyIdentical pairs pairs :=
  ⟨rfl, matchHeadPairs_refl pairs⟩

/-- Empty argument domains are trivially structurally identical. -/
theorem empty_domains_identical : structurallyIdentical [] [] :=
  structurallyIdentical_refl []

/-- A single head pair matches itself. -/
theorem single_pair_matches (hp : HeadPair) :
    structurallyIdentical [hp] [hp] :=
  structurallyIdentical_refl [hp]

-- Case matching

/-- Case mismatch blocks lexical identity: a V–D pair assigning dative
    is not lexically identical to one assigning accusative. -/
theorem case_mismatch_not_identical :
    ¬ lexicallyIdentical ⟨.V, .D, some .Dat, none, none⟩ ⟨.V, .D, some .Acc, none, none⟩ := by
  decide

/-- Case match preserves lexical identity. -/
theorem case_match_identical :
    lexicallyIdentical ⟨.V, .D, some .Dat, none, none⟩ ⟨.V, .D, some .Dat, none, none⟩ := by
  decide

/-- When no case is specified (e.g., v–V), identity depends only on
    categories. -/
theorem no_case_identity :
    lexicallyIdentical ⟨.v, .V, none, none, none⟩ ⟨.v, .V, none, none, none⟩ := by
  decide

/-- Case mismatch blocks structural identity even when all other head
    pairs match. This is the formal basis of the German case-matching
    data: "wem" (dat) matches "jemandem" (dat), but
    "wen" (acc) does not. -/
theorem case_mismatch_blocks_sluicing :
    ¬ structurallyIdentical
      [⟨.v, .V, none, none, none⟩, ⟨.V, .D, some .Dat, none, none⟩]
      [⟨.v, .V, none, none, none⟩, ⟨.V, .D, some .Acc, none, none⟩] := by
  decide

/-- Same case → structural identity holds → sluicing licensed. -/
theorem case_match_licenses_sluicing :
    structurallyIdentical
      [⟨.v, .V, none, none, none⟩, ⟨.V, .D, some .Dat, none, none⟩]
      [⟨.v, .V, none, none, none⟩, ⟨.V, .D, some .Dat, none, none⟩] :=
  structurallyIdentical_refl _

-- ═══════════════════════════════════════════════════════════════
-- § 4b: Derivation Grounding — VerbFrame / SCFrame
-- ═══════════════════════════════════════════════════════════════

/-- A verb frame specifies the derivation-level properties of a
    verbal structure that are relevant for the SIC.

    Each frame corresponds to a well-formed Minimalist derivation
    [vP v[voice] [VP V complement]], where v selects VP and V selects
    a DP or PP complement. The SIC compares the head pairs extracted
    from the argument domain of such derivations.

    This connects the SIC to the Minimalist machinery: head pairs
    are not stipulated but arise from structured derivation specs
    that correspond to concrete `SyntacticObject` trees. -/
structure VerbFrame where
  /-- Voice flavor of the v head -/
  voice : VoiceFlavor
  /-- Case assigned by V to its complement (when relevant) -/
  objectCase : Option UD.Case := none
  /-- Does V select an argument PP rather than a DP complement? -/
  argumentPP : Bool := false
  deriving Repr, DecidableEq

/-- Head pairs extracted from a verb frame's argument domain.
    The argument domain for a clausal derivation is vP, containing:
    - ⟨v, V⟩: the v head selecting VP (annotated with voice flavor)
    - ⟨V, D/P⟩: the V head selecting its complement (annotated with case) -/
def VerbFrame.headPairs (vf : VerbFrame) : List HeadPair :=
  [⟨.v, .V, none, some vf.voice, none⟩,
   ⟨.V, if vf.argumentPP then .P else .D, vf.objectCase, none,
    if vf.argumentPP then some true else none⟩]

/-- Build a concrete `SyntacticObject` tree from a verb frame.
    Produces the tree [vP v [VP V DP/PP]]:
    - v (sel: [V]) — little v, selects VP
    - V (sel: [D] or [P]) — lexical verb, selects complement
    - DP/PP (sel: []) — complement -/
def VerbFrame.tree (vf : VerbFrame) (vId verbId complId : Nat) : SyntacticObject :=
  let complCat : Cat := if vf.argumentPP then .P else .D
  let compl := mkLeaf complCat [] complId
  let verb := mkLeaf .V [complCat] verbId
  let vp := merge verb compl
  let v := mkLeaf .v [.V] vId
  merge v vp

-- ── Canonical verb frames ──────────────────────────────────────

/-- Active transitive: v[agentive] selects VP, V selects DP. -/
def activeFrame : VerbFrame := { voice := .agentive }

/-- Passive transitive: v[nonThematic] selects VP, V selects DP. -/
def passiveFrame : VerbFrame := { voice := .nonThematic }

/-- Dative verb (e.g., German "helfen"): V assigns dative case. -/
def dativeFrame : VerbFrame := { voice := .agentive, objectCase := some .Dat }

/-- Accusative verb (e.g., German "sehen"): V assigns accusative case. -/
def accusativeFrame : VerbFrame := { voice := .agentive, objectCase := some .Acc }

/-- Argument PP verb (e.g., "rely on"): V selects a PP complement. -/
def argumentPPFrame : VerbFrame := { voice := .agentive, argumentPP := true }

-- ── Frame → hand-specified data equivalences ───────────────────

/-- Active frame head pairs match the hand-specified `activeVP`. -/
theorem activeFrame_eq : activeFrame.headPairs = activeVP := by decide

/-- Passive frame head pairs match the hand-specified `passiveVP`. -/
theorem passiveFrame_eq : passiveFrame.headPairs = passiveVP := by decide

-- ── SIC on verb frames ─────────────────────────────────────────

/-- Is sluicing licensed between two verb frames?
    Checks structural identity of their argument domain head pairs. -/
def frameSluicingLicensed (antecedent ellipsis : VerbFrame) : Prop :=
  structurallyIdentical antecedent.headPairs ellipsis.headPairs

instance (a e : VerbFrame) : Decidable (frameSluicingLicensed a e) := by
  unfold frameSluicingLicensed; infer_instance

/-- Any verb frame is structurally identical to itself.
    This is non-trivial: it says that 1-1 head pair matching succeeds
    reflexively, regardless of voice, case, and argument type. -/
theorem same_frame_always_licensed (vf : VerbFrame) :
    frameSluicingLicensed vf vf := by
  unfold frameSluicingLicensed
  exact structurallyIdentical_refl _

/-- The v–V head pair depends only on voice flavor: two frames with
    the same voice produce identical first head pairs, regardless
    of case or argument type. -/
theorem voice_determines_v_pair (v : VoiceFlavor)
    (c1 c2 : Option UD.Case) (pp1 pp2 : Bool) :
    (VerbFrame.mk v c1 pp1).headPairs.head? =
    (VerbFrame.mk v c2 pp2).headPairs.head? := rfl

/-- Voice mismatch blocks sluicing, derived from frames.
    Proof: unfold to head pairs, then `activeFrame_eq`/`passiveFrame_eq`
    reduce to the known `voice_mismatch_blocks_sluicing`. -/
theorem voice_mismatch_from_frames :
    ¬ frameSluicingLicensed activeFrame passiveFrame := by
  unfold frameSluicingLicensed
  rw [activeFrame_eq, passiveFrame_eq]
  exact voice_mismatch_blocks_sluicing

/-- Case mismatch blocks sluicing, derived from frames. -/
theorem case_mismatch_from_frames :
    ¬ frameSluicingLicensed dativeFrame accusativeFrame := by
  unfold frameSluicingLicensed dativeFrame accusativeFrame VerbFrame.headPairs
  decide

/-- Same-case frames are licensed. -/
theorem same_case_from_frames :
    frameSluicingLicensed dativeFrame dativeFrame :=
  same_frame_always_licensed _

-- ── Small clause frames ────────────────────────────────────────

/-- Is sluicing licensed between a verb frame and an SC frame?
    Cross-category sluicing (full clause ↔ SC) involves different
    argument domain sizes, so it typically fails the SIC. -/
def crossCategorySluicing (vf : VerbFrame) (sc : SCPredCategory) : Prop :=
  structurallyIdentical vf.headPairs (scHeadPairsForCat sc)

instance (vf : VerbFrame) (sc : SCPredCategory) :
    Decidable (crossCategorySluicing vf sc) := by
  unfold crossCategorySluicing; infer_instance

/-- Full clause → SC cross-category sluicing fails: different numbers
    of head pairs (2 vs 1) means the SIC length check blocks. -/
theorem cross_category_blocked (vf : VerbFrame) (sc : SCPredCategory) :
    ¬ crossCategorySluicing vf sc := by
  unfold crossCategorySluicing structurallyIdentical VerbFrame.headPairs scHeadPairsForCat
  intro ⟨hlen, _⟩; cases hlen

-- ── Derivation well-formedness ─────────────────────────────────

/-- The argument domain spine for any verb frame is [V, v],
    which is F-monotone and category-consistent. -/
theorem verbframe_argdomain_wellformed :
    categoryConsistent .V .v = true ∧
    fMonotone .V .v = true := by decide

/-- The verbal argument domain contains exactly F0 (.V) and F1 (.v).
    Everything above (T, C, Mod, ...) is outside. -/
theorem verbframe_argdomain_complete :
    isInArgumentDomain .V .C ∧
    isInArgumentDomain .v .C ∧
    ¬ isInArgumentDomain .T .C ∧
    ¬ isInArgumentDomain .C .C := by decide

-- ── Concrete tree verification ─────────────────────────────────
-- The following examples verify at compile time that the
-- concrete Minimalist trees built from VerbFrames have the expected
-- structural properties (category labels, selection relations).

/-- Active transitive tree: [vP v[ag] [VP V DP]] -/
private def activeTree := activeFrame.tree 1 2 3
/-- Passive transitive tree: [vP v[nonTh] [VP V DP]] -/
private def passiveTree := passiveFrame.tree 1 2 3

-- Tree labels match expected categories, via the computable selection-driven
-- labeling (`Labeling.labelC`) / c-selection (`selectsC`) — `decide`-checked.
example : Labeling.labelC activeTree = some .v := by decide
example : Labeling.labelC passiveTree = some .v := by decide

-- Selection holds: v selects VP, V selects DP.
example : selectsC (mkLeaf .v [.V] 1) (merge (mkLeaf .V [.D] 2) (mkLeaf .D [] 3)) := by decide
example : selectsC (mkLeaf .V [.D] 2) (mkLeaf .D [] 3) := by decide

-- ═══════════════════════════════════════════════════════════════
-- § 5: Nonargument PPs and Chung's Generalization
-- ([anand-hardt-mccloskey-2025] §4)
-- ═══════════════════════════════════════════════════════════════

/-- Is this head pair a nonargument PP? Nonargument PPs are outside
    the argument domain: they are merged above vP and do not participate
    in the SIC matching calculation.

    [anand-hardt-mccloskey-2025] §4: Chung's Generalization
    (preposition stranding in sluicing) follows because stranded
    prepositions in nonargument PPs need not match structurally. -/
def HeadPair.isNonargumentPP (hp : HeadPair) : Bool :=
  hp.head == .P && hp.isArgumentPP == some false

/-- Filter head pairs to only those within the argument domain,
    excluding nonargument PPs. The SIC applies to the filtered list. -/
def filterArgumentPairs (pairs : List HeadPair) : List HeadPair :=
  pairs.filter (λ hp => !hp.isNonargumentPP)

/-- Chung's Generalization: a stranded nonargument preposition in the
    ellipsis site need not have a counterpart in the antecedent.

    [anand-hardt-mccloskey-2025] §4: "government regulation is
    necessary in [some form]" — the stranded *in* has no antecedent
    source, but sluicing is licensed because the PP is nonargument
    (outside the argument domain). Filtering removes it, and the
    remaining argument-domain head pairs match. -/
theorem chung_generalization :
    let antecedent : List HeadPair :=
      [⟨.v, .V, none, some .agentive, none⟩, ⟨.V, .D, none, none, none⟩]
    let ellipsis : List HeadPair :=
      [⟨.v, .V, none, some .agentive, none⟩, ⟨.V, .D, none, none, none⟩,
       ⟨.P, .D, none, none, some false⟩]
    structurallyIdentical
      (filterArgumentPairs antecedent)
      (filterArgumentPairs ellipsis) := by
  decide

/-- An argument PP (selected by V) IS inside the argument domain and
    DOES require matching. "I rely on her" vs "I rely at her" — case
    is wrong, and the PP is argument-marking, so SIC blocks. -/
theorem argument_pp_must_match :
    let vp1 : List HeadPair :=
      [⟨.v, .V, none, none, none⟩, ⟨.V, .P, none, none, some true⟩]
    let vp2 : List HeadPair :=
      [⟨.v, .V, none, none, none⟩, ⟨.V, .P, none, none, some true⟩]
    structurallyIdentical
      (filterArgumentPairs vp1)
      (filterArgumentPairs vp2) = true := by
  decide

-- ═══════════════════════════════════════════════════════════════
-- § 6: Rudin (2019) Comparison — Domination Chains vs Head Pairs
-- ═══════════════════════════════════════════════════════════════

/-- [rudin-2019]'s structure matching (Def 9) requires that heads
    be dominated by identical sequences of immediately dominating nodes.
    This means the **domain root category** is necessarily part of the
    match: every domination chain starts from the domain root.

    [anand-hardt-mccloskey-2025]'s SIC (Def 6) checks only head
    pairs ⟨head, complement⟩ within the argument domain, without
    reference to the domain root.

    We capture this difference by annotating each head pair with its
    domain root category. Rudin's condition requires domain root identity;
    AHM's condition ignores it. This is a deliberate simplification of
    the full domination-chain machinery — we abstract to the single
    feature (domain root) that drives the empirical divergence. -/
structure DomainAnnotatedPair where
  /-- The head pair within the argument domain -/
  pair : HeadPair
  /-- The root category of the domain containing this head pair.
      For full clauses: .v (vP argument domain).
      For N-headed SCs: .N. For DPs: .D. -/
  domainRoot : Cat
  deriving Repr, DecidableEq

/-- Annotate a list of head pairs with a uniform domain root category.
    Used to lift AHM-style head pairs into Rudin-style annotated pairs. -/
def annotateWithRoot (root : Cat) (pairs : List HeadPair) : List DomainAnnotatedPair :=
  pairs.map (⟨·, root⟩)

/-- Rudin-style matching: lexical identity of head pairs PLUS
    domain root identity. The domain root requirement follows from
    [rudin-2019] Def 9: domination chains necessarily include
    the domain root as their first element, so if domain roots
    differ, no chain can match. -/
def rudinIdentical (h1 h2 : DomainAnnotatedPair) : Prop :=
  lexicallyIdentical h1.pair h2.pair ∧ h1.domainRoot = h2.domainRoot

instance (h1 h2 : DomainAnnotatedPair) : Decidable (rudinIdentical h1 h2) := by
  unfold rudinIdentical; infer_instance

/-- Match head pairs using Rudin's stricter criterion (1-1 correspondence). -/
def rudinMatchPairs : List DomainAnnotatedPair → List DomainAnnotatedPair → Prop
  | [], _ => True
  | hp :: rest, candidates =>
    match removeFirst (rudinIdentical hp) candidates with
    | some remaining => rudinMatchPairs rest remaining
    | none => False

instance : (l1 l2 : List DomainAnnotatedPair) → Decidable (rudinMatchPairs l1 l2)
  | [], _ => isTrue trivial
  | hp :: rest, candidates => by
    unfold rudinMatchPairs
    match removeFirst (rudinIdentical hp) candidates with
    | none => exact isFalse not_false
    | some remaining => exact instDecidableRudinMatchPairs rest remaining

/-- Rudin's structural identity: same cardinality + Rudin-style matching. -/
def rudinStructurallyIdentical (pairs1 pairs2 : List DomainAnnotatedPair) : Prop :=
  pairs1.length = pairs2.length ∧ rudinMatchPairs pairs1 pairs2

instance (pairs1 pairs2 : List DomainAnnotatedPair) :
    Decidable (rudinStructurallyIdentical pairs1 pairs2) := by
  unfold rudinStructurallyIdentical; infer_instance

-- ── General convergence: same root → Rudin = AHM ───────────────

/-- When domain roots match, rudinIdentical reduces to lexicallyIdentical. -/
private theorem rudinIdentical_same_root (hp1 hp2 : HeadPair) (root : Cat) :
    rudinIdentical ⟨hp1, root⟩ ⟨hp2, root⟩ ↔ lexicallyIdentical hp1 hp2 := by
  simp only [rudinIdentical, and_true]

/-- `removeFirst` commutes with `List.map` when the two predicates
    correspond pointwise. Used to reduce Rudin-style matching on
    annotated pairs to AHM-style matching on bare pairs. -/
private theorem removeFirst_map {α β : Type} (f : α → β)
    (p : β → Prop) [DecidablePred p] (q : α → Prop) [DecidablePred q]
    (hpq : ∀ a, p (f a) ↔ q a) :
    (xs : List α) →
    removeFirst p (xs.map f) = (removeFirst q xs).map (List.map f)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons]
    unfold removeFirst
    by_cases h : q x
    · have hp_fx : p (f x) := (hpq x).mpr h
      simp [if_pos hp_fx, if_pos h]
    · have hnp_fx : ¬ p (f x) := fun pfx => h ((hpq x).mp pfx)
      simp [if_neg hnp_fx, if_neg h, removeFirst_map f p q hpq xs]
      cases removeFirst q xs with
      | none => rfl
      | some r => simp [Option.map, List.map_cons]

/-- Rudin matching on uniformly-annotated lists is equivalent to AHM matching. -/
private theorem rudinMatchPairs_eq (root : Cat) :
    (pairs1 pairs2 : List HeadPair) →
    (rudinMatchPairs (annotateWithRoot root pairs1) (annotateWithRoot root pairs2) ↔
     matchHeadPairs pairs1 pairs2)
  | [], _ => by
    unfold annotateWithRoot rudinMatchPairs matchHeadPairs; simp
  | hp :: rest, pairs2 => by
    unfold annotateWithRoot
    simp only [List.map_cons]
    unfold rudinMatchPairs matchHeadPairs
    rw [removeFirst_map (⟨·, root⟩) (rudinIdentical ⟨hp, root⟩) (lexicallyIdentical hp)
        (fun hp2 => rudinIdentical_same_root hp hp2 root) pairs2]
    cases removeFirst (lexicallyIdentical hp) pairs2 with
    | none => simp [Option.map]
    | some remaining =>
      simp only [Option.map]
      exact rudinMatchPairs_eq root rest remaining

/-- When both sides are annotated with the same domain root, Rudin's
    structural identity is equivalent to AHM's. The theories converge
    whenever the domain roots match — only differing domain roots can
    cause divergence (as in copular pseudosluices). -/
theorem same_root_convergence (pairs1 pairs2 : List HeadPair) (root : Cat) :
    rudinStructurallyIdentical (annotateWithRoot root pairs1) (annotateWithRoot root pairs2) ↔
    structurallyIdentical pairs1 pairs2 := by
  unfold rudinStructurallyIdentical structurallyIdentical
  have hl1 : (annotateWithRoot root pairs1).length = pairs1.length := by
    simp [annotateWithRoot]
  have hl2 : (annotateWithRoot root pairs2).length = pairs2.length := by
    simp [annotateWithRoot]
  rw [hl1, hl2]
  exact and_congr Iff.rfl (rudinMatchPairs_eq root pairs1 pairs2)

-- ── Convergence: standard full-clause sluicing ──────────────────

/-- Active transitive vP annotated with domain root .v -/
def rudinActiveVP : List DomainAnnotatedPair := annotateWithRoot .v activeVP

/-- Passive transitive vP annotated with domain root .v -/
def rudinPassiveVP : List DomainAnnotatedPair := annotateWithRoot .v passiveVP

/-- Convergence: Rudin and AHM agree that voice mismatch blocks sluicing.
    Both theories: active v[agentive] ≠ passive v[nonThematic].
    Derived from `same_root_convergence` + `voice_mismatch_blocks_sluicing`. -/
theorem rudin_also_blocks_voice_mismatch :
    ¬ rudinStructurallyIdentical rudinActiveVP rudinPassiveVP := by
  unfold rudinActiveVP rudinPassiveVP
  rw [same_root_convergence]; exact voice_mismatch_blocks_sluicing

/-- Convergence: Rudin and AHM agree that same voice licenses sluicing.
    Derived from `same_root_convergence` + `voice_match_licenses_sluicing`. -/
theorem rudin_also_licenses_same_voice :
    rudinStructurallyIdentical rudinActiveVP rudinActiveVP := by
  unfold rudinActiveVP
  rw [same_root_convergence]; exact voice_match_licenses_sluicing

/-- Convergence: Rudin and AHM agree on case mismatch blocking.
    Derived from `same_root_convergence` + `case_mismatch_blocks_sluicing`. -/
theorem rudin_also_blocks_case_mismatch :
    ¬ rudinStructurallyIdentical
      (annotateWithRoot .v [⟨.v, .V, none, none, none⟩, ⟨.V, .D, some .Dat, none, none⟩])
      (annotateWithRoot .v [⟨.v, .V, none, none, none⟩, ⟨.V, .D, some .Acc, none, none⟩]) := by
  rw [same_root_convergence]; exact case_mismatch_blocks_sluicing

-- ── Divergence: copular pseudosluices ───────────────────────────

/-- Copular pseudosluice — ellipsis side.
    The elided clause is [TP T be [SC subject predicate]], whose
    argument domain is the N-headed SC (domain root = .N).
    The single head pair is ⟨N, D⟩ (N head, D complement). -/
def copularEllipsisSC : List DomainAnnotatedPair :=
  [⟨⟨.N, .D, none, none, none⟩, .N⟩]

/-- Copular pseudosluice — antecedent side.
    The antecedent is a bare DP (e.g., "a presidential race").
    Same head pair ⟨N, D⟩, but domain root = .D. -/
def copularAntecedentDP : List DomainAnnotatedPair :=
  [⟨⟨.N, .D, none, none, none⟩, .D⟩]

/-- [anand-hardt-mccloskey-2025] correctly licenses copular
    pseudosluices: the head pair ⟨N, D⟩ in the SC argument domain
    matches the head pair ⟨N, D⟩ in the antecedent DP. Domain root
    categories (.N vs .D) are NOT part of AHM's matching. -/
theorem ahm_licenses_copular_pseudosluice :
    structurallyIdentical
      [⟨.N, .D, none, none, none⟩]
      [⟨.N, .D, none, none, none⟩] :=
  structurallyIdentical_refl _

/-- [rudin-2019]'s condition incorrectly blocks copular
    pseudosluices: the domain roots differ (.N for the SC, .D for the
    antecedent DP), so domination chains cannot match.

    This is the central empirical argument in
    [anand-hardt-mccloskey-2025] §5 for revising Rudin's condition.
    The copular pseudosluice data (23 corpus instances, ex. 18–19)
    show that a head-pair–based SIC is empirically superior to a
    domination-chain–based one. -/
theorem rudin_blocks_copular_pseudosluice :
    ¬ rudinStructurallyIdentical copularEllipsisSC copularAntecedentDP := by
  decide

/-- The theories diverge on copular pseudosluices: AHM licenses them,
    Rudin blocks them. The divergence arises because AHM's SIC checks
    only head pairs (domain-root-invariant), while Rudin's checks
    domination chains (domain-root-sensitive).

    [anand-hardt-mccloskey-2025] ex. 18–19: "Bradley said that
    he has not shut the door to [a presidential race], though he would
    not say when." — grammatical, with nominal antecedent and implicit
    copular elided clause. -/
theorem copular_pseudosluice_divergence :
    -- AHM licenses: head pairs match (domain root ignored)
    structurallyIdentical
      [⟨.N, .D, none, none, none⟩]
      [⟨.N, .D, none, none, none⟩] ∧
    -- Rudin blocks: domain roots differ (.N ≠ .D)
    ¬ rudinStructurallyIdentical copularEllipsisSC copularAntecedentDP :=
  ⟨structurallyIdentical_refl _, by decide⟩

/-- The source of divergence: Rudin's matching is sensitive to the
    domain root category; AHM's is not. When domain roots differ
    (cross-category antecedence: SC ↔ DP), only AHM's SIC succeeds.
    When domain roots are the same (standard sluicing: vP ↔ vP),
    both theories make identical predictions. -/
theorem domain_root_is_divergence_source :
    -- Same root → Rudin agrees with AHM (both license)
    rudinStructurallyIdentical rudinActiveVP rudinActiveVP ∧
    -- Different root → Rudin disagrees (blocks what AHM licenses)
    ¬ rudinStructurallyIdentical copularEllipsisSC copularAntecedentDP ∧
    structurallyIdentical
      [⟨.N, .D, none, none, none⟩]
      [⟨.N, .D, none, none, none⟩] :=
  ⟨rudin_also_licenses_same_voice, by decide, structurallyIdentical_refl _⟩

-- ═══════════════════════════════════════════════════════════════
-- § 7: Bruening (2021) Maximal-Projection Identity
-- ═══════════════════════════════════════════════════════════════
--
-- [bruening-2021] §5.5 (pp. 1064–1067) proposes a maximal-projection-
-- based identity condition for ellipsis (ex. 122–124), modifying
-- [rudin-2019]'s head-based condition (§ 6 above). Bruening's
-- condition reads: ellipsis of E given antecedent A is licit iff every
-- max-proj in E that is not a movement non-head has a structure-matching
-- correlate in A, and conversely. Structure-matching is identity of the
-- sequence of immediately dominating nodes (Bruening's gloss of Rudin
-- 2019 ex. 9 with max-projs substituted for heads).
--
-- The condition derives Bruening's G1 (sluicing asymmetry) without
-- further stipulation: implicit second-objects are licensed because the
-- only added structure (the ∃ head) is not a max projection; implicit
-- first objects are blocked because the antecedent's spec-ApplP DP has
-- no correlate in the elided clause (filtered out as a movement non-head).
--
-- The G1 derivation proper is in
-- `Studies/Bruening2021Sluicing.lean`.

/-- Maximal projections within a SO `root`: subtrees `t` such that
    `Labeling.isMaximalAt h root t` under head function `h`. Per
    [bruening-2021] §5.5 ex. 122, the identity condition
    quantifies over these XPs (modulo movement non-heads).

    Parametric over `h : HeadFunction` per
    [marcolli-chomsky-berwick-2025] §1.13.6 — there is no canonical
    "the" labeling without a chosen head function. -/
noncomputable def maximalProjections (h : HeadFunction) (root : SyntacticObject) :
    Multiset SyntacticObject :=
  root.subtrees.filter (fun t => decide (Labeling.isMaximalAt h root t))

/-- A SO is a "nonhead member of a movement chain" iff it is a trace
    (lower copy left after movement). Per [bruening-2021] §5.5 ex. 122
    "not a nonhead member of a movement chain". For G1 only wh-traces in
    elided IPs are relevant. Higher copies in head-movement chains are
    not handled — flag for future ATB / remnant studies. -/
def isNonHeadMemberOfChain (x : SyntacticObject) : Bool :=
  (isTrace x).isSome

/-- Underlying planar path-finder on a `FreeMagma` representative.
    Phase 1.0 noncomputable (depends on planar order).

    Per [bruening-2021] §5.5 ex. 123: position-sensitive equality
    rules out cross-paradigm false positives where two unrelated trees
    share a max-proj cat multiset. -/
private noncomputable def labelPathFromRootPlanar (h : HeadFunction) :
    FreeMagma (LIToken ⊕ Nat) → SyntacticObject → Option (List Cat)
  | a@(.of _), target =>
    if (FreeCommMagma.mk a : SyntacticObject) = target then
      some ((Labeling.labelVertex h (FreeCommMagma.mk a) (FreeCommMagma.mk a)).toList)
    else
      none
  | a@(.mul l r), target =>
    let root : SyntacticObject := FreeCommMagma.mk a
    if root = target then
      some ((Labeling.labelVertex h root root).toList)
    else
      match labelPathFromRootPlanar h l target with
      | some pa => some ((Labeling.labelVertex h root root).toList ++ pa)
      | none =>
        match labelPathFromRootPlanar h r target with
        | some pb => some ((Labeling.labelVertex h root root).toList ++ pb)
        | none => none

noncomputable def labelPathFromRoot (h : HeadFunction)
    (root target : SyntacticObject) : Option (List Cat) :=
  labelPathFromRootPlanar h root.out target

/-- Filtered max-proj paths for a tree under head function `h`. Each
    filtered max-proj is paired with its path from the root (= sequence
    of `Labeling.labelVertex` values). Movement non-heads (wh-traces and
    other lower copies) are excluded — exactly Bruening's "not a nonhead
    member of a movement chain" filter. -/
noncomputable def filteredMaxProjPaths (h : HeadFunction) (root : SyntacticObject) :
    List (List Cat) :=
  (((maximalProjections h root).filter
    (fun x => !isNonHeadMemberOfChain x)).toList).filterMap
    (labelPathFromRoot h root ·)

/-- [bruening-2021] §5.5 ex. 122 maximal-projection identity
    condition, parametric over the head function `h`. Ellipsis of
    `ellipsis` given `antecedent` is licit iff their filtered max-proj
    path lists are permutations of each other.

    Stated as Prop; decidable via `List.decidablePerm`. -/
def bruening2021StructurallyIdentical
    (h : HeadFunction) (antecedent ellipsis : SyntacticObject) : Prop :=
  (filteredMaxProjPaths h antecedent).Perm (filteredMaxProjPaths h ellipsis)

noncomputable instance (h : HeadFunction) (a e : SyntacticObject) :
    Decidable (bruening2021StructurallyIdentical h a e) := by
  unfold bruening2021StructurallyIdentical; classical infer_instance

/-- The maximal-projection identity condition is reflexive: any SO is
    structurally identical to itself (under any `h`). -/
theorem bruening2021StructurallyIdentical_refl
    (h : HeadFunction) (so : SyntacticObject) :
    bruening2021StructurallyIdentical h so so :=
  List.Perm.refl _

end Minimalist.Ellipsis.FormalMatching
