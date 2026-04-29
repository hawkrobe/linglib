import Linglib.Theories.Syntax.Minimalist.Ellipsis.FormalMatching

/-! # Bruening 2021 §5.5 — Sluicing with implicit arguments
@cite{bruening-2021}

Implicit arguments in English double object constructions.
*Natural Language and Linguistic Theory* 39:1023–1085.

Formalizes Bruening's maximal-projection-based identity condition
(§5.5 ex. 122–124, p. 1065) and derives **Generalization 1** (sluicing
asymmetry, §2.4 summary point 1, p. 1040): implicit second-objects in
DOC license sluicing, but implicit first objects do not.

The identity condition is in
`Theories/Syntax/Minimalist/Ellipsis/FormalMatching.lean` (§ 7) as
`bruening2021StructurallyIdentical`, alongside @cite{rudin-2019} (§ 6) and
@cite{anand-hardt-mccloskey-2025} (§§ 1-5). This file consumes that
substrate to prove G1 against concrete antecedent/elided
SyntacticObjects modeling Bruening's ex. (121) and (124).

See `Phenomena/ArgumentStructure/Studies/Bruening2021.lean` for the
G2/G3 classification side; the `TODO(G1)` comment in that file's
deferred-substrate section is satisfied here.

Bruening's analysis modifies @cite{rudin-2019}'s head-based identity
condition (cited at §5.5 p. 1065) and engages with @cite{chung-2013} on
the syntactic-identity question for sluicing.
-/

namespace Bruening2021Sluicing

open Minimalist
open Minimalist.Ellipsis.FormalMatching

/-! ### Lexical-item leaves

Pattern from `Phenomena/ArgumentStructure/Studies/HaddicanEtAl2026.lean:109`.
Each leaf has a unique `id`; traces use `mkTrace` (id ≥ 10000). -/

def DP_they_serve : SyntacticObject := mkLeafPhon .D [] "they" 1
/-- Voice head selecting ApplP. Per @cite{bruening-2021} (121a) p. 1064:
    in DOC, Voice merges directly with ApplP (no intermediate VP layer);
    Voice's selectional feature is therefore `.Appl` for the DOC structure
    (it would be `.V` for the PP frame; cf. p. 1043 (70) PP-frame tree). -/
def Voice_act  : SyntacticObject := mkLeafPhon .Voice [.Appl] "Voice[act]" 3
def DP_us      : SyntacticObject := mkLeafPhon .D [] "us" 5
def Appl_h     : SyntacticObject := mkLeafPhon .Appl [.V] "∅" 6

/-- LexicalItem for the simple V "serve" (selecting D). -/
def serve_LI : LexicalItem := LexicalItem.simple .V [.D] "serve"

/-- LexicalItem for the ∃ functional head Bruening adjoins to V to license
    indef-implicit second objects (§4.2 ex. 96). After head-adjunction it
    closes off V's selectional feature. Encoded with empty selectional
    stack and `.V` outer category (it adjoins INTO V). -/
def ExistOp_LI : LexicalItem := LexicalItem.simple .V [] "∃"

/-- The complex head V+∃ formed by Bruening's head-adjunction (§5.2 ex. 108).
    Encoded as a single leaf via `LexicalItem.combine` so that ∃ is NOT a
    max projection in the resulting tree — exactly the structural condition
    Bruening's identity argument relies on (p. 1065: "Crucially, ∃ can be
    ignored because it is not a maximal projection"). -/
def V_serve_exists : SyntacticObject :=
  .leaf ⟨LexicalItem.combine serve_LI ExistOp_LI, 4⟩

/-- The simple V "serve" leaf (without the ∃ head), for the elided clause
    where the second object is a wh-trace, not bound by ∃. -/
def V_serve : SyntacticObject := .leaf ⟨serve_LI, 4⟩

def DP_they    : SyntacticObject := mkLeafPhon .D [] "they" 11
def DP_someone : SyntacticObject := mkLeafPhon .D [] "someone" 12
def V_charge   : SyntacticObject := mkLeafPhon .V [.D] "charge" 13
def DP_amount  : SyntacticObject := mkLeafPhon .D [] "way too much" 14

/-- Wh-trace from sluicing's wh-movement (Bruening §5.5: the wh-element
    moves to Spec-CP outside the ellipsis site, leaving a trace inside
    the elided IP). -/
def whTrace0   : SyntacticObject := mkTrace 0
def whTrace1   : SyntacticObject := mkTrace 1

/-! ### G1 case 1: implicit second-object sluicing licit (Bruening ex. 121, p. 1064)

Antecedent: "She is going to serve us [∃]" — DOC with implicit second
object (∃ adjoined to V_serve).
Elided clause for "but I don't know what" — wh-trace in object position;
∃ is gone but it was a head (not a max projection), so the identity
condition does not require a correlate. -/

def serve_doc_antecedent : SyntacticObject :=
  -- [VoiceP DP_they_serve [Voice [ApplP DP_us [Appl' Appl V+∃_complex]]]]
  -- where V+∃_complex is one LEAF (head-adjunction product), so ∃ is
  -- not a max-proj. Bruening §5.2 ex. (108) p. 1059.
  merge DP_they_serve
    (merge Voice_act
      (merge DP_us
        (merge Appl_h V_serve_exists)))

def serve_doc_elided : SyntacticObject :=
  -- [VoiceP DP_they_serve [Voice [ApplP DP_us [Appl' Appl [VP V_serve t]]]]]
  -- The VP node here MIRRORS the V+∃ leaf in the antecedent's structurally-
  -- identical position; the wh-trace inside is filtered as a movement
  -- non-head. Both the antecedent's V+∃ leaf and the elided's VP-node
  -- have outerCat .V, satisfying Bruening's structure-match (ex. 123).
  merge DP_they_serve
    (merge Voice_act
      (merge DP_us
        (merge Appl_h
          (merge V_serve whTrace0))))

/-! ### G1 case 2: implicit first-object sluicing blocked (Bruening ex. 124, p. 1066)

Antecedent: "They charged someone way too much" — DOC with both objects
overt (no implicit args).
Elided clause for "but we don't know who" — attempts to slice "who" as
the implicit first object. The wh-trace replaces `DP_someone` in
spec-ApplP position; that trace is filtered as a movement non-head.
Antecedent's `DP_someone` then has no structure-matching correlate in the
elided clause's filtered max-projs — match fails, ellipsis blocked. -/

def charged_doc_antecedent : SyntacticObject :=
  merge DP_they
    (merge Voice_act
      (merge DP_someone
        (merge Appl_h
          (merge V_charge DP_amount))))

def charged_doc_elided : SyntacticObject :=
  -- Wh-trace replaces DP_someone in spec-ApplP position
  merge DP_they
    (merge Voice_act
      (merge whTrace1
        (merge Appl_h
          (merge V_charge DP_amount))))

/-! ### G1 theorems -/

/-- Implicit second-object DOC sluicing is licit. Per @cite{bruening-2021}
    ex. 121, p. 1064: only `∃` differs between antecedent and elided, and
    `∃` is a head (not a maximal projection), so the identity condition
    ignores it. The max-projs in both clauses agree categorially per
    Bruening's enumeration on p. 1065 — both label as
    [Voice, D, Appl, D, V] — modulo the wh-trace which is filtered as a
    movement non-head. -/
theorem g1_serve_implicit_second_obj_licensed :
    bruening2021StructurallyIdentical serve_doc_antecedent serve_doc_elided := by
  decide

/-- Implicit first-object DOC sluicing is blocked. Per @cite{bruening-2021}
    ex. 124, p. 1066: the antecedent's spec-ApplP DP (`someone`) has no
    structure-matching correlate in the elided clause (which has a wh-trace
    there, filtered out as a movement non-head).

    This is also where Bruening's max-proj condition diverges from
    @cite{rudin-2019}'s head-based identity (§5.5 p. 1065): Rudin's
    head-pair condition is satisfied for this case (V/Appl/Voice heads
    all match between antecedent and elided), but Bruening's max-proj
    condition is not. The full Rudin-side prediction would require
    lifting these SyntacticObject trees to `DomainAnnotatedPair` lists
    (`FormalMatching.lean:587`); flagged as follow-up. -/
theorem g1_charged_implicit_first_obj_blocked :
    ¬ bruening2021StructurallyIdentical charged_doc_antecedent charged_doc_elided := by
  decide

/-- @cite{bruening-2021} **Generalization 1** (§2.4 summary point 1, p. 1040;
    §5.5 derivation pp. 1064–1067). The sluicing asymmetry — the load-bearing
    empirical claim of the paper — derived from the maximal-projection
    identity condition (ex. 122) without further stipulation.

    This is the `TODO(G1)` flagged in
    `Phenomena/ArgumentStructure/Studies/Bruening2021.lean`'s deferred-
    substrate section. -/
theorem g1_sluicing_asymmetry :
    bruening2021StructurallyIdentical serve_doc_antecedent serve_doc_elided
    ∧ ¬ bruening2021StructurallyIdentical charged_doc_antecedent charged_doc_elided :=
  ⟨g1_serve_implicit_second_obj_licensed,
   g1_charged_implicit_first_obj_blocked⟩

/-! ### Stress tests / sanity checks

These verify the matcher behaves correctly on edge cases — reflexivity,
symmetry, cross-paradigm rejection, and adversarial near-misses. -/

-- Reflexivity: every tree structurally matches itself.
example : bruening2021StructurallyIdentical serve_doc_antecedent serve_doc_antecedent := by decide
example : bruening2021StructurallyIdentical serve_doc_elided serve_doc_elided := by decide
example : bruening2021StructurallyIdentical charged_doc_antecedent charged_doc_antecedent := by decide
example : bruening2021StructurallyIdentical charged_doc_elided charged_doc_elided := by decide

-- Symmetry: bidirectional matching is order-independent.
example : bruening2021StructurallyIdentical serve_doc_elided serve_doc_antecedent := by decide
example : ¬ bruening2021StructurallyIdentical charged_doc_elided charged_doc_antecedent := by decide

-- Cross-paradigm rejection: serve trees ↔ charged trees should not match
-- (different verb classes, different complement-position contents).
example : ¬ bruening2021StructurallyIdentical serve_doc_antecedent charged_doc_antecedent := by decide
example : ¬ bruening2021StructurallyIdentical serve_doc_antecedent charged_doc_elided := by decide
example : ¬ bruening2021StructurallyIdentical serve_doc_elided charged_doc_antecedent := by decide
example : ¬ bruening2021StructurallyIdentical serve_doc_elided charged_doc_elided := by decide

-- Filtered max-proj counts agree with Bruening's textual enumeration on
-- p. 1066: serve-licit case has 5/5 (after wh-trace filter), charged
-- case has 6/5 (extra unmatched antecedent NP_someone is the blocker).
example : ((maximalProjections serve_doc_antecedent).filter
            (fun x => !isNonHeadMemberOfChain x)).length = 5 := by decide
example : ((maximalProjections serve_doc_elided).filter
            (fun x => !isNonHeadMemberOfChain x)).length = 5 := by decide
example : ((maximalProjections charged_doc_antecedent).filter
            (fun x => !isNonHeadMemberOfChain x)).length = 6 := by decide
example : ((maximalProjections charged_doc_elided).filter
            (fun x => !isNonHeadMemberOfChain x)).length = 5 := by decide

-- ∃ is correctly NOT a max-proj of the antecedent (it's part of V+∃
-- complex head, not a separate node).
example : ¬ V_serve ∈ (maximalProjections serve_doc_antecedent) := by decide

-- The wh-trace IS a max-proj of charged_doc_elided but is filtered.
example : whTrace1 ∈ (maximalProjections charged_doc_elided) := by decide
example : ¬ whTrace1 ∈ ((maximalProjections charged_doc_elided).filter
                          (fun x => !isNonHeadMemberOfChain x)) := by decide

end Bruening2021Sluicing
