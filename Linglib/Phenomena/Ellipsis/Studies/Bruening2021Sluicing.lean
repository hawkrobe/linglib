import Linglib.Theories.Syntax.Minimalist.Ellipsis.FormalMatching
import Linglib.Phenomena.ArgumentStructure.Studies.Bruening2021

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
`bruening2021Identity`, alongside @cite{rudin-2019} (§ 6) and
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

def DP_she     : SyntacticObject := mkLeafPhon .D [] "she" 1
def Voice_act  : SyntacticObject := mkLeafPhon .Voice [.V] "Voice[act]" 3
def V_serve    : SyntacticObject := mkLeafPhon .V [.D] "serve" 4
def DP_us      : SyntacticObject := mkLeafPhon .D [] "us" 5
def Appl_h     : SyntacticObject := mkLeafPhon .Appl [.V] "∅" 6
/-- The ∃ functional head Bruening adjoins to V to license indef-implicit
    second objects (§4.2 ex. 96). Encoded as a `.V`-cat leaf with phon
    "∃" — sufficient for §5.5 G1, where ∃'s only structural role is to
    differ between antecedent (where it adjoins to V) and elided clause
    (where wh-movement leaves a trace in object position instead). -/
def ExistOp    : SyntacticObject := mkLeafPhon .V [] "∃" 7
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
  -- [VoiceP DP_she [Voice [ApplP DP_us [Appl' Appl [VP V_serve ∃]]]]]
  merge DP_she
    (merge Voice_act
      (merge DP_us
        (merge Appl_h
          (merge V_serve ExistOp))))

def serve_doc_elided : SyntacticObject :=
  -- Wh-movement of "what" leaves trace in object position; ∃ replaced by trace
  merge DP_she
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
    ignores it. -/
theorem g1_serve_implicit_second_obj_licensed :
    bruening2021Identity serve_doc_antecedent serve_doc_elided = true := by
  decide

/-- Implicit first-object DOC sluicing is blocked. Per @cite{bruening-2021}
    ex. 124, p. 1066: the antecedent's spec-ApplP DP (`someone`) has no
    structure-matching correlate in the elided clause (which has a wh-trace
    there, filtered out as a movement non-head). -/
theorem g1_charged_implicit_first_obj_blocked :
    bruening2021Identity charged_doc_antecedent charged_doc_elided = false := by
  decide

/-- @cite{bruening-2021} **Generalization 1** (§2.4 summary point 1, p. 1040;
    §5.5 derivation pp. 1064–1067). The sluicing asymmetry — the load-bearing
    empirical claim of the paper — derived from the maximal-projection
    identity condition (ex. 122) without further stipulation.

    This is the `TODO(G1)` flagged in
    `Phenomena/ArgumentStructure/Studies/Bruening2021.lean`'s deferred-
    substrate section. -/
theorem g1_sluicing_asymmetry :
    bruening2021Identity serve_doc_antecedent serve_doc_elided = true
    ∧ bruening2021Identity charged_doc_antecedent charged_doc_elided = false :=
  ⟨g1_serve_implicit_second_obj_licensed,
   g1_charged_implicit_first_obj_blocked⟩

/-! ### Cross-framework contrast: Bruening vs Rudin 2019 -/

/-- @cite{bruening-2021} §5.5 (p. 1065) explicitly modifies @cite{rudin-2019}'s
    head-based identity condition to use maximal projections. The G1 case
    is precisely where the two diverge: Rudin's head-pair condition is
    satisfied for `charged_doc` (the V/Appl/Voice heads all match between
    antecedent and elided), but Bruening's max-proj condition is not (the
    antecedent's spec-ApplP DP `someone` has no correlate in the elided
    clause's filtered max-projs).

    The full Rudin-side prediction would require lifting our SyntacticObject
    trees to `DomainAnnotatedPair` lists (FormalMatching.lean:587), which
    is a larger task; flagged for follow-up. We land the Bruening-side
    blocking claim now. -/
theorem bruening_diverges_from_rudin_on_g1 :
    bruening2021Identity charged_doc_antecedent charged_doc_elided = false :=
  g1_charged_implicit_first_obj_blocked

end Bruening2021Sluicing
