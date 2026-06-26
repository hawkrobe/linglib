import Linglib.Syntax.Minimalist.Movement.VerbMovementParameter
import Linglib.Studies.Westergaard2009
import Linglib.Fragments.German.V2

/-!
# Head Movement in Bulgarian LHM and Germanic V2
[harizanov-gribanova-2019]

Connects the Minimalist analysis of head movement to empirical verb
position data.

## Bulgarian Long Head Movement

[lambova-2004c] (cited in [harizanov-gribanova-2019] examples
(29), (48), (52)): both word orders are grammatical with the same meaning.

**Order A (participle before auxiliary):**
    Pročeli bjaha studentite statijata.
    read be.3p.pst the.students the.article
    'The students had read the article.'

**Order B (auxiliary before participle):**
    Studentite bjaha pročeli statijata.
    the.students be.3p.pst read the.article
    'The students had read the article.'

## Germanic V2

- `models_root_v2`: German root declaratives are V2 (consistent with V-to-C)
- `models_embedded_verb_final`: German embedded clauses are verb-final

## Disputed: V-to-I in German embedded clauses

[harizanov-gribanova-2019] (§5.1.2) and [westergaard-2009]
(Table 3.1) make incompatible claims about whether the finite verb
raises to I/T/Fin in German embedded finite clauses.

- **[harizanov-gribanova-2019]**, with [haider-2010] as the
  strongest contemporary German-internal anchor: V does NOT raise to
  T in embedded non-V2 clauses — it "stays below adverbs/negation."
  The only V-movement step in German is the V-to-C step in matrix
  V2 contexts. (Quoted in `GermanicV2.lean`.)
- **[westergaard-2009]**: German is +Fin° in Table 3.1. Combined
  with OV base order, +Fin° derives the verb-final embedded surface
  order via raising to Fin (rather than via the verb staying in V).

The empirical diagnostic — [roberts-1993]'s V-to-I diagnostic
kit — is the position of the embedded finite verb relative to
sentence adverbs (e.g. *oft*, *wahrscheinlich*) and negation. Both
analyses derive verb-final surface order; they disagree about whether
V crosses I on the way there. The codebase records Westergaard's
positive claim via `German.german`'s `.Fin` membership;
[harizanov-gribanova-2019]'s denial lives in prose ("no V-to-I"
is not a positive Lean witness), but the contradiction with
Westergaard is formalized as a refutation theorem below via the
`westergaardToMovementParam` projection.
-/

namespace HarizanovGribanova2019

-- ============================================================================
-- Germanic V2 ([vikner-1995])
-- ============================================================================

open Westergaard2009
open Minimalist (ForceHead V2Profile)

/-- German root declaratives are V2 — consistent with V-to-C head movement. -/
theorem models_root_v2 :
    de_decl.v2Status = .obligatory := by decide

/-- German embedded clauses are verb-final — no V-to-C in the presence
    of an overt complementizer. -/
theorem models_embedded_verb_final :
    de_emb.v2Status = .impossible := by decide

/-- The root-clause sentence from [vikner-1995]. -/
theorem root_sentence :
    de_decl.sentence = "Diesen Film haben die Kinder gesehen" := rfl

-- ============================================================================
-- Westergaard's contested +Fin° claim for German
-- ============================================================================

/-- [westergaard-2009]'s positive claim: German embedded clauses
    have V-to-I (= +Fin°). [harizanov-gribanova-2019] disputes
    this analytically (no V-to-I; verb stays in V). Re-exported from
    `Westergaard2009.fin_only_german` so this file's H&G-vs-Westergaard
    section has the witness in scope; the actual `decide` lives in
    Westergaard2009. The H&G "no V-to-I" denial is encoded as a
    refutation theorem below via the `westergaardToMovementParam`
    projection. -/
theorem westergaard_german_plus_fin :
    ForceHead.Fin ∈ German.german :=
  Westergaard2009.fin_only_german.1

-- ============================================================================
-- Refutation: H&G vs. Westergaard on German V-to-I
-- ============================================================================

open Minimalist (VMovementParam)

/-- Project [westergaard-2009]'s V2 micro-parameter profile into
    [pollock-1989]'s V-movement parameter: the +Fin°
    micro-parameter (V-to-Fin / V-to-I) in the V2 profile corresponds
    to `.raises` in `VMovementParam`; its absence corresponds to
    `.inSitu`. Lets the otherwise-incompatible Westergaard and H&G
    accounts contradict each other on a common Lean object. -/
def westergaardToMovementParam (p : V2Profile) [Decidable (ForceHead.Fin ∈ p)] :
    VMovementParam :=
  if ForceHead.Fin ∈ p then .raises else .inSitu

/-- [harizanov-gribanova-2019]'s prediction for German embedded
    finite clauses: V stays in V — no V-to-I, no V-to-T. -/
def germanHG : VMovementParam := .inSitu

/-- [harizanov-gribanova-2019] predicts `.inSitu` for German
    embedded clauses; [westergaard-2009]'s V2 profile, projected
    via `westergaardToMovementParam`, predicts `.raises`. The two
    frameworks make contradictory predictions about a single Lean
    object — formalizing the long-standing Vikner-vs.-Haider /
    Westergaard-vs.-H&G dispute about V-to-I in German. -/
theorem hg_westergaard_german_disagree :
    germanHG ≠ westergaardToMovementParam German.german := by decide

end HarizanovGribanova2019
