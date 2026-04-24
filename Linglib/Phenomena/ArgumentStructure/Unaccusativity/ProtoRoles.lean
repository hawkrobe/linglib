import Linglib.Theories.Semantics.Verb.EntailmentProfile
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Proto-roles and unaccusativity
@cite{dowty-1991} @cite{levin-hovav-1995} @cite{storment-2026}

How Dowty's proto-role profiles (@cite{dowty-1991}) interact with the
syntactic unaccusativity diagnostics (auxiliary selection,
there-insertion, quotative inversion). This file is the formalizer's
synthesis: neither Dowty 1991 (which doesn't run a syntactic
unaccusativity diagnostic) nor Storment 2026 (which doesn't engage
proto-role counting) makes these comparisons.

The interaction is mixed. For canonical unaccusatives ("arrive") and
canonical unergatives ("speak"), proto-role counting and syntactic
unaccusativity agree. For manner-of-speaking verbs, they diverge:
MoS subjects are volitional, sentient, independently existing — a
clear proto-agent profile — yet @cite{storment-2026}'s quotative-
inversion diagnostic classifies them as unaccusative.

The divergence is documented in the syntactic literature (going back
to @cite{levin-hovav-1995}) but isn't ordinarily formalized as a
proto-role/diagnostic mismatch. This file makes the contrast explicit.

## Files
- Dowty's predicates `PredictsUnaccusative` / `PredictsUnergative`
  live in `Theories/Semantics/Verb/EntailmentProfile.lean`.
- The MoS verb data lives in `Fragments/English/Predicates/Verbal.lean`.
-/

namespace Phenomena.ArgumentStructure.Unaccusativity.ProtoRoles

open Semantics.Verb.EntailmentProfile
open Fragments.English.Predicates.Verbal

/-! ## §1. Canonical alignment cases

Proto-role counting agrees with syntactic unaccusativity for the textbook
cases: `arrive` (P-Patient profile) is unaccusative; `speak`
(P-Agent profile) is unergative. -/

/-- The proto-role profile of an MoS verb subject: volitional, sentient,
    exists independently — three P-Agent entailments, no P-Patient
    entailments. Constructed once for reuse below. -/
def mosSubjectProfile : EntailmentProfile where
  volition := true
  sentience := true
  causation := false
  movement := false
  independentExistence := true
  changeOfState := false
  incrementalTheme := false
  causallyAffected := false
  stationary := false
  dependentExistence := false

/-- Dowty's counting algorithm classifies the MoS subject profile as
    proto-agentive (3 P-Agent entailments, 0 P-Patient). -/
theorem mos_profile_predicts_unergative :
    PredictsUnergative mosSubjectProfile := by decide

theorem mos_profile_not_predicted_unaccusative :
    ¬ PredictsUnaccusative mosSubjectProfile := by decide

/-! ## §2. The MoS divergence

Despite Dowty's prediction, every MoS verb in the Fragment is annotated
unaccusative — because it passes Storment's QI diagnostic. This is the
formalizer's-side observation: Dowty would predict unergative, the QI
diagnostic returns unaccusative. -/

/-- The Storment-side syntactic classification: `whisper` is unaccusative
    in the Fragment, on the basis of the QI diagnostic. -/
theorem whisper_qi_unaccusative : whisper.unaccusative = true := rfl

/-- Together: Dowty proto-role counting and the QI-based syntactic
    diagnostic disagree for `whisper`. The disagreement holds for the
    other MoS verbs too (same subject profile, same Fragment annotation),
    but `whisper` is the canonical instance. -/
theorem whisper_dowty_qi_divergence :
    PredictsUnergative mosSubjectProfile ∧ whisper.unaccusative = true :=
  ⟨by decide, rfl⟩

/-! ## §3. Where the divergence comes from

Dowty's counting is a lexical-semantic algorithm; QI is a syntactic
diagnostic. @cite{levin-hovav-1995} argued the syntax-semantics
interface is *thematically determined* but has its own logic — verbs
with the same lexical-semantic profile can pattern differently
syntactically. The MoS case is one fault line where the two
classifications come apart. -/

end Phenomena.ArgumentStructure.Unaccusativity.ProtoRoles
