import Linglib.Core.Case.Basic
import Linglib.Features.Prominence

/-!
# Alignment Case-Assignment Functions
@cite{dixon-1994} @cite{comrie-1989} @cite{marantz-1991}

The SAP-indexed counterpart to `Theories/Syntax/Case/Dependent.lean`'s
configural algorithm. Each `Alignment.X.assignCase` is a function from
`Features.Prominence.ArgumentRole` to `Core.Case` capturing the canonical
case pattern of alignment type X. The configural derivations in
`Dependent.lean` (Marantz/Baker) and the typology classifier in
`Phenomena/Alignment/Typology.lean` (WALS-style observation) are checked
against the functions here as ground truth.

## Coverage

- `Alignment.nominativeAccusative.assignCase` — accusative alignment (S = A, P
  distinct). The default for Indo-European, Niger-Congo, much of Eurasia.
- `Alignment.ergative.assignCase` — canonical ergative-absolutive (S = P, A
  distinct). Found in Mayan perfective, Basque, Inuit, Australian languages.
- `Alignment.extendedErgative.assignCase` — Mayan non-perfective pattern: S/A
  both bear genitive (Set A), P bears absolutive. Per @cite{coon-2013}
  + @cite{imanishi-2020}, this arises when a nominalized clause embeds the
  external argument so the subject receives genitive from D rather than
  ergative from v. The "extended ergative" label is from @cite{dixon-1994}.

## Ditransitive defaults (R, T)

`ArgumentRole` has 5 constructors covering ditransitives. Ditransitive case
alignment (indirective vs secundative vs neutral, per @cite{haspelmath-2005}'s
typology) is its own dimension orthogonal to monotransitive alignment. The
R/T cases below pick conservative defaults intended to support monotransitive
reasoning at zero cost; **they have no published audit trail and no current
consumers in linglib** (no call site applies `.assignCase .R` or `.T`). Treat
them as scaffolding subject to revision when ditransitive consumers arrive:

- `ergative.{R, T} → ABS`: most ergative languages neutralize ditransitive
  R/T with monotransitive P, but secundative languages (some Bantu) override.
- `nominativeAccusative.R → DAT`: typical for Indo-European and Uralic
  ditransitive paradigms; English/many Bantu/Tagalog have R → ACC instead
  ("double-object" / secundative). The DAT default is IE-biased.
- `nominativeAccusative.T → ACC`: standard.
- `extendedErgative.{R, T} → ABS`: **UNVERIFIED** — Cholan ditransitives in
  non-perfective aspect aren't well-documented in the published literature;
  this default may not survive empirical validation. Flagged for future
  audit when Mateo-Toledo 2008 / Pascual 2007 (Q'anjob'al) or detailed
  Cholan ditransitive data become available.
-/

namespace Alignment

open Features.Prominence (ArgumentRole)

namespace ergative

/-- Ergative-absolutive case assignment.
    Monotransitive: `A → ERG`, `S | P → ABS`. R/T default to ABS. -/
def assignCase : ArgumentRole → Core.Case
  | .A => .erg
  | .S | .P => .abs
  | .R | .T => .abs

end ergative

namespace nominativeAccusative

/-- Nominative-accusative case assignment.
    Monotransitive: `S | A → NOM`, `P → ACC`. R defaults to DAT (the
    recipient case found in Indo-European and Uralic ditransitive
    paradigms); T to ACC. **R → DAT is IE-biased** — secundative and
    double-accusative languages (English, many Bantu, Tagalog) assign
    R → ACC instead and would override this default. -/
def assignCase : ArgumentRole → Core.Case
  | .A | .S => .nom
  | .P | .T => .acc
  | .R => .dat

end nominativeAccusative

namespace extendedErgative

/-- Cholan/Q'anjob'alan non-perfective: `S | A → GEN` (from D under
    nominalization), `P → ABS` (from Voice). Per @cite{coon-2013};
    @cite{imanishi-2020} parameterizes the same surface pattern via inherent
    vs structural Case. R/T default to ABS. -/
def assignCase : ArgumentRole → Core.Case
  | .A | .S => .gen
  | .P => .abs
  | .R | .T => .abs

end extendedErgative

namespace tripartite

/-- Tripartite case assignment: A → ERG, P → ACC, S → ABS — three
    distinct cases, one per argument. Found in San Juan Atitán Mam
    (Mayan, K'ichean-Mamean) per @cite{scott-2023} ch. 3, and (per
    @cite{dixon-1994} §2.1.5) attested in Pitta-Pitta, Wangkumara,
    and several other Australian languages. Mam lacks independent
    DP case morphology — the tripartite analysis is recoverable only
    from agreement patterns (Set A on A, no agreement on P, Set B
    on S). R/T default to ACC (consistent with P) since Mam
    ditransitives aren't documented in the analyzed corpus. -/
def assignCase : ArgumentRole → Core.Case
  | .A => .erg
  | .P => .acc
  | .S => .abs
  | .R | .T => .acc

end tripartite

namespace invertedErgative

/-- Kaqchikel-type non-perfective (specifically PROG sentences with the
    `ajin` matrix predicate): `S | A → ABS`, `P → GEN`. The OBJECT
    receives ergative/genitive case rather than the subject — opposite
    of the canonical extended-ergative pattern.

    Per @cite{imanishi-2014} §3.3.1 ("Kaqchikel: ERG=OBJ", p. 122):
    "Kaqchikel exhibits a cross-linguistically rare alignment pattern
    in the nominative-accusative system found in the progressives and
    in the complement position of certain embedding verbs – the object
    of a transitive verb is aligned with an ergative or genitive
    agreement morpheme."

    Imanishi's mechanism: the Unaccusative Requirement on Nominalization
    (eq. 90, p. 123) forces nominalized transitive verbs in Kaqchikel to
    passivize, removing the external argument. The object becomes the
    only Case-less DP in the nominalized clause and receives ergative
    Case from D as phase head ("phase head ergative Case", his central
    thesis). The subject is base-generated in the matrix (Spec-PredP
    headed by `ajin`) and gets absolutive from Infl.

    Construction-specific: this pattern arises specifically in
    progressive `ajin` constructions and certain embedding-verb
    constructions (e.g., `chäp` 'begin' in (117), p. 137 — though that
    construction has a slightly different sub-pattern with all subjects
    getting ERG too). The `chäp` variant is not encoded here.

    Dialectal variation (per @cite{imanishi-2014} fn. 26, p. 141): "My
    Kaqchikel consultants do not accept nominalized patterns as in (120).
    This is presumably because of dialectal differences." Some Kaqchikel
    varieties may not show the inverted pattern even in PROG sentences;
    @cite{garcia-matzar-rodriguez-guajan-1997} document broader patterns
    that Imanishi's consultants don't accept. R/T default to ABS. -/
def assignCase : ArgumentRole → Core.Case
  | .A | .S => .abs
  | .P => .gen
  | .R | .T => .abs

end invertedErgative

-- ============================================================================
-- § Universal Alignment Properties
-- ============================================================================

theorem ergative_distinguishes_A :
    ergative.assignCase .A ≠ ergative.assignCase .S := by decide

theorem ergative_groups_S_with_P :
    ergative.assignCase .S = ergative.assignCase .P := rfl

theorem accusative_distinguishes_P :
    nominativeAccusative.assignCase .P ≠ nominativeAccusative.assignCase .S := by decide

theorem accusative_groups_S_with_A :
    nominativeAccusative.assignCase .S = nominativeAccusative.assignCase .A := rfl

theorem extendedErgative_groups_S_with_A :
    extendedErgative.assignCase .S = extendedErgative.assignCase .A := rfl

theorem extendedErgative_distinguishes_P :
    extendedErgative.assignCase .P ≠ extendedErgative.assignCase .A := by decide

theorem invertedErgative_groups_S_with_A :
    invertedErgative.assignCase .S = invertedErgative.assignCase .A := rfl

theorem invertedErgative_distinguishes_P :
    invertedErgative.assignCase .P ≠ invertedErgative.assignCase .A := by decide

/-- Inverted ergative is the mirror image of extended ergative on the A/P
    axis: where extended-ergative gives A → GEN and P → ABS, inverted
    gives A → ABS and P → GEN. The S/A grouping is the same in both. -/
theorem invertedErgative_swaps_extendedErgative_on_AP :
    invertedErgative.assignCase .A = extendedErgative.assignCase .P ∧
    invertedErgative.assignCase .P = extendedErgative.assignCase .A := ⟨rfl, rfl⟩

/-- Tripartite distinguishes all three SAP arguments — the
    distinguishing property of tripartite alignment vs the others
    (which all collapse at least one pair). -/
theorem tripartite_distinguishes_all :
    tripartite.assignCase .A ≠ tripartite.assignCase .P ∧
    tripartite.assignCase .A ≠ tripartite.assignCase .S ∧
    tripartite.assignCase .P ≠ tripartite.assignCase .S := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The five alignments are pairwise distinct on the agent: each picks
    a different case for A (erg, nom, gen, abs, erg). Tripartite shares
    A → ERG with canonical ergative — they differ on P (acc vs abs). -/
theorem alignments_distinct_on_A :
    ergative.assignCase .A = .erg ∧
    nominativeAccusative.assignCase .A = .nom ∧
    extendedErgative.assignCase .A = .gen ∧
    invertedErgative.assignCase .A = .abs ∧
    tripartite.assignCase .A = .erg := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Tripartite is distinguished from canonical ergative by P: tripartite
    gives P → ACC, canonical gives P → ABS (grouping with S). -/
theorem tripartite_differs_from_ergative_on_P :
    tripartite.assignCase .P ≠ ergative.assignCase .P := by decide

end Alignment
