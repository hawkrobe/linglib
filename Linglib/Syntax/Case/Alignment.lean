/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Features.Case.Basic
import Linglib.Features.Prominence
import Mathlib.Data.Fintype.Prod

/-!
# Alignment Case-Assignment Functions
[dixon-1994] [comrie-1989] [marantz-1991]

The SAP-indexed counterpart to `Syntax/Case/Dependent.lean`'s
configural algorithm. Each `Alignment.X.assignCase` is a function from
`Features.Prominence.ArgumentRole` to `Case` capturing the canonical
case pattern of alignment type X. The configural derivations in
`Dependent.lean` (Marantz/Baker) and the observational `AlignmentType` enum
(WALS-style classification, below) are checked against the case-assignment
functions here as ground truth.

## Coverage

- `Alignment.nominativeAccusative.assignCase` — accusative alignment (S = A, P
  distinct). The default for Indo-European, Niger-Congo, much of Eurasia.
- `Alignment.ergative.assignCase` — canonical ergative-absolutive (S = P, A
  distinct). Found in Mayan perfective, Basque, Inuit, Australian languages.
- `Alignment.extendedErgative.assignCase` — Mayan non-perfective pattern: S/A
  both bear genitive (Set A), P bears absolutive. Per [coon-2013]
  + [imanishi-2020], this arises when a nominalized clause embeds the
  external argument so the subject receives genitive from D rather than
  ergative from v. The "extended ergative" label is from [dixon-1994].

## Ditransitive defaults (R, T)

`ArgumentRole` has 5 constructors covering ditransitives. Ditransitive case
alignment (indirective vs secundative vs neutral, per [haspelmath-2005]'s
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
def assignCase : ArgumentRole → Case
  | .A => .erg
  | .S | .P => .abs
  | .R | .T => .abs

theorem assignCase_A : assignCase .A = .erg := rfl
theorem assignCase_P : assignCase .P = .abs := rfl
theorem assignCase_S : assignCase .S = .abs := rfl

end ergative

namespace nominativeAccusative

/-- Nominative-accusative case assignment.
    Monotransitive: `S | A → NOM`, `P → ACC`. R defaults to DAT (the
    recipient case found in Indo-European and Uralic ditransitive
    paradigms); T to ACC. **R → DAT is IE-biased** — secundative and
    double-accusative languages (English, many Bantu, Tagalog) assign
    R → ACC instead and would override this default. -/
def assignCase : ArgumentRole → Case
  | .A | .S => .nom
  | .P | .T => .acc
  | .R => .dat

end nominativeAccusative

namespace extendedErgative

/-- Cholan/Q'anjob'alan non-perfective: `S | A → GEN` (from D under
    nominalization), `P → ABS` (from Voice). Per [coon-2013];
    [imanishi-2020] parameterizes the same surface pattern via inherent
    vs structural Case. R/T default to ABS. -/
def assignCase : ArgumentRole → Case
  | .A | .S => .gen
  | .P => .abs
  | .R | .T => .abs

end extendedErgative

namespace tripartite

/-- Tripartite case assignment: A → ERG, P → ACC, S → ABS — three
    distinct cases, one per argument. Found in San Juan Atitán Mam
    (Mayan, K'ichean-Mamean) per [scott-2023] ch. 3, and (per
    [dixon-1994] §2.1.5) attested in Pitta-Pitta, Wangkumara,
    and several other Australian languages. Mam lacks independent
    DP case morphology — the tripartite analysis is recoverable only
    from agreement patterns (Set A on A, no agreement on P, Set B
    on S). R/T default to ACC (consistent with P) since Mam
    ditransitives aren't documented in the analyzed corpus. -/
def assignCase : ArgumentRole → Case
  | .A => .erg
  | .P => .acc
  | .S => .abs
  | .R | .T => .acc

theorem assignCase_A : assignCase .A = .erg := rfl
theorem assignCase_P : assignCase .P = .acc := rfl
theorem assignCase_S : assignCase .S = .abs := rfl

end tripartite

namespace invertedErgative

/-- Kaqchikel-type non-perfective (specifically PROG sentences with the
    `ajin` matrix predicate): `S | A → ABS`, `P → GEN`. The OBJECT
    receives ergative/genitive case rather than the subject — opposite
    of the canonical extended-ergative pattern.

    Per [imanishi-2014] §3.3.1 ("Kaqchikel: ERG=OBJ", p. 122):
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

    Dialectal variation (per [imanishi-2014] fn. 26, p. 141): "My
    Kaqchikel consultants do not accept nominalized patterns as in (120).
    This is presumably because of dialectal differences." Some Kaqchikel
    varieties may not show the inverted pattern even in PROG sentences;
    [garcia-matzar-rodriguez-guajan-1997] document broader patterns
    that Imanishi's consultants don't accept. R/T default to ABS. -/
def assignCase : ArgumentRole → Case
  | .A | .S => .abs
  | .P => .gen
  | .R | .T => .abs

end invertedErgative

-- ============================================================================
-- § Alignment as a partition of the core roles — Bell(3) = 5
-- ============================================================================

/-! An *alignment* is which of the core monotransitive roles {S, A, P} an
analysis groups together — the partition of {S, A, P} that
`assign : ArgumentRole → Case` induces (the kernel of `assign`, *restricted to
the three core roles*: the full `Setoid.ker` over `ArgumentRole` would also
constrain the ditransitive scaffolding roles R, T, which alignment does not).
This is a point in the partition lattice of a three-element set, orthogonal to
the Case *labels* used — `nominativeAccusative`, `extendedErgative`, and
`invertedErgative` induce the *same* partition with different cases. A
three-element set has exactly five partitions (`Bell 3 = 5`), hence five
monotransitive alignments; `coreSig` is the decidable code for the partition.

This partition object **replaces** the scattered per-alignment
`_groups_S_with_X` / `_distinguishes_P` theorems this file used to carry
(restatements of it, now retired); only `tripartite_distinguishes_all` is kept,
as it is re-exported by downstream consumers. -/

/-- Tripartite distinguishes all three SAP arguments — the defining property of
    tripartite alignment. Re-exported as the case-distinctness fact by
    `Scott2023.voice_based_tripartite` and `Mam.Agreement.tripartite_alignment`;
    the general partition picture is `assignCase_partitions` below. -/
theorem tripartite_distinguishes_all :
    tripartite.assignCase .A ≠ tripartite.assignCase .P ∧
    tripartite.assignCase .A ≠ tripartite.assignCase .S ∧
    tripartite.assignCase .P ≠ tripartite.assignCase .S := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Ergative distinguishes A and groups P with S — the defining property of
    ergative alignment (the partition `{S,P}|{A}` of `assignCase_partitions`).
    Kept, like `tripartite_distinguishes_all`, as the re-export target for
    per-language alignment facts (`Kaqchikel.erg_abs_alignment`,
    `Kiche.erg_abs_pattern`). -/
theorem ergative_distinguishes_A :
    ergative.assignCase .A ≠ ergative.assignCase .P ∧
    ergative.assignCase .P = ergative.assignCase .S :=
  ⟨by decide, rfl⟩

/-- The core-role signature `(S≈A, S≈P, A≈P)` of an alignment — a faithful code
    for its partition of {S, A, P}: transitivity makes the three pairwise
    relations determine, and be determined by, the partition. -/
def coreSig (assign : ArgumentRole → Case) : Bool × Bool × Bool :=
  (decide (assign .S = assign .A),
   decide (assign .S = assign .P),
   decide (assign .A = assign .P))

/-- A signature is **consistent** (realizable as a partition) iff, by
    transitivity, any two of the three role-equalities force the third — ruling
    out the three "exactly two true" triples. -/
def ConsistentSig (s : Bool × Bool × Bool) : Bool :=
  (!(s.1 && s.2.1) || s.2.2) && (!(s.1 && s.2.2) || s.2.1) && (!(s.2.1 && s.2.2) || s.1)

/-- Every alignment's signature is consistent: it really is a partition. -/
theorem coreSig_consistent (assign : ArgumentRole → Case) :
    ConsistentSig (coreSig assign) = true := by
  by_cases h1 : assign .S = assign .A <;> by_cases h2 : assign .S = assign .P <;>
    by_cases h3 : assign .A = assign .P <;> simp_all [coreSig, ConsistentSig]

/-- **Bell(3) = 5.** Exactly five signatures are consistent — the five partitions
    of a three-element set: neutral `(T,T,T)`, accusative `(T,F,F)`, ergative
    `(F,T,F)`, horizontal `(F,F,T)`, tripartite `(F,F,F)`. The three "exactly two
    equalities" triples are forbidden by transitivity. -/
theorem consistent_sigs :
    Finset.univ.filter (fun s : Bool × Bool × Bool => ConsistentSig s = true) =
      {(true, true, true), (true, false, false), (false, true, false),
       (false, false, true), (false, false, false)} := by decide

theorem bell_three_eq_five :
    (Finset.univ.filter (fun s : Bool × Bool × Bool => ConsistentSig s = true)).card = 5 := by
  rw [consistent_sigs]; decide

/-- The five `assignCase` functions realize only **three** of the five
    partitions: `nominativeAccusative`, `extendedErgative`, and `invertedErgative`
    all induce the accusative partition `{S,A}|{P}` — they differ only in Case
    *labels*, not alignment (the kernel generalizing the one instance noticed in
    `Dixon1994.extendedErgative_groups_S_with_A_like_accusative`). -/
theorem assignCase_partitions :
    coreSig nominativeAccusative.assignCase = (true, false, false) ∧
    coreSig extendedErgative.assignCase    = (true, false, false) ∧
    coreSig invertedErgative.assignCase    = (true, false, false) ∧
    coreSig ergative.assignCase            = (false, true, false) ∧
    coreSig tripartite.assignCase          = (false, false, false) := by decide

/-- The horizontal partition `{A,P}|{S}` (A and P align, S apart — attested,
    Pamir-type) is a genuine partition of {S, A, P} realized by **none** of the
    `assignCase` functions here. (It is also absent from `AlignmentType`.) -/
theorem horizontal_unrealized :
    ConsistentSig (false, false, true) = true ∧
    coreSig nominativeAccusative.assignCase ≠ (false, false, true) ∧
    coreSig ergative.assignCase            ≠ (false, false, true) ∧
    coreSig tripartite.assignCase          ≠ (false, false, true) ∧
    coreSig extendedErgative.assignCase    ≠ (false, false, true) ∧
    coreSig invertedErgative.assignCase    ≠ (false, false, true) := by decide

-- ============================================================================
-- § Ditransitive alignment ([haspelmath-2005])
-- ============================================================================

/-- Ditransitive alignment: how R (recipient) and T (theme) are coded relative
    to monotransitive P — the ditransitive analogue of the monotransitive
    alignment above, hence co-located with it (used by `Dixon1994` and
    `Haspelmath2021`). -/
inductive DitransitiveAlignment where
  /-- R = T = P: no distinction among non-agent arguments. -/
  | neutral
  /-- T = P ≠ R: R distinctly marked, T patterns with P (indirective;
      analogous to accusative — English "give the book TO Mary"). -/
  | indirective
  /-- R = P ≠ T: T distinctly marked, R patterns with P (secundative;
      analogous to ergative — many Bantu applicatives). -/
  | secundative
  /-- R ≠ T ≠ P: all three roles distinctly marked. -/
  | tripartite
  deriving DecidableEq, BEq, Repr

/-- Whether this ditransitive alignment marks R distinctly from P. -/
def DitransitiveAlignment.marksR : DitransitiveAlignment → Bool
  | .indirective => true
  | .tripartite  => true
  | _            => false

/-- Whether this ditransitive alignment marks T distinctly from P. -/
def DitransitiveAlignment.marksT : DitransitiveAlignment → Bool
  | .secundative => true
  | .tripartite  => true
  | _            => false

/-- A language's ditransitive alignment profile. -/
structure DitransitiveProfile where
  name : String
  iso639 : String
  alignment : DitransitiveAlignment
  notes : String := ""
  deriving Repr, DecidableEq

/-! ### Observational alignment type (WALS Chs 98/99/100)

The 5-way WALS classification ([comrie-2013]) of how a language groups S/A/P.
The case-assignment functions above are the kernel; this enum is the
observational label, grounded in the partition `coreSig` induces by
`partitionSig_grounded`. -/

/-- Morphosyntactic alignment type: five categories classifying how a language
    groups the three core grammatical relations S, A, P. -/
inductive AlignmentType where
  /-- S = A = P: no morphological distinction (e.g. Mandarin, Thai). -/
  | neutral
  /-- S = A ≠ P: subject + agent grouped, patient distinct (most common). -/
  | accusative
  /-- S = P ≠ A: absolutive grouping, agent distinct (e.g. Basque). -/
  | ergative
  /-- S ≠ A ≠ P: all three distinctly marked (rare; Nez Perce). -/
  | tripartite
  /-- Active / split-S: S splits into agent-like and patient-like. -/
  | active
  deriving DecidableEq, BEq, Repr

instance : Inhabited AlignmentType := ⟨.neutral⟩

/-- Whether this alignment marks the agent (A) distinctly from S. -/
def AlignmentType.marksAgent (a : AlignmentType) : Prop := a = .ergative ∨ a = .tripartite

instance (a : AlignmentType) : Decidable a.marksAgent := by
  unfold AlignmentType.marksAgent; infer_instance

/-- Whether this alignment marks the patient (P) distinctly from S. -/
def AlignmentType.marksPatient (a : AlignmentType) : Prop := a = .accusative ∨ a = .tripartite

instance (a : AlignmentType) : Decidable a.marksPatient := by
  unfold AlignmentType.marksPatient; infer_instance

/-! ### Split ergativity [blake-1994] [dixon-1994]

A `SplitErgativity Factor` is parameterised by the conditioning factor (aspect,
person, animacy, …); `alignment` projects to the ergative or accusative family.
The Hindi aspect-conditioned split (`hindiSplit`) is the canonical worked
example, used as the cross-linguistic reference point by the Yukatek/Hindi
fragments and the Mayan/Silverstein studies. -/

open Features (AlignmentFamily)

/-- A split-ergative system ([blake-1994], [dixon-1994]): alignment varies by
    some conditioning factor. -/
structure SplitErgativity (Factor : Type) where
  ergCondition : Factor → Bool

def SplitErgativity.alignment {Factor : Type} (split : SplitErgativity Factor)
    (f : Factor) : AlignmentFamily :=
  if split.ergCondition f then .ergative else .accusative

inductive Aspect where
  | perfective
  | imperfective
  deriving DecidableEq, Repr

/-- The canonical aspect-conditioned split: perfective ⇒ ergative, imperfective
    ⇒ accusative (Hindi-Urdu). The reference instance other aspect-split
    languages are compared against. -/
def hindiSplit : SplitErgativity Aspect :=
  { ergCondition := fun a => a == .perfective }

theorem hindi_perfective_erg : hindiSplit.alignment .perfective = .ergative := rfl

theorem hindi_imperfective_acc : hindiSplit.alignment .imperfective = .accusative := rfl

/-! ### Grounding the enum in the partition object -/

/-- `AlignmentType` as the core-role signature `(S≈A, S≈P, A≈P)` of the partition
    it denotes (`coreSig` vocabulary). `active` is **not** a partition of {S,A,P}
    — it splits S — so it has no signature (`none`). -/
def AlignmentType.partitionSig : AlignmentType → Option (Bool × Bool × Bool)
  | .neutral    => some (true, true, true)
  | .accusative => some (true, false, false)
  | .ergative   => some (false, true, false)
  | .tripartite => some (false, false, false)
  | .active     => none

/-- The four partition-denoting `AlignmentType`s agree with the partitions the
    corresponding `assignCase` functions induce — grounding the enum in the
    kernel object rather than maintaining it independently. -/
theorem partitionSig_grounded :
    AlignmentType.accusative.partitionSig = some (coreSig nominativeAccusative.assignCase) ∧
    AlignmentType.ergative.partitionSig = some (coreSig ergative.assignCase) ∧
    AlignmentType.tripartite.partitionSig = some (coreSig tripartite.assignCase) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Alignment
