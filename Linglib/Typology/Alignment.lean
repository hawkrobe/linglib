import Linglib.Datasets.WALS.Features.F98A
import Linglib.Datasets.WALS.Features.F99A
import Linglib.Datasets.WALS.Features.F100A

/-!
# Typology.Alignment
@cite{comrie-1978} @cite{comrie-2013} @cite{dixon-1994} @cite{dixon-1972}
@cite{dryer-haspelmath-2013} @cite{haspelmath-2005} @cite{haspelmath-2021}
@cite{wals-2013}

Per-language typological substrate for morphosyntactic alignment, covering
how languages mark the core grammatical relations S (sole argument of
intransitive), A (agent of transitive), and P (patient of transitive).
Three WALS chapters by @cite{comrie-2013}:

- **Ch 98**: alignment of case marking of full noun phrases.
- **Ch 99**: alignment of case marking of pronouns.
- **Ch 100**: alignment of verbal person marking.

Plus ditransitive alignment from @cite{haspelmath-2005}.

Mirrors the `Linglib/Typology/{Possession,Negation,Comparison,Coordination,
Modality,Gender}` substrate-extension pattern. Fragment-importable.

## What lives here

- `AlignmentType` (5-way: neutral / accusative / ergative / tripartite /
  active) + projection helpers.
- `AlignmentProfile` per-language struct + cross-domain helpers.
- `DitransitiveAlignment` (4-way: neutral / indirective / secundative /
  tripartite) + projection helpers.
- `DitransitiveProfile` per-language struct.
- WALS converters: `fromWALS98A`, `fromWALS99A`, `fromWALS100A`.
- WALS aggregate sample-size + corpus-only generalisations from Ch 98/99/100.

## Theory-laden caveats

- **`AlignmentType` collapses some WALS distinctions.** WALS Ch 98
  distinguishes "marked nominative" from canonical accusative; we merge
  both into `.accusative`. WALS Ch 100 has `.hierarchical` and `.split`
  values that don't map cleanly to our 5-way enum (`fromWALS100A` returns
  `Option AlignmentType` for these).
- **`active` vs split-S.** What we call `.active` covers both
  semantically-conditioned split-S (Georgian, Guarani) and
  aspect-conditioned split (Yukatek). The split mechanism differs, but
  WALS lumps them.

## Out of scope

The 22-language sample, cross-linguistic generalisations (Dixon,
Silverstein), ditransitive sample, and Fragment-bridge theorems live in
`Phenomena/Alignment/Studies/Dixon1994.lean`.
@cite{comrie-1989}'s typology generalisations are in
`Phenomena/Case/Studies/Comrie1989.lean`.
-/

set_option autoImplicit false

namespace Typology.Alignment

private abbrev ch98  := Datasets.WALS.F98A.allData
private abbrev ch99  := Datasets.WALS.F99A.allData
private abbrev ch100 := Datasets.WALS.F100A.allData

-- ============================================================================
-- §1. Alignment types (Ch 98/99/100)
-- ============================================================================

/-- Morphosyntactic alignment type for case marking or verbal person marking.
    Five categories classifying how a language groups the three core
    grammatical relations S, A, P. -/
inductive AlignmentType where
  /-- S = A = P: no morphological distinction (e.g. Mandarin, Thai). -/
  | neutral
  /-- S = A ≠ P: subject + agent grouped, patient distinct (most common). -/
  | accusative
  /-- S = P ≠ A: absolutive grouping, agent distinct (e.g. Basque). -/
  | ergative
  /-- S ≠ A ≠ P: all three distinctly marked (rare; Nez Perce). -/
  | tripartite
  /-- Active / split-S: S splits into agent-like and patient-like
      (e.g. Georgian, Guarani). -/
  | active
  deriving DecidableEq, BEq, Repr

instance : Inhabited AlignmentType := ⟨.neutral⟩

/-- Whether this alignment marks the agent (A) distinctly from S. -/
def AlignmentType.marksAgent : AlignmentType → Bool
  | .ergative   => true
  | .tripartite => true
  | _           => false

/-- Whether this alignment marks the patient (P) distinctly from S. -/
def AlignmentType.marksPatient : AlignmentType → Bool
  | .accusative => true
  | .tripartite => true
  | _           => false

/-- Whether this alignment groups S with A (nominative-accusative pattern). -/
def AlignmentType.IsNomAcc (a : AlignmentType) : Prop := a = .accusative

instance : DecidablePred AlignmentType.IsNomAcc :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- Whether this alignment groups S with P (absolutive-ergative pattern). -/
def AlignmentType.IsAbsErg (a : AlignmentType) : Prop := a = .ergative

instance : DecidablePred AlignmentType.IsAbsErg :=
  fun _ => inferInstanceAs (Decidable (_ = _))

-- ============================================================================
-- §2. AlignmentProfile (Fragment-side joint)
-- ============================================================================

/-- A language's alignment profile across WALS Chs 98/99/100. -/
structure AlignmentProfile where
  /-- Language name. -/
  name : String
  /-- ISO 639-3 code. -/
  iso639 : String
  /-- Ch 98: alignment of case marking of full NPs. -/
  npAlignment : AlignmentType
  /-- Ch 99: alignment of case marking of pronouns. -/
  pronAlignment : AlignmentType
  /-- Ch 100: alignment of verbal person marking. -/
  verbAlignment : AlignmentType
  /-- Notes on the alignment system. -/
  notes : String := ""
  deriving Repr, DecidableEq

/-- Whether NP and pronoun alignment match (no split ergativity in case). -/
def AlignmentProfile.caseUniform (p : AlignmentProfile) : Bool :=
  p.npAlignment == p.pronAlignment

/-- Whether the language shows the classic NP-ergative / pronoun-accusative
    split (@cite{dixon-1994}'s generalization). -/
def AlignmentProfile.dixonSplit (p : AlignmentProfile) : Bool :=
  p.npAlignment == .ergative && p.pronAlignment == .accusative

/-- Whether all three domains have the same alignment. -/
def AlignmentProfile.fullyUniform (p : AlignmentProfile) : Bool :=
  p.npAlignment == p.pronAlignment && p.pronAlignment == p.verbAlignment

/-- Whether the language has any ergative alignment in any domain. -/
def AlignmentProfile.hasAnyErgative (p : AlignmentProfile) : Bool :=
  p.npAlignment == .ergative || p.pronAlignment == .ergative ||
  p.verbAlignment == .ergative

/-- Whether the language has accusative alignment in both NP and pronoun
    case-marking domains. -/
def AlignmentProfile.accusativeCase (p : AlignmentProfile) : Bool :=
  p.npAlignment == .accusative && p.pronAlignment == .accusative

-- ============================================================================
-- §3. Ditransitive alignment (Haspelmath 2005)
-- ============================================================================

/-- Ditransitive alignment classifies how R (recipient) and T (theme) are
    coded relative to monotransitive P (@cite{haspelmath-2005}). -/
inductive DitransitiveAlignment where
  /-- R = T = P: no distinction among non-agent arguments. -/
  | neutral
  /-- T = P ≠ R: R distinctly marked, T patterns with P. Indirective —
      analogous to accusative for monotransitives.
      E.g. English "give the book TO Mary". -/
  | indirective
  /-- R = P ≠ T: T distinctly marked, R patterns with P. Secundative —
      analogous to ergative. E.g. many Bantu applicatives. -/
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

-- ============================================================================
-- §4. WALS converters
-- ============================================================================

/-- WALS Ch 98A → `AlignmentType`. WALS distinguishes standard and marked-
    nominative accusative; we merge both. -/
def fromWALS98A : Datasets.WALS.F98A.NPCaseAlignment → AlignmentType
  | .neutral                => .neutral
  | .nominativeAccusative   => .accusative
  | .nominativeAccusative_3 => .accusative
  | .ergativeAbsolutive     => .ergative
  | .tripartite             => .tripartite
  | .activeInactive         => .active

/-- WALS Ch 99A → `AlignmentType`. WALS has a `.none` value (no pronouns or
    no case on pronouns); we map it to `.neutral`. -/
def fromWALS99A : Datasets.WALS.F99A.PronounCaseAlignment → AlignmentType
  | .neutral                => .neutral
  | .nominativeAccusative   => .accusative
  | .nominativeAccusative_3 => .accusative
  | .ergativeAbsolutive     => .ergative
  | .tripartite             => .tripartite
  | .activeInactive         => .active
  | .none                   => .neutral

/-- WALS Ch 100A → `Option AlignmentType`. The `.hierarchical` and `.split`
    values don't map cleanly to our 5-way enum and return `none`. -/
def fromWALS100A :
    Datasets.WALS.F100A.VerbalPersonAlignment → Option AlignmentType
  | .neutral      => some .neutral
  | .accusative   => some .accusative
  | .ergative     => some .ergative
  | .active       => some .active
  | .hierarchical => none
  | .split        => none

-- ============================================================================
-- Theory-neutral WALS distribution facts
-- ============================================================================

/-- Ch 98: neutral NP alignment is the modal pattern (no case marking). -/
theorem ch98_neutral_modal :
    let neutral := (ch98.filter (·.value == .neutral)).length
    neutral > (ch98.filter (·.value == .ergativeAbsolutive)).length ∧
    neutral > (ch98.filter (·.value == .tripartite)).length ∧
    neutral > (ch98.filter (·.value == .activeInactive)).length := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Ch 98: among case-marking systems, accusative outnumbers ergative. -/
theorem ch98_accusative_gt_ergative :
    (ch98.filter (·.value == .nominativeAccusative)).length +
    (ch98.filter (·.value == .nominativeAccusative_3)).length >
    (ch98.filter (·.value == .ergativeAbsolutive)).length := by
  native_decide

/-- Ch 99: accusative outnumbers ergative for pronoun case marking. -/
theorem ch99_accusative_gt_ergative :
    (ch99.filter (·.value == .nominativeAccusative)).length +
    (ch99.filter (·.value == .nominativeAccusative_3)).length >
    (ch99.filter (·.value == .ergativeAbsolutive)).length := by
  native_decide

/-- Ch 100: accusative is the dominant verbal-person-marking pattern. -/
theorem ch100_accusative_dominant :
    (ch100.filter (·.value == .accusative)).length >
    (ch100.filter (·.value == .ergative)).length ∧
    (ch100.filter (·.value == .accusative)).length >
    (ch100.filter (·.value == .active)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 98: tripartite NP alignment is extremely rare. -/
theorem ch98_tripartite_rare :
    (ch98.filter (·.value == .tripartite)).length * 30 < ch98.length := by
  native_decide

/-- Ch 99: tripartite pronoun alignment is extremely rare. -/
theorem ch99_tripartite_rare :
    (ch99.filter (·.value == .tripartite)).length * 30 < ch99.length := by
  native_decide

end Typology.Alignment
