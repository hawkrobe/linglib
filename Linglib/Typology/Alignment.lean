import Linglib.Features.Case.Basic
import Linglib.Syntax.Case.Alignment

/-!
# Typology.Alignment
[comrie-1978] [comrie-2013] [dixon-1994] [dixon-1972]
[dryer-haspelmath-2013] [haspelmath-2005] [haspelmath-2021]
[wals-2013]

Per-language typological substrate for morphosyntactic alignment, covering
how languages mark the core grammatical relations S (sole argument of
intransitive), A (agent of transitive), and P (patient of transitive).
Three WALS chapters by [comrie-2013]:

- **Ch 98**: alignment of case marking of full noun phrases.
- **Ch 99**: alignment of case marking of pronouns.
- **Ch 100**: alignment of verbal person marking.

Plus ditransitive alignment from [haspelmath-2005].

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
`Studies/Dixon1994.lean`.
[comrie-1989]'s typology generalisations are in
`Studies/Comrie1989.lean`.
-/

set_option autoImplicit false

namespace Typology.Alignment

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

-- `AlignmentProfile` (the bundled per-language record) now lives with its data
-- and analysis in `Studies/Dixon1994.lean`; the theory-neutral WALS alignment
-- distribution facts now live with the WALS data in
-- `Data/WALS/AlignmentDistribution.lean`.

/-! ### Split Ergativity [blake-1994] [dixon-1994]

A `SplitErgativity Factor` is parameterised by the conditioning factor
(aspect, person, animacy, …); `alignment` projects to either the ergative
or accusative family. The Hindi aspect-conditioned split (perfective ⇒
ergative; imperfective ⇒ accusative) is the canonical worked example. -/

open Features (AlignmentFamily)

/-- A split-ergative system ([blake-1994], [dixon-1994]):
    alignment varies by some conditioning factor. -/
structure SplitErgativity (Factor : Type) where
  ergCondition : Factor → Bool

def SplitErgativity.alignment {Factor : Type} (split : SplitErgativity Factor)
    (f : Factor) : AlignmentFamily :=
  if split.ergCondition f then .ergative else .accusative

inductive Aspect where
  | perfective
  | imperfective
  deriving DecidableEq, Repr

def hindiSplit : SplitErgativity Aspect :=
  { ergCondition := fun a => a == .perfective }

theorem hindi_perfective_erg :
    hindiSplit.alignment .perfective = .ergative := rfl

theorem hindi_imperfective_acc :
    hindiSplit.alignment .imperfective = .accusative := rfl

-- ============================================================================
-- § Grounding `AlignmentType` in the partition object (retirement seam)
-- ============================================================================

/-! `AlignmentType` is a hand-maintained enum in this `Typology` drawer; its
content is the partition of the core roles {S, A, P} — the kernel
`Setoid.ker` of a case-assignment, formalized as the partition object in
`Syntax/Case/Alignment.lean`. Grounding the enum in that object (below) is a
first step toward retiring this enum in favour of the principled partition
layer. -/

/-- `AlignmentType` as the core-role signature `(S≈A, S≈P, A≈P)` of the
    partition it denotes (`Alignment.coreSig` vocabulary). `active` is **not** a
    partition of {S,A,P} — it splits S into agent-like/patient-like — so it has
    no signature (`none`); that is the principled reason it sits apart from the
    four genuine partitions. -/
def AlignmentType.partitionSig : AlignmentType → Option (Bool × Bool × Bool)
  | .neutral    => some (true, true, true)
  | .accusative => some (true, false, false)
  | .ergative   => some (false, true, false)
  | .tripartite => some (false, false, false)
  | .active     => none

/-- The four partition-denoting `AlignmentType`s agree with the partitions the
    corresponding `Alignment.X.assignCase` functions induce — grounding the enum
    in the kernel object rather than maintaining it independently. -/
theorem partitionSig_grounded :
    AlignmentType.accusative.partitionSig
        = some (_root_.Alignment.coreSig _root_.Alignment.nominativeAccusative.assignCase) ∧
    AlignmentType.ergative.partitionSig
        = some (_root_.Alignment.coreSig _root_.Alignment.ergative.assignCase) ∧
    AlignmentType.tripartite.partitionSig
        = some (_root_.Alignment.coreSig _root_.Alignment.tripartite.assignCase) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The enum denotes only four of the five partitions of {S, A, P}: it is missing
    horizontal `{A,P}|{S}` (`Alignment.horizontal_unrealized`), and its fifth
    value `active` is split-S, not a partition (`none`). -/
theorem alignmentType_misses_horizontal_and_active_is_split :
    AlignmentType.active.partitionSig = none ∧
    (∀ a : AlignmentType, a.partitionSig ≠ some (false, false, true)) := by
  refine ⟨rfl, fun a => ?_⟩
  cases a <;> decide

end Typology.Alignment
