import Linglib.Studies.Bondarenko2022
import Linglib.Fragments.Greek.StandardModern.Complementizers

/-!
# Angelopoulos 2026: On clausal complementation, once more
[angelopoulos-2026]

Greek *oti*- and *pu*-clauses present three puzzles (§1): near-
complementary distribution after verbs (*oti* with saying/belief, *pu*
with emotive factives, ex. 1); freedom as internal arguments and
derived subjects but a ban from external-argument position (§2.2); and
a novel stativity restriction on complement *pu*-clauses (§2.3).

The analysis reverses selection (§3.1): *oti* and *pu* bear an
uninterpretable [n]-feature checked by a light noun merged in their
specifier (partly adopting Arsenijević 2009; the paper is neutral on
the categorial status of *oti* and *pu*, fn. 3). The noun must
incorporate into a lexical verbal head — possible from complement
position, impossible from Spec,vP (nearest head T) or under P — which
derives the argument asymmetry and the P-ban (§3.1 ex. 27–32). The
*oti* ~ *pu* distribution follows from the content/situation dichotomy
(§3.2, adopting [bondarenko-2022]); the stativity restriction from
aspectual-head selection (§4.1: vState selects both otiP and puP,
vEvent only otiP). §7.1 extends the adjunct-selection account to
Uyghur *dep* (= *de* 'say' + converb *-ip*, per Major 2024) — the
structural parallel of Buryat *gɘ-žɘ*.

§7.3 departs from [bondarenko-2022]'s transparent syntax–semantics
mapping: bare *oti*-clauses are merged in COMPLEMENT position (the §2
argumenthood diagnostics: clitic doubling, passivization, derived
subjects) while composing via Predicate Modification (the explanans
reading, [elliott-2020-embedding]) — the same syntactic position
yields either composition mode.

## Main declarations

- `bearsN` — the §3.1 [n]-feature datum over the fragment entries
- `NounHost`, `ClausePosition`, `licensedIn` — the incorporation
  mechanism and the derived argument-position asymmetry
- `selectsClause`, `pu_requires_stative` — the §4.1 stativity locus
- `clauseSort` — *oti* = content, *pu* = situation, consuming
  `Bondarenko2022.NominalSort` (§3.2 ex. 33–34)
- `bareOtiAttested`, `transparency_conflates_axes` — the §7.3
  counterclaim against `Bondarenko2022.transparentSSMapping`
-/

namespace Angelopoulos2026

open Greek.StandardModern.Complementizers
open Bondarenko2022 (NominalSort)

/-! ### Reversed selection: the [n]-feature (§3.1) -/

/-- *oti* and *pu* bear an uninterpretable [n]-feature checked by a
light noun merged in their specifier (§3.1); *na* does not (its
licensing is mood-driven). Paper-specific datum projected over the
fragment entries; the paper is neutral on the category of *oti* and
*pu* (fn. 3). -/
def bearsN (c : Complementizer) : Prop := c = oti ∨ c = pu

instance : DecidablePred bearsN := fun c => by
  unfold bearsN; infer_instance

/-! ### Incorporation licensing and the argument asymmetry (§3.1) -/

/-- Heads adjacent to a clause's light noun. Only a lexical verbal
head licenses noun incorporation ([hale-keyser-1993]); functional T
and P do not (§3.1 ex. 29–32). -/
inductive NounHost where
  | vLex
  | t
  | p
  deriving DecidableEq, Fintype, Repr

/-- Whether a host licenses light-noun incorporation. -/
def NounHost.licenses : NounHost → Prop
  | .vLex => True
  | .t    => False
  | .p    => False

/-- Positions a bare oti/pu-clause can occupy, each with the nearest
potential incorporation host: internal arguments sit under an
aspectual v; incorporation precedes movement for derived subjects;
the nearest head above Spec,vP is T; P cannot host (§3.1 ex. 27–32). -/
inductive ClausePosition where
  | internalArgument
  | derivedSubject
  | externalArgument
  | pComplement
  deriving DecidableEq, Fintype, Repr

/-- The nearest potential incorporation host from each position. -/
def ClausePosition.nearestHost : ClausePosition → NounHost
  | .internalArgument => .vLex
  | .derivedSubject   => .vLex
  | .externalArgument => .t
  | .pComplement      => .p

/-- A bare oti/pu-clause is licensed in a position iff the nearest
host licenses light-noun incorporation — the paper's derivation of
the distribution, not a stipulated table. -/
def licensedIn (pos : ClausePosition) : Prop := pos.nearestHost.licenses

/-- Internal arguments and derived subjects are licensed (§2.1–2.2). -/
theorem internal_and_derived_subject_licensed :
    licensedIn .internalArgument ∧ licensedIn .derivedSubject :=
  ⟨trivial, trivial⟩

/-- The external-argument ban (§2.2): T cannot host incorporation. -/
theorem external_argument_banned : ¬ licensedIn .externalArgument :=
  fun h => h

/-- Bare clauses are excluded after P (ex. 31c, 32c). -/
theorem p_complement_banned : ¬ licensedIn .pComplement :=
  fun h => h

/-! ### The stativity locus (§4.1) -/

/-- Aspectual heads introducing internal arguments (§4.1, following
Borer and Merchant as cited there). -/
inductive AspectualHead where
  | vState
  | vEvent
  deriving DecidableEq, Fintype, Repr

/-- §4.1: vState selects both otiP and puP as its complement; vEvent
selects only otiP. -/
def selectsClause : AspectualHead → Complementizer → Prop
  | .vState, c => c = oti ∨ c = pu
  | .vEvent, c => c = oti

/-- The stativity restriction (§2.3), derived: a *pu*-complement
forces the stative aspectual head. -/
theorem pu_requires_stative (h : AspectualHead)
    (hp : selectsClause h pu) : h = .vState := by
  cases h
  · rfl
  · exact absurd (show pu = oti from hp) (by decide)

/-- The verb-level reflex over the fragment sample: the *pu*-only
matrix verbs (ex. 1b, 13–14, 20) are all stative. -/
theorem pu_only_verbs_stative :
    ∀ v ∈ [metaniono, areso, xerome], v.vendlerClass = some .state := by
  decide

/-! ### Content vs situation (§3.2) -/

/-- The sort of clause each complementizer introduces — *oti* content,
*pu* situation — which must match the incorporating noun's sort
(§3.2). The sorts and their diagnostics ('true'/'mistaken' vs
'happen', ex. 33–34) are [bondarenko-2022]'s (`Bondarenko2022.NominalSort`,
§2.2.3); *na* is outside the dichotomy. -/
def clauseSort (c : Complementizer) : Option NominalSort :=
  if c = oti then some .content
  else if c = pu then some .situation
  else none

/-- The assigned sorts pass the §3.2 diagnostics: *oti*'s sort is
truth-evaluable, *pu*'s occurrence-compatible (ex. 33–34, matching
[bondarenko-2022] §2.2.3). -/
theorem clauseSort_matches_diagnostics :
    clauseSort oti = some .content ∧
    NominalSort.truthEvaluable .content ∧
    clauseSort pu = some .situation ∧
    NominalSort.occurrenceCompatible .situation :=
  ⟨by decide, trivial, by decide, trivial⟩

/-! ### Against the transparent syntax–semantics mapping (§7.3) -/

/-- Syntactic position of an embedded clause — one of the two axes
[bondarenko-2022]'s `ClauseStructurePath` conflates. -/
inductive SynPosition where
  | complement
  | adjunct
  deriving DecidableEq, Repr

/-- Composition mode — the other axis. -/
inductive CompMode where
  | pm
  | fa
  deriving DecidableEq, Repr

/-- The paper's claim for bare *oti*-clauses (§2 diagnostics + §7.3):
complement position composing via PM is attested (the explanans
reading); FA requires the nominalizing D (§7.3 ex. 57), so bare
clauses never compose via FA from either position. -/
def bareOtiAttested : SynPosition → CompMode → Prop
  | .complement, .pm => True
  | .complement, .fa => False
  | .adjunct,    .pm => True
  | .adjunct,    .fa => False

/-- [bondarenko-2022]'s transparent mapping restated on the split
axes: a bare clause composing via PM must be a syntactic adjunct
(the composition path is reflected in syntax). -/
def transparentBare : SynPosition → CompMode → Prop
  | .adjunct, .pm => True
  | _, _ => False

/-- The §7.3 divergence: bare *oti*-clauses occupy complement position
while composing via PM — attested here, excluded by the transparent
mapping. Conditional on the paper's premises: the clauses are BARE
(no covert nominal shell — the analysis rejects Arsenijević's DP
layer and Faure's case-less-DP treatment, §3.1) and are internal
ARGUMENTS (clitic doubling, passivization, derived subjects,
§2.1–2.2). [bondarenko-2022] can deny either premise. -/
theorem diverges_from_transparent_mapping :
    bareOtiAttested .complement .pm ∧
    ¬ transparentBare .complement .pm :=
  ⟨trivial, fun h => h⟩

/-- Against `Bondarenko2022.transparentSSMapping` directly: Bondarenko
predicts the (bare, argument) cell empty
(`Bondarenko2022.bare_argument_predicted_impossible`), identifying
argument position with the FA path; Greek realizes syntactic
argumenthood for bare clauses WITHOUT FA — the identification of the
two axes is what fails. -/
theorem transparency_conflates_axes :
    ¬ Bondarenko2022.transparentSSMapping .bareArgument ∧
    bareOtiAttested .complement .pm :=
  ⟨Bondarenko2022.bare_argument_predicted_impossible, trivial⟩

end Angelopoulos2026
