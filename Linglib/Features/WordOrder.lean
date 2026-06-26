import Linglib.Data.WALS.Features.F81A
import Linglib.Data.WALS.Features.F82A
import Linglib.Data.WALS.Features.F83A

/-!
# Word-order typology: per-language profile substrate
[dryer-2013-wals] [greenberg-1963] [dryer-1992]

Framework-agnostic substrate for storing per-language word-order data
(WALS Chs 81–83), under a bare-root `WordOrder` namespace in `Features/`
(graduated from the dissolving `Typology/`), like `Features/Case`.

The key record is `WordOrderProfile`, a flat bundle of three orthogonal WALS
classifications constrained by the cross-field `WordOrderProfile.IsConsistent`
invariant; `WordOrderProfile.ofWALS` derives it from WALS by ISO lookup.

## Epistemic distinction: `noDominant` vs `notInWALS`

The three enums each carry both `.noDominant` (WALS-attested
nondominance, e.g., German Ch 81 — *itself a finding* about the
language) and `.notInWALS` (the language is not coded in this WALS
chapter). A consumer that filtered on `≠ .noDominant` would otherwise
silently include unencoded languages as "genuinely nondominant".

## Independence assumption and `IsConsistent`

The three fields are bundled *independently* even though they are
not logically independent: SOV basicOrder entails sv + ov projections,
etc. WALS codes them independently for empirical-coverage reasons (a
language can be Ch 81 nondominant but Ch 82 dominant — German is
exactly this), so the substrate mirrors WALS rather than collapsing
fields. The `WordOrderProfile.IsConsistent` predicate rules out
internally contradictory combinations.

## Greenbergian vs Dryerian primacy

The substrate is *neutral* on which classification is theoretically
primary. [greenberg-1963] treated `BasicOrder` as primary;
[dryer-1992] explicitly demoted SOV/SVO/VSO in favour of OV/VO
(Branching Direction Theory). Consumers downstream choose which
fields to read.

## Scope

Covers WALS Chs 81–83 (clausal word-order features). Sibling
substrates carry adjacent typology: `Typology/Adposition.lean` for
Ch 85; nominal-internal and correlation-pair profiles can be added
when consumers demand them. Cross-tabulation primitives for
correlation tables (Gibson 2025-style 2×2 head-direction tables) live
in their consuming Studies file (`Studies/
Gibson2025.lean`) until a second framework consumer materialises.
-/

/-- Head direction of a syntactic construction: head-initial (VO, prepositions,
head-initial FocP, …) vs head-final. Used for word-order typology and constraints
like FOFC. Root-named (consumed across Fragments, Studies, Syntax). -/
inductive HeadDirection where
  | headInitial
  | headFinal
  deriving Repr, DecidableEq

namespace WordOrder

-- ============================================================================
-- Enums
-- ============================================================================

/-- WALS Ch 81: six-way classification of basic constituent order.
    `noDominant` is WALS's "lacking a dominant word order" code (a
    substantive finding about the language); `notInWALS` is absence
    from the chapter. The two are epistemically different and must
    not be conflated. -/
inductive BasicOrder where
  | sov | svo | vso | vos | ovs | osv
  /-- WALS-attested "lacking a dominant word order" (Ch 81). -/
  | noDominant
  /-- Language not coded in WALS Ch 81. -/
  | notInWALS
  deriving DecidableEq, Repr

/-- WALS Ch 82: binary classification of subject–verb order. -/
inductive SVOrder where
  | sv | vs
  /-- WALS-attested "lacking a dominant order" (Ch 82). -/
  | noDominant
  /-- Language not coded in WALS Ch 82. -/
  | notInWALS
  deriving DecidableEq, Repr

/-- WALS Ch 83: binary classification of object–verb order. -/
inductive OVOrder where
  | ov | vo
  /-- WALS-attested "lacking a dominant order" (Ch 83). -/
  | noDominant
  /-- Language not coded in WALS Ch 83. -/
  | notInWALS
  deriving DecidableEq, Repr

/-- A bundle of WALS-style word-order classifications for a single
    language. The three fields are bundled independently because
    WALS codes them independently; the `IsConsistent` predicate
    captures the logical entailments between them. -/
structure WordOrderProfile where
  basicOrder : BasicOrder
  svOrder : SVOrder
  ovOrder : OVOrder
  deriving Repr, DecidableEq

-- ============================================================================
-- WALS converters and ISO lookups
-- ============================================================================

namespace BasicOrder

/-- Convert WALS F81A's `BasicWordOrder` value to a `BasicOrder`. -/
def ofWALS81A : Data.WALS.F81A.BasicWordOrder → BasicOrder
  | .sov => .sov
  | .svo => .svo
  | .vso => .vso
  | .vos => .vos
  | .ovs => .ovs
  | .osv => .osv
  | .noDominantOrder => .noDominant

/-- Look up Ch 81 basic order for an ISO 639-3 code. Returns
    `.notInWALS` when the language is absent from the chapter. -/
def ofWALS (iso : String) : BasicOrder :=
  match Data.WALS.Datapoint.lookupISO Data.WALS.F81A.allData iso with
  | some d => ofWALS81A d.value
  | none => .notInWALS

end BasicOrder

namespace SVOrder

/-- Convert WALS F82A's `SubjectVerbOrder` to an `SVOrder`. -/
def ofWALS82A : Data.WALS.F82A.SubjectVerbOrder → SVOrder
  | .sv => .sv
  | .vs => .vs
  | .noDominantOrder => .noDominant

/-- Look up Ch 82 subject–verb order for an ISO 639-3 code. Returns
    `.notInWALS` when the language is absent from the chapter. -/
def ofWALS (iso : String) : SVOrder :=
  match Data.WALS.Datapoint.lookupISO Data.WALS.F82A.allData iso with
  | some d => ofWALS82A d.value
  | none => .notInWALS

end SVOrder

namespace OVOrder

/-- Convert WALS F83A's `ObjectVerbOrder` to an `OVOrder`. -/
def ofWALS83A : Data.WALS.F83A.ObjectVerbOrder → OVOrder
  | .ov => .ov
  | .vo => .vo
  | .noDominantOrder => .noDominant

/-- Look up Ch 83 object–verb order for an ISO 639-3 code. Returns
    `.notInWALS` when the language is absent from the chapter. -/
def ofWALS (iso : String) : OVOrder :=
  match Data.WALS.Datapoint.lookupISO Data.WALS.F83A.allData iso with
  | some d => ofWALS83A d.value
  | none => .notInWALS

end OVOrder

/-- Construct a `WordOrderProfile` for a language by ISO 639-3 lookup
    against WALS chapters 81/82/83. Each field independently falls
    back to `.notInWALS` if its WALS chapter has no entry. Use this as
    the default backend in Fragment files; override per-field when
    grammar-grounded sources disagree with WALS or fill its gaps. -/
def WordOrderProfile.ofWALS (iso : String) : WordOrderProfile :=
  { basicOrder := BasicOrder.ofWALS iso
    svOrder := SVOrder.ofWALS iso
    ovOrder := OVOrder.ofWALS iso }

-- ============================================================================
-- BasicOrder → SVOrder/OVOrder projections (and consistency)
-- ============================================================================

/-- The SVOrder a basic order entails (`none` if basic order is
    itself uninformative). Subject precedes verb in SOV, SVO, OSV
    (V is final or last in those orders); verb precedes subject in
    VSO, VOS, OVS. -/
def BasicOrder.entailedSV : BasicOrder → Option SVOrder
  | .sov | .svo | .osv => some .sv
  | .vso | .vos | .ovs => some .vs
  | .noDominant | .notInWALS => none

/-- The OVOrder a basic order entails. -/
def BasicOrder.entailedOV : BasicOrder → Option OVOrder
  | .sov | .ovs | .osv => some .ov
  | .svo | .vso | .vos => some .vo
  | .noDominant | .notInWALS => none

/-- A profile is consistent if its `svOrder` and `ovOrder` either
    match what `basicOrder` entails, or are themselves uninformative
    (`.noDominant` / `.notInWALS`). The latter accommodates languages
    coded in some WALS chapters but not others (e.g., German has
    nondominant Ch 81 but dominant Ch 82). When `basicOrder` itself
    is uninformative, no constraint is imposed on the projections. -/
def WordOrderProfile.IsConsistent (p : WordOrderProfile) : Prop :=
  (match p.basicOrder.entailedSV with
   | none => True
   | some entailed =>
     p.svOrder = entailed ∨ p.svOrder = .noDominant ∨ p.svOrder = .notInWALS) ∧
  (match p.basicOrder.entailedOV with
   | none => True
   | some entailed =>
     p.ovOrder = entailed ∨ p.ovOrder = .noDominant ∨ p.ovOrder = .notInWALS)

instance (p : WordOrderProfile) : Decidable p.IsConsistent := by
  unfold WordOrderProfile.IsConsistent
  cases p.basicOrder.entailedSV <;> cases p.basicOrder.entailedOV <;>
    infer_instance

-- ============================================================================
-- Classification predicates over BasicOrder
-- ============================================================================
-- These are abbrevs (transparent) so `Decidable` resolves automatically
-- via `BasicOrder`'s `DecidableEq`. Add new predicates here when a
-- second consumer materialises (rather than letting individual studies
-- re-stipulate them).

namespace BasicOrder

/-- `b` is SOV. -/
abbrev IsSOV (b : BasicOrder) : Prop := b = .sov

/-- `b` is SVO. -/
abbrev IsSVO (b : BasicOrder) : Prop := b = .svo

/-- `b` is VSO. -/
abbrev IsVSO (b : BasicOrder) : Prop := b = .vso

/-- `b` has Subject before Object: SOV, SVO, or VSO.
    [greenberg-1963] Universal 1's antecedent. -/
abbrev IsSubjectBeforeObject (b : BasicOrder) : Prop :=
  b = .sov ∨ b = .svo ∨ b = .vso

/-- `b` has Object before Subject: VOS, OVS, or OSV.
    [greenberg-1963] Universal 1's negative class. -/
abbrev IsObjectBeforeSubject (b : BasicOrder) : Prop :=
  b = .vos ∨ b = .ovs ∨ b = .osv

end BasicOrder

namespace OVOrder

/-- `o` is OV (object precedes verb). [dryer-1992]'s primary
    typological classification under Branching Direction Theory. -/
abbrev IsOV (o : OVOrder) : Prop := o = .ov

/-- `o` is VO (verb precedes object). -/
abbrev IsVO (o : OVOrder) : Prop := o = .vo

end OVOrder

-- ============================================================================
-- Verb position (theory-neutral OVOrder projection)
-- ============================================================================

/-- Verb position in the clause as derived from object–verb order.
    Theory-neutral: VO ⇒ post-verbal object (verb precedes
    complement), OV ⇒ pre-verbal object (verb follows complement). -/
inductive VerbPosition where
  /-- Verb precedes complement (head-initial VP). -/
  | postverbal
  /-- Verb follows complement (head-final VP). -/
  | preverbal
  deriving DecidableEq, Repr

/-- Project an `OVOrder` to a `VerbPosition`. Returns `none` for
    uninformative orders (`.noDominant`, `.notInWALS`). -/
def OVOrder.verbPosition : OVOrder → Option VerbPosition
  | .vo => some .postverbal
  | .ov => some .preverbal
  | .noDominant | .notInWALS => none

end WordOrder
