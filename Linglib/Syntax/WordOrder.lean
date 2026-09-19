import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Data.WALS.Features.F81A
import Linglib.Data.WALS.Features.F82A
import Linglib.Data.WALS.Features.F83A

/-!
# Word-order typology

Framework-agnostic per-language word-order substrate (WALS chapters 81–83), under
a bare-root `WordOrder` namespace in `Features/`.

## Main definitions

* `BasicOrder`, `SVOrder`, `OVOrder` : the WALS Ch 81/82/83 constituent-order
  classifications ([dryer-2013-wals]).
* `WordOrderProfile` : the three classifications bundled per language, with the
  cross-field invariant `WordOrderProfile.IsConsistent` and the ISO-639-3 lookup
  constructor `WordOrderProfile.ofWALS`.
* `HeadDirection` : head-initial vs head-final, root-named, with `HeadDirection.swap` the
  opposite direction.
* `BasicOrder.IsSubjectBeforeObject` : the antecedent of [greenberg-1963] Universal 1.
* `OVOrder.headDirection` : the head direction of the verb phrase an object–verb order
  projects to, the sister of `Adposition.AdpositionOrder.headDirection`.

## Implementation notes

Each enum carries both `.noDominant` (a WALS-attested *finding* of no dominant order,
e.g. German Ch 81) and `.notInWALS` (uncoded in that chapter); filtering on
`≠ .noDominant` would otherwise misread uncoded languages as nondominant. The three
fields are bundled independently because WALS codes them independently (German is Ch 81
nondominant yet Ch 82 dominant), so `WordOrderProfile.IsConsistent` — not the type —
enforces their entailments. The substrate is neutral on primacy: [greenberg-1963] takes
`BasicOrder` as primary, [dryer-1992] the OV/VO cut.
-/

/-- Head direction of a construction: head-initial, the head preceding its complement as in
VO order and prepositions, or head-final. Root-named, consumed across Fragments, Studies and
Syntax. -/
inductive HeadDirection where
  | headInitial
  | headFinal
  deriving DecidableEq, Repr, Fintype

namespace HeadDirection

/-- The opposite direction. -/
def swap : HeadDirection → HeadDirection
  | headInitial => headFinal
  | headFinal => headInitial

@[simp] theorem swap_headInitial : headInitial.swap = headFinal := rfl

@[simp] theorem swap_headFinal : headFinal.swap = headInitial := rfl

@[simp] theorem swap_swap : ∀ d : HeadDirection, d.swap.swap = d := by decide

theorem swap_involutive : Function.Involutive swap := swap_swap

theorem swap_injective : Function.Injective swap := swap_involutive.injective

theorem swap_ne : ∀ d : HeadDirection, d.swap ≠ d := by decide

theorem swap_eq_iff_eq_swap {d e : HeadDirection} : d.swap = e ↔ d = e.swap :=
  swap_involutive.eq_iff

/-- A direction is a given one or its opposite. -/
theorem eq_or_eq_swap : ∀ d e : HeadDirection, e = d ∨ e = d.swap := by decide

end HeadDirection

namespace WordOrder

/-! ### Classifications -/

/-- WALS Ch 81: the six-way classification of basic constituent order. -/
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

/-- A language's WALS Ch 81/82/83 word-order classifications, bundled. -/
structure WordOrderProfile where
  basicOrder : BasicOrder
  svOrder : SVOrder
  ovOrder : OVOrder
  deriving Repr, DecidableEq

/-! ### WALS converters and ISO lookups -/

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

/-- Derive a `WordOrderProfile` by ISO-639-3 lookup against WALS Ch 81/82/83; each
    field falls back to `.notInWALS` when its chapter has no entry. The default
    Fragment backend — override per field where grammars disagree with or extend WALS. -/
def WordOrderProfile.ofWALS (iso : String) : WordOrderProfile :=
  { basicOrder := BasicOrder.ofWALS iso
    svOrder := SVOrder.ofWALS iso
    ovOrder := OVOrder.ofWALS iso }

/-! ### Projections and consistency -/

/-- The `SVOrder` a basic order entails (`none` if the basic order is uninformative):
    subject precedes verb in SOV/SVO/OSV, verb precedes subject in VSO/VOS/OVS. -/
def BasicOrder.entailedSV : BasicOrder → Option SVOrder
  | .sov | .svo | .osv => some .sv
  | .vso | .vos | .ovs => some .vs
  | .noDominant | .notInWALS => none

/-- The OVOrder a basic order entails. -/
def BasicOrder.entailedOV : BasicOrder → Option OVOrder
  | .sov | .ovs | .osv => some .ov
  | .svo | .vso | .vos => some .vo
  | .noDominant | .notInWALS => none

/-- A profile is consistent when `svOrder` and `ovOrder` each either match what
    `basicOrder` entails or are uninformative (`.noDominant` / `.notInWALS`) — the
    latter for languages coded in some WALS chapters but not others. -/
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

/-! ### Classification predicates

`abbrev`s (transparent, so `Decidable` resolves via `BasicOrder`'s `DecidableEq`). -/

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

/-! ### Head direction of the verb phrase -/

/-- The head direction of the verb phrase an object–verb order projects to: VO is head-initial
and OV head-final, and the uninformative orders (`.noDominant`, `.notInWALS`) project to
nothing. -/
def OVOrder.headDirection : OVOrder → Option HeadDirection
  | .vo => some .headInitial
  | .ov => some .headFinal
  | .noDominant | .notInWALS => none

end WordOrder
