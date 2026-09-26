module

public import Linglib.Syntax.Anaphora.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Ellipsis

This file defines Merchant's [E] feature and the deletion domain it determines. An [E] feature on a
functional head instructs the phonology not to pronounce the head's complement, under the
presupposition that the complement is given, and each kind of ellipsis is an [E] feature at a
position of the spine: VP-ellipsis puts it on Voice and deletes vP, sluicing puts it on C and
deletes TP, and v-stranding VP-ellipsis puts it on v and deletes VP alone. A position is external to
an ellipsis when it lies outside the deletion domain; it then survives deletion and is invisible to
the identity condition, so a mismatch in a feature its head bears is tolerated. Lowering [E] shrinks
the domain, so whatever a higher ellipsis tolerates a lower one tolerates too, which is Sailor's
generalization. A deletion spine is any preorder of positions with a deletion-domain relation that
is irreflexive and monotone in the position of [E]; the clausal spine and the nominal spine of
[benz-salzmann-2025] are instances. [E]-deletion is one model of the depth of [hankamer-sag-1976]:
the null sites of a spine are the complements [E] silences and the null pro-forms, and they meet the
conditions of `Anaphor.DepthModel`.

## Main definitions

* `Minimalist.DeletionSpine`: positions with a deletion-domain relation, and
  `Minimalist.DeletionSpine.External`, a position outside the domain of [E] at another.
* `Minimalist.SpinePosition`: the positions of the clausal spine, V, the VP-adjunction site, v,
  Voice, T and C, linearly ordered by height.
* `Minimalist.NominalSpinePosition`: the positions of the nominal spine, N, the site of
  prenominal modifiers, n, Num and D.
* `Minimalist.Ellipsis`: an ellipsis, identified by the position of its [E] feature on a spine,
  with `Minimalist.Ellipsis.sluicing`, `Minimalist.Ellipsis.vpEllipsis`,
  `Minimalist.Ellipsis.vStrandingVPE` and `Minimalist.Ellipsis.nPEllipsis`.
* `Minimalist.Ellipsis.Mismatch`: the dimensions in which an elided phrase may differ from its
  antecedent, each regulated by a head of the spine.
* `Minimalist.AgainReading`: the two readings of *again* and their adjunction sites.
* `Minimalist.NullSite`: a null site of a spine, an [E] deletion domain or a null pro-form, with
  its `Anaphor.DepthModel` instance.

## Main results

* `Minimalist.DeletionSpine.external_self`: the [E]-bearing head survives its own ellipsis, the
  core of X-stranding.
* `Minimalist.Ellipsis.Tolerates.of_le`: Sailor's generalization, a mismatch tolerated by an
  ellipsis is tolerated by every lower one.
* `Minimalist.NullSite.not_silences_ePosition`: the head bearing [E] lies outside the site it
  silences.

## Implementation notes

The VP-adjunction site is a position of its own, below v but outside v's complement, so that
restitutive *again* and manner roots survive v-stranding VP-ellipsis while V does not; it is what
separates the domain of [E] on v from that of [E] on Voice. A null site built from [E] carries a
position of its deletion domain, since a head at the bottom of a spine has no complement on it to
silence; that witness is what the surface condition of `Anaphor.DepthModel` asks for.

## References

* [merchant-2001]
* [merchant-2013]
* [kalyakin-2026]
* [sailor-2014]
* [liptak-saab-2014]
* [benz-salzmann-2025]
* [hankamer-sag-1976]
-/

@[expose] public section

namespace Minimalist

/-- A deletion spine is a preorder of positions with a deletion-domain relation. `InDomain d p`
holds when `d` lies in the complement of `p`, which an [E] feature on `p` deletes; no position is
in its own domain, and raising [E] never shrinks the domain. -/
class DeletionSpine (α : Type*) [Preorder α] where
  /-- `d` lies in the deletion domain of [E] at `p`. -/
  InDomain : α → α → Prop
  not_inDomain_self : ∀ p, ¬ InDomain p p
  inDomain_mono : ∀ d, Monotone (InDomain d)

export DeletionSpine (InDomain not_inDomain_self inDomain_mono)

namespace DeletionSpine

variable {α : Type*} [Preorder α] [DeletionSpine α] {d p q : α}

/-- `d` is external to ellipsis at `p` when it lies outside the deletion domain, so that it
survives deletion and is invisible to the identity condition. -/
def External (d p : α) : Prop := ¬ InDomain d p

instance [DecidableRel (InDomain (α := α))] (d p : α) : Decidable (External d p) :=
  inferInstanceAs (Decidable (¬ _))

/-- The [E]-bearing head survives its own ellipsis, which is the core of X-stranding: a head that
has moved to the [E]-bearing position is pronounced while its base position is deleted. -/
theorem external_self (p : α) : External p p := not_inDomain_self p

/-- Sailor's generalization. What is external at an [E] position is external at every lower
one. -/
theorem External.of_le (h : External d p) (hq : q ≤ p) : External d q :=
  fun hd ↦ h (inDomain_mono d hq hd)

end DeletionSpine

export DeletionSpine (External external_self)

/-! ### The clausal spine -/

/-- The positions of the clausal spine that ellipsis distinguishes, lowest first. They are the
lexical verb, the VP-adjunction site of restitutive *again* and manner roots, v, Voice, T and C. -/
inductive SpinePosition
  | V
  | vpAdjunct
  | v
  | Voice
  | T
  | C
  deriving DecidableEq, Repr

namespace SpinePosition

/-- Height in the spine. -/
def rank : SpinePosition → ℕ
  | .V => 0
  | .vpAdjunct => 1
  | .v => 2
  | .Voice => 3
  | .T => 4
  | .C => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

instance : LinearOrder SpinePosition := .lift' rank rank_injective

/-- `d` lies in the complement of `p` when it is below `p`, except that the VP-adjunction site is
outside the complement of v: adjuncts to VP belong to the VP projection but are not selected by
v, and are deleted only by an [E] above v. -/
def InDomain (d p : SpinePosition) : Prop := d < p ∧ (d = .vpAdjunct → .v < p)

instance : DecidableRel InDomain := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : DeletionSpine SpinePosition where
  InDomain := InDomain
  not_inDomain_self p h := lt_irrefl p h.1
  inDomain_mono _ _ _ h := fun ⟨hd, ha⟩ ↦ ⟨hd.trans_le h, fun e ↦ (ha e).trans_le h⟩

instance : DecidableRel (DeletionSpine.InDomain (α := SpinePosition)) :=
  inferInstanceAs (DecidableRel InDomain)

end SpinePosition

/-! ### The nominal spine -/

/-- The positions of the nominal spine, lowest first: the noun with its postnominal dependents,
the site of prenominal modifiers, the categorizer n, Num and D. The modifier site is inside nP but
outside n's complement, the nominal counterpart of the clausal VP-adjunction site. -/
inductive NominalSpinePosition
  | N
  | npAdjunct
  | n
  | Num
  | D
  deriving DecidableEq, Repr

namespace NominalSpinePosition

/-- Height in the spine. -/
def rank : NominalSpinePosition → ℕ
  | .N => 0
  | .npAdjunct => 1
  | .n => 2
  | .Num => 3
  | .D => 4

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

instance : LinearOrder NominalSpinePosition := .lift' rank rank_injective

/-- `d` lies in the complement of `p` when it is below `p`, except that prenominal modifiers are
not in n's complement, though they are in Num's. -/
def InDomain (d p : NominalSpinePosition) : Prop := d < p ∧ (d = .npAdjunct → .n < p)

instance : DecidableRel InDomain := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : DeletionSpine NominalSpinePosition where
  InDomain := InDomain
  not_inDomain_self p h := lt_irrefl p h.1
  inDomain_mono _ _ _ h := fun ⟨hd, ha⟩ ↦ ⟨hd.trans_le h, fun e ↦ (ha e).trans_le h⟩

instance : DecidableRel (DeletionSpine.InDomain (α := NominalSpinePosition)) :=
  inferInstanceAs (DecidableRel InDomain)

end NominalSpinePosition

/-! ### Ellipsis types -/

/-- An ellipsis is identified by the position of its [E] feature on a spine; its deletion domain
is that head's complement. -/
structure Ellipsis (α : Type*) where
  /-- The head carrying [E]. -/
  ePosition : α
  deriving DecidableEq, Repr

namespace Ellipsis

section Spine

variable {α : Type*} [Preorder α] [DeletionSpine α] {e e' : Ellipsis α} {d : α}

/-- `e.Deletes d` when the position `d` lies in the deletion domain of `e`. -/
def Deletes (e : Ellipsis α) (d : α) : Prop := InDomain d e.ePosition

instance [DecidableRel (InDomain (α := α))] : Decidable (e.Deletes d) :=
  inferInstanceAs (Decidable (InDomain _ _))

/-- `e.Spares d` when the position `d` is external to `e` and survives it. -/
def Spares (e : Ellipsis α) (d : α) : Prop := External d e.ePosition

instance [DecidableRel (InDomain (α := α))] : Decidable (e.Spares d) :=
  inferInstanceAs (Decidable (External _ _))

theorem spares_ePosition (e : Ellipsis α) : e.Spares e.ePosition := external_self _

theorem Spares.of_le (h : e.Spares d) (hle : e'.ePosition ≤ e.ePosition) : e'.Spares d :=
  DeletionSpine.External.of_le h hle

end Spine

/-- Sluicing puts [E] on C and deletes TP. -/
def sluicing : Ellipsis SpinePosition := ⟨.C⟩

/-- VP-ellipsis puts [E] on Voice and deletes vP, so that Voice is external to the ellipsis. -/
def vpEllipsis : Ellipsis SpinePosition := ⟨.Voice⟩

/-- v-stranding VP-ellipsis puts [E] on v and deletes VP alone, stranding the light verb. -/
def vStrandingVPE : Ellipsis SpinePosition := ⟨.v⟩

/-- nP-ellipsis puts [E] on Num and deletes nP, the configuration [liptak-saab-2014] find in
Spanish: the noun, the categorizer and prenominal modifiers are all deleted. -/
def nPEllipsis : Ellipsis NominalSpinePosition := ⟨.Num⟩

/-! ### Mismatches -/

/-- A dimension in which an elided phrase may differ from its antecedent, each regulated by a head
of the spine: voice by Voice, the causative, dative, prepositional and middle alternations by
flavours of v, and the lexical verb by V. -/
inductive Mismatch
  | voice
  | transitivity
  | dative
  | prepositional
  | middle
  | lexical
  deriving DecidableEq, Repr

/-- The head that regulates each dimension. -/
def Mismatch.head : Mismatch → SpinePosition
  | .voice => .Voice
  | .transitivity | .dative | .prepositional | .middle => .v
  | .lexical => .V

variable {e e' : Ellipsis SpinePosition}

/-- `e.Tolerates m` when the head regulating `m` is external to `e`, so that a mismatch in `m`
is invisible to the identity condition. -/
def Tolerates (e : Ellipsis SpinePosition) (m : Mismatch) : Prop := e.Spares m.head

instance (e : Ellipsis SpinePosition) (m : Mismatch) : Decidable (e.Tolerates m) :=
  inferInstanceAs (Decidable (e.Spares _))

/-- Sailor's generalization. A mismatch tolerated by an ellipsis is tolerated by every ellipsis
whose [E] sits lower. -/
theorem Tolerates.of_le {m : Mismatch} (h : e.Tolerates m) (hle : e'.ePosition ≤ e.ePosition) :
    e'.Tolerates m :=
  Spares.of_le h hle

end Ellipsis

/-! ### Null sites and depth -/

/-- A null site of a spine: the complement an [E]-bearing head leaves unpronounced, which must
contain some position, or a null pro-form, a head without a complement, such as *pro* or an empty
noun. -/
inductive NullSite (α : Type*) [Preorder α] [DeletionSpine α] where
  | elided (e : Ellipsis α) (h : ∃ d, e.Deletes d)
  | proform (p : α)

namespace NullSite

variable {α : Type*} [Preorder α] [DeletionSpine α]

/-- [E]-deletion yields a surface anaphor, and a null pro-form a deep one. -/
def depth : NullSite α → Anaphor.Depth
  | .elided .. => .surface
  | .proform _ => .deep

/-- The positions a null site leaves unpronounced: the deletion domain of an [E]-bearing head, and
none for a pro-form. -/
def Silences : NullSite α → α → Prop
  | .elided e _, d => e.Deletes d
  | .proform _, _ => False

/-- [E]-deletion realizes Hankamer and Sag's depth: an [E] site silences its complement, and a
null pro-form silences nothing. -/
instance : Anaphor.DepthModel (NullSite α) α where
  depth := depth
  Silences := Silences
  exists_silences_of_surface
    | .elided _ h, _ => h
    | .proform _, h => nomatch h
  not_silences_of_deep
    | .elided .., _, h => nomatch h
    | .proform _, _, _ => id

instance [DecidableRel (InDomain (α := α))] : ∀ (s : NullSite α) (d : α), Decidable (s.Silences d)
  | .elided e _, _ => inferInstanceAs (Decidable (e.Deletes _))
  | .proform _, _ => inferInstanceAs (Decidable False)

@[simp] theorem silences_elided {e : Ellipsis α} {h : ∃ d, e.Deletes d} {d : α} :
    (elided e h).Silences d ↔ e.Deletes d := .rfl

/-- The head that bears [E] lies outside the site it silences, which is what lets a head moved
there strand. -/
theorem not_silences_ePosition {e : Ellipsis α} (h : ∃ d, e.Deletes d) :
    ¬ (elided e h).Silences e.ePosition :=
  e.spares_ePosition

end NullSite

/-! ### The two readings of *again* -/

/-- The two readings of *again* and their adjunction sites. Repetitive *again* adjoins to vP or
VoiceP and presupposes an earlier event, restitutive *again* adjoins to VP and presupposes an
earlier result state. -/
inductive AgainReading
  | repetitive
  | restitutive
  deriving DecidableEq, Repr

/-- The adjunction site of each reading. -/
def AgainReading.site : AgainReading → SpinePosition
  | .repetitive => .Voice
  | .restitutive => .vpAdjunct

end Minimalist
