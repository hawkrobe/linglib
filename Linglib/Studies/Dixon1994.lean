import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Case.Alignment
import Linglib.Data.Examples.Dixon1994

/-!
# Dixon (1994): Ergativity

This file formalizes the theory of [dixon-1994]. Its premiss is that every language works in
terms of three universal syntactic-semantic relations, S, A and O, §1.1, and that a language is
ergative at some level of its grammar when that level treats S like O and unlike A, and
accusative when it treats S like A and unlike O, §8.2. Morphological marking may be split,
Chapter 4. A split conditioned by the verb, §4.1, divides S into Sa, marked like A, and So,
marked like O: a split-S language fixes each intransitive verb's class and a fluid-S language
marks each instance of use by whether its referent controls the activity, and either system is
accusative over Sa and ergative over So. A split conditioned by the NP, §4.2, follows the
Nominal Hierarchy of Figure 4.5, from first person pronouns down to inanimate common nouns:
accusative marking of O extends in from the left end and ergative marking of A from the right,
the two segments either meeting, Dyirbal and Kuku-Yalanji, or overlapping in a tripartite
zone, Cashinawa and Yidiny, while a gap in which neither applies would leave A and O
undistinguished and is unattested, type (g) of the Appendix to Chapter 4. A split conditioned
by tense, aspect or mood, §4.3, puts the ergative marking in the past or the perfective. At the
level of inter-clausal syntax, Chapter 6, a pivot is the pair of functions, S/A or S/O, that an
NP common to two linked clauses must bear in each; passive puts O into derived S and antipassive
puts A into derived S, §6.1, so that passive alone feeds an S/A pivot for an NP in O function
and antipassive alone feeds an S/O pivot for one in A function, which is why a language with a
thoroughgoing S/O pivot must have an antipassive, §6.2.3. Of the eleven configurations of a
common NP in two linked clauses, §6.2.1, English with its S/A pivot passivizes a clause in
which the NP is O and Dyirbal with its S/O pivot antipassivizes one in which it is A, §6.2.2.

## Implementation notes

S, A and O are `ArgumentRole.S`, `.A` and `.P`, following the substrate's Comrie letters, and
a marking of the core relations is any function out of `ArgumentRole`, so that ergativity and
accusativity are the identifications of S the marking makes, as in `Alignment.coreSig`. The
Nominal Hierarchy is a linear order with first person at the top; an NP-conditioned split is
a pair of monotone marking functions, accusative marking an upper set and ergative a lower set,
and the pattern at a position is the `AlignmentType` the two markings induce. The tables of
§4.2 are given as cutoffs, with the optional accusative of Yidiny's proper names and kin terms
counted as marking; Latin and Waga-Waga, the types with one marking absent or total, are given
directly. Pivots and derivations are the framework of §6.2.1 over core functions, with the
periphery as `none`; the constructions that satisfy a pivot without derivation, such as
Dyirbal's *-ŋurra* and instrumentive, are recorded in the rows only. Not formalized: the
markedness generalizations of §3.4, the bound-versus-free split of §4.2.1, the main-versus-
subordinate split of §4.4, the universal category of subject of Chapter 5, and the mixed
pivots of §6.2.4.

## References

* [dixon-1994]
* [dixon-1972]
* [silverstein-1976]
* [comrie-1978]
-/

namespace Dixon1994

open Alignment

/-! ### S, A and O, §1.1 and §8.2 -/

variable {κ : Type*}

/-- A marking of the core relations, by case, cross-referencing or constituent order, treats S
like O and unlike A: ergativity at that level of the grammar, §8.2. -/
def IsErgative (m : ArgumentRole → κ) : Prop := m .S = m .P ∧ m .S ≠ m .A

/-- The marking treats S like A and unlike O: accusativity. -/
def IsAccusative (m : ArgumentRole → κ) : Prop := m .S = m .A ∧ m .S ≠ m .P

theorem isErgative_ergative : IsErgative ergative.assignCase := ⟨rfl, by decide⟩

theorem isAccusative_nominativeAccusative : IsAccusative nominativeAccusative.assignCase :=
  ⟨rfl, by decide⟩

/-- No marking is ergative and accusative at once, since S can be identified with only one of A
and O; a language is ergative in some parts of its grammar and accusative in others. -/
theorem IsAccusative.not_isErgative {m : ArgumentRole → κ} (h : IsAccusative m) :
    ¬ IsErgative m :=
  λ h' => h.2 h'.1

/-! ### Splits conditioned by the verb, §4.1 -/

/-- The two subtypes of S in a split-S or fluid-S language: Sa, marked like A, and So, marked
like O. -/
inductive SClass
  | sa
  | so
  deriving DecidableEq, Repr

/-- A fluid-S system, §4.1.2: the S of an instance of use is Sa when its referent controls the
activity and So otherwise. A split-S system, §4.1.1, is instead a fixed class for each verb. -/
def fluidS {I : Type*} (control : I → Prop) [DecidablePred control] (i : I) : SClass :=
  if control i then .sa else .so

/-- The marking of an S of class `c` under a transitive marking `m`: like A or like O. -/
def SClass.marking (m : ArgumentRole → κ) : SClass → ArgumentRole → κ
  | c, .S => match c with
    | .sa => m .A
    | .so => m .P
  | _, r => m r

/-- A split system is a mixture of the two simple patterns, §4.1.1: over Sa verbs it is
accusative and over So verbs ergative, whenever A and O are distinguished. -/
theorem marking_sa_so {m : ArgumentRole → κ} (h : m .A ≠ m .P) :
    IsAccusative (SClass.sa.marking m) ∧ IsErgative (SClass.so.marking m) :=
  ⟨⟨rfl, h⟩, ⟨rfl, h.symm⟩⟩

/-! ### Splits conditioned by the NP: the Nominal Hierarchy, §4.2 -/

/-- The Nominal Hierarchy, Figure 4.5, by likelihood of being in A rather than in O function:
first person pronouns, second person pronouns, demonstratives and third person pronouns,
proper names, then common nouns with human, animate and inanimate reference. -/
inductive Nominal
  | firstPerson
  | secondPerson
  | thirdPerson
  | properName
  | human
  | animate
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- Position on the hierarchy, higher to the left. -/
def Nominal.rank : Nominal → ℕ
  | .firstPerson => 6
  | .secondPerson => 5
  | .thirdPerson => 4
  | .properName => 3
  | .human => 2
  | .animate => 1
  | .inanimate => 0

instance : LinearOrder Nominal :=
  LinearOrder.lift' Nominal.rank λ a b h => by cases a <;> cases b <;> simp_all [Nominal.rank]

variable {H : Type*} [LinearOrder H]

/-- An NP-conditioned split, §4.2: accusative marking of O extends in from the left of the
hierarchy over an upper set of positions, and ergative marking of A extends in from the right
over a lower set. -/
structure HierarchySplit (H : Type*) [LinearOrder H] where
  /-- The positions whose O is marked accusative. -/
  accusative : H → Bool
  /-- The positions whose A is marked ergative. -/
  ergative : H → Bool
  accusative_mono : ∀ p q, p ≤ q → accusative p → accusative q
  ergative_anti : ∀ p q, p ≤ q → ergative q → ergative p

namespace HierarchySplit

variable (s : HierarchySplit H) (p q : H)

/-- The pattern at a position: accusative where only O is marked, ergative where only A is,
tripartite where both are, and neutral, all three functions alike, where neither is. -/
def pattern : AlignmentType :=
  if s.accusative p then (if s.ergative p then .tripartite else .accusative)
  else (if s.ergative p then .ergative else .neutral)

/-- The two markings must at least meet, §4.2: A and O are distinguished at a position exactly
when one of them applies there. -/
theorem marks_iff :
    (s.pattern p).marksAgent ∨ (s.pattern p).marksPatient ↔ s.accusative p ∨ s.ergative p := by
  unfold pattern
  split_ifs <;> simp_all [AlignmentType.marksAgent, AlignmentType.marksPatient]

theorem pattern_eq_accusative_iff :
    s.pattern p = .accusative ↔ s.accusative p ∧ ¬ s.ergative p := by
  unfold pattern; split_ifs <;> simp_all

theorem pattern_eq_ergative_iff : s.pattern p = .ergative ↔ ¬ s.accusative p ∧ s.ergative p := by
  unfold pattern; split_ifs <;> simp_all

theorem pattern_eq_tripartite_iff :
    s.pattern p = .tripartite ↔ s.accusative p ∧ s.ergative p := by
  unfold pattern; split_ifs <;> simp_all

theorem pattern_eq_neutral_iff : s.pattern p = .neutral ↔ ¬ s.accusative p ∧ ¬ s.ergative p := by
  unfold pattern; split_ifs <;> simp_all

variable {s p q}

/-- Above an accusative position the pattern stays accusative. -/
theorem pattern_eq_accusative (h : s.pattern p = .accusative) (hpq : p ≤ q) :
    s.pattern q = .accusative := by
  rw [pattern_eq_accusative_iff] at *
  exact ⟨s.accusative_mono p q hpq h.1, λ hq => h.2 (s.ergative_anti p q hpq hq)⟩

/-- Below an ergative position the pattern stays ergative. -/
theorem pattern_eq_ergative (h : s.pattern q = .ergative) (hpq : p ≤ q) :
    s.pattern p = .ergative := by
  rw [pattern_eq_ergative_iff] at *
  exact ⟨λ hp => h.1 (s.accusative_mono p q hpq hp), s.ergative_anti p q hpq h.2⟩

/-- The overlap of the two markings and a gap between them exclude each other: a split is of
type (d) of the Appendix to Chapter 4 or of the unattested type (g), never both. -/
theorem not_tripartite_and_neutral (ht : s.pattern p = .tripartite)
    (hn : s.pattern q = .neutral) : False := by
  rw [pattern_eq_tripartite_iff] at ht
  rw [pattern_eq_neutral_iff] at hn
  rcases le_total p q with hpq | hqp
  · exact hn.1 (s.accusative_mono p q hpq ht.1)
  · exact hn.2 (s.ergative_anti q p hqp ht.2)

/-- The split with accusative marking from the left down to `a` and ergative marking from the
right up to `e`. -/
def ofCutoffs (a e : H) : HierarchySplit H where
  accusative p := decide (a ≤ p)
  ergative p := decide (p ≤ e)
  accusative_mono _ _ hpq h := by simpa using le_trans (by simpa using h) hpq
  ergative_anti _ _ hpq h := by simpa using le_trans hpq (by simpa using h)

end HierarchySplit

/-- Dyirbal, Table 4.1: accusative for first and second person pronouns, ergative from third
person pronouns rightwards, the two meeting without overlap. -/
def dyirbal : HierarchySplit Nominal := .ofCutoffs .secondPerson .thirdPerson

/-- Cashinawa, Table 4.2: accusative down to third person pronouns and ergative from third
person pronouns rightwards, overlapping there. -/
def cashinawa : HierarchySplit Nominal := .ofCutoffs .thirdPerson .thirdPerson

/-- Yidiny, Table 4.3: accusative down to proper names and kin terms, ergative from human
deictics rightwards, overlapping over the middle of the hierarchy. -/
def yidiny : HierarchySplit Nominal := .ofCutoffs .properName .thirdPerson

/-- Latin, type (a): accusative for pronouns and masculine and feminine nouns, no ergative, so
that neuter nouns have one form for S, A and O. -/
def latin : HierarchySplit Nominal where
  accusative p := decide (.human ≤ p)
  ergative _ := false
  accusative_mono _ _ hpq h := by simpa using le_trans (by simpa using h) hpq
  ergative_anti _ _ _ h := h

/-- Waga-Waga, type (f), fn. 14: ergative on every NP constituent, accusative down to human
common nouns, so that the left and middle of the hierarchy are tripartite. -/
def wagaWaga : HierarchySplit Nominal where
  accusative p := decide (.human ≤ p)
  ergative _ := true
  accusative_mono _ _ hpq h := by simpa using le_trans (by simpa using h) hpq
  ergative_anti _ _ _ h := h

/-- The patterns the cutoffs induce: Dyirbal's markings meet at third person pronouns, type
(c); Cashinawa and Yidiny overlap in tripartite zones, type (d); Latin leaves neuter nouns
neutral, type (a); Waga-Waga is tripartite down to human nouns and ergative below, type (f). -/
theorem patterns :
    (∀ p, dyirbal.pattern p ≠ .tripartite ∧ dyirbal.pattern p ≠ .neutral) ∧
      dyirbal.pattern .secondPerson = .accusative ∧ dyirbal.pattern .thirdPerson = .ergative ∧
      cashinawa.pattern .thirdPerson = .tripartite ∧ cashinawa.pattern .properName = .ergative ∧
      yidiny.pattern .thirdPerson = .tripartite ∧ yidiny.pattern .properName = .tripartite ∧
      yidiny.pattern .human = .ergative ∧ latin.pattern .animate = .neutral ∧
      wagaWaga.pattern .human = .tripartite ∧ wagaWaga.pattern .animate = .ergative := by
  decide

/-! ### Splits conditioned by tense, aspect or mood, §4.3 -/

/-- Dixon's generalization for an aspect-conditioned split: the ergative marking is found in
the perfective, never in the imperfective alone. -/
def AspectOriented (s : SplitErgativity Aspect) : Prop :=
  s.ergCondition .imperfective → s.ergCondition .perfective

theorem aspectOriented_hindiSplit : AspectOriented hindiSplit := λ h => nomatch h

/-! ### Passive, antipassive and pivots, §6.1 and §6.2 -/

/-- The two pivots, §6.2: the functions an NP common to two linked clauses must bear in each,
S or A in a language with accusative syntax and S or O in one with ergative syntax. -/
inductive Pivot
  | SA
  | SO
  deriving DecidableEq, Repr, Fintype

/-- Whether a core function is a pivot function. -/
def Pivot.Admits : Pivot → ArgumentRole → Prop
  | .SA, .S | .SA, .A => True
  | .SO, .S | .SO, .P => True
  | _, _ => False

instance (π : Pivot) (r : ArgumentRole) : Decidable (π.Admits r) := by
  cases π <;> cases r <;> unfold Pivot.Admits <;> infer_instance

/-- The two derivations of §6.1, each forming an intransitive from a transitive clause. -/
inductive Derivation
  | passive
  | antipassive
  deriving DecidableEq, Repr, Fintype

/-- The derived function of a core function: passive puts O into S and A into the periphery,
antipassive puts A into S and O into the periphery, and the ditransitive roles are peripheral. -/
def Derivation.apply : Derivation → ArgumentRole → Option ArgumentRole
  | .passive, .P => some .S
  | .antipassive, .A => some .S
  | _, .S => some .S
  | _, _ => none

/-- A derivation feeds a pivot for an NP in function `r` when the derived function is a pivot
function. -/
def Feeds (π : Pivot) (d : Derivation) (r : ArgumentRole) : Prop :=
  ∃ g, d.apply r = some g ∧ π.Admits g

/-- A common NP needs a derivation in a clause exactly when its function there is not a pivot
function: O under an S/A pivot and A under an S/O pivot. -/
theorem not_admits_iff :
    (∀ r ∈ ArgumentRole.core, ¬ Pivot.SA.Admits r ↔ r = .P) ∧
      ∀ r ∈ ArgumentRole.core, ¬ Pivot.SO.Admits r ↔ r = .A := by
  decide

/-- Passive alone feeds an S/A pivot for an NP in O function, and antipassive alone feeds an
S/O pivot for an NP in A function, §6.2.1 and §6.2.2; each derivation demotes the other
function to the periphery. So a language with a thoroughgoing S/O pivot must have an
antipassive, §6.2.3. -/
theorem feeds_iff :
    (∀ d, Feeds .SA d .P ↔ d = .passive) ∧ (∀ d, Feeds .SO d .A ↔ d = .antipassive) ∧
      ¬ Feeds .SA .passive .A ∧ ¬ Feeds .SO .antipassive .P :=
  ⟨λ d => by cases d <;> simp [Feeds, Derivation.apply, Pivot.Admits],
    λ d => by cases d <;> simp [Feeds, Derivation.apply, Pivot.Admits],
    (λ ⟨_, h, _⟩ => nomatch h), λ ⟨_, h, _⟩ => nomatch h⟩

/-- Interchange A and O, leaving S and the ditransitive roles alone. -/
def swapAO : ArgumentRole → ArgumentRole
  | .A => .P
  | .P => .A
  | r => r

/-- Passive and antipassive are parallel with A and O interchanged, §6.1. -/
theorem apply_swapAO (r : ArgumentRole) :
    Derivation.passive.apply r = Derivation.antipassive.apply (swapAO r) := by
  cases r <;> rfl

end Dixon1994
