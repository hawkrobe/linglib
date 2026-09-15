import Linglib.Semantics.Modality.Kernel
import Linglib.Semantics.Questions.Partition.Basic
import Linglib.Data.Examples.VonFintelGillies2010

/-!
# von Fintel & Gillies (2010): Must … Stay … Strong!

This file formalizes [von-fintel-gillies-2010]'s defense of a strong epistemic *must* against
the Mantra that *must φ* is weaker than its prejacent, Karttunen's problem (2). On the paper's
analysis *must* stays at the top of the scale of epistemic strength (1) and entails its
prejacent, and the felt weakness is an evidential presupposition: the kernel of direct
information must not directly settle the prejacent, though its modal base may entail it. The
kernel apparatus, the explicit-representation implementation of settling (§7.1) and the
presuppositional operators (Definitions 4 to 6), is `Semantics/Modality/Kernel.lean`; this file
carries the worked kernel of Figure 3(a), Billy's weather reports in the colors of the
Mastermind scenario of §2 (`mastermindK`), on which *must blue* is defined and true while
*might red* is undefined, so that indirectness and weakness come apart (§4.1), the validity of
*if φ, must ψ; φ; so ψ* (Argument 4.3.1) and the contradictoriness of *must φ but perhaps not φ*
(Argument 4.3.2), and the second implementation of settling by the partition a kernel induces,
a subject matter in which the prejacent is an issue (Definition 7, §7.2), with the two
implementations shown non-equivalent in both directions (`settlesByPartition`).

## Implementation notes

The four worlds are red, blue, green and unknown, with *red or blue* and *not red* the kernel
propositions `P ∪ Q` and `W \ P` of the paper's figure. A subject matter is a `Setoid`, and a
proposition is an issue in it when the setoid decides the proposition. The paper's examples
are the rows of `Data.Examples.VonFintelGillies2010`.

## References

* [von-fintel-gillies-2010]
* [kratzer-1991]
* [karttunen-1972]
-/

namespace VonFintelGillies2010

/-! ### The kernel model (§7.1)

A four-world instantiation of §7.1's worked kernel `K = {P ∪ Q, W \ P}`
(Billy's weather report, Figure 3(a)), skinned with the colors of the §2
Mastermind scenario (Pascal asking Mordecai *Must there be two reds?*):
`P` = red-only, `Q` = blue, so `redOrBlue = P ∪ Q` and `notRed = W \ P`.
`B_K = {w1}` entails *blue* without either kernel proposition settling it. -/

open Modality
open Modality.Kratzer

/-- Four worlds, with `w0` red, `w1` blue, `w2` green, and `w3` unknown. -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr, Inhabited

/-- `⟦red or blue⟧ = {w0, w1}`, the paper's `P ∪ Q`. -/
abbrev redOrBlue : World → Prop := λ w => w = .w0 ∨ w = .w1

/-- `⟦not red⟧ = {w1, w2, w3}`, the paper's `W \ P`. -/
abbrev notRed : World → Prop := (· ≠ .w0)

/-- `⟦blue⟧ = {w1}`, the paper's `Q`. -/
abbrev blue : World → Prop := (· = .w1)

/-- `⟦red⟧ = {w0}`, the paper's `P`. -/
abbrev red : World → Prop := (· = .w0)

/-- `⟦not blue⟧`, used by the [von-fintel-gillies-2021] can't dilemma. -/
abbrev notBlue : World → Prop := (· ≠ .w1)

/-- The §7.1 kernel `{P ∪ Q, W \ P}` in Mastermind colors. -/
def mastermindK : Kernel World := ⟨[redOrBlue, notRed]⟩

/-- A one-proposition kernel whose base properly contains ⟦blue⟧. -/
def indirectK : Kernel World := ⟨[redOrBlue]⟩

theorem mastermind_base : mastermindK.base = ({.w1} : Set World) := by
  ext w
  cases w <;> simp [Kernel.base, mastermindK, propIntersection, redOrBlue, notRed]

theorem mastermind_blue_unsettled :
    ¬ mastermindK.directlySettles blue := by
  rintro ⟨x, hx, hxor⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · rcases hxor with h_sub | h_disj
    · exact (show ¬ blue .w0 from by decide)
        (h_sub (show redOrBlue .w0 from by decide))
    · exact Set.disjoint_left.mp h_disj (show redOrBlue .w1 from by decide)
        (show blue .w1 from by decide)
  · rcases List.mem_singleton.mp hx' with rfl
    rcases hxor with h_sub | h_disj
    · exact (show ¬ blue .w2 from by decide)
        (h_sub (show notRed .w2 from by decide))
    · exact Set.disjoint_left.mp h_disj (show notRed .w1 from by decide)
        (show blue .w1 from by decide)

theorem mastermind_blue_follows : mastermindK.followsFrom blue := by
  rw [Kernel.followsFrom_iff, mastermind_base]
  rintro w rfl
  rfl

theorem mastermind_must_blue_defined :
    (kernelMust mastermindK blue).presup .w0 :=
  mastermind_blue_unsettled

theorem mastermind_must_blue_true :
    (kernelMust mastermindK blue).assertion .w0 :=
  mastermind_blue_follows

theorem mastermind_red_settled :
    mastermindK.directlySettles red :=
  ⟨notRed, by simp [mastermindK], Or.inr (Set.disjoint_left.mpr λ _ hnr hr => hnr hr)⟩

theorem mastermind_might_red_undefined :
    ¬(kernelMight mastermindK red).presup .w0 := λ h =>
  h mastermind_red_settled

theorem mastermind_redOrBlue_settled :
    mastermindK.directlySettles redOrBlue :=
  ⟨redOrBlue, by simp [mastermindK], Or.inl subset_rfl⟩

/-! ### Deep theorems -/

/-- `B_K` can entail `φ` without `K` directly settling it, so must `φ` can be
simultaneously defined and true. -/
theorem entailment_settling_gap :
    ∃ (k : Kernel World) (φ : World → Prop),
      k.followsFrom φ ∧ ¬ k.directlySettles φ :=
  ⟨mastermindK, blue, mastermind_blue_follows, mastermind_blue_unsettled⟩

/-- Indirectness and assertion strength are orthogonal dimensions: must can
be defined and true, undefined, or defined and false (§4.1). -/
theorem indirectness_neq_weakness :
    ((kernelMust mastermindK blue).presup .w0 ∧
     (kernelMust mastermindK blue).assertion .w0) ∧
    ¬(kernelMust mastermindK red).presup .w0 ∧
    ((kernelMust indirectK blue).presup .w0 ∧
     ¬(kernelMust indirectK blue).assertion .w0) := by
  refine ⟨⟨mastermind_must_blue_defined, mastermind_must_blue_true⟩,
    λ h => h mastermind_red_settled, ?_, ?_⟩
  · rintro ⟨x, hx, hxor⟩
    rcases List.mem_singleton.mp hx with rfl
    rcases hxor with h_sub | h_disj
    · exact (show ¬ blue .w0 from by decide)
        (h_sub (show redOrBlue .w0 from by decide))
    · exact Set.disjoint_left.mp h_disj (show redOrBlue .w1 from by decide)
        (show blue .w1 from by decide)
  · intro h
    have hw0 : World.w0 ∈ indirectK.base :=
      mem_propIntersection.mpr λ p hp => by
        rcases List.mem_singleton.mp hp with rfl; decide
    exact (by decide : ¬ blue World.w0) (h hw0)

variable {W : Type*} (k : Kernel W)

/-- The argument form "if φ, must ψ; φ; therefore ψ" is valid under realistic
`B_K` (Argument 4.3.1). -/
theorem modus_ponens_with_must (φ ψ : W → Prop) (w : W)
    (hReal : w ∈ k.base)
    (hCond : φ w → (kernelMust k ψ).assertion w)
    (hPhi : φ w) :
    ψ w :=
  Modality.must_entails_prejacent k ψ w hReal (hCond hPhi)

/-- Must `φ` and might `¬φ` are jointly contradictory
(Argument 4.3.2). -/
theorem must_perhaps_contradiction (φ : W → Prop) (w : W)
    (hMust : (kernelMust k φ).assertion w) :
    ¬(kernelMight k (λ w' => ¬ φ w')).assertion w := by
  intro hc
  obtain ⟨w', hw', hφneg⟩ := (Kernel.compatibleWith_iff _ _).mp hc
  exact hφneg (hMust hw')

/-! ### Implementation 2: settling by partitions (Definition 7, §7.2)

Def 7 presents subject matters as equivalence relations on `W`: `S[P]` keeps
the pairs of `S` that agree on `P`, and `P` is an *issue* in `S` iff
`S[P] = S`. The subject matter S_K determined by a kernel is the refinement
`S_o[P₁]…[Pₙ]` of the universal relation along each kernel proposition —
equivalently, the relation "agrees on every `X ∈ K`". Implementation 2:
K directly settles P iff P is an issue in S_K. -/

/-- The subject matter `S_K` of a kernel, relating worlds that agree on every
    proposition in `K`. -/
def subjectMatter : Setoid W where
  r w v := ∀ p ∈ k.props, (p w ↔ p v)
  iseqv := ⟨λ _ _ _ => Iff.rfl, λ h p hp => (h p hp).symm,
    λ h h' p hp => (h p hp).trans (h' p hp)⟩

/-- `P` is an *issue* in a subject matter `S`: `S`-equivalent worlds never
    disagree on `P`. -/
def IsIssue (s : Setoid W) (φ : W → Prop) : Prop := s.Decides {w | φ w}

/-- `K` settles `P` by partition iff `P` is an issue in `S_K`. -/
def settlesByPartition (φ : W → Prop) : Prop :=
  IsIssue (subjectMatter k) φ

/-- `B_K` lies in a single cell of the subject matter. -/
theorem subjectMatter_rel_base {v w : W} (hv : v ∈ k.base) (hw : w ∈ k.base) :
    (subjectMatter k).r v w := λ p hp =>
  iff_of_true (mem_propIntersection.mp hv p hp) (mem_propIntersection.mp hw p hp)

/-- If `K` settles `φ` by partition then `B_K ⊆ ⟦φ⟧` or `B_K ⊆ ⟦¬φ⟧`; as
    with `explicit_implies_entailment`, the converse fails. -/
theorem partition_implies_entailment (φ : W → Prop)
    (h : settlesByPartition k φ) :
    k.followsFrom φ ∨ k.followsFrom (λ w => ¬ φ w) := by
  rcases Set.eq_empty_or_nonempty k.base with hEmpty | ⟨w₀, hw₀⟩
  · exact Or.inl λ w hw => absurd (hEmpty ▸ hw) (Set.notMem_empty w)
  · exact (Classical.em (φ w₀)).imp
      (λ hφ v hv => (Setoid.decides_iff.1 h w₀ v (subjectMatter_rel_base k hw₀ hv)).mp hφ)
      (λ hφ v hv hφv =>
        hφ ((Setoid.decides_iff.1 h w₀ v (subjectMatter_rel_base k hw₀ hv)).mpr hφv))

/-! ### Non-equivalence of the two implementations (§7.2)

Implementation 1 settles supersets of K-propositions that Implementation 2
misses (`K = {P}` settles `P ∪ Q` explicitly, but there are worlds agreeing
on `P` that disagree on `P ∪ Q`); Implementation 2 settles propositions
determined jointly by K-propositions that no single proposition settles
(`blue` is determined by `redOrBlue` together with `notRed`). -/

/-- `S_K` for `K = {red}` does not make `redOrBlue` an issue: `w1` and `w2`
    agree on `red` but disagree on `redOrBlue`. -/
private theorem not_settles_redOrBlue :
    ¬ settlesByPartition ⟨[red]⟩ redOrBlue := by
  intro h
  have h12 := Setoid.decides_iff.1 h .w1 .w2 (λ p hp => by
    rcases List.mem_singleton.mp hp with rfl; decide)
  exact absurd (h12.mp (by decide)) (by decide)

/-- Explicit settling does not imply partition settling: `K = {red}` settles
    `redOrBlue` explicitly (`red ⊆ redOrBlue`) but not by partition. -/
theorem explicit_not_implies_partition :
    ∃ (k : Kernel World) (φ : World → Prop),
      k.directlySettles φ ∧ ¬ settlesByPartition k φ :=
  ⟨⟨[red]⟩, redOrBlue,
    ⟨red, by simp, Or.inl λ _ hw => Or.inl hw⟩, not_settles_redOrBlue⟩

/-- Partition settling does not imply explicit settling: `mastermindK`
    settles `blue` by partition — its cells decide `redOrBlue` and `notRed`,
    which jointly determine `blue` — but no single kernel proposition entails
    or excludes it. -/
theorem partition_not_implies_explicit :
    ∃ (k : Kernel World) (φ : World → Prop),
      settlesByPartition k φ ∧ ¬ k.directlySettles φ := by
  refine ⟨mastermindK, blue, Setoid.decides_iff.2 λ w v h => ?_, mastermind_blue_unsettled⟩
  have h1 := h redOrBlue (by simp [mastermindK])
  have h2 := h notRed (by simp [mastermindK])
  revert h1 h2
  cases w <;> cases v <;> decide

/-- Entailment does not imply partition settling: `K = {red}` entails
    `redOrBlue` (`B_K = {w0} ⊆ ⟦redOrBlue⟧`) but does not settle it by
    partition. -/
theorem entailment_not_implies_partition :
    ∃ (k : Kernel World) (φ : World → Prop),
      k.followsFrom φ ∧ ¬ settlesByPartition k φ :=
  ⟨⟨[red]⟩, redOrBlue,
    λ w hw => Or.inl (mem_propIntersection.mp hw red (by simp)),
    not_settles_redOrBlue⟩

end VonFintelGillies2010
