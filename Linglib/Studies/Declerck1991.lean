import Linglib.Semantics.Tense.Reichenbach
import Mathlib.Tactic.DeriveFintype

/-!
# Declerck (1991): Tense in English

This file formalizes the tense system of [declerck-1991]. Time divides into two time-spheres,
the past, lying wholly before the temporal zero-point t₀, and the present, which contains t₀
and is thereby divided into a pre-present, a present and a post-present sector; with the past
sector these are the four absolute sectors, and each has its absolute tense, the preterit, the
present perfect, the present tense and the future tense, so that the preterit and the present
perfect differ in sphere and not in the time of the situation. Every tense represents the time
of the situation as coinciding with a time of orientation, the situation-TO, and relates it by
a chain of anteriority, simultaneity and posteriority relations to a binding TO, ultimately
t₀: the four relative tenses, the past perfect, the conditional, the future perfect and the
conditional perfect, relate the situation to a TO already established in a temporal domain.
Where the chain relates the situation-TO only to an intermediate TO, its relation to t₀ is not
expressed, so the conditional, the future perfect and the conditional perfect are vague, not
ambiguous, among the three orderings of the situation against t₀ that [reichenbach-1947]'s
format distinguishes as separate tenses. The tenses are chains, a realization assigns times
along a chain from a binding TO, t₀ or the pseudo-t₀ of a post-present domain, and the
projection onto the shared Reichenbach frame shows the vagueness as three orderings of R
against S.

## Implementation notes

Temporal subordination against shift of domain, the Present and Future Perspective Systems,
the principle of unmarked temporal interpretation and the modal past are matters of discourse
the chains do not decide; the companion grammar's examples of them, [declerck-1991-grammar],
are the rows of `Data/Examples/Declerck1991.json`.

## References

* [declerck-1991]
* [declerck-1991-grammar]
* [reichenbach-1947]
-/

namespace Declerck1991

open Tense

/-! ### Time-spheres, sectors and tenses -/

/-- The two time-spheres: the past, lying wholly before t₀, and the present, which contains
it. -/
inductive TimeSphere where
  | past
  | present
  deriving DecidableEq, Repr, Fintype

/-- The four absolute sectors, defined in direct relation to t₀: the past sphere as one sector,
and the three sectors t₀ divides the present sphere into. -/
inductive Sector where
  | past
  | prePresent
  | present
  | postPresent
  deriving DecidableEq, Repr, Fintype

/-- The eight tenses of English. -/
inductive Tense where
  | preterit
  | present
  | presentPerfect
  | future
  | pastPerfect
  | conditional
  | futurePerfect
  | conditionalPerfect
  deriving DecidableEq, Repr, Fintype

/-- The time-sphere a tense locates its situation in: the preterit and the present perfect
differ only here, the same situation lying in the past sector or in the pre-present as the
speaker conceives it. -/
def Tense.sphere : Tense → TimeSphere
  | .preterit | .pastPerfect | .conditional | .conditionalPerfect => .past
  | .present | .presentPerfect | .future | .futurePerfect => .present

/-- A tense's chain of relations from the binding TO outward to the situation-TO, each link
relating a TO to the one before: `.lt` anteriority, `.eq` simultaneity, `.gt` posteriority. The
past perfect is anteriority to a past TO, the conditional posteriority to one, the future
perfect anteriority to a post-present TO, and the conditional perfect anteriority to a TO
posterior to a past one. -/
def Tense.chain : Tense → List Ordering
  | .preterit | .presentPerfect => [.lt]
  | .present => [.eq]
  | .future => [.gt]
  | .pastPerfect => [.lt, .lt]
  | .conditional => [.lt, .gt]
  | .futurePerfect => [.gt, .lt]
  | .conditionalPerfect => [.lt, .gt, .lt]

/-- An absolute tense relates the situation-TO to t₀ directly; a relative tense relates it to
a TO already established in a domain. -/
def Tense.IsAbsolute (t : Tense) : Prop := t.chain.length = 1

instance : DecidablePred Tense.IsAbsolute := λ _ => inferInstanceAs (Decidable (_ = _))

/-- The absolute sector of the domain a tense's situation lies in: the past sphere is one
sector, and in the present sphere the first link places the domain before, at or after t₀. -/
def Tense.sector (t : Tense) : Sector :=
  match t.sphere, t.chain.head? with
  | .past, _ => .past
  | .present, some .lt => .prePresent
  | .present, some .gt => .postPresent
  | .present, _ => .present

/-- Each absolute sector has exactly one absolute tense to locate a situation in it. -/
theorem absolute_sector_bijective :
    (∀ s : Sector, ∃ t : Tense, t.IsAbsolute ∧ t.sector = s) ∧
      ∀ t u : Tense, t.IsAbsolute → u.IsAbsolute → t.sector = u.sector → t = u := by
  decide

/-! ### Realizations -/

section Realizations

variable {T : Type*} [LinearOrder T]

/-- Times realizing a tense from a binding TO: each TO stands to the one before in the relation
the chain gives, the last being the situation-TO. The binding TO is t₀ in an absolute use and,
in the Present Perspective System, the pseudo-t₀ of a post-present domain. -/
def Realizes (t : Tense) (binding : T) (tos : List T) : Prop :=
  tos.zipWith compare (binding :: tos) = t.chain

instance (t : Tense) (binding : T) (tos : List T) : Decidable (Realizes t binding tos) :=
  inferInstanceAs (Decidable (_ = _))

/-- The Reichenbach frame of a realization from t₀: S = P = t₀ and R = E = the situation-TO,
since every tense represents the time of the situation as coinciding with its TO. -/
def toFrame (t0 : T) (tos : List T) : ReichenbachFrame T :=
  ⟨t0, t0, tos.getLast?.getD t0, tos.getLast?.getD t0⟩

/-- No frame of a realization is perfect in Reichenbach's sense: the perfect lives in the
chain, as anteriority to a TO, not in the relation of E to R. -/
theorem toFrame_not_isPerfect (t0 : T) (tos : List T) : ¬ (toFrame t0 tos).isPerfect :=
  lt_irrefl _

/-- A chain of anteriorities does fix the situation against t₀: the past perfect's situation
lies before t₀. -/
theorem pastPerfect_lt (t0 to2 ts : T) (h : Realizes .pastPerfect t0 [to2, ts]) : ts < t0 := by
  simp only [Realizes, Tense.chain, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.cons.injEq, compare_lt_iff_lt, and_true] at h
  exact h.2.trans h.1

end Realizations

/-- The conditional, the future perfect and the conditional perfect relate the situation-TO to
an intermediate TO only, so its relation to t₀ is not expressed: each has realizations with the
situation before, at and after t₀, the three orderings of R against S that
[reichenbach-1947]'s format distinguishes as separate tenses, and the tense is vague among
them rather than ambiguous. -/
theorem vague :
    ∀ o : Ordering,
      (∃ to2 ts : ℤ, Realizes .conditional 0 [to2, ts] ∧
        compare (toFrame 0 [to2, ts]).referenceTime 0 = o) ∧
      (∃ to2 ts : ℤ, Realizes .futurePerfect 0 [to2, ts] ∧
        compare (toFrame 0 [to2, ts]).referenceTime 0 = o) ∧
      (∃ to2 to3 ts : ℤ, Realizes .conditionalPerfect 0 [to2, to3, ts] ∧
        compare (toFrame 0 [to2, to3, ts]).referenceTime 0 = o)
  | .lt => ⟨⟨-3, -1, by decide, by decide⟩, ⟨3, -1, by decide, by decide⟩,
      ⟨-6, 3, -1, by decide, by decide⟩⟩
  | .eq => ⟨⟨-3, 0, by decide, by decide⟩, ⟨3, 0, by decide, by decide⟩,
      ⟨-6, 3, 0, by decide, by decide⟩⟩
  | .gt => ⟨⟨-3, 1, by decide, by decide⟩, ⟨3, 1, by decide, by decide⟩,
      ⟨-6, 3, 1, by decide, by decide⟩⟩

end Declerck1991
