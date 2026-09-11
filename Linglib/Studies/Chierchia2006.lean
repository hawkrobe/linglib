import Linglib.Semantics.Exhaustification.Antiexhaustive
import Linglib.Semantics.Exhaustification.PreExhaustified
import Linglib.Logic.Modal.Basic
import Linglib.Studies.Haspelmath1997

/-!
# Chierchia (2006): Broaden your views

This file formalizes the theory of polarity-sensitive items in [chierchia-2006]: all of them are
existentials that activate domain alternatives, [kadmon-landman-1993]'s domain widening, and the
alternatives are factored into meaning by an enrichment operation whose result an
implicature-freezing operator σ locks in place. The items differ in two respects, (94): the size
of the alternatives, large subdomains (MAX) enriched by the even-like `evenEnrich`, or every
subdomain that stands a chance (MIN) enriched by the antiexhaustive `Exhaustification.oMinus`;
and whether σ presupposes proper strengthening. Pure negative-polarity items (*mai*, *ever*) are
MAX; *any* is MIN with the plain σ, a negative-polarity item under negation and a universal
free-choice item elsewhere; Italian *qualsiasi* is MIN with the presuppositional σ, a pure
free-choice item; the existential free-choice items (*irgendein*, *uno N qualsiasi*) add the
uniqueness implicature of their indefinite morphology and distribute over the worlds of a modal,
after [kratzer-shimoyama-2002].

The theorems derive the distributions from the operators. `evenEnrich_eq_or_eq_empty` makes
even-like enrichment vacuous or contradictory, so a MAX item is confined to the positions where
its alternatives are entailed (`evenEnrich_image_antitone_eq`) and can never meet the
presupposition of the strong σ, footnote 33. `oMinus_dMinAlts_iff` is the universal reading
(63d); `not_properlyStrengthens_oMinus_antitone` is why *qualsiasi* has no negative-polarity
construal, (70)–(72), while `properlyStrengthens_oMinus` is the positive case (71).
`oMinus_exactlyOne_eq_empty` is the clash of the uniqueness and free-choice implicatures that
keeps an existential free-choice item out of episodic sentences, (82), and
`exactlyOne_consistent_under_possibility` exhibits the distribution over worlds that a
possibility modal restores, (84)–(85). The typological observation the paper opens with, that
*any* does double duty while *mai* and *qualunque* do not, is read off [haspelmath-1997]'s
Italian and English series. The paper's examples are the rows of
`Data/Examples/Chierchia2006.json`.

## Implementation notes

The relation "stronger relative to the common ground" in the definition of E, (50a), is taken
as entailment. Enrichment operations apply to propositions, sets of worlds; the freezing
operator σ and the recursive computation of enriched meanings (appendix A3) are not represented,
so an LF's two scopes for σ and negation appear as the two compositions of an enrichment with
an antitone context. MAX alternatives are any family of subdomain existentials; MIN alternatives
are `Exhaustification.dMinAlts`, the subdomains containing a possible witness, (61b).

## TODO

* The intervention effect (86)–(87), a DP between σ and the item, is a syntactic stipulation in
  the paper and is not formalized.

## References

* [chierchia-2006]
* [kadmon-landman-1993]
* [kratzer-shimoyama-2002]
* [haspelmath-1997]
-/

namespace Chierchia2006

open Exhaustification ModalLogic Indefinite

/-! ### The lexicon of polarity-sensitive items, (94) -/

/-- The domain alternatives an item activates: the large subdomains, (46), or every subdomain
that stands a chance, (56) and (61b). -/
inductive DomainAlternatives where
  | max
  | min
  deriving DecidableEq, Repr

/-- The parameters of a polarity-sensitive item in (94): the size of its domain alternatives,
whether indefinite morphology adds the uniqueness implicature, and whether the freezing
operator σ it selects presupposes proper strengthening, (72). -/
structure PSIProfile where
  alternatives : DomainAlternatives
  scalar : Bool
  presuppositional : Bool
  deriving DecidableEq, Repr

/-- Pure negative-polarity items, *mai*, *ever*, *alcuno*: σ[D-MAX]. -/
def pureNPI : PSIProfile := ⟨.max, false, false⟩

/-- *Any*: σ[D-MIN], a negative-polarity item under negation and a universal free-choice item
elsewhere. -/
def npiFci : PSIProfile := ⟨.min, false, false⟩

/-- The pure universal free-choice items *qualsiasi*, *qualunque*: the presuppositional σ over
MIN alternatives. -/
def pureFci : PSIProfile := ⟨.min, false, true⟩

/-- German *irgendein*: σ[MIN, SCAL], an existential free-choice item with negative-polarity
uses. -/
def existentialNpiFci : PSIProfile := ⟨.min, true, false⟩

/-- Italian *uno N qualsiasi*: the presuppositional σ over MIN alternatives with the uniqueness
implicature. -/
def existentialPureFci : PSIProfile := ⟨.min, true, true⟩

/-! ### Even-like enrichment of large alternatives, §4 -/

section Even

variable {W : Type*}

/-- Even-like enrichment `E`, (50a) and (108b): the prejacent, which is at least as strong as
every alternative. -/
def evenEnrich (C : Set (Set W)) (p : Set W) : Set W := {w | w ∈ p ∧ ∀ q ∈ C, p ⊆ q}

theorem evenEnrich_subset (C : Set (Set W)) (p : Set W) : evenEnrich C p ⊆ p := λ _ h => h.1

/-- The even-like implicature is a condition on the alternatives, not on the world: enrichment
is vacuous or a contradiction. -/
theorem evenEnrich_eq_or_eq_empty (C : Set (Set W)) (p : Set W) :
    evenEnrich C p = p ∨ evenEnrich C p = ∅ := by
  by_cases h : ∀ q ∈ C, p ⊆ q
  · exact .inl (Set.ext λ w => ⟨λ hw => hw.1, λ hw => ⟨hw, h⟩⟩)
  · exact .inr (Set.eq_empty_of_forall_notMem λ _ hw => h hw.2)

/-- An alternative the prejacent does not entail makes even-like enrichment a contradiction: the
deviance of a pure negative-polarity item at its existential, (47)–(48) and (52). -/
theorem evenEnrich_eq_empty_of_not_subset {C : Set (Set W)} {p q : Set W} (hq : q ∈ C)
    (h : ¬ p ⊆ q) : evenEnrich C p = ∅ :=
  Set.eq_empty_of_forall_notMem λ _ hw => h (hw.2 q hq)

/-- Under an antitone embedding, alternatives that each entail the prejacent are entailed by the
embedded prejacent, so even-like enrichment is vacuous: domain widening comes to fruition in a
downward-entailing context, (49) and (53). -/
theorem evenEnrich_image_antitone_eq {C : Set W → Set W} (hC : Antitone C) {A : Set (Set W)}
    {p : Set W} (hA : ∀ q ∈ A, q ⊆ p) : evenEnrich (C '' A) (C p) = C p :=
  Set.Subset.antisymm (evenEnrich_subset _ _)
    (λ _ hw => ⟨hw, by rintro _ ⟨q, hq, rfl⟩; exact hC (hA q hq)⟩)

/-- Footnote 33: an item triggering the even-like implicature can meet the presupposition of the
strong σ only by a contradiction, so pure negative-polarity items select the plain σ. -/
theorem eq_empty_of_properlyStrengthens_evenEnrich {C : Set (Set W)} {p : Set W}
    (h : ProperlyStrengthens (· ∈ evenEnrich C p) (· ∈ p)) : evenEnrich C p = ∅ :=
  (evenEnrich_eq_or_eq_empty C p).resolve_left λ heq =>
    not_properlyStrengthens_of_iff (λ w => by rw [heq]) h

end Even

/-! ### Antiexhaustiveness, §5 -/

section Antiexhaustive

variable {W E : Type*} (D : List E) (P : E → Set W)

/-- A subdomain existential with a witness outside another subdomain is not entailed by it: the
premise of (48), that every large alternative is stronger than the widest statement. -/
theorem existsIn_not_subset {D' : List E} {a : E} {w : W} (ha : a ∈ D) (hPa : P a w)
    (hD' : ∀ x ∈ D', ¬ P x w) : ¬ existsIn D P ⊆ existsIn D' P :=
  λ h => let ⟨x, hx, hPx⟩ := h ⟨a, ha, hPa⟩; hD' x hx hPx

/-- Negation over σ: the rhetorical reading of *any* and *qualunque* under negation, (64) and
(69), denies the universal. -/
theorem compl_oMinus_dMinAlts_iff (w : W) (hD : ∃ a ∈ D, ∃ v, P a v) :
    w ∈ (oMinus (dMinAlts D P) (existsIn D P))ᶜ ↔
      ¬ ∀ a ∈ D, (∃ v, P a v) → P a w := by
  rw [Set.mem_compl_iff, ← oMinus_dMinAlts_iff D P w hD]
  rfl

/-- σ over negation: under an antitone context the free-choice implicature is entailed by the
assertion and vanishes, so *any* acts as a negative-polarity item, (65)–(66). -/
theorem oMinus_dMinAlts_antitone_eq {C : Set W → Set W} (hC : Antitone C) :
    oMinus (C '' dMinAlts D P) (C (existsIn D P)) = C (existsIn D P) :=
  oMinus_image_antitone_eq hC (by rintro _ ⟨D', hD', -, rfl⟩; exact existsIn_subset D P hD')

/-- The presupposition of the strong σ, (72), fails under an antitone context, since the
enrichment coincides with the plain statement: *qualunque* has no negative-polarity construal,
(70). -/
theorem not_properlyStrengthens_oMinus_antitone {C : Set W → Set W} (hC : Antitone C) :
    ¬ ProperlyStrengthens (· ∈ oMinus (C '' dMinAlts D P) (C (existsIn D P)))
      (· ∈ C (existsIn D P)) :=
  not_properlyStrengthens_of_iff λ w => by rw [oMinus_dMinAlts_antitone_eq D P hC]

/-- In a positive context the antiexhaustive enrichment properly strengthens the statement,
(71): a world where one possible witness is actual and another is not satisfies the statement
but not its enrichment. -/
theorem properlyStrengthens_oMinus {a b : E} {w : W} (ha : a ∈ D) (hb : b ∈ D) (hPa : P a w)
    (hbpos : ∃ v, P b v) (hnb : ¬ P b w) :
    ProperlyStrengthens (· ∈ oMinus (dMinAlts D P) (existsIn D P)) (· ∈ existsIn D P) :=
  ⟨λ _ h => h.1, w, ⟨a, ha, hPa⟩,
    λ h => hnb (antiexh_yields_universal D P w h b hb hbpos)⟩

/-- Under a possibility modal, the antiexhaustive enrichment is the free-choice distribution:
some possible witness is possible, and every possible witness is a possibility, (93c)–(93d). -/
theorem oMinus_diamond_dMinAlts_iff (R : W → W → Prop) (w : W) :
    oMinus ((◇[R] ·) '' dMinAlts D P) (◇[R] (existsIn D P)) w ↔
      ◇[R] (existsIn D P) w ∧ ∀ a ∈ D, (∃ v, P a v) → ◇[R] (P a) w := by
  constructor
  · rintro ⟨hp, hall⟩
    refine ⟨hp, λ a ha hpos => ?_⟩
    obtain ⟨v, hv, x, hx, hPx⟩ :=
      hall _ ⟨_, ⟨[a], by simpa using ha, ⟨a, List.mem_singleton_self a, hpos⟩, rfl⟩,
        rfl⟩
    obtain rfl := List.mem_singleton.1 hx
    exact ⟨v, hv, hPx⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rintro _ ⟨_, ⟨D', hD', ⟨b, hb, hbpos⟩, rfl⟩, rfl⟩
    obtain ⟨v, hv, hPb⟩ := h b (hD' b hb) hbpos
    exact ⟨v, hv, b, hb, hPb⟩

end Antiexhaustive

/-! ### Existential free-choice items, §6 -/

section Existential

variable {W E : Type*} (D : List E) (P : E → Set W)

/-- The exhaustified indefinite, (81b): exactly one member of the domain is a witness. -/
def exactlyOne (D : List E) : Set W := {w | ∃ x ∈ D, P x w ∧ ∀ y ∈ D, P y w → y = x}

/-- The D-variants of the exhaustified indefinite, (81c). -/
def exactlyOneAlts : Set (Set W) := dVariants (exactlyOne P) D (λ x => ∃ v, P x v)

/-- The clash of the uniqueness and free-choice implicatures, (82): with two possible witnesses,
exactly one member of each singleton subdomain and of their pair cannot all be witnesses, so an
existential free-choice item in an episodic sentence is contradictory. -/
theorem oMinus_exactlyOne_eq_empty {a b : E} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hapos : ∃ v, P a v) (hbpos : ∃ v, P b v) :
    oMinus (exactlyOneAlts D P) (exactlyOne P D) = ∅ := by
  refine Set.eq_empty_of_forall_notMem λ w ⟨_, hall⟩ => ?_
  obtain ⟨x, hx, hPx, -⟩ :=
    hall _ ⟨[a], by simpa using ha, ⟨a, List.mem_singleton_self a, hapos⟩, rfl⟩
  obtain rfl := List.mem_singleton.1 hx
  obtain ⟨y, hy, hPy, -⟩ :=
    hall _ ⟨[b], by simpa using hb, ⟨b, List.mem_singleton_self b, hbpos⟩, rfl⟩
  obtain rfl := List.mem_singleton.1 hy
  obtain ⟨z, -, -, huniq⟩ :=
    hall _ ⟨[x, y], by simp [ha, hb], ⟨x, by simp, hapos⟩, rfl⟩
  exact hab ((huniq x (by simp) hPx).trans (huniq y (by simp) hPy).symm)

/-- The worlds accessible from the evaluation world `0` in the model of (85). -/
private def accessible : Fin 3 → Fin 3 → Prop := λ w v => w = 0 ∧ v ≠ 0

/-- Doctor `d` is married exactly in world `d + 1`, the distribution of (85). -/
private def married : Fin 2 → Set (Fin 3) := λ d w => w = d.succ

/-- The rescue by a possibility modal, (84)–(85): two doctors, each married in one accessible
world, satisfy the modalized statement together with every modalized alternative. -/
theorem exactlyOne_consistent_under_possibility :
    oMinus ((◇[accessible] ·) '' exactlyOneAlts [0, 1] married)
      (◇[accessible] (exactlyOne married [0, 1])) 0 := by
  refine ⟨⟨1, ⟨rfl, by decide⟩, 0, by simp, rfl, λ y _ hy => ?_⟩, ?_⟩
  · exact Fin.succ_injective _ (hy.symm.trans (by decide : (1 : Fin 3) = Fin.succ 0))
  rintro _ ⟨_, ⟨D', hD', ⟨d, hd, -⟩, rfl⟩, rfl⟩
  exact ⟨d.succ, ⟨rfl, Fin.succ_ne_zero d⟩, d, hd, rfl,
    λ y _ hy => (Fin.succ_injective _ hy).symm⟩

end Existential

/-! ### Double duty on the implicational map -/

/-- Roughly half of the languages in [haspelmath-1997]'s survey use one series for negative
polarity and free choice, English among them: the *any*-series covers direct negation and free
choice. -/
theorem any_double_duty :
    ∃ e ∈ Haspelmath1997.english.forms,
      e.covers .directNeg = true ∧ e.covers .freeChoice = true := by
  decide

/-- The other half separate the two, as Romance does: no Italian series covering direct
negation covers free choice, and the free-choice series *-unque* covers no negation function. -/
theorem italian_separates_uses :
    ∀ e ∈ Haspelmath1997.italian.forms,
      (e.covers .directNeg = true → e.covers .freeChoice = false) ∧
        (e.covers .freeChoice = true →
          e.covers .directNeg = false ∧ e.covers .indirectNeg = false) := by
  decide

end Chierchia2006
