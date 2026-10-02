module

public import Linglib.Semantics.Reference.Rigidity
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Logic.Modal.Extensional

/-!
# Choice functions

A choice function picks an individual out of a property. For Reinhart and for Winter an
indefinite noun phrase denotes the value of such a function rather than an existential
quantifier, and it scopes where the function variable is bound rather than where a quantifier
would raise to. A choice function is *correct* when it picks a member of every nonempty property.
Kratzer gives the function implicit arguments, skolem indices that are bound like pronouns;
Mirrazi adds a world argument that an intensional operator can bind, so that the function picks
different individuals at different worlds, and Owusu feeds the same situation to the function and
to the restrictor. Under an operator that is extensional at the matrix situation the bound and
free construals of that argument coincide, so a choice-functional indefinite takes wide scope
over negation, while a situation quantifier separates them.

## Main definitions

* `Reference.CF`, `CF.IsCorrect`: choice functions over a domain, and correctness.
* `Reference.SkolemCF`, `SkolemCF.applyIntension`, `SkolemCF.applyIntensionAt`: situation-indexed
  choice functions applied to intensional restrictors, with the situation argument free or bound
  (`Reference.SitVarStatus`).
* `Reference.IndefiniteAnalysis`, `IndefiniteAnalysis.CanPseudoDeDicto`: the existential and
  choice-functional analyses of an indefinite determiner, and which of them, with a world
  variable, yields the wide pseudo-scope de dicto reading.

## Main results

* `bound_free_collapse`, `bound_free_diverge_box`: extensional operators neutralize, and
  situation quantifiers separate, the free and bound construals of the situation argument.
* `isCorrect_some_of_apply`, `CF.IsCorrect.forall_apply_iff_some_iff`: a correct choice
  function witnesses the existential reading, and agrees with it on every predicate only when the
  restrictor has a single member.
* `CF.exists_isCorrect_iff_some`, `CF.forall_isCorrect_iff_every`: quantifying over
  correct choice functions gives the existential and universal readings on a nonempty restrictor.
* `CF.exists_isCorrect_forall_iff`, `CF.exists_isCorrect_forall_iff_of_injective`,
  `SkolemCF.exists_isCorrect_forall_iff`: a choice function whose restrictor contains a bound
  variable, and a skolemized one whose index is bound, take no scope relative to the binder.

## References

* [reinhart-1997]
* [winter-1997]
* [kratzer-1998-pseudoscope]
* [owusu-2022]
* [mirrazi-2024]
* [elbourne-2013]
* [zimmermann-2026]
-/

@[expose] public section

namespace Reference

variable {S E : Type*}

/-- A choice function sends a property to an individual ([reinhart-1997]). -/
def CF (E : Type*) := (E → Prop) → E

/-- A choice function is correct when it picks a member of every nonempty property. -/
def CF.IsCorrect (f : CF E) : Prop := ∀ P : E → Prop, (∃ x, P x) → P (f P)

/-- A skolemized choice function is a choice function at each index, an individual or a
situation ([kratzer-1998-pseudoscope]). -/
def SkolemCF (S E : Type*) := S → CF E

/-- A skolemized choice function is correct when it is correct at every index. -/
def SkolemCF.IsCorrect (f : SkolemCF S E) : Prop := ∀ s, (f s).IsCorrect

/-- The two analyses of an indefinite determiner are an existential quantifier, scoping by
quantifier raising, and a choice function, scoping by the binding of its situation variable. -/
inductive IndefiniteAnalysis where
  | existential
  | choiceFunction
  deriving DecidableEq, Repr

/-- An indefinite yields the wide pseudo-scope de dicto reading when it is choice-functional and
its determiner carries a world variable ([mirrazi-2024]). The function is then existentially
closed above negation while its output varies across the worlds of the operator. -/
def IndefiniteAnalysis.CanPseudoDeDicto : IndefiniteAnalysis → Bool → Prop
  | .choiceFunction, hasWorldVar => hasWorldVar = true
  | .existential, _ => False

instance : ∀ t b, Decidable (IndefiniteAnalysis.CanPseudoDeDicto t b)
  | .choiceFunction, _ => inferInstanceAs (Decidable (_ = true))
  | .existential, _ => inferInstanceAs (Decidable False)

/-! ### The situation argument, free or bound -/

/-- A situation variable is free, resolved to a contextually salient situation, or bound by an
intensional operator ([elbourne-2013]). -/
inductive SitVarStatus where
  | free
  | bound
  deriving DecidableEq, Repr

/-- `f.applyIntension s P` applies the skolemized choice function at `s` to the restrictor `P`
evaluated at the same `s`, as in [owusu-2022]'s entry for Akan *bí*. -/
def SkolemCF.applyIntension (f : SkolemCF S E) (s : S) (P : S → E → Prop) : E := f s (P s)

/-- On a rigid restrictor the intensional application is the extensional one. -/
theorem SkolemCF.applyIntension_const (f : SkolemCF S E) (s : S) (N : E → Prop) :
    f.applyIntension s (fun _ ↦ N) = f s N := rfl

/-- Intensional application with the situation argument free, anchored to the context
situation `s₀`, or bound, riding the local situation `sOp` of a scope-taking operator. -/
def SkolemCF.applyIntensionAt (f : SkolemCF S E) : SitVarStatus → S → S → (S → E → Prop) → E
  | .free, _, s₀, P => f.applyIntension s₀ P
  | .bound, sOp, _, P => f.applyIntension sOp P

/-- A world-skolemized choice function picks different individuals at different worlds even
on a rigid restrictor, which is [mirrazi-2024]'s answer to the fixed-set problem. -/
theorem SkolemCF.applyIntensionAt_bound_ne (f : SkolemCF S E) {w₁ w₂ : S} {P : E → Prop}
    (h : f w₁ P ≠ f w₂ P) :
    f.applyIntensionAt .bound w₁ w₂ (fun _ ↦ P) ≠ f.applyIntensionAt .bound w₂ w₁ (fun _ ↦ P) :=
  h

open ModalLogic

/-- Under an operator extensional at the matrix situation, the bound and free construals of the
situation argument are truth-conditionally indistinguishable, for any function and restrictor;
at pointwise negation this is wide scope only ([zimmermann-2026]). -/
theorem bound_free_collapse {O : (S → Prop) → S → Prop} {s₀ : S} (hO : IsExtensionalAt O s₀)
    (f : SkolemCF S E) (P : S → E → Prop) (VP : E → S → Prop) :
    O (fun s ↦ VP (f.applyIntensionAt .bound s s₀ P) s) s₀ ↔
      O (fun s ↦ VP (f.applyIntensionAt .free s s₀ P) s) s₀ :=
  iff_of_eq (hO _ _ rfl)

/-- A situation quantifier separates the bound and free construals. The witness has two
situations, a restrictor whose extension varies, and a function tracking its situation. -/
theorem bound_free_diverge_box :
    ∃ (S E : Type) (R : SetRel S S) (f : SkolemCF S E) (P : S → E → Prop) (VP : E → S → Prop)
      (s₀ : S), Box R (fun s ↦ VP (f.applyIntensionAt .bound s s₀ P) s) s₀ ∧
        ¬ Box R (fun s ↦ VP (f.applyIntensionAt .free s s₀ P) s) s₀ :=
  ⟨Bool, Bool, .univ, fun s _ ↦ s, fun s x ↦ x = s, fun x s ↦ x = s, false, fun _ _ ↦ rfl,
    fun h ↦ Bool.noConfusion (h true trivial)⟩

/-- `Box` is not extensional, so the operator side of the dichotomy is genuine. -/
theorem box_not_isExtensionalAt :
    ∃ (S : Type) (R : SetRel S S) (s₀ : S), ¬ IsExtensionalAt (Box R) s₀ :=
  ⟨Bool, .univ, false, not_isExtensionalAt_iff_exists_witness.mpr
    ⟨fun s ↦ s = s, fun s ↦ false = s, rfl,
      fun h ↦ Bool.noConfusion ((iff_of_eq h).mp (fun _ _ ↦ rfl) true trivial)⟩⟩

/-! ### The existential reading

A correct choice function witnesses the existential reading `GQ.some` on a nonempty
restrictor, but the two analyses are not equivalent: the existential reading asserts the
existence of a witness, the choice function commits to one, and distinct correct functions
commit differently. -/

open Quantifier Quantifier.GQ Quantifier.NP

/-- A correct choice function whose output satisfies the predicate witnesses the existential
reading. -/
theorem isCorrect_some_of_apply {f : CF E} (hf : f.IsCorrect) {N VP : E → Prop} (hN : ∃ x, N x)
    (hVP : VP (f N)) : GQ.some N VP :=
  ⟨f N, hf N hN, hVP⟩

/-- A correct choice function agrees with the existential reading on every predicate exactly
when its pick is the only member of the restrictor. -/
theorem CF.IsCorrect.forall_apply_iff_some_iff {f : CF E} (hf : f.IsCorrect) {N : E → Prop}
    (hN : ∃ x, N x) : (∀ VP : E → Prop, VP (f N) ↔ GQ.some N VP) ↔ ∀ x, N x → x = f N := by
  refine ⟨fun h x hx ↦ ((h (· = x)).mpr ⟨x, hx, rfl⟩).symm, fun h VP ↦
    ⟨isCorrect_some_of_apply hf hN, ?_⟩⟩
  rintro ⟨x, hx, hVP⟩
  rwa [h x hx] at hVP

/-- Every member of a property is the pick of some correct choice function. -/
theorem CF.exists_isCorrect_apply_eq {N : E → Prop} {x : E} (hx : N x) :
    ∃ f : CF E, f.IsCorrect ∧ f N = x := by
  classical
  refine ⟨fun P ↦ if P = N then x else if h : ∃ y, P y then h.choose else x, fun P hP ↦ ?_,
    by simp⟩
  beta_reduce
  split_ifs with hPN
  exacts [hPN ▸ hx, hP.choose_spec]

/-- Existential quantification over correct choice functions is the existential reading. -/
theorem CF.exists_isCorrect_iff_some {N : E → Prop} (hN : ∃ x, N x) (VP : E → Prop) :
    (∃ f : CF E, f.IsCorrect ∧ VP (f N)) ↔ GQ.some N VP :=
  ⟨fun ⟨_, hf, h⟩ ↦ isCorrect_some_of_apply hf hN h, fun ⟨_, hx, h⟩ ↦
    let ⟨f, hf, hfx⟩ := CF.exists_isCorrect_apply_eq hx; ⟨f, hf, hfx ▸ h⟩⟩

/-- Universal quantification over correct choice functions is the universal reading, on a
nonempty restrictor. -/
theorem CF.forall_isCorrect_iff_every {N : E → Prop} (hN : ∃ x, N x) (VP : E → Prop) :
    (∀ f : CF E, f.IsCorrect → VP (f N)) ↔ every N VP :=
  ⟨fun h _ hx ↦ let ⟨f, hf, hfx⟩ := CF.exists_isCorrect_apply_eq hx; hfx ▸ h f hf,
    fun h _ hf ↦ h _ (hf N hN)⟩

/-- On an empty restrictor a correct choice function is unconstrained, so universal
quantification over correct choice functions ranges over the whole domain, where the
universal reading is vacuous. -/
theorem CF.forall_isCorrect_iff_of_not_exists {N : E → Prop} (hN : ¬ ∃ x, N x) (VP : E → Prop) :
    (∀ f : CF E, f.IsCorrect → VP (f N)) ↔ ∀ x, VP x := by
  classical
  refine ⟨fun h x ↦ ?_, fun h f _ ↦ h _⟩
  have := h (fun P ↦ if hP : ∃ y, P y then hP.choose else x) fun P hP ↦ by
    beta_reduce
    split_ifs
    exact hP.choose_spec
  beta_reduce at this
  rwa [dite_eq_right hN] at this

/-- A choice function applied to a restrictor that contains a bound variable takes no scope
relative to the binder. Since the restrictor already varies with the variable, one correct
function can be assembled from the pointwise choices. -/
theorem CF.exists_isCorrect_forall_iff [Nonempty E] {ι : Type*} (R : ι → E → Prop)
    (VP : E → Prop) :
    (∃ f : CF E, f.IsCorrect ∧ ∀ i, VP (f (R i))) ↔
      ∀ i, ∃ f : CF E, f.IsCorrect ∧ VP (f (R i)) := by
  classical
  refine ⟨fun ⟨f, hf, h⟩ i ↦ ⟨f, hf, h i⟩, fun h ↦ ?_⟩
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    choose F hF hVP using h
    refine ⟨fun P ↦ if hP : ∃ i, P = R i then F hP.choose P else F i₀ P, fun P hP ↦ ?_,
      fun i ↦ ?_⟩
    · beta_reduce
      split_ifs <;> exact hF _ P hP
    · beta_reduce
      split_ifs with h'
      · have := hVP h'.choose
        rwa [← h'.choose_spec] at this
      · exact (h' ⟨i, rfl⟩).elim
  · obtain ⟨x⟩ := ‹Nonempty E›
    obtain ⟨f, hf, -⟩ := CF.exists_isCorrect_apply_eq (N := (· = x)) rfl
    exact ⟨f, hf, fun i ↦ (hι ⟨i⟩).elim⟩

/-- When distinct values of a bound variable give distinct restrictors, a choice function takes
no scope relative to the binder even if the predicate also contains the variable. -/
theorem CF.exists_isCorrect_forall_iff_of_injective [Nonempty E] {ι : Type*}
    {R : ι → E → Prop} (hR : Function.Injective R) (VP : ι → E → Prop) :
    (∃ f : CF E, f.IsCorrect ∧ ∀ i, VP i (f (R i))) ↔
      ∀ i, ∃ f : CF E, f.IsCorrect ∧ VP i (f (R i)) := by
  classical
  refine ⟨fun ⟨f, hf, h⟩ i ↦ ⟨f, hf, h i⟩, fun h ↦ ?_⟩
  choose F hF hVP using h
  obtain ⟨x⟩ := ‹Nonempty E›
  obtain ⟨g, hg, -⟩ := CF.exists_isCorrect_apply_eq (N := (· = x)) rfl
  refine ⟨fun P ↦ if hP : ∃ i, R i = P then F hP.choose P else g P, fun P hP ↦ ?_, fun i ↦ ?_⟩
  · beta_reduce
    split_ifs
    exacts [hF _ P hP, hg P hP]
  · beta_reduce
    split_ifs with hP
    · rw [show hP.choose = i from hR hP.choose_spec]
      exact hVP i
    · exact absurd ⟨i, rfl⟩ hP

/-- A skolemized choice function whose index a binder ranges over takes no scope relative to
the binder, since a correct function can be assembled from the choices at each index. -/
theorem SkolemCF.exists_isCorrect_forall_iff (N : S → E → Prop) (VP : S → E → Prop) :
    (∃ F : SkolemCF S E, F.IsCorrect ∧ ∀ s, VP s (F s (N s))) ↔
      ∀ s, ∃ f : CF E, f.IsCorrect ∧ VP s (f (N s)) := by
  refine ⟨fun ⟨F, hF, h⟩ s ↦ ⟨F s, hF s, h s⟩, fun h ↦ ?_⟩
  choose F hF hVP using h
  exact ⟨F, hF, hVP⟩

end Reference
