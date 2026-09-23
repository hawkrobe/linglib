module

public import Linglib.Semantics.Reference.Rigidity
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Logic.Modal.Extensional

/-!
# Choice functions

The referential semantics of indefinites: a choice function picks an individual out of a
property, so an indefinite noun phrase denotes an individual rather than an existential
quantifier ([reinhart-1997], [winter-1997]), and its scope is the binding site of the function
variable rather than a quantifier-raising site. A choice function is *correct* when it picks a
member of every nonempty property (`CF.IsCorrect`). A *skolemized* choice function takes a
situation argument ([kratzer-1998-pseudoscope]); [owusu-2022] feeds the same situation to the
function and to an intensional restrictor (`SkolemCF.applyIntension`), and [mirrazi-2024]
lets an intensional operator bind that argument, so the function picks different individuals
at different worlds while its existential closure sits above negation (`SkolemCF.applyIntensionAt`
under `SitVarStatus.bound`). Under an operator extensional at the matrix situation the bound and
free construals coincide (`bound_free_collapse`), which is why a choice-functional indefinite
takes wide scope over negation; a situation quantifier separates them (`bound_free_diverge_box`).

## Main definitions

* `Reference.CF`, `CF.IsCorrect`: choice functions over a domain, and correctness.
* `Reference.SkolemCF`, `SkolemCF.applyIntension`, `SkolemCF.applyIntensionAt`: situation-indexed
  choice functions applied to intensional restrictors, with the situation argument free or bound
  (`Reference.SitVarStatus`).
* `Reference.IndefiniteAnalysis`, `IndefiniteAnalysis.CanPseudoDeDicto`: the existential and
  choice-functional analyses of an indefinite determiner, and which of them, with a world
  variable, yields the wide pseudo-scope de dicto reading.

## Main results

* `cf_wide_scope_specific`, `exists_narrow_scope_under_negation`: the choice-functional
  indefinite under negation is specific, where the existential one may take narrow scope.
* `bound_free_collapse`, `bound_free_diverge_box`: extensional operators neutralize, and
  situation quantifiers separate, the free and bound construals of the situation argument.
* `isCorrect_some_of_apply`, `correct_cfs_disagree_on_some_sem`: a correct choice function
  witnesses the existential reading, and distinct correct functions commit to distinct witnesses.
* `CF.exists_isCorrect_iff_some_sem`, `CF.forall_isCorrect_iff_every_sem`: quantifying over
  correct choice functions gives the existential and universal readings on a nonempty restrictor.
* `CF.exists_isCorrect_forall_iff`: a choice function whose restrictor contains a bound variable
  takes no scope relative to the binder.

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

/-- A skolemized choice function is a choice function at each situation
([kratzer-1998-pseudoscope]). -/
def SkolemCF (S E : Type*) := S → CF E

/-- A skolemized choice function is correct when it is correct at every situation. -/
def SkolemCF.IsCorrect (f : SkolemCF S E) : Prop := ∀ s, (f s).IsCorrect

/-- The two analyses of an indefinite determiner are an existential quantifier, scoping by
quantifier raising, and a choice function, scoping by the binding of its situation variable. -/
inductive IndefiniteAnalysis where
  | existential
  | choiceFunction
  deriving DecidableEq, Repr

/-- An indefinite yields the wide pseudo-scope de dicto reading when it is choice-functional and
its determiner carries a world variable ([mirrazi-2024]): existential closure of the function
above negation, with the function's output varying across the worlds of the operator. -/
def IndefiniteAnalysis.CanPseudoDeDicto : IndefiniteAnalysis → Bool → Prop
  | .choiceFunction, hasWorldVar => hasWorldVar = true
  | .existential, _ => False

instance : ∀ t b, Decidable (IndefiniteAnalysis.CanPseudoDeDicto t b)
  | .choiceFunction, _ => inferInstanceAs (Decidable (_ = true))
  | .existential, _ => inferInstanceAs (Decidable False)

/-! ### Scope under negation -/

/-- The wide-scope reading of a choice-functional indefinite under negation is specific: a
correct function picks a restrictor member, so its failing the predicate witnesses a restrictor
member that fails it. -/
theorem cf_wide_scope_specific {f : CF E} (hf : f.IsCorrect) {N VP : E → Prop} (hN : ∃ x, N x)
    (h : ¬ VP (f N)) : ∃ x, N x ∧ ¬ VP x :=
  ⟨f N, hf N hN, h⟩

/-- An existential indefinite can take narrow scope under negation, since the negated
existential is satisfiable on a nonempty restrictor. -/
theorem exists_narrow_scope_under_negation {N VP : E → Prop} (h : ∀ x, N x → ¬ VP x) :
    ¬ ∃ x, N x ∧ VP x :=
  fun ⟨x, hN, hVP⟩ ↦ h x hN hVP

/-! ### The situation argument, free or bound -/

/-- The status of a situation variable ([elbourne-2013]): free, resolved to a contextually
salient situation, or bound by an intensional operator. -/
inductive SitVarStatus where
  | free
  | bound
  deriving DecidableEq, Repr

/-- A skolemized choice function applied at `s` to an intensional restrictor evaluated at the
same `s`: [owusu-2022]'s entry for Akan *bí*, the situation shared by function and restrictor. -/
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
on a rigid restrictor: [mirrazi-2024]'s answer to the fixed-set problem. -/
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
    ∃ (S E : Type) (R : S → S → Prop) (f : SkolemCF S E) (P : S → E → Prop) (VP : E → S → Prop)
      (s₀ : S), box R (fun s ↦ VP (f.applyIntensionAt .bound s s₀ P) s) s₀ ∧
        ¬ box R (fun s ↦ VP (f.applyIntensionAt .free s s₀ P) s) s₀ :=
  ⟨Bool, Bool, ⊤, fun s _ ↦ s, fun s x ↦ x = s, fun x s ↦ x = s, false, fun _ _ ↦ rfl,
    fun h ↦ Bool.noConfusion (h true trivial)⟩

/-- `box` is not extensional, so the operator side of the dichotomy is genuine. -/
theorem box_not_isExtensionalAt :
    ∃ (S : Type) (R : S → S → Prop) (s₀ : S), ¬ IsExtensionalAt (box R) s₀ :=
  ⟨Bool, ⊤, false, not_isExtensionalAt_iff_exists_witness.mpr
    ⟨fun s ↦ s = s, fun s ↦ false = s, rfl,
      fun h ↦ Bool.noConfusion ((iff_of_eq h).mp (fun _ _ ↦ rfl) true trivial)⟩⟩

/-! ### The existential reading

A correct choice function witnesses the existential reading `some_sem` on a nonempty
restrictor, but the two analyses are not equivalent: the existential reading asserts the
existence of a witness, the choice function commits to one, and distinct correct functions
commit differently. -/

open Quantifier Quantifier.GQ Quantifier.NP

/-- A correct choice function whose output satisfies the predicate witnesses the existential
reading. -/
theorem isCorrect_some_of_apply {f : CF E} (hf : f.IsCorrect) {N VP : E → Prop} (hN : ∃ x, N x)
    (hVP : VP (f N)) : some_sem N VP :=
  ⟨f N, hf N hN, hVP⟩

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
theorem CF.exists_isCorrect_iff_some_sem {N : E → Prop} (hN : ∃ x, N x) (VP : E → Prop) :
    (∃ f : CF E, f.IsCorrect ∧ VP (f N)) ↔ some_sem N VP :=
  ⟨fun ⟨_, hf, h⟩ ↦ isCorrect_some_of_apply hf hN h, fun ⟨_, hx, h⟩ ↦
    let ⟨f, hf, hfx⟩ := CF.exists_isCorrect_apply_eq hx; ⟨f, hf, hfx ▸ h⟩⟩

/-- Universal quantification over correct choice functions is the universal reading, on a
nonempty restrictor. -/
theorem CF.forall_isCorrect_iff_every_sem {N : E → Prop} (hN : ∃ x, N x) (VP : E → Prop) :
    (∀ f : CF E, f.IsCorrect → VP (f N)) ↔ every_sem N VP :=
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
relative to the binder: since the restrictor already varies with the variable, one correct
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

/-- Two correct choice functions disagree on the same restrictor and predicate. Over `Bool`,
the function preferring `true` hits the witness of `(· = true)` and the one preferring `false`
does not. -/
theorem correct_cfs_disagree_on_some_sem :
    ∃ f₁ f₂ : CF Bool, f₁.IsCorrect ∧ f₂.IsCorrect ∧
      ∃ N VP : Bool → Prop, some_sem N VP ∧ VP (f₁ N) ∧ ¬ VP (f₂ N) := by
  classical
  refine ⟨fun P ↦ if P true then true else false, fun P ↦ if P false then false else true,
    ?_, ?_, fun _ ↦ True, (· = true), ⟨true, trivial, rfl⟩, by simp, by simp⟩
  · rintro P ⟨x, hx⟩
    by_cases h : P true
    · simp [h]
    · cases x <;> simp_all
  · rintro P ⟨x, hx⟩
    by_cases h : P false
    · simp [h]
    · cases x <;> simp_all

end Reference
