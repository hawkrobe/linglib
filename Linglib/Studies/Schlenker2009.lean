module

public import Linglib.Semantics.Presupposition.SyntacticEnvironment
public import Linglib.Semantics.Presupposition.BeliefEmbedding
public import Linglib.Studies.Heim1983

/-!
# Schlenker (2009): Local Contexts

This file formalizes the paper's theory of local contexts for the propositional fragment of its
language L, following the definitions and theorems of its Appendix C. A restriction on the
denotation of an expression is transparent in a syntactic environment, relative to a context set,
when conjoining it to any denotation of the expression's type changes the truth value at no world
of the context (`Presupposition.Transparent`). The incremental theory consults every good final of
the string up to the expression, the symmetric theory only the actual sentence. The local context
is the least transparent restriction, and a presupposition is satisfied when its local context
entails it. The paper's Transparency theory (C.8, `TranspI`, `TranspS`) requires the presupposition
itself to be transparent at every trigger; local satisfaction (C.17, `SatI`, `SatS`) requires the
local context to entail it.

In the propositional fragment every local context exists, and the incremental local context of any
position is [karttunen-1974-presupposition]'s (`isLocalContext_goodFinals`): an argument of negation
and the first argument of a connective take the global context, and the second argument of a
conjunction or a conditional takes the context updated with the first, the second disjunct the
context updated with the first disjunct's negation (the paper's (18)–(33)). The two theories are
then equivalent (C.21, `satI_iff_transpI`, `satS_iff_transpS`), the incremental one predicts
presuppositions at least as strong as the symmetric one (C.20, `SatI.satS`), and incremental
Transparency is admittance by the dynamic semantics of [heim-1983], with [beaver-2001]'s
disjunction (Theorem 1 of C.9, `transpI_iff_admits`; its update clause is `Formula.ccp_get`), so
that incremental satisfaction is too (C.22, `satI_iff_admits`). The examples (20)–(32) of the
paper follow. Belief reports use two-dimensional denotations: the local context of the complement
of *believe* is the set of pairs of an utterance world in the context and a world doxastically
accessible from it (`isLocalContext_believe`), which is the substrate's `BeliefLocalCtx.atWorld`.

## Implementation notes

* Only the propositional fragment of L is formalized. Theorem 2 of C.9 and C.23 need quantifiers.
* The continuations a theory consults at a gap are represented by the set of functions from the
  gap's truth set to the sentence's, one for each continuation (`goodFinals` for the incremental
  theory, the actual sentence for the symmetric one). A good final replaces the material after the
  gap; for the first argument of a conjunction or a disjunction the connective follows the gap in
  the string and is itself free (`SyntacticEnvironment.SameInitialString`).
* The paper quantifies over the expressions that may fill the gap and assumes that every
  proposition is denoted (C.3); here the gap's denotation ranges over all propositions.
* C.22's conditions Non-Triviality and Constancy concern quantificational clauses and domains, so
  they hold trivially in the propositional fragment and are omitted. Since local contexts exist
  there (C.16), the general definition of satisfaction (C.18) agrees with the special one (C.19)
  and only the special one is defined.

## References

* [schlenker-2009]
* [karttunen-1974-presupposition]
* [heim-1983]
* [beaver-2001]
* [heim-1992]
-/

@[expose] public section

namespace Schlenker2009

open Presupposition Presupposition.BeliefEmbedding Heim1983 DynamicSemantics

variable {Atom W : Type*} (I : Atom → Set W)

/-! ### Transparency and local satisfaction -/

/-- The incremental theory consults at a gap one continuation for each good final (C.8.i, C.10). -/
def goodFinals (K : SyntacticEnvironment Atom) : Set (Set W → Set W) :=
  (·.truth I) '' {K' | K.SameInitialString K'}

/-- C.8.i: a formula satisfies incremental Transparency in `C` when at every trigger the
presupposition is a transparent restriction for every good final. -/
def TranspI (C : Set W) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, Transparent C (goodFinals I o.1) (I o.2.1)

/-- C.8.ii: a formula satisfies symmetric Transparency in `C` when at every trigger the
presupposition is a transparent restriction for the actual sentence. -/
def TranspS (C : Set W) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, Transparent C {o.1.truth I} (I o.2.1)

/-- C.17: incremental local satisfaction: at every trigger, the incremental local context entails
the presupposition. -/
def SatI (C : Set W) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, Satisfied C (goodFinals I o.1) ⟨(· ∈ I o.2.1), (· ∈ I o.2.2)⟩

/-- C.17: symmetric local satisfaction: at every trigger, the symmetric local context entails the
presupposition. -/
def SatS (C : Set W) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, Satisfied C {o.1.truth I} ⟨(· ∈ I o.2.1), (· ∈ I o.2.2)⟩

theorem isTruthFunctional_of_mem_goodFinals {K : SyntacticEnvironment Atom}
    {f : Set W → Set W} (hf : f ∈ goodFinals I K) : IsTruthFunctional f := by
  obtain ⟨K', -, rfl⟩ := hf
  exact SyntacticEnvironment.isTruthFunctional_truth I K'

theorem isTruthFunctional_of_mem_singleton {K : SyntacticEnvironment Atom}
    {f : Set W → Set W} (hf : f ∈ ({K.truth I} : Set (Set W → Set W))) : IsTruthFunctional f :=
  hf ▸ SyntacticEnvironment.isTruthFunctional_truth I K

/-! ### Local contexts in the propositional fragment -/

/-- C.16 with §2.3: the incremental local context of any gap is
[karttunen-1974-presupposition]'s. -/
theorem isLocalContext_goodFinals [Nonempty Atom] (K : SyntacticEnvironment Atom) (C : Set W) :
    IsLocalContext C (goodFinals I K) (K.localContext I C) := by
  have h := isLocalContext_of_isTruthFunctional (C := C) (env := goodFinals I K) fun _ hf ↦
    isTruthFunctional_of_mem_goodFinals I hf
  rwa [show {w | ∃ f ∈ goodFinals I K, DependsAt f w} = K.localContext I Set.univ from
    Set.ext fun w ↦ Set.exists_mem_image.trans
      (SyntacticEnvironment.exists_dependsAt_iff I K w),
    ← SyntacticEnvironment.localContext_eq_inter] at h

/-- (18), (27): the first argument of a connective takes the global context. -/
theorem isLocalContext_left [Nonempty Atom] (c : Connective) (G : Formula Atom) (C : Set W) :
    IsLocalContext C (goodFinals I [.left c G]) C :=
  isLocalContext_goodFinals I _ C

/-- (21): negation is a hole. -/
theorem isLocalContext_not [Nonempty Atom] (C : Set W) :
    IsLocalContext C (goodFinals I [(.not : SyntacticEnvironment.Step Atom)]) C :=
  isLocalContext_goodFinals I _ C

/-- (24), (30), (33): the second argument of a conjunction or a conditional takes the context
updated with the first, the second disjunct the context updated with the first's negation. -/
theorem isLocalContext_right [Nonempty Atom] (c : Connective) (F : Formula Atom) (C : Set W) :
    IsLocalContext C (goodFinals I [.right c F]) (c.localContext C (F.truth I)) :=
  isLocalContext_goodFinals I _ C

/-! ### Transparency, satisfaction and dynamic semantics -/

/-- C.21 (incremental): local satisfaction is Transparency. -/
theorem satI_iff_transpI (C : Set W) (F : Formula Atom) : SatI I C F ↔ TranspI I C F :=
  forall₂_congr fun _ _ ↦
    satisfied_iff_transparent (fun _ hf ↦ isTruthFunctional_of_mem_goodFinals I hf) _

/-- C.21 (symmetric): local satisfaction is Transparency. -/
theorem satS_iff_transpS (C : Set W) (F : Formula Atom) : SatS I C F ↔ TranspS I C F :=
  forall₂_congr fun _ _ ↦
    satisfied_iff_transparent (fun _ hf ↦ isTruthFunctional_of_mem_singleton I hf) _

theorem TranspI.transpS {C : Set W} {F : Formula Atom} (h : TranspI I C F) : TranspS I C F :=
  fun o ho ↦ (h o ho).anti <| Set.singleton_subset_iff.2 <|
    Set.mem_image_of_mem (·.truth I) (SyntacticEnvironment.SameInitialString.refl o.1)

/-- C.20: incremental satisfaction predicts presuppositions at least as strong as symmetric
satisfaction. -/
theorem SatI.satS {C : Set W} {F : Formula Atom} (h : SatI I C F) : SatS I C F :=
  (satS_iff_transpS I C F).2 (TranspI.transpS I ((satI_iff_transpI I C F).1 h))

/-- Theorem 1 of C.9: incremental Transparency is admittance by the formula's context change
potential, which updates the context to its worlds at which the formula is true
(`Formula.ccp_get`). -/
theorem transpI_iff_admits (C : Set W) (F : Formula Atom) :
    TranspI I C F ↔ (F.ccp I).Admits C := by
  rw [Formula.admits_ccp_iff]
  have henv {K : SyntacticEnvironment Atom} : ∀ f ∈ goodFinals I K, IsTruthFunctional f :=
    fun _ hf ↦ isTruthFunctional_of_mem_goodFinals I hf
  have hdep [Nonempty Atom] (K : SyntacticEnvironment Atom) (w : W) :
      (∃ f ∈ goodFinals I K, DependsAt f w) ↔ w ∈ K.localContext I Set.univ :=
    Set.exists_mem_image.trans (SyntacticEnvironment.exists_dependsAt_iff I K w)
  refine ⟨fun h w hw ↦ (Formula.filter_presup_iff I F w).2 fun o ho hl ↦ ?_,
    fun h o ho ↦ (transparent_iff_subset henv).2 fun w ⟨hw, hl⟩ ↦ ?_⟩
  · have : Nonempty Atom := ⟨o.2.1⟩
    exact (transparent_iff_subset henv).1 (h o ho) ⟨hw, (hdep o.1 w).2 hl⟩
  · have : Nonempty Atom := ⟨o.2.1⟩
    exact (Formula.filter_presup_iff I F w).1 (h hw) o ho ((hdep o.1 w).1 hl)

/-- C.22: incremental satisfaction is admittance by the formula's context change potential. -/
theorem satI_iff_admits (C : Set W) (F : Formula Atom) : SatI I C F ↔ (F.ccp I).Admits C :=
  (satI_iff_transpI I C F).trans (transpI_iff_admits I C F)

/-! ### Examples (§2.3) -/

variable {p p' q q' : Atom} {C : Set W}

/-- (20): `(pp' and q)` and `(pp' or q)` presuppose `p`. -/
theorem satI_initial_iff {c : Connective} (hc : c ≠ .cond) :
    SatI I C (.bin c (.trigger p p') (.atom q)) ↔ C ⊆ I p := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  cases c <;> simp_all [Set.subset_def, Formula.filter, Connective.filter, PartialProp.andFilter,
    PartialProp.orFilter] <;> exact Iff.rfl

/-- (23): `(not pp')` presupposes `p`. -/
theorem satI_not_iff : SatI I C (.not (.trigger p p')) ↔ C ⊆ I p := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  rfl

/-- (26): `(p and qq')` presupposes `(if p . q)`. -/
theorem satI_and_iff :
    SatI I C (.bin .conj (.atom p) (.trigger q q')) ↔
      C ⊆ (Formula.bin .cond (.atom p) (.atom q)).truth I := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  simp [Set.subset_def, Formula.filter, Formula.truth, Connective.filter, Connective.eval,
    PartialProp.andFilter]
  exact Iff.rfl

/-- (29): `(if pp' . q)` presupposes `p`. -/
theorem satI_if_iff : SatI I C (.bin .cond (.trigger p p') (.atom q)) ↔ C ⊆ I p := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  simp [Set.subset_def, Formula.filter, Connective.filter, PartialProp.impFilter]
  exact Iff.rfl

/-- (32): `(if p . qq')` presupposes `(if p . q)`. -/
theorem satI_then_iff :
    SatI I C (.bin .cond (.atom p) (.trigger q q')) ↔
      C ⊆ (Formula.bin .cond (.atom p) (.atom q)).truth I := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  simp [Set.subset_def, Formula.filter, Formula.truth, Connective.filter, Connective.eval,
    PartialProp.impFilter]
  exact Iff.rfl

/-! ### Belief reports (§3.1.2) -/

/-- `(believe _)` with two-dimensional denotations, sets of pairs of an utterance world and a
world of evaluation: the report holds at the utterance world when the complement holds at
every world the agent's beliefs there allow. -/
def believe (dox : W → W → Prop) : Set (Set (W × W) → Set W) :=
  {fun d ↦ {w₀ | ∀ w, dox w₀ w → (w₀, w) ∈ d}}

/-- (52): the local context of the complement of *believe* pairs each utterance world of the
context with the worlds the agent's beliefs there allow, the substrate's
`BeliefLocalCtx.atWorld`. -/
theorem isLocalContext_believe {Agent : Type*} (blc : BeliefLocalCtx W Agent) :
    IsLocalContext blc.globalCtx (believe (blc.dox blc.agent))
      {q | q.2 ∈ blc.atWorld q.1} := by
  constructor
  · rintro _ rfl d w₀ hw₀
    exact ⟨fun h w hw ↦ (h w hw).2, fun h w hw ↦ ⟨⟨hw₀, hw⟩, h w hw⟩⟩
  · rintro x hx ⟨w₀, w⟩ ⟨hw₀, hw⟩
    exact ((hx _ rfl Set.univ w₀ hw₀).2 fun _ _ ↦ trivial) w hw |>.1

/-! ### The King conditional ([heim-1983]) -/

variable {king son bald : W → Prop}

/-- "If the king has a son, the king's son is bald": incremental satisfaction is admittance by
Heim's context change potential, both holding iff the context entails a king. -/
theorem satI_king_iff_admits {k s ks b : Atom} (hk : I k = {w | king w}) (hs : I s = {w | son w})
    (hks : I ks = {w | king w ∧ son w}) (C : Set W) :
    SatI I C (.bin .cond (.trigger k s) (.trigger ks b)) ↔
      (ifKingHasSon king son bald).Admits C := by
  rw [satI_iff_admits, king_admits_iff, Formula.admits_ccp_iff]
  simp only [Formula.filter, Connective.filter, PartialProp.impFilter, PartialProp.Admits,
    hk, hs, hks, Set.subset_def, Set.mem_ofPred_eq]
  exact ⟨fun h w hw ↦ (h w hw).1, fun h w hw ↦ ⟨h w hw, fun hsn ↦ ⟨h w hw, hsn⟩⟩⟩

end Schlenker2009
