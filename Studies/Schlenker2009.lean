module

public import Linglib.Semantics.Presupposition.SyntacticEnvironment
public import Linglib.Semantics.Presupposition.QuantifiedClause
public import Studies.Heim1983
public import Studies.Heim1992

/-!
# Schlenker (2009): Local Contexts

A restriction on the denotation of an expression is transparent in a syntactic environment,
relative to a context set, when conjoining it to any denotation of the expression's type changes
the truth value at no world of the context. The local context of the expression is the least
transparent restriction, and a presupposition is satisfied when its local context entails it. The
incremental theory consults every good final of the string up to the expression, and the symmetric
theory only the actual sentence. This file covers the propositional fragment of the paper's
language after its Appendix C, its quantified clauses, the belief reports of its third section, and
the comparison with supervaluations and Strong Kleene logic in the appendix of Schlenker's 2008
manuscript, which the published appendix shortens.

## Main statements

* `isLocalContext_goodFinals`: the incremental local context of every position is Karttunen's,
  the global context except in a second argument, which takes the context updated with the first
  argument, or with its negation in a disjunction.
* `satI_iff_transpI`, `satS_iff_transpS`, `satI_iff_admits`: satisfaction in the local context is
  Transparency, and the incremental kind is admittance by Heim's context change potentials with
  Beaver's disjunction.
* `isLocalContext_believe`, `satisfied_believe_iff_admits`: the local context of the complement of
  *believe* pairs each world of the context with the worlds compatible with the agent's beliefs
  there, and it entails a presupposition iff the context admits the report under Heim's belief
  rule.
* `kleeneI_iff_superI`, `TranspI.kleeneI`, `transpS_not_kleeneS_not_superS`: checked
  incrementally, Kleene and supervaluation acceptability coincide and follow from Transparency,
  and checked symmetrically, Transparency accepts a sentence that both reject.
* `transparent_scope_iff_universal`, `not_exists_isLocalContext_infinitelyMany`,
  `scopeDefined_not_transparent_no`: in a quantified sentence Transparency gives universal
  projection under Non-Triviality, the scope of *infinitely many* has no local context, and with
  *no* Strong Kleene accepts a sentence that Transparency rejects.

## Implementation notes

* The gap's denotation ranges over all propositions, where the paper quantifies over the
  expressions that may fill the gap and assumes that every proposition is denoted.
* The continuations a theory consults at a gap are the functions from the gap's truth set to the
  sentence's, one for each good final for the incremental theory (`goodFinals`) and the actual
  sentence's for the symmetric one. For the first argument of a conjunction or a disjunction the
  connective follows the gap in the string and is itself free.
* A trigger whose presupposition fails at a world may be resolved either way (`resolve`).
  Supervaluation resolves all tokens of a trigger alike (`SuperDefined`) and Kleene each token
  separately (`TokenDefined`), which `tokenDefined_iff` shows is the Strong Kleene evaluation.
* The incremental Kleene and supervaluation results are proved by reducing acceptability to
  entailment of the filtering presupposition (`kleeneI_iff`, `superI_iff`), not by the
  manuscript's induction on the number of triggers.

## TODO

* Theorem 2 of C.9 is formalized for a single quantified clause, against the universal
  presupposition rather than a dynamic semantics for quantifiers, which linglib does not define.
  The conditions on quantificational clauses and domains in the equivalence with dynamic semantics
  hold trivially in the propositional fragment and are omitted there.

## References

* [schlenker-2009]
* [schlenker-2008b]
* [karttunen-1974-presupposition]
* [heim-1983]
* [beaver-2001]
* [heim-1992]
-/

@[expose] public section

namespace Schlenker2009

open Presupposition Heim1983 DynamicSemantics

variable {Atom W : Type*} (I : Atom → Set W)

/-! ### Transparency and local satisfaction -/

/-- The incremental theory consults at a gap one continuation for each good final (C.8.i, C.10). -/
def goodFinals (K : SyntacticEnvironment Atom) : Set (Set W → Set W) :=
  (·.truth I) '' {K' | K.SameInitialString K'}

/-- A formula satisfies incremental Transparency in `C` when at every trigger the presupposition is
a transparent restriction for every good final (C.8.i). -/
def TranspI (C : Set W) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, Transparent C (goodFinals I o.1) (I o.2.1)

/-- A formula satisfies symmetric Transparency in `C` when at every trigger the presupposition is a
transparent restriction for the actual sentence (C.8.ii). -/
def TranspS (C : Set W) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, Transparent C {o.1.truth I} (I o.2.1)

/-- Incremental local satisfaction holds of a formula in `C` when at every trigger the incremental
local context entails the presupposition (C.17). -/
def SatI (C : Set W) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, Satisfied C (goodFinals I o.1) (I o.2.1)

/-- Symmetric local satisfaction holds of a formula in `C` when at every trigger the symmetric local
context entails the presupposition (C.17). -/
def SatS (C : Set W) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, Satisfied C {o.1.truth I} (I o.2.1)

theorem isTruthFunctional_of_mem_goodFinals {K : SyntacticEnvironment Atom}
    {f : Set W → Set W} (hf : f ∈ goodFinals I K) : IsTruthFunctional f := by
  obtain ⟨K', -, rfl⟩ := hf
  exact SyntacticEnvironment.isTruthFunctional_truth I K'

theorem isTruthFunctional_of_mem_singleton {K : SyntacticEnvironment Atom}
    {f : Set W → Set W} (hf : f ∈ ({K.truth I} : Set (Set W → Set W))) : IsTruthFunctional f :=
  hf ▸ SyntacticEnvironment.isTruthFunctional_truth I K

/-! ### Local contexts in the propositional fragment -/

/-- The incremental local context of any gap is [karttunen-1974-presupposition]'s (C.16 with
§2.3). -/
theorem isLocalContext_goodFinals [Nonempty Atom] (K : SyntacticEnvironment Atom) (C : Set W) :
    IsLocalContext C (goodFinals I K) (K.localContext I C) := by
  have h := isLocalContext_of_isTruthFunctional (C := C) (env := goodFinals I K) fun _ hf ↦
    isTruthFunctional_of_mem_goodFinals I hf
  rwa [show {w | ∃ f ∈ goodFinals I K, DependsAt f w} = K.localContext I Set.univ from
    Set.ext fun w ↦ Set.exists_mem_image.trans
      (SyntacticEnvironment.exists_dependsAt_iff I K w),
    ← SyntacticEnvironment.localContext_eq_inter] at h

/-- The first argument of a connective takes the global context, (18) and (27). -/
theorem isLocalContext_left [Nonempty Atom] (c : Connective) (G : Formula Atom) (C : Set W) :
    IsLocalContext C (goodFinals I [.left c G]) C :=
  isLocalContext_goodFinals I _ C

/-- Negation is a hole, (21). -/
theorem isLocalContext_not [Nonempty Atom] (C : Set W) :
    IsLocalContext C (goodFinals I [(.not : SyntacticEnvironment.Step Atom)]) C :=
  isLocalContext_goodFinals I _ C

/-- The second argument of a conjunction or a conditional takes the context updated with the first,
the second disjunct the context updated with the first's negation, (24), (30) and (33). -/
theorem isLocalContext_right [Nonempty Atom] (c : Connective) (F : Formula Atom) (C : Set W) :
    IsLocalContext C (goodFinals I [.right c F]) (c.localContext C (F.truth I)) :=
  isLocalContext_goodFinals I _ C

/-- The symmetric local context of any gap is the worlds of the context at which the truth value
of the actual sentence depends on the gap. -/
theorem isLocalContext_symmetric (K : SyntacticEnvironment Atom) (C : Set W) :
    IsLocalContext C {K.truth I} (C ∩ {w | DependsAt (K.truth I) w}) := by
  simpa using isLocalContext_of_isTruthFunctional (C := C) fun _ hf ↦
    isTruthFunctional_of_mem_singleton I hf

/-! ### Transparency, satisfaction and dynamic semantics -/

/-- Incremental local satisfaction is incremental Transparency (C.21). -/
theorem satI_iff_transpI (C : Set W) (F : Formula Atom) : SatI I C F ↔ TranspI I C F :=
  forall₂_congr fun _ _ ↦
    satisfied_iff_transparent (fun _ hf ↦ isTruthFunctional_of_mem_goodFinals I hf) _

/-- Symmetric local satisfaction is symmetric Transparency (C.21). -/
theorem satS_iff_transpS (C : Set W) (F : Formula Atom) : SatS I C F ↔ TranspS I C F :=
  forall₂_congr fun _ _ ↦
    satisfied_iff_transparent (fun _ hf ↦ isTruthFunctional_of_mem_singleton I hf) _

theorem TranspI.transpS {C : Set W} {F : Formula Atom} (h : TranspI I C F) : TranspS I C F :=
  fun o ho ↦ (h o ho).anti <| Set.singleton_subset_iff.2 <|
    Set.mem_image_of_mem (·.truth I) (SyntacticEnvironment.SameInitialString.refl o.1)

/-- Incremental satisfaction predicts presuppositions at least as strong as symmetric satisfaction
(C.20). -/
theorem SatI.satS {C : Set W} {F : Formula Atom} (h : SatI I C F) : SatS I C F :=
  (satS_iff_transpS I C F).2 (TranspI.transpS I ((satI_iff_transpI I C F).1 h))

/-- Incremental Transparency is admittance by the formula's context change potential, which updates
the context to its worlds at which the formula is true (`Formula.ccp_get`; Theorem 1 of C.9). -/
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

/-- Incremental satisfaction is admittance by the formula's context change potential (C.22). -/
theorem satI_iff_admits (C : Set W) (F : Formula Atom) : SatI I C F ↔ (F.ccp I).Admits C :=
  (satI_iff_transpI I C F).trans (transpI_iff_admits I C F)

/-- Symmetric satisfaction requires each trigger's presupposition at the worlds of the context
at which the truth value of the sentence depends on the trigger. -/
theorem satS_iff (C : Set W) (F : Formula Atom) :
    SatS I C F ↔ ∀ o ∈ F.occurrences, C ∩ {w | DependsAt (o.1.truth I) w} ⊆ I o.2.1 :=
  forall₂_congr fun o _ ↦ satisfied_iff (isLocalContext_symmetric I o.1 C) _

/-! ### Examples (§2.3) -/

variable {p p' q q' : Atom} {C : Set W}

/-- `(pp' and q)` and `(pp' or q)` presuppose `p`, (20). -/
theorem satI_initial_iff {c : Connective} (hc : c ≠ .cond) :
    SatI I C (.bin c (.trigger p p') (.atom q)) ↔ C ⊆ I p := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  cases c <;> simp_all [Set.subset_def, Formula.filter, Connective.filter, PartialProp.andFilter,
    PartialProp.orFilter] <;> exact Iff.rfl

/-- `(not pp')` presupposes `p`, (23). -/
theorem satI_not_iff : SatI I C (.not (.trigger p p')) ↔ C ⊆ I p := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  rfl

/-- `(p and qq')` presupposes `(if p . q)`, (26). -/
theorem satI_and_iff :
    SatI I C (.bin .conj (.atom p) (.trigger q q')) ↔
      C ⊆ (Formula.bin .cond (.atom p) (.atom q)).truth I := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  simp [Set.subset_def, Formula.filter, Formula.truth, Connective.filter, Connective.eval,
    PartialProp.andFilter]
  exact Iff.rfl

/-- `(if pp' . q)` presupposes `p`, (29). -/
theorem satI_if_iff : SatI I C (.bin .cond (.trigger p p') (.atom q)) ↔ C ⊆ I p := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  simp [Set.subset_def, Formula.filter, Connective.filter, PartialProp.impFilter]
  exact Iff.rfl

/-- `(if p . qq')` presupposes `(if p . q)`, (32). -/
theorem satI_then_iff :
    SatI I C (.bin .cond (.atom p) (.trigger q q')) ↔
      C ⊆ (Formula.bin .cond (.atom p) (.atom q)).truth I := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  simp [Set.subset_def, Formula.filter, Formula.truth, Connective.filter, Connective.eval,
    PartialProp.impFilter]
  exact Iff.rfl

/-! ### A trigger alone, and symmetric conjunction -/

/-- A trigger standing alone presupposes `p` on the incremental theory. -/
theorem satI_trigger_iff : SatI I C (.trigger p p') ↔ C ⊆ I p := by
  rw [satI_iff_admits, Formula.admits_ccp_iff]
  rfl

/-- A trigger standing alone presupposes `p` on the symmetric theory. -/
theorem satS_trigger_iff : SatS I C (.trigger p p') ↔ C ⊆ I p := by
  simp [satS_iff, Formula.occurrences, SyntacticEnvironment.truth, DependsAt]

/-- On the symmetric theory `(pp' and q)` presupposes `(if q . p)`, since the local context of a
conjunct is the context updated with the other conjunct, whichever comes first. -/
theorem satS_and_left_iff :
    SatS I C (.bin .conj (.trigger p p') (.atom q)) ↔
      C ⊆ (Formula.bin .cond (.atom q) (.atom p)).truth I := by
  simp [satS_iff, Formula.occurrences, SyntacticEnvironment.truth, SyntacticEnvironment.Step.truth,
    DependsAt, Connective.eval, Formula.truth, Set.subset_def]

/-- On the symmetric theory `(q and pp')` presupposes `(if q . p)`, as on the incremental one. -/
theorem satS_and_right_iff :
    SatS I C (.bin .conj (.atom q) (.trigger p p')) ↔
      C ⊆ (Formula.bin .cond (.atom q) (.atom p)).truth I := by
  simp [satS_iff, Formula.occurrences, SyntacticEnvironment.truth, SyntacticEnvironment.Step.truth,
    DependsAt, Connective.eval, Formula.truth, Set.subset_def]

/-! ### Belief reports (§3.1.2) -/

section Belief

variable (Dox : W → Set W) {C : Set W}

/-- The meaning of `(believe _)` on two-dimensional denotations, sets of pairs of an utterance world
and a world of evaluation. The report holds at the utterance world when the complement holds at
every world compatible with the agent's beliefs there, (51). -/
def believe : Set (Set (W × W) → Set W) :=
  {fun d ↦ {w₀ | ∀ w ∈ Dox w₀, (w₀, w) ∈ d}}

/-- The local context of the complement of *believe* pairs each utterance world of the context with
the worlds compatible with the agent's beliefs there, (52). -/
theorem isLocalContext_believe :
    IsLocalContext C (believe Dox) {q | q.1 ∈ C ∧ q.2 ∈ Dox q.1} := by
  constructor
  · rintro _ rfl d w₀ hw₀
    exact ⟨fun h w hw ↦ (h w hw).2, fun h w hw ↦ ⟨⟨hw₀, hw⟩, h w hw⟩⟩
  · rintro x hx ⟨w₀, w⟩ ⟨hw₀, hw⟩
    exact ((hx _ rfl Set.univ w₀ hw₀).2 fun _ _ ↦ trivial) w hw |>.1

/-- The worlds of evaluation of the local context of the complement of *believe* are the image of
the context under the doxastic accessibility, the worlds compatible with the agent's beliefs at some
world of the context. -/
theorem image_snd_localContext_believe :
    Prod.snd '' {q : W × W | q.1 ∈ C ∧ q.2 ∈ Dox q.1} = (SetRel.ofSuccessors Dox).image C := by
  ext; simp [and_comm]

/-- A presupposition about the world of evaluation is satisfied in the complement of *believe* iff
every world compatible with the agent's beliefs at a world of the context satisfies it (p. 3:32). -/
theorem satisfied_believe_iff {P : Set W} :
    Satisfied C (believe Dox) (Prod.snd ⁻¹' P) ↔ (SetRel.ofSuccessors Dox).image C ⊆ P := by
  rw [satisfied_iff (isLocalContext_believe Dox), ← Set.image_subset_iff,
    image_snd_localContext_believe]

end Belief

/-- The complement's presupposition is satisfied in the complement of *believe* iff the context
admits the report under rule (18) of [heim-1992], which the paper calls the standard result obtained
in Heim's framework (p. 3:32). -/
theorem satisfied_believe_iff_admits {E : Type*} (Dox : E → W → Set W) (a : E)
    (p : PartialProp W) {C : Set W} :
    Satisfied C (believe (Dox a)) (Prod.snd ⁻¹' p.presup) ↔
      (Heim1992.believes Dox a (CCP.Partial.ofPartialProp p)).Admits C := by
  rw [satisfied_believe_iff, Heim1992.admits_believes_iff]

/-! ### The King conditional ([heim-1983]) -/

variable {king son bald : W → Prop}

/-- For *if the king has a son, the king's son is bald*, incremental satisfaction is admittance by
Heim's context change potential, both holding iff the context entails a king. -/
theorem satI_king_iff_admits {k s ks b : Atom} (hk : I k = {w | king w}) (hs : I s = {w | son w})
    (hks : I ks = {w | king w ∧ son w}) (C : Set W) :
    SatI I C (.bin .cond (.trigger k s) (.trigger ks b)) ↔
      (ifKingHasSon king son bald).Admits C := by
  rw [satI_iff_admits, king_admits_iff, Formula.admits_ccp_iff]
  simp only [Formula.filter, Connective.filter, PartialProp.impFilter, PartialProp.Admits,
    hk, hs, hks, Set.subset_def, Set.mem_ofPred_eq]
  exact ⟨fun h w hw ↦ (h w hw).1, fun h w hw ↦ ⟨h w hw, fun hsn ↦ ⟨h w hw, hsn⟩⟩⟩

/-! ### Strong Kleene and supervaluations (items 24–41 of [schlenker-2008b]) -/

section Trivalent

variable {w : W}

/-- The classical value at `w` of `F`, at the gap `K` of a larger formula, when each trigger whose
presupposition fails at `w` takes the value `ρ` gives its position and its type (items 24–25). -/
def resolve (w : W) (ρ : SyntacticEnvironment Atom → Atom → Atom → Prop) :
    SyntacticEnvironment Atom → Formula Atom → Prop
  | _, .atom p => w ∈ I p
  | K, .trigger p p' => w ∈ I p ∧ w ∈ I p' ∨ w ∉ I p ∧ ρ K p p'
  | K, .not F => ¬ resolve w ρ (.not :: K) F
  | K, .bin c F G => c.eval (resolve w ρ (.left c G :: K) F) (resolve w ρ (.right c F :: K) G)

/-- `F` is super-defined at `w` when every resolution of its trigger types gives it the same value
(item 25). -/
def SuperDefined (w : W) (F : Formula Atom) : Prop :=
  ∀ σ σ' : Atom → Atom → Prop, resolve I w (fun _ ↦ σ) [] F ↔ resolve I w (fun _ ↦ σ') [] F

/-- `F` is Kleene-defined at `w` when every resolution of its trigger tokens gives it the same value
(items 27–28). -/
def TokenDefined (w : W) (F : Formula Atom) : Prop :=
  ∀ ρ ρ', resolve I w ρ [] F ↔ resolve I w ρ' [] F

/-- Symmetric Kleene acceptability, by the Strong Kleene evaluation of item 40, which Theorem 41
(`tokenDefined_iff`) shows equivalent to items 27–28 (item 29b). -/
def KleeneS (C : Set W) (F : Formula Atom) : Prop := (F.strong I).Admits C

/-- Symmetric supervaluation acceptability (item 26b). -/
def SuperS (C : Set W) (F : Formula Atom) : Prop := ∀ w ∈ C, SuperDefined I w F

/-- A property holds of `F` incrementally when it holds of the string up to each trigger completed
by any good final without triggers (items 26a, 29a). -/
def Incrementally (P : Formula Atom → Prop) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, ∀ K', o.1.SameInitialString K' → K'.TriggerFreeFinal →
    P (K'.fill (.trigger o.2.1 o.2.2))

/-- Incremental Kleene acceptability (item 29a). -/
def KleeneI (C : Set W) (F : Formula Atom) : Prop :=
  ∀ w ∈ C, Incrementally (fun X ↦ (X.strong I).presup w) F

/-- Incremental supervaluation acceptability (item 26a). -/
def SuperI (C : Set W) (F : Formula Atom) : Prop :=
  ∀ w ∈ C, Incrementally (SuperDefined I w) F

/-! #### Resolutions -/

theorem resolve_congr {ρ ρ' : SyntacticEnvironment Atom → Atom → Atom → Prop}
    {K : SyntacticEnvironment Atom} (F : Formula Atom) (h : ∀ L, ρ (L ++ K) = ρ' (L ++ K)) :
    resolve I w ρ K F ↔ resolve I w ρ' K F := by
  induction F generalizing K with
  | atom p => rfl
  | trigger p p' => simp only [resolve, show ρ K = ρ' K from h []]
  | not F ih =>
    exact not_congr (ih fun L ↦ by
      have := h (L ++ [.not]); rwa [List.append_assoc, List.singleton_append] at this)
  | bin c F G ihF ihG =>
    simp only [resolve]
    rw [ihF fun L ↦ by
      have := h (L ++ [.left c G]); rwa [List.append_assoc, List.singleton_append] at this,
      ihG fun L ↦ by
      have := h (L ++ [.right c F]); rwa [List.append_assoc, List.singleton_append] at this]

/-- A resolution of trigger types does not depend on the positions. -/
theorem resolve_const (σ : Atom → Atom → Prop) (K K' : SyntacticEnvironment Atom)
    (F : Formula Atom) : resolve I w (fun _ ↦ σ) K F ↔ resolve I w (fun _ ↦ σ) K' F := by
  induction F generalizing K K' with
  | atom p => rfl
  | trigger p p' => rfl
  | not F ih => exact not_congr (ih _ _)
  | bin c F G ihF ihG => simp only [resolve]; rw [ihF _ (.left c G :: K'), ihG _ (.right c F :: K')]

private theorem append_left_ne_append_right {L L' K : SyntacticEnvironment Atom} {c c' : Connective}
    {F G : Formula Atom} : L ++ .left c G :: K ≠ L' ++ .right c' F :: K := by
  intro h
  have hl : L.length = L'.length := by simpa using congrArg List.length h
  obtain ⟨-, h'⟩ := List.append_inj h hl
  cases h'

open Classical in
/-- Resolutions of the two arguments of a binary connective combine into one. -/
private theorem exists_resolve_merge (c : Connective) (F G : Formula Atom)
    (K : SyntacticEnvironment Atom) (ρ₁ ρ₂ : SyntacticEnvironment Atom → Atom → Atom → Prop) :
    ∃ ρ, (resolve I w ρ (.left c G :: K) F ↔ resolve I w ρ₁ (.left c G :: K) F) ∧
      (resolve I w ρ (.right c F :: K) G ↔ resolve I w ρ₂ (.right c F :: K) G) :=
  ⟨fun K₀ ↦ if ∃ L, K₀ = L ++ .left c G :: K then ρ₁ K₀ else ρ₂ K₀,
    resolve_congr I F fun L ↦ ite_eq_left ⟨L, rfl⟩,
    resolve_congr I G fun _ ↦ ite_eq_right fun ⟨_, h⟩ ↦ append_left_ne_append_right h.symm⟩

/-- On its filtering presupposition, a formula takes its classical value under every resolution. -/
theorem resolve_of_filter_presup {F : Formula Atom} (h : (F.filter I).presup w)
    (ρ : SyntacticEnvironment Atom → Atom → Atom → Prop) (K : SyntacticEnvironment Atom) :
    resolve I w ρ K F ↔ w ∈ F.truth I := by
  induction F generalizing K with
  | atom p => rfl
  | trigger p p' =>
    have hp : w ∈ I p := h
    simp only [resolve, Formula.truth, Set.mem_inter_iff, hp, not_true_eq_false, false_and,
      or_false, true_and]
  | not F ih => exact not_congr (ih h _)
  | bin c F G ihF ihG =>
    rw [Formula.filter_presup_bin] at h
    simp only [resolve, Formula.truth, Set.mem_ofPred_eq, ihF h.1]
    cases c <;> simp only [Connective.eval, Connective.localContext, Set.mem_inter_iff,
      Set.mem_univ, true_and, Set.mem_compl_iff] at h ⊢
    · by_cases ht : w ∈ F.truth I
      · rw [ihG (h.2 ht)]
      · simp [ht]
    · by_cases ht : w ∈ F.truth I
      · rw [ihG (h.2 ht)]
      · simp [ht]
    · by_cases ht : w ∈ F.truth I
      · simp [ht]
      · rw [ihG (h.2 ht)]

/-! #### Theorem 41: Strong Kleene is supervaluation over trigger tokens -/

private theorem inf_ne_neg_one {a b : SignType} : a ⊓ b ≠ -1 ↔ a ≠ -1 ∧ b ≠ -1 := by
  cases a <;> cases b <;> decide
private theorem inf_ne_one {a b : SignType} : a ⊓ b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by
  cases a <;> cases b <;> decide
private theorem sup_ne_neg_one {a b : SignType} : a ⊔ b ≠ -1 ↔ a ≠ -1 ∨ b ≠ -1 := by
  cases a <;> cases b <;> decide
private theorem sup_ne_one {a b : SignType} : a ⊔ b ≠ 1 ↔ a ≠ 1 ∧ b ≠ 1 := by
  cases a <;> cases b <;> decide
private theorem neg_ne_neg_one {a : SignType} : -a ≠ -1 ↔ a ≠ 1 := by
  cases a <;> decide
private theorem neg_ne_one {a : SignType} : -a ≠ 1 ↔ a ≠ -1 := by
  cases a <;> decide

/-- A formula can be true under some resolution of its tokens iff its Strong Kleene value is not
false, and false under some resolution iff its value is not true. -/
private theorem exists_resolve_iff (F : Formula Atom) (K : SyntacticEnvironment Atom) :
    ((∃ ρ, resolve I w ρ K F) ↔ (F.strong I).eval w ≠ -1) ∧
      ((∃ ρ, ¬ resolve I w ρ K F) ↔ (F.strong I).eval w ≠ 1) := by
  induction F generalizing K with
  | atom p =>
    simp [resolve, Formula.strong, PartialProp.eval_eq_false_iff, PartialProp.eval_eq_true_iff]
  | trigger p p' =>
    have e₁ : (∃ ρ, resolve I w ρ K (.trigger p p')) ↔ (w ∈ I p ∧ w ∈ I p' ∨ w ∉ I p) :=
      ⟨fun ⟨_, h⟩ ↦ h.imp_right And.left,
        fun h ↦ ⟨fun _ _ _ ↦ True, h.imp_right fun h ↦ ⟨h, trivial⟩⟩⟩
    have e₀ : (∃ ρ, ¬ resolve I w ρ K (.trigger p p')) ↔ ¬ (w ∈ I p ∧ w ∈ I p') :=
      ⟨fun ⟨_, h⟩ hp ↦ h (.inl hp),
        fun h ↦ ⟨fun _ _ _ ↦ False, fun h' ↦ h'.elim h fun h'' ↦ h''.2⟩⟩
    refine ⟨e₁.trans ?_, e₀.trans ?_⟩ <;>
      simp only [Formula.strong, ne_eq, PartialProp.eval_eq_false_iff,
        PartialProp.eval_eq_true_iff]
    tauto
  | not F ih =>
    simp only [resolve, Formula.strong, PartialProp.eval_neg, neg_ne_neg_one, neg_ne_one, not_not]
    exact ⟨(ih _).2, (ih _).1⟩
  | bin c F G ihF ihG =>
    obtain ⟨hF₁, hF₀⟩ := ihF (.left c G :: K)
    obtain ⟨hG₁, hG₀⟩ := ihG (.right c F :: K)
    have merge := exists_resolve_merge I (w := w) c F G K
    cases c <;> simp only [resolve, Formula.strong, Connective.strong, Connective.eval,
      PartialProp.eval_andStrong, PartialProp.eval_orStrong, PartialProp.eval_neg, inf_ne_neg_one,
      inf_ne_one, sup_ne_neg_one, sup_ne_one, neg_ne_neg_one, neg_ne_one, ← hF₁, ← hF₀, ← hG₁,
      ← hG₀]
    · refine ⟨⟨fun ⟨ρ, a, b⟩ ↦ ⟨⟨ρ, a⟩, ⟨ρ, b⟩⟩, fun ⟨⟨ρ₁, a⟩, ⟨ρ₂, b⟩⟩ ↦ ?_⟩,
        ⟨fun ⟨ρ, h⟩ ↦ ?_, fun h ↦ h.elim (fun ⟨ρ, a⟩ ↦ ⟨ρ, fun h ↦ a h.1⟩)
          (fun ⟨ρ, b⟩ ↦ ⟨ρ, fun h ↦ b h.2⟩)⟩⟩
      · obtain ⟨ρ, e₁, e₂⟩ := merge ρ₁ ρ₂; exact ⟨ρ, e₁.2 a, e₂.2 b⟩
      · by_cases a : resolve I w ρ (.left .conj G :: K) F
        · exact .inr ⟨ρ, fun b ↦ h ⟨a, b⟩⟩
        · exact .inl ⟨ρ, a⟩
    · refine ⟨⟨fun ⟨ρ, h⟩ ↦ ?_, fun h ↦ h.elim (fun ⟨ρ, a⟩ ↦ ⟨ρ, fun h ↦ absurd h a⟩)
          (fun ⟨ρ, b⟩ ↦ ⟨ρ, fun _ ↦ b⟩)⟩,
        ⟨fun ⟨ρ, h⟩ ↦ ⟨⟨ρ, by tauto⟩, ⟨ρ, fun b ↦ h fun _ ↦ b⟩⟩, fun ⟨⟨ρ₁, a⟩, ⟨ρ₂, b⟩⟩ ↦ ?_⟩⟩
      · by_cases a : resolve I w ρ (.left .cond G :: K) F
        · exact .inr ⟨ρ, h a⟩
        · exact .inl ⟨ρ, a⟩
      · obtain ⟨ρ, e₁, e₂⟩ := merge ρ₁ ρ₂; exact ⟨ρ, fun h ↦ b (e₂.1 (h (e₁.2 a)))⟩
    · refine ⟨⟨fun ⟨ρ, h⟩ ↦ h.elim (fun a ↦ .inl ⟨ρ, a⟩) (fun b ↦ .inr ⟨ρ, b⟩),
          fun h ↦ h.elim (fun ⟨ρ, a⟩ ↦ ⟨ρ, .inl a⟩) (fun ⟨ρ, b⟩ ↦ ⟨ρ, .inr b⟩)⟩,
        ⟨fun ⟨ρ, h⟩ ↦ ⟨⟨ρ, fun a ↦ h (.inl a)⟩, ⟨ρ, fun b ↦ h (.inr b)⟩⟩,
          fun ⟨⟨ρ₁, a⟩, ⟨ρ₂, b⟩⟩ ↦ ?_⟩⟩
      obtain ⟨ρ, e₁, e₂⟩ := merge ρ₁ ρ₂
      exact ⟨ρ, fun h ↦ h.elim (fun h ↦ a (e₁.1 h)) (fun h ↦ b (e₂.1 h))⟩

/-- Where the Strong Kleene evaluation is defined, every resolution of the tokens gives its value
(the value half of Theorem 41). -/
theorem resolve_iff_of_presup {F : Formula Atom} (h : (F.strong I).presup w)
    (ρ : SyntacticEnvironment Atom → Atom → Atom → Prop) :
    resolve I w ρ [] F ↔ (F.strong I).assertion w := by
  obtain ⟨h₁, h₀⟩ := exists_resolve_iff I (w := w) F []
  by_cases ha : (F.strong I).assertion w
  · have he : (F.strong I).eval w = 1 := (PartialProp.eval_eq_true_iff _ _).2 ⟨h, ha⟩
    exact iff_of_true (by by_contra hn; exact h₀.1 ⟨ρ, hn⟩ he) ha
  · have he : (F.strong I).eval w = -1 := (PartialProp.eval_eq_false_iff _ _).2 ⟨h, ha⟩
    exact iff_of_false (fun hr ↦ h₁.1 ⟨ρ, hr⟩ he) ha

/-- A formula is Kleene-defined in the sense of items 27–28 iff its Strong Kleene evaluation is
defined (Theorem 41). -/
theorem tokenDefined_iff (F : Formula Atom) : TokenDefined I w F ↔ (F.strong I).presup w := by
  refine ⟨fun hd ↦ by_contra fun hp ↦ ?_, fun hp ρ ρ' ↦ by
    rw [resolve_iff_of_presup I hp, resolve_iff_of_presup I hp]⟩
  obtain ⟨h₁, h₀⟩ := exists_resolve_iff I (w := w) F []
  have he := (PartialProp.eval_eq_indet_iff _ _).2 hp
  obtain ⟨ρ, hρ⟩ := h₁.2 (by rw [he]; decide)
  obtain ⟨ρ', hρ'⟩ := h₀.2 (by rw [he]; decide)
  exact hρ' ((hd ρ ρ').1 hρ)

/-! #### Lemmas 6–8 and 11: Kleene and supervaluations -/

/-- Where the Strong Kleene evaluation is defined, the supervaluation is defined, with the same
value by `resolve_iff_of_presup` (Lemma 7, item 31). -/
theorem superDefined_of_presup {F : Formula Atom} (h : (F.strong I).presup w) :
    SuperDefined I w F :=
  fun _ _ ↦ (tokenDefined_iff I F).2 h _ _

theorem resolve_congr_occurrences {ρ ρ' : SyntacticEnvironment Atom → Atom → Atom → Prop}
    {K : SyntacticEnvironment Atom} (F : Formula Atom)
    (h : ∀ o ∈ F.occurrences, ρ (o.1 ++ K) o.2.1 o.2.2 ↔ ρ' (o.1 ++ K) o.2.1 o.2.2) :
    resolve I w ρ K F ↔ resolve I w ρ' K F := by
  induction F generalizing K with
  | atom p => rfl
  | trigger p p' =>
    have := h _ (List.mem_singleton_self ([], p, p'))
    simp only [List.nil_append] at this
    simp only [resolve, this]
  | not F ih =>
    refine not_congr (ih fun o ho ↦ ?_)
    have := h _ (List.mem_map_of_mem (f := fun o ↦ (o.1 ++ [.not], o.2)) ho)
    simpa only [List.append_assoc, List.singleton_append] using this
  | bin c F G ihF ihG =>
    simp only [resolve]
    rw [ihF fun o ho ↦ ?_, ihG fun o ho ↦ ?_]
    · have := h _ (List.mem_append_right _
        (List.mem_map_of_mem (f := fun o ↦ (o.1 ++ [.right c F], o.2)) ho))
      simpa only [List.append_assoc, List.singleton_append] using this
    · have := h _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun o ↦ (o.1 ++ [.left c G], o.2)) ho))
      simpa only [List.append_assoc, List.singleton_append] using this

/-- When every trigger occurs once, the supervaluation and the Strong Kleene evaluation are defined
together (Lemma 6, item 30). -/
theorem superDefined_iff_of_nodup {F : Formula Atom} (hF : (F.occurrences.map Prod.snd).Nodup) :
    SuperDefined I w F ↔ (F.strong I).presup w := by
  refine ⟨fun hs ↦ (tokenDefined_iff I F).1 fun ρ ρ' ↦ ?_, superDefined_of_presup I⟩
  have key (ρ : SyntacticEnvironment Atom → Atom → Atom → Prop) : resolve I w ρ [] F ↔
      resolve I w (fun _ p p' ↦ ∃ o ∈ F.occurrences, o.2 = (p, p') ∧ ρ o.1 p p') [] F :=
    resolve_congr_occurrences I F fun o ho ↦ by
      simp only [List.append_nil]
      refine ⟨fun h ↦ ⟨o, ho, rfl, h⟩, fun ⟨o', ho', he, h⟩ ↦ ?_⟩
      obtain rfl := List.inj_on_of_nodup_map hF ho' ho he
      exact h
  rw [key ρ, key ρ']
  exact hs _ _

/-- Symmetric Kleene acceptability implies symmetric super-acceptability (Lemma 8, item 32). -/
theorem KleeneS.superS {C : Set W} {F : Formula Atom} (h : KleeneS I C F) : SuperS I C F :=
  fun _ hw ↦ superDefined_of_presup I (h hw)

/-- Incremental Kleene acceptability implies incremental super-acceptability (Lemma 8, item 32). -/
theorem KleeneI.superI {C : Set W} {F : Formula Atom} (h : KleeneI I C F) : SuperI I C F :=
  fun w hw o ho K' hK hT ↦ superDefined_of_presup I (h w hw o ho K' hK hT)

/-- `(pp' or (not pp'))` is symmetrically super-acceptable in the set of all worlds, but not
Kleene-acceptable there when `p` is not a tautology (Lemma 11, item 37). -/
theorem superS_not_kleeneS {p p' : Atom} {w₀ : W} (hw₀ : w₀ ∉ I p) :
    SuperS I Set.univ (.bin .disj (.trigger p p') (.not (.trigger p p'))) ∧
      ¬ KleeneS I Set.univ (.bin .disj (.trigger p p') (.not (.trigger p p'))) := by
  refine ⟨fun w _ σ σ' ↦ ?_, fun h ↦ ?_⟩
  · simp only [resolve, Connective.eval]
    tauto
  · have h₀ : (Formula.strong I (.bin .disj (.trigger p p') (.not (.trigger p p')))).presup w₀ :=
      h (Set.mem_univ w₀)
    simp [Formula.strong, Connective.strong, PartialProp.orStrong, PartialProp.neg, hw₀] at h₀

/-! #### Incremental acceptability -/

theorem Incrementally.congr {P Q : Formula Atom → Prop} (h : ∀ X, P X ↔ Q X)
    {F : Formula Atom} : Incrementally P F ↔ Incrementally Q F :=
  forall₂_congr fun _ _ ↦ forall_congr' fun _ ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
    h _

theorem incrementally_atom (P : Formula Atom → Prop) (p : Atom) :
    Incrementally P (.atom p) := by
  simp [Incrementally, Formula.occurrences]

theorem incrementally_trigger {P : Formula Atom → Prop} {p p' : Atom} :
    Incrementally P (.trigger p p') ↔ P (.trigger p p') := by
  simp only [Incrementally, Formula.occurrences, List.mem_singleton, forall_eq]
  refine ⟨fun h ↦ h [] (.refl []) fun _ _ h ↦ by simp at h, fun h K' hK _ ↦ ?_⟩
  cases hK
  exact h

theorem incrementally_not {P : Formula Atom → Prop} {F : Formula Atom} :
    Incrementally P (.not F) ↔ Incrementally (fun X ↦ P (.not X)) F := by
  simp only [Incrementally, Formula.occurrences, List.forall_mem_map]
  refine forall₂_congr fun o _ ↦ ⟨fun h K' hK hT ↦ ?_, fun h K' hK hT ↦ ?_⟩
  · have := h (K' ++ [.not])
      (SyntacticEnvironment.sameInitialString_append_singleton.2 ⟨K', .not, rfl, hK, .not⟩)
      (SyntacticEnvironment.triggerFreeFinal_append.2
        ⟨hT, SyntacticEnvironment.triggerFreeFinal_singleton.2 fun _ _ h ↦ by cases h⟩)
    rwa [SyntacticEnvironment.fill_append] at this
  · obtain ⟨K'', s', rfl, hK'', hs⟩ :=
      SyntacticEnvironment.sameInitialString_append_singleton.1 hK
    cases hs
    rw [SyntacticEnvironment.fill_append]
    exact h K'' hK'' (SyntacticEnvironment.triggerFreeFinal_append.1 hT).1

theorem incrementally_bin {P : Formula Atom → Prop} {c : Connective} {F G : Formula Atom} :
    Incrementally P (.bin c F G) ↔
      Incrementally (fun X ↦ ∀ c' G', (c = .cond ↔ c' = .cond) → G'.occurrences = [] →
        P (.bin c' X G')) F ∧ Incrementally (fun Y ↦ P (.bin c F Y)) G := by
  simp only [Incrementally, Formula.occurrences, List.forall_mem_append, List.forall_mem_map]
  refine and_congr (forall₂_congr fun o _ ↦ ⟨fun h K' hK hT c' G' hc hG ↦ ?_,
    fun h K' hK hT ↦ ?_⟩) (forall₂_congr fun o _ ↦ ⟨fun h K' hK hT ↦ ?_, fun h K' hK hT ↦ ?_⟩)
  · have := h (K' ++ [.left c' G'])
      (SyntacticEnvironment.sameInitialString_append_singleton.2
        ⟨K', _, rfl, hK, .left hc G G'⟩)
      (SyntacticEnvironment.triggerFreeFinal_append.2
        ⟨hT, SyntacticEnvironment.triggerFreeFinal_singleton.2 fun _ _ h ↦ by cases h; exact hG⟩)
    rwa [SyntacticEnvironment.fill_append] at this
  · obtain ⟨K'', s', rfl, hK'', hs⟩ :=
      SyntacticEnvironment.sameInitialString_append_singleton.1 hK
    obtain ⟨hT'', hTs⟩ := SyntacticEnvironment.triggerFreeFinal_append.1 hT
    cases hs with
    | left hc _ G' =>
      rw [SyntacticEnvironment.fill_append]
      exact h K'' hK'' hT'' _ G' hc (SyntacticEnvironment.triggerFreeFinal_singleton.1 hTs _ _ rfl)
  · have := h (K' ++ [.right c F])
      (SyntacticEnvironment.sameInitialString_append_singleton.2 ⟨K', _, rfl, hK, .right c F⟩)
      (SyntacticEnvironment.triggerFreeFinal_append.2
        ⟨hT, SyntacticEnvironment.triggerFreeFinal_singleton.2 fun _ _ h ↦ by cases h⟩)
    rwa [SyntacticEnvironment.fill_append] at this
  · obtain ⟨K'', s', rfl, hK'', hs⟩ :=
      SyntacticEnvironment.sameInitialString_append_singleton.1 hK
    cases hs
    rw [SyntacticEnvironment.fill_append]
    exact h K'' hK'' (SyntacticEnvironment.triggerFreeFinal_append.1 hT).1

/-- A property of formulas that is decided like definedness, at triggers, under negation, and at
each argument of a connective, holds incrementally of a formula iff the filtering presupposition
holds. -/
private theorem incrementally_iff_filter (P : Formula Atom → Prop)
    (htrig : ∀ p p' : Atom, P (.trigger p p') ↔ w ∈ I p)
    (hnot : ∀ X : Formula Atom, P (.not X) ↔ P X)
    (hleft : ∀ (c : Connective) (X : Formula Atom), (∀ (c' : Connective) (G' : Formula Atom),
      (c = .cond ↔ c' = .cond) → G'.occurrences = [] → P (.bin c' X G')) ↔ P X)
    (hright : ∀ (c : Connective) (F Y : Formula Atom), (F.filter I).presup w →
      (P (.bin c F Y) ↔ (w ∈ c.localContext Set.univ (F.truth I) → P Y)))
    (F : Formula Atom) : Incrementally P F ↔ (F.filter I).presup w := by
  induction F with
  | atom p => exact iff_of_true (incrementally_atom P p) trivial
  | trigger p p' => rw [incrementally_trigger, htrig]; rfl
  | not F ih => rw [incrementally_not, Incrementally.congr hnot, ih]; rfl
  | bin c F G ihF ihG =>
    rw [incrementally_bin, Incrementally.congr (hleft c), ihF, Formula.filter_presup_bin]
    refine and_congr_right fun hF ↦ ?_
    rw [Incrementally.congr (hright c F · hF), ← ihG]
    exact ⟨fun h hk o ho K' hK hT ↦ h o ho K' hK hT hk, fun h o ho K' hK hT hk ↦ h hk o ho K' hK hT⟩

/-- A tautology, from any atom. -/
private def taut (a : Atom) : Formula Atom := .bin .cond (.atom a) (.atom a)

private theorem occurrences_taut (a : Atom) : (taut a).occurrences = [] := rfl

private theorem filter_presup_of_occurrences {F : Formula Atom} (h : F.occurrences = []) :
    (F.filter I).presup w :=
  (Formula.filter_presup_iff I F w).2 fun o ho ↦ by simp [h] at ho

/-- On its filtering presupposition, a formula's Strong Kleene evaluation is defined and true iff
the formula is. -/
theorem strong_of_filter_presup {F : Formula Atom} (h : (F.filter I).presup w) :
    (F.strong I).presup w ∧ ((F.strong I).assertion w ↔ w ∈ F.truth I) := by
  have hp : (F.strong I).presup w := (tokenDefined_iff I F).1 fun ρ ρ' ↦ by
    rw [resolve_of_filter_presup I h, resolve_of_filter_presup I h]
  exact ⟨hp, (resolve_iff_of_presup I hp fun _ _ _ ↦ True).symm.trans
    (resolve_of_filter_presup I h _ _)⟩

/-- Incremental Strong Kleene definedness is the filtering presupposition. -/
theorem incrementally_strong_iff (w : W) (F : Formula Atom) :
    Incrementally (fun X ↦ (X.strong I).presup w) F ↔ (F.filter I).presup w := by
  refine incrementally_iff_filter I _ (fun _ _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) (fun c X ↦ ?_)
    (fun c F Y hF ↦ ?_) F
  · have : Nonempty Atom := X.nonempty_atom
    let a := Classical.arbitrary Atom
    have hpres (Y : Formula Atom) : (Y.strong I).presup w ↔ (Y.strong I).eval w ≠ 0 := by
      rw [ne_eq, PartialProp.eval_eq_indet_iff, not_not]
    have htaut : ((taut a).strong I).eval w = 1 := by
      rw [PartialProp.eval_eq_true_iff]
      by_cases ha : w ∈ I a <;>
        simp [taut, Formula.strong, Connective.strong, PartialProp.orStrong, PartialProp.neg, ha]
    refine ⟨fun h ↦ ?_, fun hX c' G' _ hG ↦ ?_⟩
    · rw [hpres]
      cases c
      · have := (hpres _).1 (h .conj (taut a) Iff.rfl rfl)
        simp only [Formula.strong, Connective.strong, PartialProp.eval_andStrong, htaut] at this
        revert this; cases (X.strong I).eval w <;> decide
      · have := (hpres _).1 (h .cond (.not (taut a)) Iff.rfl rfl)
        simp only [Formula.strong, Connective.strong, PartialProp.eval_orStrong,
          PartialProp.eval_neg, htaut] at this
        revert this; cases (X.strong I).eval w <;> decide
      · have := (hpres _).1 (h .disj (.not (taut a)) Iff.rfl rfl)
        simp only [Formula.strong, Connective.strong, PartialProp.eval_orStrong,
          PartialProp.eval_neg, htaut] at this
        revert this; cases (X.strong I).eval w <;> decide
    · obtain ⟨hGp, -⟩ := strong_of_filter_presup I (w := w) (filter_presup_of_occurrences I hG)
      cases c' <;> simp only [Formula.strong, Connective.strong, PartialProp.andStrong,
        PartialProp.orStrong, PartialProp.neg] <;> exact .inl ⟨hX, hGp⟩
  · obtain ⟨hFp, hFa⟩ := strong_of_filter_presup I hF
    cases c <;> simp only [Formula.strong, Connective.strong, PartialProp.andStrong,
      PartialProp.orStrong, PartialProp.neg, Connective.localContext, Set.mem_inter_iff,
      Set.mem_univ, true_and, Set.mem_compl_iff, hFa, hFp] <;> tauto

/-- Incremental supervaluation definedness is the filtering presupposition. -/
theorem incrementally_superDefined_iff (w : W) (F : Formula Atom) :
    Incrementally (SuperDefined I w) F ↔ (F.filter I).presup w := by
  have hconst (σ : Atom → Atom → Prop) (K : SyntacticEnvironment Atom) (X : Formula Atom) :=
    resolve_const I (w := w) σ K [] X
  have hbin (σ : Atom → Atom → Prop) (c : Connective) (X Y : Formula Atom) :
      resolve I w (fun _ ↦ σ) [] (.bin c X Y) ↔
        c.eval (resolve I w (fun _ ↦ σ) [] X) (resolve I w (fun _ ↦ σ) [] Y) := by
    simp only [resolve]
    rw [hconst σ [.left c Y] X, hconst σ [.right c X] Y]
  have hfree {G : Formula Atom} (hG : G.occurrences = []) (σ : Atom → Atom → Prop) :
      resolve I w (fun _ ↦ σ) [] G ↔ w ∈ G.truth I :=
    resolve_of_filter_presup I (filter_presup_of_occurrences I hG) _ _
  refine incrementally_iff_filter I _ (fun p p' ↦ ?_) (fun X ↦ ?_) (fun c X ↦ ?_)
    (fun c F Y hF ↦ ?_) F
  · by_cases hp : w ∈ I p
    · exact iff_of_true (fun σ σ' ↦ by simp [resolve, hp]) hp
    · refine iff_of_false (fun h ↦ ?_) hp
      have := h (fun _ _ ↦ True) (fun _ _ ↦ False)
      simp [resolve, hp] at this
  · refine forall₂_congr fun σ σ' ↦ ?_
    simp only [resolve]
    rw [hconst σ, hconst σ', not_iff_not]
  · have : Nonempty Atom := X.nonempty_atom
    let a := Classical.arbitrary Atom
    refine ⟨fun h σ σ' ↦ ?_, fun hX c' G' _ hG σ σ' ↦ ?_⟩
    · cases c
      · have := h .conj (taut a) Iff.rfl rfl σ σ'
        rw [hbin, hbin, hfree (occurrences_taut a), hfree (occurrences_taut a)] at this
        simpa [taut, Formula.truth, Connective.eval] using this
      · have := h .cond (.not (taut a)) Iff.rfl rfl σ σ'
        rw [hbin, hbin, hfree (G := (taut a).not) rfl, hfree (G := (taut a).not) rfl] at this
        exact not_iff_not.1 (by simpa [taut, Formula.truth, Connective.eval] using this)
      · have := h .disj (.not (taut a)) Iff.rfl rfl σ σ'
        rw [hbin, hbin, hfree (G := (taut a).not) rfl, hfree (G := (taut a).not) rfl] at this
        simpa [taut, Formula.truth, Connective.eval] using this
    · rw [hbin, hbin, hfree hG, hfree hG, hX σ σ']
  · have hF' (σ : Atom → Atom → Prop) := resolve_of_filter_presup I hF (fun _ ↦ σ) []
    simp only [SuperDefined, hbin, hF']
    cases c <;> by_cases ht : w ∈ F.truth I <;>
      simp [Connective.eval, Connective.localContext, ht]

/-- Incremental Kleene acceptability is entailment of the filtering presupposition, the route by
which Theorems 36 and 38a are proved here. -/
theorem kleeneI_iff (C : Set W) (F : Formula Atom) : KleeneI I C F ↔ (F.filter I).Admits C :=
  forall₂_congr fun w _ ↦ incrementally_strong_iff I w F

/-- Incremental super-acceptability is entailment of the filtering presupposition. -/
theorem superI_iff (C : Set W) (F : Formula Atom) : SuperI I C F ↔ (F.filter I).Admits C :=
  forall₂_congr fun w _ ↦ incrementally_superDefined_iff I w F

/-- Incremental Kleene acceptability is incremental super-acceptability (Theorem 36, item 36). -/
theorem kleeneI_iff_superI (C : Set W) (F : Formula Atom) : KleeneI I C F ↔ SuperI I C F :=
  (kleeneI_iff I C F).trans (superI_iff I C F).symm

/-- As item 20 notes for every theory, incremental Kleene acceptability implies symmetric Kleene
acceptability. -/
theorem KleeneI.kleeneS {C : Set W} {F : Formula Atom} (h : KleeneI I C F) : KleeneS I C F :=
  fun _ hw ↦ (strong_of_filter_presup I ((kleeneI_iff I C F).1 h hw)).1

/-- As item 20 notes for every theory, incremental super-acceptability implies symmetric
super-acceptability. -/
theorem SuperI.superS {C : Set W} {F : Formula Atom} (h : SuperI I C F) : SuperS I C F :=
  KleeneS.superS I (KleeneI.kleeneS I ((kleeneI_iff_superI I C F).2 h))

/-- Incremental Transparency implies incremental Kleene and supervaluation acceptability (Theorem
38a, item 38). -/
theorem TranspI.kleeneI {C : Set W} {F : Formula Atom} (h : TranspI I C F) :
    KleeneI I C F ∧ SuperI I C F :=
  have hK := (kleeneI_iff I C F).2 (Formula.admits_ccp_iff I |>.1 ((transpI_iff_admits I C F).1 h))
  ⟨hK, (kleeneI_iff_superI I C F).1 hK⟩

/-- With a world where `p` and `q` fail and one where both hold, `(pp' and qq')` satisfies symmetric
Transparency but is neither Kleene- nor super-acceptable (Theorem 39a, item 39). -/
theorem transpS_not_kleeneS_not_superS {p p' q q' : Atom} {w₁ w₂ : W} (hp₁ : w₁ ∉ I p)
    (hq₁ : w₁ ∉ I q) (hp₂ : w₂ ∈ I p) (hq₂ : w₂ ∈ I q) :
    TranspS I {w₁, w₂} (.bin .conj (.trigger p p') (.trigger q q')) ∧
      ¬ KleeneS I {w₁, w₂} (.bin .conj (.trigger p p') (.trigger q q')) ∧
      ¬ SuperS I {w₁, w₂} (.bin .conj (.trigger p p') (.trigger q q')) := by
  refine ⟨fun o ho f hf d w hw ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [Formula.occurrences, List.map_cons, List.map_nil, List.nil_append,
      List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [Set.mem_singleton_iff] at hf
    subst hf
    rcases hw with rfl | rfl <;> rcases ho with rfl | rfl <;>
      simp [SyntacticEnvironment.truth, SyntacticEnvironment.Step.truth, Connective.eval,
        Formula.truth, hp₁, hq₁, hp₂, hq₂]
  · have h₁ : (Formula.strong I (.bin .conj (.trigger p p') (.trigger q q'))).presup w₁ :=
      h (Set.mem_insert w₁ _)
    simp [Formula.strong, Connective.strong, PartialProp.andStrong, hp₁, hq₁] at h₁
  · have := h w₁ (Set.mem_insert _ _) (fun _ _ ↦ True) (fun _ _ ↦ False)
    simp [resolve, Connective.eval, hp₁, hq₁] at this

end Trivalent

/-! ### Quantified sentences (C.9, C.23 and items 38–39 of [schlenker-2008b]) -/

section Quantified

open Quantifier

variable {E : Type*} {q : NumberTree} {A : W → E → Prop} {C : Set W} {P : Set (W × E)}

/-- Where `q` is not constant on the row of the restrictor's size at any world of the context, as
C.9's Non-Triviality and Constancy together guarantee, a presupposition triggered in the nuclear
scope is transparent iff every individual of the restrictor satisfies it at every world of the
context. This is universal projection, the consequence of Theorem 2 of C.9 for a quantified
clause. -/
theorem transparent_scope_iff_universal [Finite E]
    (hNT : ∀ w ∈ C, ¬ q.ConstantOnRow {x | A w x}.ncard) :
    Transparent C {scopeTruth q A} P ↔ ∀ w ∈ C, ∀ e, A w e → (w, e) ∈ P := by
  rw [transparent_scopeTruth_iff]
  exact ⟨fun h w hw ↦ h w hw (hNT w hw), fun h w hw _ ↦ h w hw⟩

/-- `(Q A. _)`, with a scope that presupposes `π` and asserts `a`, is defined at `w` when every
resolution of the scope's undefined individuals gives the sentence the same value (items 25 and
27–28; with one trigger, Kleene and supervaluation definedness coincide). -/
def ScopeDefined (q : NumberTree) (A : W → E → Prop) (π a : Set (W × E)) (w : W) : Prop :=
  ∀ D D' : E → Prop, (∀ e, (w, e) ∈ π → (D e ↔ (w, e) ∈ a)) →
    (∀ e, (w, e) ∈ π → (D' e ↔ (w, e) ∈ a)) → (q.toGQ (A w) D ↔ q.toGQ (A w) D')

/-- A presupposition in the nuclear scope is transparent iff the sentence is defined at every world
of the context whatever the scope asserts. Transparency quantifies over the assertion that Kleene
and supervaluation acceptability hold fixed. -/
theorem transparent_scopeTruth_iff_forall_scopeDefined :
    Transparent C {scopeTruth q A} P ↔ ∀ a, ∀ w ∈ C, ScopeDefined q A P a w := by
  classical
  rw [transparent_iff_dependsOn]
  simp only [Set.mem_singleton_iff, forall_eq]
  refine ⟨fun h a w hw D D' hD hD' ↦ Iff.of_eq ?_, fun h w hw d d' hd ↦ propext ?_⟩
  · have := h w hw (x := {p | p.1 = w ∧ D p.2}) (y := {p | p.1 = w ∧ D' p.2})
      fun ⟨u, e⟩ hp ↦ by
        by_cases hu : u = w
        · subst hu
          exact propext (and_congr_right fun _ ↦ (hD e hp).trans (hD' e hp).symm)
        · exact propext ⟨fun h ↦ (hu h.1).elim, fun h ↦ (hu h.1).elim⟩
    simpa [scopeTruth] using this
  · exact h d w hw _ _ (fun _ _ ↦ Iff.rfl) fun e he ↦ Iff.of_eq (hd (w, e) he).symm

/-- The truth set of `(Infinitely-many P. _)` at a single world where every natural number is a
`P`, as a function of its scope. -/
def infinitelyMany (d : Set (Unit × ℕ)) : Set Unit := {u | {n | (u, n) ∈ d}.Infinite}

/-- A presupposition that fails of finitely many individuals is transparent in the scope of
*infinitely many*, which does not then presuppose that every individual satisfies it (C.23ii). -/
theorem transparent_infinitelyMany_of_finite {P : Set (Unit × ℕ)}
    (hP : {n | ((), n) ∉ P}.Finite) : Transparent Set.univ {infinitelyMany} P := by
  rintro f rfl d ⟨⟩ -
  change {n | ((), n) ∈ P ∩ d}.Infinite ↔ {n | ((), n) ∈ d}.Infinite
  exact ⟨fun h ↦ h.mono fun _ hn ↦ hn.2,
    fun h ↦ (h.sdiff hP).mono fun _ hn ↦ ⟨by simpa using hn.2, hn.1⟩⟩

/-- The scope of *infinitely many* has no local context. Leaving out any one individual is
transparent, so a least transparent restriction would contain no individual, but the empty
restriction is not transparent (C.23i). -/
theorem not_exists_isLocalContext_infinitelyMany :
    ¬ ∃ x, IsLocalContext Set.univ {infinitelyMany} x := by
  rintro ⟨x, hx, hle⟩
  obtain rfl : x = ∅ := Set.eq_empty_of_forall_notMem fun ⟨_, n⟩ h ↦
    hle (transparent_infinitelyMany_of_finite (P := {p | p.2 ≠ n})
      ((Set.finite_singleton n).subset fun m hm ↦ by simpa using hm)) h rfl
  have := hx infinitelyMany rfl Set.univ () trivial
  simp [infinitelyMany, Set.infinite_univ] at this

/-- With one world and two individuals, the first not `Q` and the second `Q` and `Q'`, the sentence
`(No P. QQ')` is false however the first individual is resolved, so it is Kleene and supervaluation
acceptable, but Transparency rejects it, since for a scope false of the second individual the
first decides (Theorems 38b and 39b; the trigger is final, so the incremental and symmetric
versions coincide). -/
theorem scopeDefined_not_transparent_no :
    ScopeDefined NumberTree.no (fun _ _ ↦ True) {p : Unit × Fin 2 | p.2 = 1} Set.univ () ∧
      ¬ Transparent {()} {scopeTruth NumberTree.no fun (_ : Unit) (_ : Fin 2) ↦ True}
        {p | p.2 = 1} := by
  refine ⟨fun D D' hD hD' ↦ ?_, fun h ↦ ?_⟩
  · have h1 : D 1 := (hD 1 rfl).2 trivial
    have h1' : D' 1 := (hD' 1 rfl).2 trivial
    simp only [NumberTree.toGQ_apply, NumberTree.no, true_and]
    refine iff_of_false (fun h ↦ ?_) fun h ↦ ?_
    · exact (Set.ncard_eq_zero (s := {x | D x}).1 h).subset (Set.mem_ofPred.2 h1) |>.elim
    · exact (Set.ncard_eq_zero (s := {x | D' x}).1 h).subset (Set.mem_ofPred.2 h1') |>.elim
  · have := (transparent_scopeTruth_iff NumberTree.no).1 h () rfl (fun hc ↦ ?_) 0 trivial
    · exact absurd this (by decide)
    · have h2 : {_x : Fin 2 | True}.ncard = 2 := by simp
      have := hc 2 0 1 1 h2.symm h2.symm
      simp [NumberTree.no] at this

end Quantified

/-! ### Quantified clauses -/

section QuantifiedClause

open Quantifier

variable {E : Type*} (J : Atom → Set (W × E)) {C : Set W} {c : QuantifiedClause Atom}

namespace QuantifiedClause

/-- The incremental theory consults at a gap of a quantified clause each good final of the gap's
argument inside each good final of the clause, namely any scope after a restrictor and the given
restrictor before a scope. -/
def goodFinals (k : QuantifiedClause.Env Atom) : Set (Set (W × E) → Set W) :=
  Set.image2 (· ∘ ·) (k.arg.finals J k.quantifier) (Schlenker2009.goodFinals J k.inner)

/-- Incremental Transparency holds for a quantified clause when at every trigger the
presupposition is a transparent restriction for every good final. -/
def TranspI (C : Set W) (c : QuantifiedClause Atom) : Prop :=
  ∀ o ∈ c.occurrences, Transparent C (goodFinals J o.1) (J o.2.1)

/-- Symmetric Transparency holds for a quantified clause when at every trigger the
presupposition is a transparent restriction for the actual clause. -/
def TranspS (C : Set W) (c : QuantifiedClause Atom) : Prop :=
  ∀ o ∈ c.occurrences, Transparent C {o.1.truth J} (J o.2.1)

/-- Incremental local satisfaction for a quantified clause. -/
def SatI (C : Set W) (c : QuantifiedClause Atom) : Prop :=
  ∀ o ∈ c.occurrences, Satisfied C (goodFinals J o.1) (J o.2.1)

/-- Symmetric local satisfaction for a quantified clause. -/
def SatS (C : Set W) (c : QuantifiedClause Atom) : Prop :=
  ∀ o ∈ c.occurrences, Satisfied C {o.1.truth J} (J o.2.1)

theorem truth_mem_goodFinals (k : QuantifiedClause.Env Atom) : k.truth J ∈ goodFinals J k :=
  Set.mem_image2_of_mem (k.arg.truth_mem_finals J k.quantifier)
    (Set.mem_image_of_mem _ (SyntacticEnvironment.SameInitialString.refl k.inner))

theorem TranspI.transpS (h : TranspI J C c) : TranspS J C c := fun o ho ↦
  (h o ho).anti (Set.singleton_subset_iff.2 (truth_mem_goodFinals J o.1))

theorem SatI.transpI (h : SatI J C c) : TranspI J C c := fun o ho ↦ (h o ho).transparent

theorem SatS.transpS (h : SatS J C c) : TranspS J C c := fun o ho ↦ (h o ho).transparent

/-- In a clause whose scope is a trigger and whose restrictor holds none, symmetric Transparency is
universal projection over the restrictor, at each world where the quantifier is not constant on
the row of the restrictor's size. -/
theorem transpS_trigger_iff [Finite E] {q : NumberTree} {R : Formula Atom} {p a : Atom}
    (hR : R.occurrences = []) :
    TranspS J C ⟨q, R, .trigger p a⟩ ↔ ∀ w ∈ C, ¬ q.ConstantOnRow {e | (w, e) ∈ R.truth J}.ncard →
      ∀ e, (w, e) ∈ R.truth J → (w, e) ∈ J p := by
  simp only [TranspS, QuantifiedClause.occurrences, hR, Formula.occurrences, List.map_nil,
    List.nil_append, List.map_cons, List.mem_singleton, forall_eq]
  exact transparent_scopeTruth_iff q

end QuantifiedClause

end QuantifiedClause

end Schlenker2009
