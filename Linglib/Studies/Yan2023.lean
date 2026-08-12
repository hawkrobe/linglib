import Linglib.Logic.Team.QBSML.FreeChoice
import Linglib.Logic.Team.BSML.Scenarios

/-!
# [yan-2023]: Monotonicity under desire as a neglect-zero effect

Chapter 4 of [yan-2023] defends an upward-monotonic semantics for desire
verbs against three classical puzzles — Ross's paradox under *want*
([ross-1944]; the desiderative version is due to [crnic-2011]), Asher's
puzzle (reported in [heim-1992]) and Heim's own teach-on-Tuesdays example
([heim-1992]) — by reducing all three to free-choice inferences in QBSML
([aloni-vanormondt-2023]): the monotonic step is semantically valid on the
NE-free fragment, the paradoxical "ok with the unwanted alternative"
inference is pragmatically valid only for the *enriched* conclusion, and
the enriched conclusion is not derivable from the premise. The dissertation
calls the general effect — semantic weakening licensing pragmatic
neglect-zero consequences — the *weakening effect triggered by
monotonicity* (WEM); this chapter is its desire-verb case study. Where no
overt disjunction occurs (Asher, Heim), the paper's one new formal object
— the **reinterpretation function** `∥·∥_P` (Definition 32) — supplies it:
a predicate `Q` with a contextually salient sub-predicate `P` is
reinterpreted as `(P ∧ Q) ∨ (¬P ∧ Q)`, licensed because the two are
classically equivalent (`eval_reinterpret_iff`) yet pragmatically distinct
under `[·]⁺`.

This file derives the chapter's account from the QBSML substrate
(`Logic/Team/QBSML/FreeChoice.lean`): the □-FC fact it invokes
(Fact 13) is `boxFC`; the quantified variant needed for Asher and Heim is
`boxExiFC`; the semantic validity of the monotonic steps is
`support_disj_inl` / `support_nec_mono`. The verbs *want* / *it is ok* are
the Hintikka-style `□`/`◇` over a bouletic accessibility relation, exactly
as in the paper (§4.4.1; the positive semantics of *want* itself is
deferred to the dissertation's Chapter 5).

## Main declarations

* `reinterpret` — Yan's reinterpretation function `∥·∥_P` (Definition 32),
  an instance of `Formula.mapAtoms`.
* `reinterpret_neFree`, `eval_reinterpret_iff` — reinterpretation stays
  NE-free and is bilaterally equivalent to the original (substitution
  *salva veritate*; the classical equivalence of `Qx` and
  `(Px ∧ Qx) ∨ (¬Px ∧ Qx)` lifted to team semantics).
* `ross_monotone`, `ross_fc`, `ross_premise`, `ross_blocked` — Ross's
  paradox: monotonicity is semantically valid, FC pragmatically valid, and
  the enriched disjunctive premise underivable (the paper's Figure 4.2).
* `asher_monotone`, `asher_fc`, `asher_premise`, `asher_blocked`,
  `asher_concl_enriched` — Asher's puzzle via reinterpretation of TRIP by
  FREE (the paper's Figure 4.3), with the non-vacuity of reinterpretation
  under `[·]⁺` witnessed at the same state, and the denotational side
  condition FREE ⊊ TRIP realised globally
  (`asherModel_free_ssubset_trip`).
* `heim_fc` — Heim's example via reinterpretation of TEACH by TUESDAY (the
  paper omits the rest of the derivation as parallel to Asher's; so do we).
-/

namespace Yan2023

open QBSML
open Team (splitsAs_empty_self)
open BSML (QVar)

/-! ### The reinterpretation function -/

section Reinterpret

variable {Var Const Pred : Type*}

/-- **Reinterpretation** `∥·∥_P` ([yan-2023] Definition 32): rewrite each
    atom `Q t` whose predicate has `P` as a (contextually salient)
    sub-predicate as the disjunction `(P t ∧ Q t) ∨ (¬P t ∧ Q t)`, and
    commute with every connective (`Formula.mapAtoms`).

    `sub P Q` plays the paper's side condition `P ⊂ Q`. That condition is
    *denotational* there (the denotation of `P` a proper subset of `Q`'s),
    but the paper leaves open against which model it is checked — in the
    agent's own desire-state denotations it must fail for blocking to
    arise, so it is only sensible against a common-ground/global model
    (realised by the two-world `asherModel` below,
    `asherModel_free_ssubset_trip`). `sub` therefore stays an
    unconstrained contextual parameter, which `eval_reinterpret_iff` shows
    is truth-conditionally harmless; the salience requirement is likewise
    contextual and not part of the function.

    The paper's language `L_D` (its Definition 24) has primitive `□`,
    derived `◇`, and no `∀`, so Definition 32 has no `◇`/`∀` clauses: the
    `.poss` clause here recovers its derived-`◇` behaviour definitionally,
    and `.univ` extends the function to the full `Formula` language.
    The `.ne` clause is a totality filler — the paper defines `∥·∥` on the
    NE-free fragment only. -/
def reinterpret (sub : Pred → Pred → Prop) [DecidableRel sub] (P : Pred) :
    Formula Var Const Pred → Formula Var Const Pred :=
  Formula.mapAtoms
    (fun Q x =>
      if sub P Q then
        .disj (.conj (.pred P x) (.pred Q x))
              (.conj (.neg (.pred P x)) (.pred Q x))
      else .pred Q x)
    (fun Q c =>
      if sub P Q then
        .disj (.conj (.predc P c) (.predc Q c))
              (.conj (.neg (.predc P c)) (.predc Q c))
      else .predc Q c)

variable (sub : Pred → Pred → Prop) [DecidableRel sub] (P : Pred)

/-- Equation lemma: reinterpretation at a variable atom. Not `@[simp]` —
    unfolding is opt-in. -/
theorem reinterpret_pred (Q : Pred) (x : Var) :
    reinterpret sub P (.pred Q x : Formula Var Const Pred) =
      if sub P Q then
        .disj (.conj (.pred P x) (.pred Q x))
              (.conj (.neg (.pred P x)) (.pred Q x))
      else .pred Q x :=
  rfl

/-- Equation lemma: reinterpretation at a constant atom. -/
theorem reinterpret_predc (Q : Pred) (c : Const) :
    reinterpret sub P (.predc Q c : Formula Var Const Pred) =
      if sub P Q then
        .disj (.conj (.predc P c) (.predc Q c))
              (.conj (.neg (.predc P c)) (.predc Q c))
      else .predc Q c :=
  rfl

/-- Reinterpretation preserves NE-freeness. -/
theorem reinterpret_neFree {φ : Formula Var Const Pred}
    (h : φ.NEFree) : (reinterpret sub P φ).NEFree :=
  h.mapAtoms
    (fun Q x => by
      show Formula.NEFree (if sub P Q then _ else _)
      split
      · exact .disj (.conj (.pred _ _) (.pred _ _))
          (.conj (.neg (.pred _ _)) (.pred _ _))
      · exact .pred _ _)
    (fun Q c => by
      show Formula.NEFree (if sub P Q then _ else _)
      split
      · exact .disj (.conj (.predc _ _) (.predc _ _))
          (.conj (.neg (.predc _ _)) (.predc _ _))
      · exact .predc _ _)

end Reinterpret

/-! ### Substitution salva veritate

The classical equivalence of `Qx` and `(Px ∧ Qx) ∨ (¬Px ∧ Qx)` justifying
reinterpretation ([yan-2023] §4.3.2) holds bilaterally in team semantics —
for *unenriched* formulas. Under `[·]⁺` the two sides diverge, which is the
entire point: the enriched reinterpreted formula carries free-choice
commitments the original does not. -/

section SalvaVeritate

variable {W Var Domain Const Pred : Type*}
variable [DecidableEq W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]
variable (M : Model W Domain Const Pred)

private theorem eval_iff_of_atom_pred (P Q : Pred) (x : Var) (b : Bool)
    (s : Finset (Index W Var Domain)) :
    eval M b (Formula.disj
        (.conj (.pred P x) (.pred Q x))
        (.conj (.neg (.pred P x)) (.pred Q x))) s ↔
      eval M b (Formula.pred Q x) s := by
  classical
  cases b with
  | true =>
    constructor
    · rintro ⟨t₁, t₂, hsplit, ⟨-, hQ₁⟩, ⟨-, hQ₂⟩⟩
      intro i hi
      rw [← hsplit] at hi
      rcases Finset.mem_union.mp hi with h | h
      · exact hQ₁ i h
      · exact hQ₂ i h
    · intro hQ
      refine ⟨s.filter (fun i => ∀ d, i.assign x = some d →
          M.relInterp₁ P i.world d),
        s.filter (fun i => ¬ ∀ d, i.assign x = some d →
          M.relInterp₁ P i.world d),
        Finset.filter_union_filter_not_eq _ s, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro i hi
        obtain ⟨his, hcond⟩ := Finset.mem_filter.mp hi
        obtain ⟨d, hd, -⟩ := hQ i his
        exact ⟨d, hd, hcond d hd⟩
      · exact fun i hi => hQ i (Finset.mem_of_mem_filter i hi)
      · intro i hi
        obtain ⟨his, hncond⟩ := Finset.mem_filter.mp hi
        push Not at hncond
        exact hncond
      · exact fun i hi => hQ i (Finset.mem_of_mem_filter i hi)
  | false =>
    constructor
    · rintro ⟨⟨t₁, t₂, hsplit₁, hnP, hnQ₁⟩, ⟨u₁, u₂, hsplit₂, hP, hnQ₂⟩⟩
      intro i hi
      rcases Finset.mem_union.mp (hsplit₁ ▸ hi) with hit₁ | hit₂
      · rcases Finset.mem_union.mp (hsplit₂ ▸ hi) with hiu₁ | hiu₂
        · obtain ⟨d, hd, hnp⟩ := hnP i hit₁
          obtain ⟨d', hd', hp⟩ := hP i hiu₁
          rw [hd, Option.some.injEq] at hd'
          exact absurd (hd' ▸ hp) hnp
        · exact hnQ₂ i hiu₂
      · exact hnQ₁ i hit₂
    · intro h
      exact ⟨⟨∅, s, splitsAs_empty_self s,
          support_empty_of_neFree (.neg (.pred P x)) M, h⟩,
        ⟨∅, s, splitsAs_empty_self s,
          support_empty_of_neFree (.pred P x) M, h⟩⟩

private theorem eval_iff_of_atom_predc (P Q : Pred) (c : Const) (b : Bool)
    (s : Finset (Index W Var Domain)) :
    eval M b (Formula.disj
        (.conj (.predc P c) (.predc Q c))
        (.conj (.neg (.predc P c)) (.predc Q c))) s ↔
      eval M b (Formula.predc Q c) s := by
  classical
  cases b with
  | true =>
    constructor
    · rintro ⟨t₁, t₂, hsplit, ⟨-, hQ₁⟩, ⟨-, hQ₂⟩⟩
      intro i hi
      rw [← hsplit] at hi
      rcases Finset.mem_union.mp hi with h | h
      · exact hQ₁ i h
      · exact hQ₂ i h
    · intro hQ
      refine ⟨s.filter (fun i => M.relInterp₁ P i.world (M.constInterp c i.world)),
        s.filter (fun i => ¬ M.relInterp₁ P i.world (M.constInterp c i.world)),
        Finset.filter_union_filter_not_eq _ s, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact fun i hi => (Finset.mem_filter.mp hi).2
      · exact fun i hi => hQ i (Finset.mem_of_mem_filter i hi)
      · exact fun i hi => (Finset.mem_filter.mp hi).2
      · exact fun i hi => hQ i (Finset.mem_of_mem_filter i hi)
  | false =>
    constructor
    · rintro ⟨⟨t₁, t₂, hsplit₁, hnP, hnQ₁⟩, ⟨u₁, u₂, hsplit₂, hP, hnQ₂⟩⟩
      intro i hi
      rcases Finset.mem_union.mp (hsplit₁ ▸ hi) with hit₁ | hit₂
      · rcases Finset.mem_union.mp (hsplit₂ ▸ hi) with hiu₁ | hiu₂
        · exact absurd (hP i hiu₁) (hnP i hit₁)
        · exact hnQ₂ i hiu₂
      · exact hnQ₁ i hit₂
    · intro h
      exact ⟨⟨∅, s, splitsAs_empty_self s,
          support_empty_of_neFree (.neg (.predc P c)) M, h⟩,
        ⟨∅, s, splitsAs_empty_self s,
          support_empty_of_neFree (.predc P c) M, h⟩⟩

/-- **Substitution salva veritate** ([yan-2023] §4.3.2): reinterpretation
    is bilaterally equivalent to the original — `∥φ∥_P` and `φ` are
    supported and anti-supported by exactly the same states. This is the
    team-semantic form of the classical equivalence
    `∀x Qx ≡ ∀x((Qx ∧ Px) ∨ (Qx ∧ ¬Px))` the paper invokes to license
    reinterpretation. Holds for any `sub` and any formula (the paper's
    conditions on `sub` — sub-predicatehood, salience — govern felicity,
    not truth); `eval_mapAtoms_iff` reduces it to the two atom
    equivalences. -/
theorem eval_reinterpret_iff (sub : Pred → Pred → Prop) [DecidableRel sub]
    (P : Pred) (φ : Formula Var Const Pred) (b : Bool)
    (s : Finset (Index W Var Domain)) :
    eval M b (reinterpret sub P φ) s ↔ eval M b φ s :=
  eval_mapAtoms_iff M
    (fun Q x b s => by
      show eval M b (if sub P Q then _ else _) s ↔ _
      split
      · exact eval_iff_of_atom_pred M P Q x b s
      · exact Iff.rfl)
    (fun Q c b s => by
      show eval M b (if sub P Q then _ else _) s ↔ _
      split
      · exact eval_iff_of_atom_predc M P Q c b s
      · exact Iff.rfl)
    φ b s

/-- Support is invariant under reinterpretation. -/
theorem support_reinterpret_iff (sub : Pred → Pred → Prop) [DecidableRel sub]
    (P : Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) :
    support M (reinterpret sub P φ) s ↔ support M φ s :=
  eval_reinterpret_iff M sub P φ true s

/-- Anti-support is invariant under reinterpretation. -/
theorem antiSupport_reinterpret_iff (sub : Pred → Pred → Prop)
    [DecidableRel sub] (P : Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) :
    antiSupport M (reinterpret sub P φ) s ↔ antiSupport M φ s :=
  eval_reinterpret_iff M sub P φ false s

end SalvaVeritate

/-! ### Ross's paradox under desire

"John wants to send the letter. ⇒ John wants to send the letter or burn
it." ([yan-2023] §4.1.3, after [crnic-2011]; deontic original
[ross-1944].) The monotonic step is semantically valid (`ross_monotone`,
the `[Want]A ⇒ [Want](A ∨ B)` mode of [yan-2023] Table 4.1, classified
semantically valid in §4.4.3); the paradoxical "ok to burn" follows by
□-FC only from the *enriched* disjunctive premise (`ross_fc`), which the
agent's actual desire state supports the premise of (`ross_premise`) but
not the enriched conclusion (`ross_blocked`) — the paper's Figure 4.2.
Enrichment placement follows Fact 13's official wide form `[□(· ∨ ·)]⁺`
rather than the figures' elliptical `□[· ∨ ·]⁺`. -/

/-- Ross-paradox predicates: sending and burning the letter. -/
inductive RossPred | send | burn
  deriving DecidableEq, Repr

/-- `SEND a`: the letter is sent (constant atom; `a` is the letter). -/
def sendL : Formula QVar Unit RossPred := .predc .send ()

/-- `BURN a`: the letter is burnt. -/
def burnL : Formula QVar Unit RossPred := .predc .burn ()

theorem sendL_neFree : sendL.NEFree := .predc _ _
theorem burnL_neFree : burnL.NEFree := .predc _ _

/-- John's bouletic state: a single desire-world where the letter is sent
    and not burnt, reflexively accessible. -/
def rossModel : Model Unit Unit Unit RossPred :=
  .ofMonadic (λ _ => {()}) (λ _ _ => ()) (λ _ P _ => P = RossPred.send)

/-- The Ross evaluation state: the single desire-world with the empty
    assignment. -/
def rossState : Finset (Index Unit QVar Unit) := {((), fun _ => none)}

/-- **Semantic validity of the monotonic step**:
    `□SEND a ⊨ □(SEND a ∨ BURN a)` — disjunction introduction under the
    bouletic `□` (`support_disj_inl` + `support_nec_mono`). -/
theorem ross_monotone {s : Finset (Index Unit QVar Unit)}
    (h : support rossModel sendL.nec s) :
    support rossModel (sendL.disj burnL).nec s :=
  support_nec_mono rossModel
    (fun _ ht => support_disj_inl rossModel burnL_neFree ht) h

/-- **Pragmatic validity of the FC step** ([yan-2023] (26), instance of
    Fact 13): `[□(SEND a ∨ BURN a)]⁺ ⊨ ◇SEND a ∧ ◇BURN a` — from the
    enriched disjunctive want, both "it is ok to send" and the paradoxical
    "it is ok to burn". Direct instance of `boxFC`. -/
theorem ross_fc {s : Finset (Index Unit QVar Unit)}
    (h : support rossModel (Formula.enrich (sendL.disj burnL).nec) s) :
    support rossModel (.poss sendL) s ∧ support rossModel (.poss burnL) s :=
  boxFC rossModel sendL_neFree burnL_neFree h

/-- The premise is assertable: John's desire state supports the enriched
    `[□SEND a]⁺`. -/
theorem ross_premise :
    support rossModel (Formula.enrich sendL.nec) rossState := by
  rw [support_enrich_nec_iff]
  refine ⟨fun i _ => ⟨fun j _ => rfl, ?_⟩, Finset.singleton_nonempty _⟩
  exact ⟨((), i.assign),
    State.mem_modalLift.mpr ⟨Finset.mem_singleton_self _, rfl⟩⟩

/-- **The block** ([yan-2023] Figure 4.2): John's desire state does *not*
    support the enriched disjunctive want `[□(SEND a ∨ BURN a)]⁺` — were it
    assertable, □-FC would force an accessible burn-world, and there is
    none. The paradox dissolves: `◇BURN a` is licensed only by a premise
    the discourse never grants. -/
theorem ross_blocked :
    ¬ support rossModel
      (Formula.enrich (sendL.disj burnL).nec) rossState := by
  intro h
  obtain ⟨-, hburn⟩ := ross_fc h
  obtain ⟨X, hX, ⟨w, hw⟩, hsupp⟩ :=
    hburn ((), fun _ => none) (Finset.mem_singleton_self _)
  have hmem : ((w, fun _ => none) : Index Unit QVar Unit) ∈
      State.modalLift X (fun _ => none) :=
    State.mem_modalLift.mpr ⟨hw, rfl⟩
  exact RossPred.noConfusion (hsupp _ hmem)

/-! ### Asher's puzzle

"Nicholas wants a free trip on the Concorde. ⇒ Nicholas wants a trip on
the Concorde." ([heim-1992], reported from Asher; [yan-2023] §4.3.2.) No
overt disjunction — the FC trigger is supplied by reinterpreting TRIP by
its salient sub-predicate FREE-TRIP: `∥TRIP x∥ = (F ∧ T)x ∨ (¬F ∧ T)x`.
The premise is `□∃x(Fx ∧ Tx)` — the paper's `◻∃xFREEx` unabbreviated, per
its footnote treating the generalization as conjunction elimination
(`TRIP(x) ∧ FREE(x) ⇒ TRIP(x)`) and its §4.5 gloss
`[Want](FREE ∧ TRIP) ⇒ [Want]TRIP`; the unabbreviated form is also what
makes the monotonic step QBSML-valid without a lexical meaning postulate.
The paper's (27) displays use `FREE` elliptically for the subscripted
`FREE_TRIP` form, so its conclusion `◊∃x¬FREEx` is our
`◇∃x(¬Fx ∧ Tx)`. -/

/-- Asher-puzzle predicates: being free and being a trip (on the
    Concorde). -/
inductive AsherPred | free | trip
  deriving DecidableEq, Repr

/-- FREE is the contextually salient sub-predicate of TRIP. -/
def subFree : AsherPred → AsherPred → Prop
  | .free, .trip => True
  | _, _ => False

instance : DecidableRel subFree := fun a b =>
  match a, b with
  | .free, .trip => .isTrue trivial
  | .free, .free => .isFalse id
  | .trip, .free => .isFalse id
  | .trip, .trip => .isFalse id

/-- `Fx ∧ Tx`: a free trip. -/
def freeTrip : Formula QVar Unit AsherPred :=
  .conj (.pred .free .x) (.pred .trip .x)

/-- `¬Fx ∧ Tx`: a non-free trip — the unwanted disjunct reinterpretation
    introduces. -/
def nonFreeTrip : Formula QVar Unit AsherPred :=
  .conj (.neg (.pred .free .x)) (.pred .trip .x)

theorem freeTrip_neFree : freeTrip.NEFree := .conj (.pred _ _) (.pred _ _)
theorem nonFreeTrip_neFree : nonFreeTrip.NEFree :=
  .conj (.neg (.pred _ _)) (.pred _ _)

/-- The premise `□∃x(Fx ∧ Tx)`: Nicholas wants a free trip. -/
def asherPremise : Formula QVar Unit AsherPred :=
  (Formula.exi .x freeTrip).nec

/-- The conclusion `□∃xTx`: Nicholas wants a trip. -/
def asherConcl : Formula QVar Unit AsherPred :=
  (Formula.exi QVar.x (.pred .trip .x)).nec

/-- Reinterpreting TRIP by FREE in the conclusion yields exactly the
    disjunctive want `□∃x((F ∧ T)x ∨ (¬F ∧ T)x)` — definitional. -/
theorem reinterpret_asherConcl :
    reinterpret subFree .free asherConcl =
      (Formula.exi QVar.x (.disj freeTrip nonFreeTrip)).nec := rfl

section AsherGeneric

variable {W Domain : Type*} [DecidableEq W] [DecidableEq Domain]
  [Fintype Domain]

/-- **Semantic validity of the monotonic step**: `□∃x(Fx ∧ Tx) ⊨ □∃xTx`
    (conjunction elimination under `∃` under `□`), for any model. -/
theorem asher_monotone (M : Model W Domain Unit AsherPred)
    {s : Finset (Index W QVar Domain)}
    (h : support M asherPremise s) : support M asherConcl s :=
  support_nec_mono M
    (fun _ h' => by
      obtain ⟨hf, hne, hs⟩ := h'
      exact ⟨hf, hne, hs.2⟩) h

/-- **The unwarranted inference** ([yan-2023] (27) and §4.4.3): the
    *enriched reinterpreted* conclusion `[□∃x∥Tx∥_F]⁺` licenses, by
    quantified □-FC, both "ok with a free trip" and "ok with a non-free
    trip" — the latter being what makes the monotonic conclusion sound
    wrong. -/
theorem asher_fc (M : Model W Domain Unit AsherPred)
    {s : Finset (Index W QVar Domain)}
    (h : support M
      (Formula.enrich (reinterpret subFree .free asherConcl)) s) :
    support M (.poss (.exi QVar.x freeTrip)) s ∧
    support M (.poss (.exi QVar.x nonFreeTrip)) s := by
  rw [reinterpret_asherConcl] at h
  exact boxExiFC M
    freeTrip_neFree nonFreeTrip_neFree h

end AsherGeneric

/-- Nicholas's bouletic state against a two-world background: in the
    desire-world `true` every trip is free; the non-desire world `false`
    has a non-free trip; only the desire-world is bouletically
    accessible. -/
def asherModel : Model Bool Unit Unit AsherPred :=
  .ofMonadic (λ _ => {true}) (λ _ _ => ()) (λ w P _ => P = .trip ∨ w = true)

/-- The Asher evaluation state: the desire-world with the empty
    assignment. -/
def asherState : Finset (Index Bool QVar Unit) := {(true, fun _ => none)}

/-- The paper's denotational side condition FREE ⊊ TRIP holds in the
    global model: FREE ⊆ TRIP at every world, strictly at the non-desire
    world. (In the desire-worlds themselves the inclusion is *not* strict —
    necessarily so, since blocking requires no accessible non-free trip;
    see `reinterpret`.) -/
theorem asherModel_free_ssubset_trip :
    (∀ w d, asherModel.relInterp₁ .free w d → asherModel.relInterp₁ .trip w d) ∧
    ∃ w d, asherModel.relInterp₁ .trip w d ∧
      ¬ asherModel.relInterp₁ .free w d :=
  ⟨fun _ _ _ => Or.inl rfl,
   false, (), Or.inl rfl, fun h => by
     rcases h with h | h
     · exact AsherPred.noConfusion h
     · exact Bool.noConfusion h⟩

/-- The premise is assertable: the desire state supports
    `[□∃x(Fx ∧ Tx)]⁺`. -/
theorem asher_premise :
    support asherModel (Formula.enrich asherPremise) asherState := by
  show support asherModel
    (Formula.enrich (Formula.exi QVar.x freeTrip).nec) asherState
  rw [support_enrich_nec_iff]
  refine ⟨fun i _ => ?_, Finset.singleton_nonempty _⟩
  have hLne : (State.modalLift {true} i.assign :
      Finset (Index Bool QVar Unit)).Nonempty :=
    ⟨(true, i.assign),
      State.mem_modalLift.mpr ⟨Finset.mem_singleton_self _, rfl⟩⟩
  have hext : (State.extendFunctional (State.modalLift {true} i.assign)
      QVar.x (fun _ => {()})).Nonempty := by
    obtain ⟨j, hj⟩ := hLne
    exact ⟨j.update QVar.x (),
      State.mem_extendFunctional.mpr
        ⟨j, hj, (), Finset.mem_singleton_self _, rfl⟩⟩
  have hpt : ∀ P : AsherPred, ∀ j ∈ State.extendFunctional
      (State.modalLift {true} i.assign) QVar.x (fun _ => ({()} : Finset Unit)),
      ∃ d, j.assign QVar.x = some d ∧ asherModel.relInterp₁ P j.world d := by
    intro P j hj
    obtain ⟨i', hi', d, -, rfl⟩ := State.mem_extendFunctional.mp hj
    exact ⟨d, by simp,
      Or.inr (Finset.mem_singleton.mp (State.mem_modalLift.mp hi').1)⟩
  refine ⟨⟨fun _ => {()}, fun _ _ => Finset.singleton_nonempty _, ?_⟩, hLne⟩
  exact ⟨⟨⟨hpt .free, hext⟩, ⟨hpt .trip, hext⟩⟩, hext⟩

/-- **The block** ([yan-2023] Figure 4.3): the desire state does *not*
    support the enriched reinterpreted conclusion `[□∃x∥Tx∥_F]⁺` — by
    `asher_fc` it would force an accessible non-free-trip witness, and all
    trips in Nicholas's desire-worlds are free. "Ok with a non-free trip"
    is licensed only by a premise the discourse never grants. -/
theorem asher_blocked :
    ¬ support asherModel
      (Formula.enrich (reinterpret subFree .free asherConcl))
      asherState := by
  intro h
  obtain ⟨-, hnf⟩ := asher_fc asherModel h
  obtain ⟨X, hX, ⟨w, hw⟩, hsupp⟩ :=
    hnf (true, fun _ => none) (Finset.mem_singleton_self _)
  obtain ⟨hf, hfne, hs⟩ := hsupp
  have hmem : ((w, fun _ => none) : Index Bool QVar Unit) ∈
      State.modalLift X (fun _ => none) :=
    State.mem_modalLift.mpr ⟨hw, rfl⟩
  obtain ⟨d, hd⟩ := hfne _ hmem
  have hjmem : Index.update ((w, fun _ => none) : Index Bool QVar Unit)
      QVar.x d ∈
      State.extendFunctional (State.modalLift X (fun _ => none))
        QVar.x hf :=
    State.mem_extendFunctional.mpr ⟨_, hmem, d, hd, rfl⟩
  obtain ⟨d', -, hnp⟩ := hs.1 _ hjmem
  exact hnp (Or.inr (Finset.mem_singleton.mp (hX hw)))

/-- **Reinterpretation is pragmatically non-vacuous** ([yan-2023] §4.4.3:
    "it is possible to have a counterexample where `[∃xQx]⁺` is supported
    but `[∃x((Px ∨ ¬Px) ∧ Qx)]⁺` is not" — displayed there with the
    `(Px ∨ ¬Px) ∧ Qx` shape rather than Definition 32's). The
    *unreinterpreted* enriched conclusion `[□∃xTx]⁺` IS supported at the
    very state where `asher_blocked` refutes the enriched reinterpreted
    form — the two classically equivalent formulas (`eval_reinterpret_iff`)
    come apart under `[·]⁺`, which is the paper's whole point. -/
theorem asher_concl_enriched :
    support asherModel (Formula.enrich asherConcl) asherState := by
  show support asherModel
    (Formula.enrich (Formula.exi QVar.x (.pred .trip .x)).nec)
    asherState
  rw [support_enrich_nec_iff]
  refine ⟨fun i _ => ?_, Finset.singleton_nonempty _⟩
  have hLne : (State.modalLift {true} i.assign :
      Finset (Index Bool QVar Unit)).Nonempty :=
    ⟨(true, i.assign),
      State.mem_modalLift.mpr ⟨Finset.mem_singleton_self _, rfl⟩⟩
  have hext : (State.extendFunctional (State.modalLift {true} i.assign)
      QVar.x (fun _ => {()})).Nonempty := by
    obtain ⟨j, hj⟩ := hLne
    exact ⟨j.update QVar.x (),
      State.mem_extendFunctional.mpr
        ⟨j, hj, (), Finset.mem_singleton_self _, rfl⟩⟩
  refine ⟨⟨fun _ => {()}, fun _ _ => Finset.singleton_nonempty _, ?_, hext⟩,
    hLne⟩
  intro j hj
  obtain ⟨i', -, d, -, rfl⟩ := State.mem_extendFunctional.mp hj
  exact ⟨d, by simp, Or.inl rfl⟩

/-! ### Heim's example

"I want to teach on Tuesdays next semester. ⇒ I want to teach next
semester." ([heim-1992]; [yan-2023] §4.3.3.) Same shape as Asher's puzzle:
TEACH is reinterpreted by its salient sub-predicate TEACH-ON-TUESDAY, and
quantified □-FC then licenses the unjustified "ok to teach on non-Tuesdays".
The paper omits the rest of the derivation as parallel to Asher's
(§4.4.3: "the details … are omitted"); so do we — the blocking countermodel
is isomorphic to `asher_blocked`'s. The paper also sketches an alternative
◊-FC route via the conditional-desire rephrasing of the example (its
(17)–(18)); that variant is not formalized here. -/

/-- Heim-example predicates: being on Tuesday and being a teaching (next
    semester). -/
inductive HeimPred | tuesday | teach
  deriving DecidableEq, Repr

/-- TUESDAY is the contextually salient sub-predicate of TEACH. -/
def subTuesday : HeimPred → HeimPred → Prop
  | .tuesday, .teach => True
  | _, _ => False

instance : DecidableRel subTuesday := fun a b =>
  match a, b with
  | .tuesday, .teach => .isTrue trivial
  | .tuesday, .tuesday => .isFalse id
  | .teach, .tuesday => .isFalse id
  | .teach, .teach => .isFalse id

/-- `TUEx ∧ TEACHx`: a Tuesday teaching. -/
def tuesdayTeach : Formula QVar Unit HeimPred :=
  .conj (.pred .tuesday .x) (.pred .teach .x)

/-- `¬TUEx ∧ TEACHx`: a non-Tuesday teaching. -/
def nonTuesdayTeach : Formula QVar Unit HeimPred :=
  .conj (.neg (.pred .tuesday .x)) (.pred .teach .x)

/-- The conclusion `□∃x TEACHx`: I want to teach next semester. -/
def heimConcl : Formula QVar Unit HeimPred :=
  (Formula.exi QVar.x (.pred .teach .x)).nec

/-- **The unwarranted inference** ([yan-2023] §4.4.3, "Reinterpretation of
    TEACH"): the enriched reinterpreted conclusion `[□∃x∥TEACHx∥_TUE]⁺`
    licenses "ok to teach on a non-Tuesday" by quantified □-FC. -/
theorem heim_fc {W Domain : Type*} [DecidableEq W] [DecidableEq Domain]
    [Fintype Domain] (M : Model W Domain Unit HeimPred)
    {s : Finset (Index W QVar Domain)}
    (h : support M
      (Formula.enrich (reinterpret subTuesday .tuesday heimConcl)) s) :
    support M (.poss (.exi QVar.x tuesdayTeach)) s ∧
    support M (.poss (.exi QVar.x nonTuesdayTeach)) s :=
  boxExiFC M
    (.conj (.pred _ _) (.pred _ _))
    (.conj (.neg (.pred _ _)) (.pred _ _)) h

end Yan2023
