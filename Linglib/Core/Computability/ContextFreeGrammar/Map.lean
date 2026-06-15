import Mathlib.Computability.ContextFreeGrammar
import Linglib.Core.Computability.StringHom

/-!
# Closure of `IsContextFree` under string homomorphism

The image of a context-free language under a string homomorphism `h : T → List T'`
is context-free. Construction: replace each terminal `a` in each grammar rule's
output with the symbol-list `(h a).map .terminal`. Nonterminals are unchanged.

Owns the `Language.stringMap` definition and proves
`Language.IsContextFree.stringMap`. Together with the parallel Bar-Hillel
proof in `InterRegular.lean`, this dissolves the closure axioms previously
in `Closure.lean`.

[hopcroft-motwani-ullman-2000] Theorem 7.24 part 4 (p. 284-285, homomorphism case).
-/

open scoped Classical

universe u v

variable {T : Type u} {T' : Type v}

/-- The homomorphic image of a language under a string homomorphism.
    `Language.stringMap h L = {h(v) | v ∈ L}`. -/
def Language.stringMap (h : Core.StringHom T T') (L : Language T) : Language T' :=
  {w | ∃ v ∈ L, Core.StringHom.apply h v = w}

namespace ContextFreeRule

variable {N : Type*}

/-- Apply a string homomorphism `h : T → List T'` to a single `Symbol`,
    producing a symbol-list. Terminals are substituted; nonterminals are
    preserved as singletons. -/
def Symbol.applyHom (h : T → List T') : Symbol T N → List (Symbol T' N)
  | .terminal a => (h a).map .terminal
  | .nonterminal X => [.nonterminal X]

/-- Apply a string homomorphism `h : T → List T'` to a symbol list (free
    monoid functoriality). -/
def applyHomList (h : T → List T') : List (Symbol T N) → List (Symbol T' N) :=
  List.flatMap (Symbol.applyHom h)

@[simp] theorem applyHomList_nil (h : T → List T') :
    applyHomList h ([] : List (Symbol T N)) = [] := rfl

@[simp] theorem applyHomList_cons (h : T → List T') (s : Symbol T N)
    (ss : List (Symbol T N)) :
    applyHomList h (s :: ss) = Symbol.applyHom h s ++ applyHomList h ss := by
  simp [applyHomList, List.flatMap_cons]

theorem applyHomList_append (h : T → List T') (xs ys : List (Symbol T N)) :
    applyHomList h (xs ++ ys) = applyHomList h xs ++ applyHomList h ys :=
  List.flatMap_append

@[simp] theorem applyHomList_singleton_terminal (h : T → List T') (a : T) :
    applyHomList h ([Symbol.terminal a] : List (Symbol T N)) = (h a).map .terminal := by
  simp [applyHomList, Symbol.applyHom]

@[simp] theorem applyHomList_singleton_nonterminal (h : T → List T') (X : N) :
    applyHomList h ([Symbol.nonterminal X] : List (Symbol T N)) = [.nonterminal X] := by
  simp [applyHomList, Symbol.applyHom]

/-- For a list of terminals, `applyHomList` becomes `flatMap h` followed by
    re-wrapping as terminals. -/
theorem applyHomList_map_terminal (h : T → List T') (w : List T) :
    applyHomList h (w.map (Symbol.terminal (N := N))) =
    (List.flatMap h w).map .terminal := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, applyHomList_cons, Symbol.applyHom, ih,
               List.flatMap_cons, List.map_append]

/-- Apply a string homomorphism to a CFG rule. -/
def applyHom (h : T → List T') (r : ContextFreeRule T N) : ContextFreeRule T' N where
  input := r.input
  output := applyHomList h r.output

@[simp] theorem applyHom_input (h : T → List T') (r : ContextFreeRule T N) :
    (r.applyHom h).input = r.input := rfl

@[simp] theorem applyHom_output (h : T → List T') (r : ContextFreeRule T N) :
    (r.applyHom h).output = applyHomList h r.output := rfl

/-- A single rule's `Rewrites` relation lifts under `applyHom`. -/
theorem Rewrites.applyHom (h : T → List T') {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (hr : r.Rewrites u v) :
    (r.applyHom h).Rewrites (applyHomList h u) (applyHomList h v) := by
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  simp only [applyHomList_append, applyHomList_singleton_nonterminal]
  exact rewrites_of_exists_parts (r.applyHom h)
    (applyHomList h p) (applyHomList h q)

end ContextFreeRule

namespace ContextFreeGrammar

/-- Apply a string homomorphism to a CFG: substitute terminals in every rule.
    Noncomputable due to `Finset.image` requiring decidable equality on rules
    (provided classically). -/
noncomputable def applyHom (h : T → List T') (G : ContextFreeGrammar T) : ContextFreeGrammar T' where
  NT := G.NT
  initial := G.initial
  rules := G.rules.image (ContextFreeRule.applyHom h)

@[simp] theorem applyHom_NT (h : T → List T') (G : ContextFreeGrammar T) :
    (G.applyHom h).NT = G.NT := rfl

@[simp] theorem applyHom_initial (h : T → List T') (G : ContextFreeGrammar T) :
    (G.applyHom h).initial = G.initial := rfl

theorem applyHom_rules (h : T → List T') (G : ContextFreeGrammar T) :
    (G.applyHom h).rules = G.rules.image (ContextFreeRule.applyHom h) := rfl

/-- `Produces` lifts under `applyHom`. -/
theorem Produces.applyHom (h : T → List T') {G : ContextFreeGrammar T}
    {u v : List (Symbol T G.NT)} (huv : G.Produces u v) :
    (G.applyHom h).Produces
      (ContextFreeRule.applyHomList h u) (ContextFreeRule.applyHomList h v) := by
  obtain ⟨r, hr_mem, hrw⟩ := huv
  refine ⟨r.applyHom h, ?_, hrw.applyHom h⟩
  rw [applyHom_rules]
  exact Finset.mem_image.mpr ⟨r, hr_mem, rfl⟩

/-- `Derives` lifts under `applyHom`. -/
theorem Derives.applyHom (h : T → List T') {G : ContextFreeGrammar T}
    {u v : List (Symbol T G.NT)} (huv : G.Derives u v) :
    (G.applyHom h).Derives
      (ContextFreeRule.applyHomList h u) (ContextFreeRule.applyHomList h v) := by
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.applyHom h)

end ContextFreeGrammar

-- ============================================================================
-- Language equality
-- ============================================================================

namespace ContextFreeGrammar

/-- Forward inclusion: every `(G.applyHom h)`-generated string is in
    `Language.stringMap h G.language`. -/
theorem applyHom_language_subset (h : T → List T') (G : ContextFreeGrammar T) :
    Language.stringMap h G.language ≤ (G.applyHom h).language := by
  rintro w' ⟨w, hw, rfl⟩
  show (G.applyHom h).Derives [.nonterminal G.initial]
        ((Core.StringHom.apply h w).map .terminal)
  have hd := Derives.applyHom h hw
  convert hd using 1
  · simp [ContextFreeRule.Symbol.applyHom]
  · simp [Core.StringHom.apply, ContextFreeRule.applyHomList_map_terminal]

-- ============================================================================
-- Backward direction helpers (private to this file)
-- ============================================================================

/-- If a terminal-only prefix `ts.map .terminal` is followed by `R` and the
    whole equals `p ++ [.nonterminal X] ++ q`, then `ts.map .terminal` is a
    prefix of `p`. -/
private lemma terminal_prefix_split {N : Type*} (ts : List T') :
    ∀ {R : List (Symbol T' N)} {p : List (Symbol T' N)} {X : N}
      {q : List (Symbol T' N)},
    ts.map (Symbol.terminal (N := N)) ++ R = p ++ [Symbol.nonterminal X] ++ q →
    ∃ p_rest, p = ts.map .terminal ++ p_rest ∧
              R = p_rest ++ [Symbol.nonterminal X] ++ q := by
  induction ts with
  | nil =>
    intro R p X q heq
    refine ⟨p, by simp, ?_⟩
    simpa using heq
  | cons t ts' ih =>
    intro R p X q heq
    rw [List.map_cons, List.cons_append] at heq
    cases p with
    | nil =>
      rw [List.nil_append, List.singleton_append, List.cons.injEq] at heq
      cases heq.1
    | cons ph pt =>
      rw [List.cons_append, List.cons_append, List.cons.injEq] at heq
      obtain ⟨hph, hrest⟩ := heq
      obtain ⟨p_rest, hpt_eq, hR_eq⟩ := ih hrest
      refine ⟨p_rest, ?_, hR_eq⟩
      rw [List.map_cons, List.cons_append, ← hph, hpt_eq]

/-- If a terminal-only prefix `ts.map .terminal` is followed by `R` and the
    whole equals `w'.map .terminal`, then `ts` is a prefix of `w'`. -/
private lemma terminal_map_prefix {N : Type*} (ts : List T') :
    ∀ {R : List (Symbol T' N)} {w' : List T'},
    ts.map (Symbol.terminal (N := N)) ++ R = w'.map .terminal →
    ∃ w'_rest, w' = ts ++ w'_rest ∧ R = w'_rest.map .terminal := by
  induction ts with
  | nil =>
    intro R w' heq
    refine ⟨w', by simp, ?_⟩
    simpa using heq
  | cons t ts' ih =>
    intro R w' heq
    rw [List.map_cons, List.cons_append] at heq
    cases w' with
    | nil =>
      rw [List.map_nil] at heq
      cases heq
    | cons w ws =>
      rw [List.map_cons, List.cons.injEq] at heq
      obtain ⟨hwt, hrest⟩ := heq
      injection hwt with htw
      obtain ⟨w'_rest, hws_eq, hR_eq⟩ := ih hrest
      refine ⟨w'_rest, ?_, hR_eq⟩
      rw [List.cons_append, hws_eq, htw]

/-- Decompose an `applyHomList` equation: if `applyHomList h m = p ++
    [.nonterminal X] ++ q`, then there exist `pm`, `qm` on the G-side with
    `m = pm ++ [.nonterminal X] ++ qm` whose images recover `p` and `q`.
    The load-bearing lemma for lifting G'-derivations to G-derivations. -/
private lemma decompose_applyHomList {h : T → List T'} {N : Type*}
    (m : List (Symbol T N)) :
    ∀ {p : List (Symbol T' N)} {X : N} {q : List (Symbol T' N)},
    ContextFreeRule.applyHomList h m = p ++ [Symbol.nonterminal X] ++ q →
    ∃ pm qm : List (Symbol T N),
      m = pm ++ [Symbol.nonterminal X] ++ qm ∧
      ContextFreeRule.applyHomList h pm = p ∧
      ContextFreeRule.applyHomList h qm = q := by
  induction m with
  | nil =>
    intro p X q heq
    rw [ContextFreeRule.applyHomList_nil] at heq
    exfalso
    have hl := congr_arg List.length heq
    simp at hl
  | cons s rest ih =>
    intro p X q heq
    rw [ContextFreeRule.applyHomList_cons] at heq
    cases s with
    | nonterminal Y =>
      simp only [ContextFreeRule.Symbol.applyHom, List.singleton_append] at heq
      cases p with
      | nil =>
        rw [List.nil_append, List.singleton_append, List.cons.injEq] at heq
        obtain ⟨hYX, hreq⟩ := heq
        injection hYX with hYX'
        refine ⟨[], rest, ?_, rfl, hreq⟩
        rw [List.nil_append, List.singleton_append, hYX']
      | cons ph pt =>
        rw [List.cons_append, List.cons_append, List.cons.injEq] at heq
        obtain ⟨hph, hrest⟩ := heq
        obtain ⟨pm', qm', hrest_eq, hpm', hqm'⟩ := ih hrest
        refine ⟨.nonterminal Y :: pm', qm', ?_, ?_, hqm'⟩
        · rw [List.cons_append, List.cons_append, hrest_eq]
        · rw [ContextFreeRule.applyHomList_cons]
          simp only [ContextFreeRule.Symbol.applyHom, List.singleton_append]
          rw [hpm', hph]
    | terminal a =>
      simp only [ContextFreeRule.Symbol.applyHom] at heq
      obtain ⟨p_rest, hp_eq, hR_eq⟩ := terminal_prefix_split (h a) heq
      obtain ⟨pm', qm', hrest_eq, hpm', hqm'⟩ := ih hR_eq
      refine ⟨.terminal a :: pm', qm', ?_, ?_, hqm'⟩
      · rw [List.cons_append, List.cons_append, hrest_eq]
      · rw [ContextFreeRule.applyHomList_cons]
        simp only [ContextFreeRule.Symbol.applyHom]
        rw [hpm']
        exact hp_eq.symm

/-- Lift a one-step `Produces` of `G.applyHom h` to a one-step `Produces` of
    `G`, given a preimage `s` of the source. -/
private lemma producesLift {h : T → List T'} {G : ContextFreeGrammar T}
    {m' t' : List (Symbol T' G.NT)} (hp : (G.applyHom h).Produces m' t')
    {s : List (Symbol T G.NT)} (hs : ContextFreeRule.applyHomList h s = m') :
    ∃ t : List (Symbol T G.NT),
      G.Produces s t ∧ ContextFreeRule.applyHomList h t = t' := by
  obtain ⟨r', hr'_mem, hrw⟩ := hp
  rw [ContextFreeGrammar.applyHom_rules] at hr'_mem
  obtain ⟨r, hr_mem, hr_eq⟩ := Finset.mem_image.mp hr'_mem
  subst hr_eq
  obtain ⟨p, q, hm'_eq, ht'_eq⟩ := hrw.exists_parts
  rw [ContextFreeRule.applyHom_input] at hm'_eq
  rw [ContextFreeRule.applyHom_output] at ht'_eq
  rw [← hs] at hm'_eq
  obtain ⟨ps, qs, hs_eq, hps, hqs⟩ := decompose_applyHomList s hm'_eq
  refine ⟨ps ++ r.output ++ qs, ?_, ?_⟩
  · refine ⟨r, hr_mem, ?_⟩
    rw [hs_eq]
    exact ContextFreeRule.rewrites_of_exists_parts r ps qs
  · rw [ContextFreeRule.applyHomList_append, ContextFreeRule.applyHomList_append,
        hps, hqs]
    exact ht'_eq.symm

/-- Lift a multi-step `Derives` of `G.applyHom h` to a `Derives` of `G`,
    given a preimage `s` of the source. -/
private lemma derivesLift {h : T → List T'} {G : ContextFreeGrammar T}
    {m' t' : List (Symbol T' G.NT)} (hd : (G.applyHom h).Derives m' t') :
    ∀ {s : List (Symbol T G.NT)}, ContextFreeRule.applyHomList h s = m' →
    ∃ t : List (Symbol T G.NT),
      G.Derives s t ∧ ContextFreeRule.applyHomList h t = t' := by
  induction hd with
  | refl =>
    intro s hs
    exact ⟨s, Relation.ReflTransGen.refl, hs⟩
  | tail _ hstep ih =>
    intro s hs
    obtain ⟨m_lift, hG_m_lift, hm_lift_eq⟩ := ih hs
    obtain ⟨t_lift, hstep_lift, ht_lift_eq⟩ := producesLift hstep hm_lift_eq
    exact ⟨t_lift, hG_m_lift.tail hstep_lift, ht_lift_eq⟩

/-- Recover a terminal preimage `w` from an `applyHomList` of a
    G-side symbol-list `t` that produces an all-terminal G'-side string
    `w'.map .terminal`. -/
private lemma liftMapTerminal {h : T → List T'} {N : Type*} :
    ∀ {t : List (Symbol T N)} {w' : List T'},
    ContextFreeRule.applyHomList h t = w'.map (Symbol.terminal (N := N)) →
    ∃ w : List T, t = w.map .terminal ∧ Core.StringHom.apply h w = w' := by
  intro t
  induction t with
  | nil =>
    intro w' heq
    rw [ContextFreeRule.applyHomList_nil] at heq
    have hw' : w' = [] := List.map_eq_nil_iff.mp heq.symm
    refine ⟨[], rfl, ?_⟩
    rw [hw']; rfl
  | cons s rest ih =>
    intro w' heq
    rw [ContextFreeRule.applyHomList_cons] at heq
    cases s with
    | nonterminal Y =>
      simp only [ContextFreeRule.Symbol.applyHom, List.singleton_append] at heq
      cases w' with
      | nil =>
        rw [List.map_nil] at heq
        cases heq
      | cons w ws =>
        rw [List.map_cons, List.cons.injEq] at heq
        cases heq.1
    | terminal a =>
      simp only [ContextFreeRule.Symbol.applyHom] at heq
      obtain ⟨w'_rest, hw'_eq, hR_eq⟩ := terminal_map_prefix (h a) heq
      obtain ⟨w_rest, hrest_eq, happly⟩ := ih hR_eq
      refine ⟨a :: w_rest, ?_, ?_⟩
      · rw [List.map_cons, hrest_eq]
      · rw [hw'_eq, ← happly]
        rfl

/-- Backward inclusion: every `(G.applyHom h)`-generated string is the image
    of some `G`-generated preimage under `h`. The construction lifts
    G'-derivations to G-derivations step-by-step using `decompose_applyHomList`
    and `liftMapTerminal`. Standard textbook construction
    ([hopcroft-motwani-ullman-2000] Theorem 7.24 part 4 (p. 284-285, homomorphism case)). -/
theorem applyHom_language_subset_inv (h : T → List T') (G : ContextFreeGrammar T) :
    (G.applyHom h).language ≤ Language.stringMap h G.language := by
  intro w' hw'
  -- hw' : (G.applyHom h).Derives [.nonterminal G.initial] (w'.map .terminal)
  have hlift : ContextFreeRule.applyHomList h
                 ([Symbol.nonterminal G.initial] : List (Symbol T G.NT)) =
               [Symbol.nonterminal G.initial] := by
    simp [ContextFreeRule.applyHomList, ContextFreeRule.Symbol.applyHom]
  obtain ⟨t, hGt, ht_eq⟩ := derivesLift hw' hlift
  obtain ⟨w, hw_term, hw_apply⟩ := liftMapTerminal ht_eq
  refine ⟨w, ?_, hw_apply⟩
  show G.Derives [.nonterminal G.initial] (w.map .terminal)
  rw [← hw_term]; exact hGt

theorem applyHom_language (h : T → List T') (G : ContextFreeGrammar T) :
    (G.applyHom h).language = Language.stringMap h G.language :=
  le_antisymm (applyHom_language_subset_inv h G) (applyHom_language_subset h G)

end ContextFreeGrammar

namespace Language.IsContextFree

theorem stringMap (h : Core.StringHom T T') {L : Language T}
    (hL : L.IsContextFree) : (Language.stringMap h L).IsContextFree := by
  obtain ⟨G, rfl⟩ := hL
  exact ⟨G.applyHom h, ContextFreeGrammar.applyHom_language h G⟩

end Language.IsContextFree
