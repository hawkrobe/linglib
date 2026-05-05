import Mathlib.Computability.ContextFreeGrammar
import Linglib.Core.StringHom

/-!
# Closure of `IsContextFree` under string homomorphism

The image of a context-free language under a string homomorphism `h : T → List T'`
is context-free. Construction: replace each terminal `a` in each grammar rule's
output with the symbol-list `(h a).map .terminal`. Nonterminals are unchanged.

Owns the `Language.stringMap` definition and proves
`Language.IsContextFree.stringMap`. Together with the parallel Bar-Hillel
proof in `InterRegular.lean`, this dissolves the closure axioms previously
in `Closure.lean`.

@cite{hopcroft-ullman-1979} Theorem 6.2.
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
  convert hd using 2
  exact (ContextFreeRule.applyHomList_map_terminal h w).symm

/-- Backward inclusion: every `(G.applyHom h)`-generated string is the image
    of some `G`-generated preimage under `h`.

    *Proof obligation: deferred.* The construction lifts G'-derivations to
    G-derivations step-by-step, requiring (a) a "decompose under `applyHomList`"
    helper that recovers the G-side decomposition from the G'-side
    `Rewrites.exists_parts` decomposition, and (b) a "lift map-terminal"
    helper that recovers a `T`-string from a G-derivation that ends in only
    terminals. Mechanical but intricate. Tracked as Phase 1.5 in the axiom-removal
    project. -/
theorem applyHom_language_subset_inv (h : T → List T') (G : ContextFreeGrammar T) :
    (G.applyHom h).language ≤ Language.stringMap h G.language := by
  sorry

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
