module

public import Linglib.Core.Computability.ContextFreeGrammar.InterRegular
public import Linglib.Core.Computability.NonContextFree.AmBnCmDn
public import Linglib.Fragments.SwissGerman.Case
public import Linglib.Data.Examples.Shieber1985

/-!
# Shieber (1985): Evidence Against the Context-Freeness of Natural Language

This file formalizes the paper's proof that Swiss German is not weakly context-free. Two facts
about the language carry the argument: verbs subcategorize for dative or accusative objects, and
subordinate clauses allow the cross-serial order in which all the noun phrases precede all the
verbs, the case requirements holding across the construction ((1)–(8)). The proof rests on four
claims about the string set alone (§3): clauses with all verbs after all noun phrases exist
(Claim 1), among them those with the noun phrases and the verbs each sorted by case (Claim 2),
the dative and the accusative verbs are as many as the dative and the accusative noun phrases
(Claim 3), and the verbs are unbounded in number (Claim 4). The homomorphism `f` sends
*d'chind*, *em Hans*, *laa* and *hälfe* to `a`, `b`, `c`, `d` and the rest of a clause to fixed
letters; intersecting the image with the regular language `w a* b* x c* d* y` leaves
`w aᵐ bⁿ x cᵐ dⁿ y`, which is not context-free, and since context-free languages are closed
under homomorphisms and under intersection with regular languages ([bar-hillel-perles-shamir-1961],
[hopcroft-motwani-ullman-2000]), neither is Swiss German. Strong non-context-freeness follows as
a corollary, and the argument, unlike the Dutch one of [bresnan-etal-1982] that
[gazdar-pullum-1982] contested, mentions neither constituent structure nor meaning.

`swissGermanLang` is any language over the paper's token classes meeting Claims 1 to 3,
`tokenStringHom` the homomorphism with the boundary material erased, `caseSorted` the regular
filter, and `stringMap_swissGerman_inter_caseSorted_eq_ambncmdn` the intersection equality that
`swiss_german_not_contextFree` feeds to the closure theorems. Claim 3 is checked against all
twenty-two clauses of the paper (`caseMatched_rows`): the starred ones are exactly those whose
case requirements go unmet, whatever the order of their constituents (§4.2), and every
case-matched clause in cross-serial order is in the language (`tokens_mem_swissGermanLang`).

## Implementation notes

* The letters follow the schema of Claim 2 and the definition of `f`, in which the accusative
  *d'chind* and *laa* precede the dative *em Hans* and *hälfe*; the prose of Claim 2 puts the
  datives first. The boundary strings `w`, `x`, `y` are erased rather than kept, the second image
  of the paper's fifth note, so the witness is `aᵐ bⁿ cᵐ dⁿ` itself.
* Verb cases are read off the Fragment's lexemes (`SwissGerman.Case.verbObjectCase`), *laa*
  being the infinitive of *lönd*; the raising verbs *haend* and *wele* take no object and count as
  boundary material.

## References

* [shieber-1985]
* [bar-hillel-perles-shamir-1961]
* [hopcroft-motwani-ullman-2000]
* [bresnan-etal-1982]
* [gazdar-pullum-1982]
-/

@[expose] public section

namespace Shieber1985

open SwissGerman.Case Data.Examples

/-! ### Tokens, the homomorphism and the language -/

/-- A token of a subordinate clause, projected to the classes the argument uses: a noun phrase
or a verb with its case, or boundary material such as the raising verbs. -/
inductive Token
  | accNP | datNP | accV | datV | boundary
  deriving DecidableEq, Repr

/-- The noun-phrase token of an object case. -/
def Token.np (c : Case) : Option Token :=
  if c = .acc then some .accNP else if c = .dat then some .datNP else none

/-- The verb token of a Fragment lexeme, by the case it requires. -/
def Token.v (v : CrossSerialVerb) : Token :=
  if verbObjectCase v = .dat then .datV else .accV

def Token.isNP : Token → Bool
  | .accNP | .datNP => true
  | _ => false

def Token.isV : Token → Bool
  | .accV | .datV => true
  | _ => false

def Token.isBoundary : Token → Bool
  | .boundary => true
  | _ => false

/-- The homomorphism `f` with the boundary erased: *d'chind* to `a`, *em Hans* to `b`, *laa*
to `c` and *hälfe* to `d`, lifted to strings by `List.flatMap`. -/
def tokenStringHom : Token → List FourSymbol
  | .accNP => [.a]
  | .datNP => [.b]
  | .accV => [.c]
  | .datV => [.d]
  | .boundary => []

/-- Any language over the tokens meeting Claims 1 to 3: with the boundary material erased, a
clause is its noun phrases followed by its verbs, with as many dative and accusative verbs as
dative and accusative noun phrases. -/
def swissGermanLang : Language Token :=
  { ts | ∃ nps vs : List Token,
      ts.filter (!·.isBoundary) = nps ++ vs ∧
      (∀ t ∈ nps, t.isNP = true) ∧ (∀ t ∈ vs, t.isV = true) ∧
      nps.count .datNP = vs.count .datV ∧ nps.count .accNP = vs.count .accV }

/-- The clause of the schema of Claim 2 with `m` accusative and `n` dative pairs. -/
def canonical (m n : ℕ) : List Token :=
  List.replicate m .accNP ++ List.replicate n .datNP ++
    List.replicate m .accV ++ List.replicate n .datV

theorem flatMap_canonical (m n : ℕ) :
    (canonical m n).flatMap tokenStringHom = makeString_ambncmdn m n := by
  simp [canonical, tokenStringHom, makeString_ambncmdn, List.flatMap_replicate]

/-! ### The paper's clauses (1)–(22) -/

/-- A clause of the paper's data: the cases of its noun phrases in order, its case-taking verbs
as Fragment lexemes in order, and its judgment. -/
structure Row where
  nps : List Case
  verbs : List CrossSerialVerb
  acceptable : Bool
  deriving DecidableEq, Repr

/-- Read the noun-phrase cases off a feature string: `A` accusative, `D` dative. -/
def parseCases (s : String) : List Case :=
  s.toList.filterMap λ
    | 'A' => some .acc
    | 'D' => some .dat
    | _ => none

/-- Read the verbs off a feature string: `L` *lönd* or *laa*, `H` *hälfe*, `A` *aastriiche*. -/
def parseVerbs (s : String) : List CrossSerialVerb :=
  s.toList.filterMap λ
    | 'L' => some .loend
    | 'H' => some .haelfe
    | 'A' => some .aastriiche
    | _ => none

def Row.ofExample (e : LinguisticExample) : Option Row := do
  let n ← e.paperFeatures.lookup "nps"
  let v ← e.paperFeatures.lookup "verbs"
  pure ⟨parseCases n, parseVerbs v, match e.judgment with | .acceptable => true | _ => false⟩

/-- The clauses (1)–(22). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Claim 3 on a clause: the dative and the accusative verbs are as many as the dative and the
accusative noun phrases. -/
def Row.CaseMatched (r : Row) : Prop :=
  r.nps.count .dat = (r.verbs.map verbObjectCase).count .dat ∧
    r.nps.count .acc = (r.verbs.map verbObjectCase).count .acc

instance : DecidablePred Row.CaseMatched := λ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem rows_complete : ∀ e ∈ Examples.all, (Row.ofExample e).isSome = true := by decide

/-- Claim 3 against the paper's data: a clause is grammatical exactly when its case requirements
are met, whatever the order of its constituents (§4.2). -/
theorem caseMatched_rows : ∀ r ∈ rows, r.acceptable = true ↔ r.CaseMatched := by decide

/-- The token string of a clause in cross-serial order: its noun phrases, then its verbs. -/
def Row.tokens (r : Row) : List Token := r.nps.filterMap Token.np ++ r.verbs.map Token.v

private theorem count_np_filterMap (cs : List Case) :
    (cs.filterMap Token.np).count .datNP = cs.count .dat ∧
      (cs.filterMap Token.np).count .accNP = cs.count .acc := by
  induction cs with
  | nil => simp
  | cons c cs ih => cases c <;> simp [Token.np] at ih ⊢ <;> omega

private theorem count_v_map (vs : List CrossSerialVerb) :
    (vs.map Token.v).count .datV = (vs.map verbObjectCase).count .dat ∧
      (vs.map Token.v).count .accV = (vs.map verbObjectCase).count .acc := by
  induction vs with
  | nil => simp
  | cons v vs ih => cases v <;> simp [Token.v, verbObjectCase, ih]

/-- Every case-matched clause in cross-serial order is in the language. -/
theorem tokens_mem_swissGermanLang (r : Row) (h : r.CaseMatched) :
    r.tokens ∈ swissGermanLang := by
  refine ⟨r.nps.filterMap Token.np, r.verbs.map Token.v, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.filter_eq_self.mpr λ t ht => ?_
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨c, -, hc⟩ := List.mem_filterMap.mp ht
      cases c <;> simp [Token.np] at hc <;> subst hc <;> decide
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp ht
      cases v <;> decide
  · intro t ht
    obtain ⟨c, -, hc⟩ := List.mem_filterMap.mp ht
    cases c <;> simp [Token.np] at hc <;> subst hc <;> decide
  · intro t ht
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp ht
    cases v <;> decide
  · rw [(count_np_filterMap r.nps).1, (count_v_map r.verbs).1]
    exact h.1
  · rw [(count_np_filterMap r.nps).2, (count_v_map r.verbs).2]
    exact h.2

/-- The schema clause is the cross-serial clause with `m` accusative and `n` dative pairs. -/
theorem canonical_eq_tokens (m n : ℕ) :
    canonical m n =
      Row.tokens ⟨List.replicate m .acc ++ List.replicate n .dat,
        List.replicate m .loend ++ List.replicate n .haelfe, true⟩ := by
  simp [canonical, Row.tokens, Token.np, Token.v, verbObjectCase]

theorem canonical_mem_swissGermanLang (m n : ℕ) : canonical m n ∈ swissGermanLang := by
  rw [canonical_eq_tokens]
  refine tokens_mem_swissGermanLang _ ⟨?_, ?_⟩ <;>
    simp [List.count_replicate, verbObjectCase]

/-! ### The regular filter `a* b* c* d*` -/

/-- The states of the automaton for `a* b* c* d*`. -/
inductive CaseSortedState
  | sA | sB | sC | sD | sDead
  deriving DecidableEq, Fintype, Repr

/-- The automaton recognizing `a* b* c* d*`. -/
def caseSortedDFA : DFA FourSymbol CaseSortedState where
  start := .sA
  accept := {.sA, .sB, .sC, .sD}
  step
    | .sA, .a => .sA | .sA, .b => .sB | .sA, .c => .sC | .sA, .d => .sD
    | .sB, .a => .sDead | .sB, .b => .sB | .sB, .c => .sC | .sB, .d => .sD
    | .sC, .a => .sDead | .sC, .b => .sDead | .sC, .c => .sC | .sC, .d => .sD
    | .sD, .a => .sDead | .sD, .b => .sDead | .sD, .c => .sDead | .sD, .d => .sD
    | .sDead, _ => .sDead

/-- The regular language `a* b* c* d*`, the image of the paper's filter with the boundary
letters erased. -/
def caseSorted : Language FourSymbol := caseSortedDFA.accepts

theorem caseSorted_isRegular : caseSorted.IsRegular :=
  ⟨CaseSortedState, inferInstance, caseSortedDFA, rfl⟩

private theorem evalFrom_replicate_a (k : ℕ) :
    caseSortedDFA.evalFrom .sA (List.replicate k .a) = .sA := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, DFA.evalFrom_cons]; exact ih

private theorem evalFrom_replicate_b (k : ℕ) (s : CaseSortedState) (h : s = .sA ∨ s = .sB) :
    caseSortedDFA.evalFrom s (List.replicate k .b) = if k = 0 then s else .sB := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, DFA.evalFrom_cons]
    rcases h with rfl | rfl <;>
    · show caseSortedDFA.evalFrom .sB (List.replicate k .b) = _
      rw [ih .sB (.inr rfl)]; cases k <;> simp

private theorem evalFrom_replicate_c (k : ℕ) (s : CaseSortedState)
    (h : s = .sA ∨ s = .sB ∨ s = .sC) :
    caseSortedDFA.evalFrom s (List.replicate k .c) = if k = 0 then s else .sC := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, DFA.evalFrom_cons]
    rcases h with rfl | rfl | rfl <;>
    · show caseSortedDFA.evalFrom .sC (List.replicate k .c) = _
      rw [ih .sC (.inr (.inr rfl))]; cases k <;> simp

private theorem evalFrom_replicate_d (k : ℕ) (s : CaseSortedState)
    (h : s = .sA ∨ s = .sB ∨ s = .sC ∨ s = .sD) :
    caseSortedDFA.evalFrom s (List.replicate k .d) = if k = 0 then s else .sD := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, DFA.evalFrom_cons]
    rcases h with rfl | rfl | rfl | rfl <;>
    · show caseSortedDFA.evalFrom .sD (List.replicate k .d) = _
      rw [ih .sD (.inr (.inr (.inr rfl)))]; cases k <;> simp

/-- Every `aᵐ bⁿ cᵐ dⁿ` passes the filter. -/
theorem makeString_ambncmdn_mem_caseSorted (m n : ℕ) : makeString_ambncmdn m n ∈ caseSorted := by
  show caseSortedDFA.evalFrom .sA (makeString_ambncmdn m n) ∈ caseSortedDFA.accept
  simp only [makeString_ambncmdn, DFA.evalFrom_of_append, evalFrom_replicate_a]
  rw [evalFrom_replicate_b n .sA (.inl rfl)]
  set s₁ := if n = 0 then CaseSortedState.sA else .sB
  have hs₁ : s₁ = .sA ∨ s₁ = .sB := by by_cases hn : n = 0 <;> simp [s₁, hn]
  rw [evalFrom_replicate_c m s₁ (hs₁.imp_right (.inl ·))]
  set s₂ := if m = 0 then s₁ else .sC
  have hs₂ : s₂ = .sA ∨ s₂ = .sB ∨ s₂ = .sC := by
    by_cases hm : m = 0
    · simp only [s₂, hm, ite_true]
      exact hs₁.imp_right .inl
    · simp [s₂, hm]
  rw [evalFrom_replicate_d n s₂ (hs₂.imp_right (·.imp_right .inl))]
  rcases hs₂ with h | h | h <;> by_cases hn : n = 0 <;>
    simp_all (config := { decide := true }) [caseSortedDFA]

private theorem evalFrom_sDead (xs : List FourSymbol) :
    caseSortedDFA.evalFrom .sDead xs = .sDead := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [DFA.evalFrom_cons]
    exact ih

private theorem sDead_notMem_accept : CaseSortedState.sDead ∉ caseSortedDFA.accept := by
  rintro (h | h | h | h) <;> exact CaseSortedState.noConfusion h

private theorem ne_sDead_of_mem_accept {s : CaseSortedState} {xs : List FourSymbol}
    (h : caseSortedDFA.evalFrom s xs ∈ caseSortedDFA.accept) :
    caseSortedDFA.evalFrom s xs ≠ .sDead :=
  λ h' => sDead_notMem_accept (h' ▸ h)

private theorem sD_decomp (xs : List FourSymbol)
    (h : caseSortedDFA.evalFrom .sD xs ∈ caseSortedDFA.accept) :
    ∃ u, xs = List.replicate u .d := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    rw [DFA.evalFrom_cons] at h
    cases x with
    | d =>
      obtain ⟨u, rfl⟩ := ih h
      exact ⟨u + 1, by rw [List.replicate_succ]⟩
    | _ => exact absurd (evalFrom_sDead xs) (ne_sDead_of_mem_accept h)

private theorem sC_decomp (xs : List FourSymbol)
    (h : caseSortedDFA.evalFrom .sC xs ∈ caseSortedDFA.accept) :
    ∃ r u, xs = List.replicate r .c ++ List.replicate u .d := by
  induction xs with
  | nil => exact ⟨0, 0, rfl⟩
  | cons x xs ih =>
    rw [DFA.evalFrom_cons] at h
    cases x with
    | c =>
      obtain ⟨r, u, rfl⟩ := ih h
      exact ⟨r + 1, u, by rw [List.replicate_succ]; rfl⟩
    | d =>
      obtain ⟨u, rfl⟩ := sD_decomp xs h
      exact ⟨0, u + 1, by simp [List.replicate]⟩
    | _ => exact absurd (evalFrom_sDead xs) (ne_sDead_of_mem_accept h)

private theorem sB_decomp (xs : List FourSymbol)
    (h : caseSortedDFA.evalFrom .sB xs ∈ caseSortedDFA.accept) :
    ∃ q r u, xs = List.replicate q .b ++ List.replicate r .c ++ List.replicate u .d := by
  induction xs with
  | nil => exact ⟨0, 0, 0, rfl⟩
  | cons x xs ih =>
    rw [DFA.evalFrom_cons] at h
    cases x with
    | b =>
      obtain ⟨q, r, u, rfl⟩ := ih h
      exact ⟨q + 1, r, u, by rw [List.replicate_succ]; rfl⟩
    | c =>
      obtain ⟨r, u, rfl⟩ := sC_decomp xs h
      exact ⟨0, r + 1, u, by simp [List.replicate]⟩
    | d =>
      obtain ⟨u, rfl⟩ := sD_decomp xs h
      exact ⟨0, 0, u + 1, by simp [List.replicate]⟩
    | a => exact absurd (evalFrom_sDead xs) (ne_sDead_of_mem_accept h)

/-- A string the filter accepts is a block string `aᵖ bᵠ cʳ dᵘ`. -/
theorem caseSorted_decomp (xs : List FourSymbol) (h : xs ∈ caseSorted) :
    ∃ p q r u, xs = List.replicate p .a ++ List.replicate q .b ++
      List.replicate r .c ++ List.replicate u .d := by
  induction xs with
  | nil => exact ⟨0, 0, 0, 0, rfl⟩
  | cons x xs ih =>
    change caseSortedDFA.evalFrom .sA (x :: xs) ∈ caseSortedDFA.accept at h
    rw [DFA.evalFrom_cons] at h
    cases x with
    | a =>
      obtain ⟨p, q, r, u, rfl⟩ := ih h
      exact ⟨p + 1, q, r, u, by rw [List.replicate_succ]; rfl⟩
    | b =>
      obtain ⟨q, r, u, rfl⟩ := sB_decomp xs h
      exact ⟨0, q + 1, r, u, by simp [List.replicate]⟩
    | c =>
      obtain ⟨r, u, rfl⟩ := sC_decomp xs h
      exact ⟨0, 0, r + 1, u, by simp [List.replicate]⟩
    | d =>
      obtain ⟨u, rfl⟩ := sD_decomp xs h
      exact ⟨0, 0, 0, u + 1, by simp [List.replicate]⟩

/-! ### The intersection and the theorem -/

private theorem count_image (ts : List Token) :
    (ts.flatMap tokenStringHom).count .a = ts.count .accNP ∧
      (ts.flatMap tokenStringHom).count .b = ts.count .datNP ∧
      (ts.flatMap tokenStringHom).count .c = ts.count .accV ∧
      (ts.flatMap tokenStringHom).count .d = ts.count .datV := by
  induction ts with
  | nil => simp
  | cons t ts ih => cases t <;> simp [List.flatMap_cons, tokenStringHom, ih]

private theorem count_filter_notBoundary (ts : List Token) :
    (ts.filter (!·.isBoundary)).count .accNP = ts.count .accNP ∧
      (ts.filter (!·.isBoundary)).count .datNP = ts.count .datNP ∧
      (ts.filter (!·.isBoundary)).count .accV = ts.count .accV ∧
      (ts.filter (!·.isBoundary)).count .datV = ts.count .datV := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.filter_cons]
    cases t <;> simp [Token.isBoundary]

private theorem count_nps_vs {nps vs : List Token} (hn : ∀ t ∈ nps, t.isNP = true)
    (hv : ∀ t ∈ vs, t.isV = true) :
    vs.count .accNP = 0 ∧ vs.count .datNP = 0 ∧ nps.count .accV = 0 ∧ nps.count .datV = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine List.count_eq_zero.mpr λ h => ?_
  · have := hv _ h; simp [Token.isV] at this
  · have := hv _ h; simp [Token.isV] at this
  · have := hn _ h; simp [Token.isNP] at this
  · have := hn _ h; simp [Token.isNP] at this

/-- The intersection equality: the image of the language under `f`, filtered to the case-sorted
shape, is `aᵐ bⁿ cᵐ dⁿ`. The homomorphism collapses each case class to a letter, the filter
forces the sorted order of Claim 2, and Claim 3 equates the exponents. -/
theorem stringMap_swissGerman_inter_caseSorted_eq_ambncmdn :
    Language.stringMap tokenStringHom swissGermanLang ⊓ caseSorted = ambncmdn := by
  ext w
  constructor
  · rintro ⟨⟨ts, ⟨nps, vs, hfilter, hn, hv, hdat, hacc⟩, rfl⟩, hw⟩
    obtain ⟨p, q, r, u, hw'⟩ := caseSorted_decomp _ hw
    obtain ⟨ha, hb, hc, hd⟩ := count_image ts
    obtain ⟨fa, fb, fc, fd⟩ := count_filter_notBoundary ts
    obtain ⟨z₁, z₂, z₃, z₄⟩ := count_nps_vs hn hv
    rw [hfilter, List.count_append] at fa fb fc fd
    have hp : p = ts.count .accNP := by
      rw [← ha, hw']; simp [List.count_replicate]
    have hq : q = ts.count .datNP := by
      rw [← hb, hw']; simp [List.count_replicate]
    have hr : r = ts.count .accV := by
      rw [← hc, hw']; simp [List.count_replicate]
    have hu : u = ts.count .datV := by
      rw [← hd, hw']; simp [List.count_replicate]
    refine (mem_ambncmdn_iff _).mpr ⟨p, q, ?_⟩
    rw [hw']
    have hpr : r = p := by omega
    have hqu : u = q := by omega
    rw [hpr, hqu]
    rfl
  · intro hw
    obtain ⟨m, n, rfl⟩ := (mem_ambncmdn_iff w).mp hw
    exact ⟨⟨canonical m n, canonical_mem_swissGermanLang m n, flatMap_canonical m n⟩,
      makeString_ambncmdn_mem_caseSorted m n⟩

/-- Swiss German is not weakly context-free: the image of the language under `f`, intersected
with the regular filter, is `aᵐ bⁿ cᵐ dⁿ`, so the closure of the context-free languages under
homomorphisms and intersection with regular languages rules the source out. -/
theorem swiss_german_not_contextFree : ¬ swissGermanLang.IsContextFree := by
  apply Language.not_isContextFree_via_witness tokenStringHom caseSorted caseSorted_isRegular
  rw [stringMap_swissGerman_inter_caseSorted_eq_ambncmdn]
  exact ambncmdn_not_contextFree

end Shieber1985
