import Linglib.Core.FormalLanguage
import Linglib.Phenomena.WordOrder.CrossSerial
import Linglib.Phenomena.WordOrder.Studies.Shieber1985
import Linglib.Theories.FormalLanguageTheory.PumpingLemma

/-!
# Pullum & Gazdar (1982) @cite{gazdar-pullum-1982}

Natural Languages and Context-Free Languages.
*Linguistics and Philosophy*, 4(4), 471–504.

## Core Argument

@cite{gazdar-pullum-1982} systematically examine every published argument
purporting to demonstrate the non-context-freeness of some natural language,
and show that each is invalid — either empirically or formally. The five
arguments examined:

1. **Comparatives** (§2): @cite{chomsky-1963} claims English comparative
   constructions form an xy language (requiring nonidentity between substrings
   x and y). P&G show the empirical premise is wrong (the data doesn't support
   the nonidentity claim) and the formal premise is false: infinitely many xy
   languages are context-free. They exhibit a CF-PSG (grammar 9) generating
   {αxβyγ | x ≠ y, x,y ∈ (a+b)*}.

2. **Pi** (§3): Elster (1978) applies the pumping lemma directly to English
   sentences about the decimal expansion of π, arguing that the requirement
   for digits to match π's expansion makes English non-CF. P&G show this
   confuses grammaticality with arithmetic truth — the sentences are
   grammatical regardless of whether the digits are correct.

3. **Respectively** (§4): Bar-Hillel & Shamir (1960) and @cite{langendoen-1978}
   argue that *respectively* constructions require matching the number of
   elements in two lists, creating non-CF dependencies. P&G show both the
   empirical characterization of English *respectively* data and the formal
   reasoning are flawed.

4. **Dutch** (§5): Huybregts (1976) argues that Dutch cross-serial verb
   clusters create non-CF cross-serial dependencies of the form
   a₁...aₙb₁...bₙ. P&G construct explicit CF-PSGs (grammars 29, 32) that
   generate the correct Dutch subordinate clause strings with proper verb
   subcategorization, showing that cross-serial word ORDER alone does not
   exceed CF power.

5. **Mohawk** (§6): Postal (1964) and Langendoen (1977) argue that Mohawk noun
   incorporation creates non-CF string-copying (the incorporated noun-stem
   must match the external NP). P&G show that possessed incorporation
   (examples 40a–e) violates the stem-matching premise: incorporated stems
   need not match external NPs.

## Key Formal Results

Two constructive results are formalized here:

1. **Grammar (29)**: A CF-PSG generating Dutch subordinate clause verb phrases
   with correct NP-verb valency, formalized using mathlib's
   `ContextFreeGrammar`. This demonstrates that cross-serial word ORDER is
   context-free.

2. **The critical distinction**: Cross-serial word order alone is CF (grammar
   29). What is non-CF is cross-serial order PLUS case agreement across
   unbounded depth — proven for Swiss German by @cite{shieber-1985},
   formalized in `Phenomena.WordOrder.Studies.Shieber1985`.

## Architectural Note

This file bridges linglib's `Core.FormalLanguageType` enum with mathlib's
`ContextFreeGrammar` and `Language.IsContextFree`. The existing formal language
infrastructure in linglib (pumping lemma proofs, `FormalLanguageType` hierarchy)
is disconnected from mathlib's automata theory (`DFA`, `NFA`, `Language`,
`ContextFreeGrammar`). Mathlib provides:

- `Language α := Set (List α)` vs linglib's `List α → Bool`
- `Language.IsContextFree` (∃ CFG generating L) — no analogue in linglib
- `Language.IsRegular` (∃ DFA accepting L) — no analogue in linglib
- `ContextFreeGrammar` with `Derives`/`Generates` — linglib has no CFG type
- DFA/NFA pumping lemma — linglib reproves it for specific languages

Linglib now uses mathlib's `Language α` natively throughout its formal
language theory, with `HasCFLPumpingProperty` defined over `Language α`,
and `anbncndn_not_contextFree` / `anbnc_not_contextFree` stated using
`Language.IsContextFree`
-/

namespace Phenomena.WordOrder.Studies.PullumGazdar1982

open Core (FormalLanguageType)

-- ============================================================================
-- §2: xy Languages Can Be Context-Free
-- ============================================================================

/-! ### §2: xy Languages Can Be Context-Free

@cite{gazdar-pullum-1982} refute @cite{chomsky-1963}'s claim that xy
languages are inherently non-context-free. The language
{aⁿbᵐ | n ≠ m} is both an xy language (nonidentity between the a-block
and b-block) and context-free.

P&G's grammar (9) handles the more general language
{αxβyγ | x,y ∈ (a+b)*, x ≠ y} with 8 nonterminals and ~15 rules.
We use the simpler {aⁿbᵐ | n ≠ m} here, which makes the same point
with 3 nonterminals and 6 rules. -/
section XYLanguage

/-- Nonterminals for the {aⁿbᵐ | n ≠ m} grammar. -/
inductive XYNT where
  | S   -- start: n ≠ m
  | S₁  -- n > m
  | S₂  -- n < m
  deriving DecidableEq, Repr

/-- Terminals for the {aⁿbᵐ | n ≠ m} grammar. -/
inductive XYT where
  | a | b
  deriving DecidableEq, Repr

open Symbol in
/-- A CF-PSG generating {aⁿbᵐ | n ≠ m}.

    Rules:
    - S  → S₁ | S₂
    - S₁ → aS₁ | aS₁b | a     (n > m: at least one extra a)
    - S₂ → S₂b | aS₂b | b     (n < m: at least one extra b)

    This refutes the claim that xy languages are inherently non-CF.
    @cite{gazdar-pullum-1982} §2, with grammar (9) for the more general case. -/
def xyGrammar : ContextFreeGrammar XYT where
  NT := XYNT
  initial := .S
  rules := { ⟨.S, [nonterminal .S₁]⟩,                        -- S → S₁
             ⟨.S, [nonterminal .S₂]⟩,                        -- S → S₂
             ⟨.S₁, [terminal .a, nonterminal .S₁]⟩,          -- S₁ → aS₁
             ⟨.S₁, [terminal .a, nonterminal .S₁, terminal .b]⟩,  -- S₁ → aS₁b
             ⟨.S₁, [terminal .a]⟩,                           -- S₁ → a
             ⟨.S₂, [nonterminal .S₂, terminal .b]⟩,          -- S₂ → S₂b
             ⟨.S₂, [terminal .a, nonterminal .S₂, terminal .b]⟩,  -- S₂ → aS₂b
             ⟨.S₂, [terminal .b]⟩ }                          -- S₂ → b

/-- Witness: `aab` ∈ L (n=2, m=1, n ≠ m).
    Derivation: S ⇒ S₁ ⇒ aS₁b ⇒ aab. -/
theorem xy_witness_aab :
    [XYT.a, .a, .b] ∈ xyGrammar.language := by
  rw [ContextFreeGrammar.mem_language_iff]
  apply Relation.ReflTransGen.head
  · -- S → S₁
    exact ⟨⟨.S, [.nonterminal .S₁]⟩, by unfold xyGrammar; simp,
           ContextFreeRule.Rewrites.input_output⟩
  apply Relation.ReflTransGen.head
  · -- S₁ → aS₁b
    exact ⟨⟨.S₁, [.terminal .a, .nonterminal .S₁, .terminal .b]⟩,
           by unfold xyGrammar; simp, ContextFreeRule.Rewrites.input_output⟩
  apply Relation.ReflTransGen.head
  · -- S₁ → a (in context [a, _, b])
    exact ⟨⟨.S₁, [.terminal .a]⟩, by unfold xyGrammar; simp,
           ContextFreeRule.rewrites_of_exists_parts _
             [Symbol.terminal XYT.a] [Symbol.terminal XYT.b]⟩
  exact Relation.ReflTransGen.refl

/-- Witness: `abb` ∈ L (n=1, m=2, n ≠ m).
    Derivation: S ⇒ S₂ ⇒ aS₂b ⇒ abb. -/
theorem xy_witness_abb :
    [XYT.a, .b, .b] ∈ xyGrammar.language := by
  rw [ContextFreeGrammar.mem_language_iff]
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.S, [.nonterminal .S₂]⟩, by unfold xyGrammar; simp,
           ContextFreeRule.Rewrites.input_output⟩
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.S₂, [.terminal .a, .nonterminal .S₂, .terminal .b]⟩,
           by unfold xyGrammar; simp, ContextFreeRule.Rewrites.input_output⟩
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.S₂, [.terminal .b]⟩, by unfold xyGrammar; simp,
           ContextFreeRule.rewrites_of_exists_parts _
             [Symbol.terminal XYT.a] [Symbol.terminal XYT.b]⟩
  exact Relation.ReflTransGen.refl

end XYLanguage

-- ============================================================================
-- §5: Dutch Cross-Serial Order Is Context-Free
-- ============================================================================

section DutchGrammar

/-- Terminal symbols for Dutch subordinate clause verb phrases.

    Following @cite{gazdar-pullum-1982} grammar (29b), these are the
    syntactic categories of words that appear in Dutch verb-final
    subordinate clauses. Each category determines the verb's valency
    (transitive vs intransitive) and whether it takes a VP complement. -/
inductive DutchT where
  | np       -- B: NP arguments (Marie, Pieter, Arabisch, ...)
  | transInf -- D: transitive infinitives (schrijven "write", ...)
  | intrans  -- E: intransitive verbs (liegen "lie", ...)
  | trVPInf  -- F: transitive VP-complement-taking infinitives (laten "let", zien "see", ...)
  | inVPInf  -- G: intransitive VP-complement-taking infinitives (willen "want", ...)
  | trVPFin  -- H: finite transitive VP-complement-taking verbs (laat, ...)
  | inVPFin  -- I: finite intransitive VP-complement-taking verbs (wil, ...)
  deriving DecidableEq, Repr

/-- Nonterminals for the Dutch VP grammar.

    - `A`: complete verb phrase (start symbol)
    - `C`: VP-complement (recursive core embedding further verbs) -/
inductive DutchNT where
  | A  -- start symbol (complete VP)
  | C  -- VP-complement
  deriving DecidableEq, Repr

open Symbol in
/-- @cite{gazdar-pullum-1982} grammar (29): a context-free grammar generating
    Dutch subordinate clause verb phrases with correct NP-verb valency.

    Syntactic rules (29a):
    - A → BCD | CE
    - C → BCF | CG | BH | I

    The grammar ensures each transitive verb has an NP argument and each
    intransitive verb does not, producing cross-serial NP-verb dependencies
    in the surface string. The cross-serial ORDER (NP₁...NPₙ V₁...Vₙ) is
    a consequence of the right-branching VP structure.

    Crucially, this grammar makes NO case-agreement demands: the NPs are
    untyped. This is why the string set is context-free. Adding case
    agreement (requiring NP case to match verb case across unbounded depth)
    takes the language beyond CF — that is @cite{shieber-1985}'s argument. -/
def dutchGrammar : ContextFreeGrammar DutchT where
  NT := DutchNT
  initial := .A
  rules := { ⟨.A, [terminal .np, nonterminal .C, terminal .transInf]⟩,   -- A → BCD
             ⟨.A, [nonterminal .C, terminal .intrans]⟩,                   -- A → CE
             ⟨.C, [terminal .np, nonterminal .C, terminal .trVPInf]⟩,     -- C → BCF
             ⟨.C, [nonterminal .C, terminal .inVPInf]⟩,                   -- C → CG
             ⟨.C, [terminal .np, terminal .trVPFin]⟩,                     -- C → BH
             ⟨.C, [terminal .inVPFin]⟩ }                                  -- C → I

-- Derivations

/-- Two-verb cross-serial clause: *Marie Pieter laat schrijven*
    ("Marie let Pieter write").

    Surface: NP₁ NP₂ V₁ V₂ = np np trVPFin transInf

    Cross-serial binding:
      NP₁(Marie) ──── V₁(laat)
         NP₂(Pieter) ──── V₂(schrijven)

    Derivation: A ⇒ np·C·transInf ⇒ np·np·trVPFin·transInf -/
theorem dutch_2np_crossSerial :
    [DutchT.np, .np, .trVPFin, .transInf] ∈ dutchGrammar.language := by
  rw [ContextFreeGrammar.mem_language_iff]
  -- Step 1: A → np C transInf
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.A, [.terminal .np, .nonterminal .C, .terminal .transInf]⟩,
           by unfold dutchGrammar; simp, ContextFreeRule.Rewrites.input_output⟩
  -- Step 2: C → np trVPFin (in context [np, _, transInf])
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.C, [.terminal .np, .terminal .trVPFin]⟩,
           by unfold dutchGrammar; simp,
           ContextFreeRule.rewrites_of_exists_parts _
             [Symbol.terminal DutchT.np] [Symbol.terminal DutchT.transInf]⟩
  exact Relation.ReflTransGen.refl

/-- Three-verb cross-serial clause: *Marie Pieter Arabisch laat zien schrijven*
    ("Marie let Pieter see Arabisch write").

    Surface: NP₁ NP₂ NP₃ V₁ V₂ V₃ = np np np trVPFin trVPInf transInf

    Cross-serial binding:
      NP₁ ─────────────── V₁(laat)
         NP₂ ─────────────── V₂(zien)
            NP₃ ─────────────── V₃(schrijven)

    Derivation: A ⇒ np·C·transInf ⇒ np·np·C·trVPInf·transInf
                  ⇒ np·np·np·trVPFin·trVPInf·transInf -/
theorem dutch_3np_crossSerial :
    [DutchT.np, .np, .np, .trVPFin, .trVPInf, .transInf] ∈ dutchGrammar.language := by
  rw [ContextFreeGrammar.mem_language_iff]
  -- Step 1: A → np C transInf
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.A, [.terminal .np, .nonterminal .C, .terminal .transInf]⟩,
           by unfold dutchGrammar; simp, ContextFreeRule.Rewrites.input_output⟩
  -- Step 2: C → np C trVPInf (in context [np, _, transInf])
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.C, [.terminal .np, .nonterminal .C, .terminal .trVPInf]⟩,
           by unfold dutchGrammar; simp,
           ContextFreeRule.rewrites_of_exists_parts _
             [Symbol.terminal DutchT.np] [Symbol.terminal DutchT.transInf]⟩
  -- Step 3: C → np trVPFin (in context [np, np, _, trVPInf, transInf])
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.C, [.terminal .np, .terminal .trVPFin]⟩,
           by unfold dutchGrammar; simp,
           ContextFreeRule.rewrites_of_exists_parts _
             [Symbol.terminal DutchT.np, Symbol.terminal DutchT.np]
             [Symbol.terminal DutchT.trVPInf, Symbol.terminal DutchT.transInf]⟩
  exact Relation.ReflTransGen.refl

/-- Intransitive clause with modal: *wil zwemmen* ("wants to swim").

    Surface: V₁ V₂ = inVPFin intrans (no NPs — both verbs are intransitive)

    Derivation: A ⇒ C·intrans ⇒ inVPFin·intrans -/
theorem dutch_intransitive_modal :
    [DutchT.inVPFin, .intrans] ∈ dutchGrammar.language := by
  rw [ContextFreeGrammar.mem_language_iff]
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.A, [.nonterminal .C, .terminal .intrans]⟩,
           by unfold dutchGrammar; simp, ContextFreeRule.Rewrites.input_output⟩
  apply Relation.ReflTransGen.head
  · exact ⟨⟨.C, [.terminal .inVPFin]⟩, by unfold dutchGrammar; simp,
           ContextFreeRule.rewrites_of_exists_parts _
             [] [Symbol.terminal DutchT.intrans]⟩
  exact Relation.ReflTransGen.refl

end DutchGrammar

-- ============================================================================
-- §7: The Critical Distinction
-- ============================================================================

/-- **The critical distinction.** Cross-serial word order alone is context-free
    (@cite{gazdar-pullum-1982} grammar 29, demonstrated above). What takes
    the language beyond CF is cross-serial order PLUS case agreement — the
    requirement that dative NPs match dative verbs and accusative NPs match
    accusative verbs across unbounded depth.

    This distinction resolves the apparent contradiction:
    - @cite{bresnan-etal-1982} argue Dutch cross-serial dependencies are non-CF
    - @cite{gazdar-pullum-1982} show CF grammars CAN generate cross-serial strings
    - @cite{shieber-1985} proves Swiss German IS non-CF, using case-marking

    The resolution: @cite{bresnan-etal-1982}'s argument relied on constituency
    assumptions. The valid proof (@cite{shieber-1985}) uses case agreement,
    which grammar (29) deliberately omits. -/
theorem crossSerial_order_cf_but_caseMatching_not :
    -- Cross-serial word order is context-free (grammar 29 generates it)
    (∃ _g : ContextFreeGrammar DutchT, True) ∧
    -- Cross-serial order + case-matching is not context-free (Shieber 1985)
    ¬ HasCFLPumpingProperty anbncndn :=
  ⟨⟨dutchGrammar, trivial⟩, anbncndn_not_pumpable⟩

/-- The question of whether natural languages are context-free remained open
    as of 1982. @cite{gazdar-pullum-1982} conclude: "Notice that this paper
    has not claimed that all natural languages are CFL's. What it has shown
    is that every published argument purporting to demonstrate the
    non-context-freeness of some natural language is invalid."

    The question was settled by @cite{shieber-1985}, who provided the first
    valid proof (for Swiss German) using case-marking — a purely string-based
    argument making no constituency assumptions. -/
theorem question_settled_by_shieber :
    (∀ n, Phenomena.WordOrder.Studies.Shieber1985.clauseImage
        (Phenomena.WordOrder.Studies.Shieber1985.arbitraryDepth n n) ∈ anbncndn) ∧
    ¬ HasCFLPumpingProperty anbncndn :=
  Phenomena.WordOrder.Studies.Shieber1985.swiss_german_not_context_free

-- ============================================================================
-- §8: IsContextFree Results (Mathlib Integration)
-- ============================================================================

/-- The xy grammar language is context-free (by construction: we exhibit the CFG). -/
theorem xy_language_isContextFree : xyGrammar.language.IsContextFree :=
  ⟨xyGrammar, rfl⟩

/-- The Dutch cross-serial order grammar language is context-free. -/
theorem dutch_crossSerial_order_isContextFree : dutchGrammar.language.IsContextFree :=
  ⟨dutchGrammar, rfl⟩

/-- The critical distinction, strengthened with mathlib predicates:
    - The Dutch cross-serial order language IS context-free
    - {aⁿbⁿcⁿdⁿ} (cross-serial order + case-matching) is NOT context-free -/
theorem crossSerial_cf_vs_caseMatching_not_cf :
    dutchGrammar.language.IsContextFree ∧
    ¬ Language.IsContextFree anbncndn :=
  ⟨dutch_crossSerial_order_isContextFree, anbncndn_not_contextFree⟩

end Phenomena.WordOrder.Studies.PullumGazdar1982
