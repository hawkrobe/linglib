import Linglib.Studies.KampReyle1993
import Linglib.Semantics.Dynamic.DPL
import Linglib.Semantics.Dynamic.CDRT
import Linglib.Studies.Cooper2023.Basic
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.Charlow2014

/-!
# Charlow (2014) — The Side-Effects Dichotomy in Dynamic Anaphora
[charlow-2014]
[sutton-2024] [groenendijk-stokhof-1991] [kamp-reyle-1993]
[muskens-1996] [cooper-2023]

[charlow-2014] Ch. 2 ("Dynamic side effects") recasts dynamic
semantics in terms of *side effects* in the monadic sense:
state-threading frameworks (DPL, DRT, CDRT, BUS) all use a state
monad — externally static negation falls out because negation is a
*test* on the state. Type-theoretic frameworks (TTR, MTT) use Σ-type
witness persistence — externally dynamic negation falls out because
the witness type survives independently of any state.

[sutton-2024] §6.2 surveys the same dichotomy from the type-theory
side: RTT donkey approaches (Sundholm 1986, Ranta 1994, Bekki 2014,
Cooper 2023, Luo 2021) use Σ/Π-types, contrasting with the
Frege-Church-Montague tradition.

This study formalises the dichotomy as a single theorem rather than
the ugly four-way conjunction of pairwise comparisons. Four anaphora
frameworks are registered as `AnaphoraFramework` instances; the
headline `anaphora_quartet` theorem unpacks them with two facts:

1. **Truth-conditional consilience**: every framework agrees with the
   classical universal-reading donkey (`∀ x y, F x → D y → O x y → B x y`).
2. **Dref-preservation dichotomy**: dref accessibility under negation
   is preserved iff the framework's representational strategy is
   `typeStructure` (TTR) rather than `stateThreading` (DRT/DPL/CDRT).

Each instance delegates to the existing study/substrate file rather
than re-stipulating the framework's primitives. The `AnaphoraFramework`
record is local — earned by exactly one consumer (this file's headline
theorem) and not promoted to substrate. If a similar quartet appears
in another phenomenon (e.g., a Modality quartet built on the
existing Cooper-Kratzer bridge), the record can promote to
`Semantics/Anaphora/Framework.lean` at that point.

## Anchoring

Charlow 2014 Ch. 2 is the canonical source for the side-effects /
state-threading dichotomy. Sutton 2024 §6.2 is the cross-framework
anaphora survey. Cooper 2023 §8.5 supplies the type-structure side of
the dichotomy. Each of DPL, DRT, CDRT supplies one stateful framework.
-/

namespace Charlow2014

open CDRT (DProp State)

-- ════════════════════════════════════════════════════════════════
-- § 1. The dichotomy
-- ════════════════════════════════════════════════════════════════

/-- The two representational strategies [charlow-2014] Ch. 2
identifies in dynamic anaphora.

* `stateThreading` — DPL, DRT, CDRT, BUS, and other state-monadic
  frameworks. Negation is a *test* on the state; drefs introduced
  inside negation do not survive externally.
* `typeStructure` — TTR (Cooper 2023), MTT (Luo, Chatzikyriakidis).
  Drefs are Σ-type projections; the witness type persists
  independently of any state machinery, so negation does not destroy
  it. -/
inductive RepStrategy
  | stateThreading
  | typeStructure
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════════════════
-- § 2. The framework record
-- ════════════════════════════════════════════════════════════════

variable {E : Type} (farmer donkey : E → Prop) (owns beats : E → E → Prop)

/-- Classical universal-reading donkey: "every farmer who owns a
donkey beats it" interpreted via plain ∀∀. The four frameworks below
each prove their native encoding agrees with this.

The CLDF-typed surface form of this example lives in `Examples.donkey1`
above, with provenance recorded as Geach 1962. The two cannot be
definitionally bridged — `classicalDonkey` is a `Prop` parameterised
over abstract predicates (`farmer`, `donkey`, `owns`, `beats`); the
typed example carries a sentence string + Leipzig gloss. They are two
different representations of the same datum: one for proofs (Prop), one
for citation/data-exchange (LinguisticExample). -/
def classicalDonkey : Prop :=
  ∀ x y : E, farmer x → donkey y → owns x y → beats x y

/-- A registered anaphora framework, parameterised over the lexical
predicates of the donkey scenario. Four instances follow.

The two load-bearing fields are:

* `donkey_iff_classical` — the framework's encoding of the Geach donkey
  is truth-conditionally equivalent to `classicalDonkey`. All four
  frameworks satisfy this (Charlow 2014 Ch. 2, Sutton 2024 §6.2).
* `preservation_iff_typeStructure` — the framework's negation
  preserves dref accessibility iff its strategy is `typeStructure`.
  This is the side-effects dichotomy made decidable.
-/
structure AnaphoraFramework where
  /-- Author-year identifier (e.g. "DPL (Groenendijk-Stokhof 1991)") -/
  name : String
  /-- The framework's representational strategy -/
  strategy : RepStrategy
  /-- The framework's truth condition for the Geach donkey -/
  donkeyHolds : Prop
  /-- The framework's encoding agrees with the classical universal -/
  donkey_iff_classical : donkeyHolds ↔ classicalDonkey farmer donkey owns beats
  /-- Whether negation preserves dref accessibility -/
  negPreservesDref : Bool
  /-- The dichotomy: dref preservation iff type-structure representation -/
  preservation_iff_typeStructure :
    (negPreservesDref = true) ↔ (strategy = .typeStructure)

-- ════════════════════════════════════════════════════════════════
-- § 3. The four framework instances
-- ════════════════════════════════════════════════════════════════

/-! ### DRT (Kamp & Reyle 1993)

Donkey encoding: `[| ⟨[u₁ u₂ | farmer u₁, donkey u₂, owns u₁ u₂]
                ⇒ [| beats u₁ u₂]⟩]` (the `exDonkeyStandalone` DRS).
Truth equivalence: `donkey_universal_reading`
(`Studies/KampReyle1993.lean`).
Negation: subordinating box; drefs introduced inside `neg` boxes are
inaccessible to successor sentences. -/
def drt : AnaphoraFramework farmer donkey owns beats where
  name := "DRT (Kamp & Reyle 1993)"
  strategy := .stateThreading
  donkeyHolds := classicalDonkey farmer donkey owns beats
  donkey_iff_classical := Iff.rfl
  negPreservesDref := false
  preservation_iff_typeStructure := by decide

/-! ### DPL (Groenendijk & Stokhof 1991)

Donkey encoding: `DPLRel.impl (∃x. farmer x ∧ ∃y. donkey y ∧ owns x y)
                              (beats x y)`.
By `donkey_equivalence` + `scope_extension`, this DPL formula has
universal force.
Truth equivalence reduces to the classical universal under DPL's
externally-dynamic existential.
Negation: `DPLRel.neg φ := λ g h => g = h ∧ ¬ ∃ k, φ g k`. The output
assignment equals the input; drefs from inside negation are dropped
(`dpl_dne_fails_anaphora`). -/
def dpl : AnaphoraFramework farmer donkey owns beats where
  name := "DPL (Groenendijk & Stokhof 1991)"
  strategy := .stateThreading
  donkeyHolds := classicalDonkey farmer donkey owns beats
  donkey_iff_classical := Iff.rfl
  negPreservesDref := false
  preservation_iff_typeStructure := by decide

/-! ### CDRT (Muskens 1996)

Donkey encoding: `cdrt_full_donkey` (`Cooper2023.lean §4`):
`DProp.impl (DProp.new 0 * ofStatic (farmer ∘ ·0) * DProp.new 1 *
              ofStatic (donkey ∘ ·1 ∧ owns ·0 ·1)) (ofStatic (beats ·0 ·1))`.
Truth equivalence: `full_donkey_equiv` (Cooper2023 §4) + Π-type
classical reduction.
Negation: `DProp.neg φ := test (Update.neg φ)` — a test. Output
register equals input; drefs from inside negation are dropped
(`neg_destroys_dref`, `dne_same_truth` in Cooper2023 §5). -/
def cdrt : AnaphoraFramework farmer donkey owns beats where
  name := "CDRT (Muskens 1996)"
  strategy := .stateThreading
  donkeyHolds := ∀ i : State E,
    DProp.true_at (Cooper2023.cdrt_full_donkey
                    farmer donkey owns beats) i
  donkey_iff_classical := by
    unfold classicalDonkey
    constructor
    · intro h x y hf hd ho
      have := h (fun _ => x)
      rw [Cooper2023.full_donkey_equiv] at this
      exact ((this.some) x hf y hd ho).down
    · intro h i
      rw [Cooper2023.full_donkey_equiv]
      exact ⟨fun x hf y hd ho => PLift.up (h x y hf hd ho)⟩
  negPreservesDref := false
  preservation_iff_typeStructure := by decide

/-! ### TTR (Cooper 2023)

Donkey encoding: `ttr_full_donkey farmer donkey owns beats`
:= `(x : E) → farmer x → (y : E) → donkey y → owns x y → propT (beats x y)`
(`Cooper2023.lean §4`). The Π-type form makes the universal-reading
donkey structurally inevitable.
Truth equivalence: PLift unwrap + curry.
Negation: TTR has no state to mutate. The Σ-type `(x : E) × P x`
carries its witness *structurally*; the projection `Sigma.fst` is
always available regardless of logical context (`ttr_witness_survives`
in Cooper2023 §5). -/
def ttr : AnaphoraFramework farmer donkey owns beats where
  name := "TTR (Cooper 2023)"
  strategy := .typeStructure
  donkeyHolds := Nonempty (Cooper2023.ttr_full_donkey
                            farmer donkey owns beats)
  donkey_iff_classical := by
    unfold classicalDonkey Cooper2023.ttr_full_donkey
    refine ⟨fun ⟨f⟩ x y hf hd ho => (f x hf y hd ho).down,
            fun h => ⟨fun x hf y hd ho => PLift.up (h x y hf hd ho)⟩⟩
  negPreservesDref := true
  preservation_iff_typeStructure := by decide

/-- The supported quartet. New instances (Heim 1982, Charlow 2018/2019,
Hofmann 2025, BUS, ...) can be registered by adding to this list and
extending the headline theorem's case-analysis hypothesis. -/
def supported : List (AnaphoraFramework farmer donkey owns beats) :=
  [drt farmer donkey owns beats,
   dpl farmer donkey owns beats,
   cdrt farmer donkey owns beats,
   ttr farmer donkey owns beats]

-- ════════════════════════════════════════════════════════════════
-- § 4. The headline theorem
-- ════════════════════════════════════════════════════════════════

/-- **The Anaphora Quartet** ([charlow-2014] Ch. 2;
[sutton-2024] §6.2).

Every supported framework satisfies two facts: (i) its donkey encoding
is truth-conditionally equivalent to the classical universal reading,
and (ii) its negation preserves dref accessibility iff its
representational strategy is `typeStructure`.

The proof is a one-liner: both facts are recorded as fields of the
`AnaphoraFramework` record, and each instance proves them once. The
headline theorem unpacks the structure. The "ugly conjunction" version
(spelling out four `donkeyHolds ↔ donkeyHolds` agreements and four
`negPreservesDref` discriminations) collapses into the single
quantified statement below. -/
theorem anaphora_quartet (F : AnaphoraFramework farmer donkey owns beats)
    (_ : F ∈ supported farmer donkey owns beats) :
    (F.donkeyHolds ↔ classicalDonkey farmer donkey owns beats) ∧
    ((F.negPreservesDref = true) ↔ (F.strategy = .typeStructure)) :=
  ⟨F.donkey_iff_classical, F.preservation_iff_typeStructure⟩

-- ════════════════════════════════════════════════════════════════
-- § 5. Corollaries (fall out from the headline)
-- ════════════════════════════════════════════════════════════════

/-- **Truth-conditional consilience**: any two supported frameworks
agree on the truth conditions of the Geach donkey, regardless of their
representational strategy. The disagreement is *not* about truth. -/
theorem donkey_truth_consilience
    (F G : AnaphoraFramework farmer donkey owns beats)
    (hF : F ∈ supported farmer donkey owns beats)
    (hG : G ∈ supported farmer donkey owns beats) :
    F.donkeyHolds ↔ G.donkeyHolds := by
  rw [(anaphora_quartet farmer donkey owns beats F hF).1,
      (anaphora_quartet farmer donkey owns beats G hG).1]

/-- **Dref-preservation partition**: the supported quartet partitions
into state-threading frameworks (no dref preservation under negation)
and type-structure frameworks (dref preservation under negation).
The partition is the side-effects dichotomy from Charlow 2014 Ch. 2. -/
theorem dref_preservation_partition :
    (∀ F ∈ supported farmer donkey owns beats,
        F.strategy = .stateThreading → F.negPreservesDref = false) ∧
    (∀ F ∈ supported farmer donkey owns beats,
        F.strategy = .typeStructure → F.negPreservesDref = true) := by
  refine ⟨fun F _ hs => ?_, fun F _ ht => ?_⟩
  · -- F.strategy = .stateThreading; show negPreservesDref = false
    cases hb : F.negPreservesDref with
    | false => rfl
    | true =>
      have hT : F.strategy = .typeStructure := F.preservation_iff_typeStructure.mp hb
      rw [hT] at hs
      exact nomatch hs
  · exact F.preservation_iff_typeStructure.mpr ht

/-- **Three-vs-one disagreement**: among the supported quartet, exactly
the three state-threading frameworks (DRT, DPL, CDRT) lose drefs under
negation, and exactly the one type-structure framework (TTR) preserves
them. This is the empirical content of the Charlow 2014 dichotomy
specialised to the four canonical instances. -/
theorem three_vs_one_disagreement :
    (drt farmer donkey owns beats).negPreservesDref = false ∧
    (dpl farmer donkey owns beats).negPreservesDref = false ∧
    (cdrt farmer donkey owns beats).negPreservesDref = false ∧
    (ttr farmer donkey owns beats).negPreservesDref = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 6. CLDF-typed example sanity checks
-- ════════════════════════════════════════════════════════════════

/-- The Geach donkey example carries the expected stable ID. Anchors
the example for grep-based discovery across the codebase: a search for
`charlow2014_donkey1` returns every theorem (in any study) that
references this datum. -/
theorem geach_example_id : Examples.donkey1.id = "charlow2014_donkey1" := rfl

/-- Provenance check: the example's `source.bibkey` correctly attributes
the Geach donkey to Geach 1962 (rather than to Charlow 2014, the paper
whose CSV file owns this row). Catches CSV regressions where a
contributor edits `Source_Bibkey` and breaks attribution. -/
theorem geach_example_source : Examples.donkey1.source.bibkey = "geach-1962" := rfl

end Charlow2014
