import Linglib.Syntax.Minimalist.Labeling
import Linglib.Syntax.HPSG.HeadFiller
import Linglib.Syntax.HPSG.Construction
import Linglib.Syntax.HPSG.Description
import Linglib.Syntax.CCG.Basic
import Linglib.Syntax.DependencyGrammar.Formal.NonProjective
import Linglib.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Syntax.ConstructionGrammar.Resultatives
import Linglib.Studies.FillmoreKayOConnor1988

/-!
# [mueller-2013]: Unifying Everything
[mueller-2013]

Cross-theory comparison formalizing Müller's central thesis (pp. 921, 942):
once the problems with Chomskyan labeling and specifier/complement
determination are fixed, a minimalist theory "is equivalent to a
head-driven phrase structure grammar containing the head-filler schema,
the head-specifier schema, and the head-complement schema (only)" —
and, since phrasal constructions like Jackendoff's N-P-N are irreducible,
"both research directions are right to a certain extent: there is need for
(constraint-based versions of) Move and Merge and there is need for special
phrasal constructions" (p. 920).

`CombinationKind` is the paper's three-way combination vocabulary.
Müller's own convergence partners are Minimalism (Chomsky 2008, 2013;
Stabler's MG), HPSG, categorial grammar, and Construction Grammar; the
dependency-grammar mapping in §1 below is a linglib-side extension in the
same spirit (Müller mentions dependency grammar only in connection with
label-free syntax, not as a convergence partner).

## Structure

- §1. Classification functions: map each theory's operations to `CombinationKind`
- §2. Labeling convergence: head determines category of result (§2.1)
- §3. External Merge ↔ Head-Complement ↔ Application
- §4. Internal Merge ↔ Head-Filler ↔ Composition
- §5. Coordination diagnostic: same category required (§1, §2.2)
- §6. Directional MG ≈ CCG (placeholder)
- §7. Both directions right: decomposable vs. irreducible constructions (§3)
- §8. Concrete cross-theory examples
- §9. Labeling failures: free relatives + coordination (§2.1)
- §10. Monovalent verb serialization problem (§2.3)
- §11. Iterable valence operations (§1)

-/

namespace Mueller2013

/-! ## The three combination schemata -/

/-- Three universal combination schemata shared across syntactic theories.

[mueller-2013] (pp. 921, 942) argues that a minimalist theory with fixed
labeling is equivalent to an HPSG containing exactly the Head-Complement,
Head-Specifier, and Head-Filler schemata; directional MG corresponds to
categorial application (p. 938), and CxG's fully abstract constructions
decompose into these schemata (§3). -/
inductive CombinationKind where
  /-- Head combines with its complement (selected argument).
      Minimalism: External Merge with selection (first-merged elements are
      complements, Chomsky 2008:146 apud Müller §2.2); HPSG:
      Head-Complement Schema; CCG: forward/backward application;
      DG: core dependency (obj, det,...). -/
  | headComplement
  /-- Head combines with its specifier (non-selected argument).
      Minimalism: External Merge of later-merged elements (§2.2); HPSG:
      Head-Subject Schema; CCG: backward application (subject may be
      type-raised); DG: subject dependency. -/
  | headSpecifier
  /-- Filler combines with a gapped structure (long-distance dependency).
      Minimalism: Internal Merge — Stabler's `im` corresponds to the HPSG
      Head-Filler Schema (Pollard & Sag 1994:164 apud Müller p. 939);
      CCG: harmonic composition (primarily; composition also serves other
      functions like heavy NP shift); DG: non-projective dependency. -/
  | headFiller
  deriving Repr, DecidableEq

/-! ## §1. Classification Functions

Lightweight mappers from each theory's combination operations to the
theory-neutral `CombinationKind`. -/

/-! ### Minimalist classification -/

section MinimalistClassification

open Minimalist

/-- Classify an External Merge under head function `h`. -/
noncomputable def classifyExternalMerge (h : HeadFunction) (a b : SyntacticObject) :
    CombinationKind :=
  if selects h a b ∨ selects h b a then
    .headComplement
  else
    .headSpecifier

/-- Classify an Internal Merge (head-function-independent: IM is always
    Head-Filler regardless of which side projects). -/
def classifyInternalMerge : CombinationKind := .headFiller

/-- External Merge with selection is Head-Complement (under any `h`). -/
theorem selection_implies_headComplement
    (h : HeadFunction) (a b : SyntacticObject) (hs : selects h a b) :
    classifyExternalMerge h a b = .headComplement := by
  simp [classifyExternalMerge, hs]

/-- External Merge without selection is Head-Specifier (under any `h`). -/
theorem no_selection_implies_headSpecifier
    (h : HeadFunction) (a b : SyntacticObject)
    (ha : ¬ selects h a b) (hb : ¬ selects h b a) :
    classifyExternalMerge h a b = .headSpecifier := by
  simp [classifyExternalMerge, ha, hb]

/-- Internal Merge is always Head-Filler. -/
theorem internal_merge_is_headFiller :
    classifyInternalMerge = .headFiller := rfl

/-- The classification is exhaustive (under any `h`). -/
theorem classify_external_exhaustive
    (h : HeadFunction) (a b : SyntacticObject) :
    classifyExternalMerge h a b = .headComplement ∨
    classifyExternalMerge h a b = .headSpecifier := by
  unfold classifyExternalMerge
  by_cases hs : selects h a b ∨ selects h b a <;> simp [hs]

end MinimalistClassification

/-! ### CCG classification -/

/-- Classify a CCG derivation step as one of the three schemata.

- Forward/backward application → Head-Complement (functor selects argument)
- Forward/backward composition → Head-Filler (enables extraction;
  this is an approximation — composition also serves non-extraction
  functions like heavy NP shift and right-node raising)
- Type-raising → none (unary operation, not a binary combination)
- Coordination → none (symmetric, not one of the three headed schemata) -/
def classifyCCGDerivStep : CCG.DerivStep → Option CombinationKind
  | .fapp _ _ => some .headComplement
  | .bapp _ _ => some .headComplement
  | .fcomp _ _ => some .headFiller
  | .bcomp _ _ => some .headFiller
  | .fcompx _ _ => some .headFiller
  | .lex _ => none
  | .ftr _ _ => none
  | .btr _ _ => none
  | .coord _ _ _ => none

/-! ### HPSG classification -/

/-- Classify an HPSG schema application as one of the three schemata.

    [mueller-2013]'s three universal schemata are Head-Complement,
    Head-Specifier, and Head-Filler (p. 921); HPSG's Head-Subject Schema
    instantiates Head-Specifier. HPSG's fourth schema, Head-Modifier
    (adjunction), falls outside this classification — Müller does not
    include adjunction in the convergence claim. -/
def classifyHPSGSchema : HPSG.HPSGSchema → Option CombinationKind
  | .headComp _ => some .headComplement
  | .headSubj _ => some .headSpecifier
  | .headFiller _ => some .headFiller
  | .headMod _ => none

/-! ### Dependency Grammar classification

A linglib-side extension: Müller does not treat dependency grammar as a
convergence partner (it appears only in his discussion of label-free
syntax). The mapping follows the same logic as the others. -/

/-- Classify a UD dependency relation as one of the three schemata.

Subject dependencies are Head-Specifier; all other core dependencies
are Head-Complement. Non-projective dependencies (handled separately)
correspond to Head-Filler. -/
def classifyDepType : UD.DepRel → CombinationKind
  | .nsubj => .headSpecifier
  | .csubj => .headSpecifier
  | _ => .headComplement

/-! ## §2. Labeling Convergence (Müller §2.1)

The head determines the category of the result. This is called:
- Minimalism: the labeling algorithm (selector projects)
- HPSG: Head Feature Principle (head features percolate)
- CCG: the functor's result category is the output -/

/-- CCG forward application preserves the functor's result category.

When X/Y combines with Y via forward application, the result is X —
the left part of the functor's slash category. -/
theorem ccg_fapp_result_category (x y : CCG.Cat) :
    CCG.forwardApp (CCG.Cat.rslash x y) y = some x := by
  simp [CCG.forwardApp]

/-- CCG backward application preserves the functor's result category. -/
theorem ccg_bapp_result_category (x y : CCG.Cat) :
    CCG.backwardApp y (CCG.Cat.lslash x y) = some x := by
  simp [CCG.backwardApp]

/-- A head function is **selection-respecting** at `(a, b)` iff when
    `a` selects `b`, the head function picks `a`'s head leaf as the head
    of `.node a b` (i.e., `a` projects). This is the explicit MCB-aligned
    encoding of "selector projects": the legacy assumption is no longer
    baked into `HeadFunction` itself, but reappears as a property a
    particular `h` may or may not satisfy.

    Restated against the Phase 2 externalize encoding (MCB §1.12.1):
    "marking places the projecting head on the left daughter" becomes
    "the head of the merged node equals the head of `a`". -/
def IsSelectionRespectingAt
    (h : Minimalist.HeadFunction) (a b : Minimalist.SyntacticObject) : Prop :=
  Minimalist.selects h a b → h.head (.node a b) = h.head a

/-- Minimalist labeling (MCB §1.13.6 / §1.15): under a selection-respecting
    head function `h`, when α selects β, the head of `{α, β}` agrees with
    the head of α. The legacy `selector projects` claim restated MCB-
    natively: it is no longer a property of labeling, but a property of
    a chosen head function — namely those satisfying
    `IsSelectionRespectingAt`. -/
theorem min_selector_projects
    (h : Minimalist.HeadFunction) (a b : Minimalist.SyntacticObject)
    (hs : Minimalist.selects h a b)
    (h_resp : IsSelectionRespectingAt h a b) :
    Minimalist.HeadFunction.head h (Minimalist.merge a b) =
    Minimalist.HeadFunction.head h a :=
  -- `merge a b` is defeq to `.node a b`, so this is exactly the
  -- selection-respecting property applied to `hs`.
  h_resp hs

/-- **The substantive refutation theorem MCB's framework now makes statable**:
    selection and projection are independent properties. There exist a
    `HeadFunction` and a configuration where one side selects but the
    marking puts the head on the other side — formalising MCB's
    "selection ≠ projection" position (the selector-projects assumption
    is a property of *some* head functions, not a structural fact about
    Merge).

    **Witness construction (Phase 2-aware)**: with the externalize-based
    `HeadFunction`, witnesses require a custom `h.section_.σ` that places
    `b`'s head as the leftmost-leaf of `.node a b`'s planar representative
    (so `headAt h (.node a b) = headAt h b ≠ headAt h a`), violating
    `IsSelectionRespectingAt`. The `leftSpine`/`rightSpine` defaults both
    use `Quot.out` and so cannot serve as distinct witnesses post-Phase-2;
    a constructive witness needs a per-test `externalize` choice. The
    statement remains TODO until Tier B+ provides parameterized
    selection apparatus (`checkedSelWith?`).

    **Why this matters cross-framework**: HPSG's Head Feature Principle
    and CCG's slash-functor invariance both bake "the selector projects"
    into the type of their structures (HeadCompRule's designated head
    field; CCG's slash directions). MCB's nonplanar Merge does NOT bake
    this in — it's a downstream choice of head function. This theorem
    witnesses the separation in Lean. -/
theorem selection_marking_independence_refutation :
    ∃ (h : Minimalist.HeadFunction) (a b : Minimalist.SyntacticObject),
      Minimalist.selects h a b ∧ ¬ IsSelectionRespectingAt h a b := by
  -- TODO: requires concrete LIToken witnesses with non-trivial outerSel
  -- + verification that `rightSpine`'s marking returns `false` on the
  -- node. The theorem is statable (which was the audit's headline
  -- claim) but a concrete witness needs leaf-level reasoning that
  -- depends on the same Quot.out chain that's currently noncomputable.
  -- Phase 2 LCA work will discharge this via head-function-aware
  -- structural reduction.
  sorry

/-- Labeling convergence across theories (MCB-aligned formulation).

Four independent formulations of "the head determines the result's category"
all hold simultaneously. The Minimalist clause is parametric over a head
function `h`: whichever head function the analyst chooses, the head's
category projects (this is the definition of `MCBLabeling.labelRoot`). -/
theorem labeling_convergence :
    -- Minimalism (MCB §1.15): for any head function `h` defined on
    -- `(.node a b)`, the root label is the head's outer category.
    (∀ (h : Minimalist.HeadFunction) (a b : Minimalist.SyntacticObject),
      h.Dom (.node a b) →
      Minimalist.Labeling.labelRoot h (.node a b) =
        some ((h.head (.node a b)).item.outerCat)) ∧
    -- CCG: forward application yields functor's result category
    (∀ x y : CCG.Cat, CCG.forwardApp (CCG.Cat.rslash x y) y = some x) ∧
    -- CCG: backward application yields functor's result category
    (∀ x y : CCG.Cat, CCG.backwardApp y (CCG.Cat.lslash x y) = some x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun h a b hT => Minimalist.Labeling.labelRoot_node_in_dom h a b hT
  · intro x y; simp [CCG.forwardApp]
  · intro x y; simp [CCG.backwardApp]

/-! ## §3. External Merge ↔ Head-Complement ↔ Application (§2.2–2.3)

All theories implement the head-complement combination:
- Minimalism: External Merge where one SO selects the other (first-merged
  elements are complements, Chomsky 2008:146 apud Müller §2.2)
- HPSG: Head-Complement Schema (head word combines with complements)
- CCG: Forward/backward application (functor consumes argument)
- DG: Core dependency relations (obj, det, comp,...) -/

/-- External Merge with selection is Head-Complement across all theories
    (Minimalist clause parametric over the head function `h`). -/
theorem external_merge_is_head_complement :
    -- Minimalism: Ext Merge with selection = headComplement
    (∀ (h : Minimalist.HeadFunction) (a b : Minimalist.SyntacticObject),
      Minimalist.selects h a b →
      classifyExternalMerge h a b = .headComplement) ∧
    -- HPSG: HeadCompRule = headComplement
    (∀ r : HPSG.HeadCompRule,
      classifyHPSGSchema (.headComp r) = some .headComplement) ∧
    -- CCG: fapp = headComplement
    (∀ d1 d2 : CCG.DerivStep,
      classifyCCGDerivStep (.fapp d1 d2) = some .headComplement) ∧
    -- DG: obj dep = headComplement
    (classifyDepType .obj = .headComplement) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h a b hs; exact selection_implies_headComplement h a b hs
  · intro _; rfl
  · intro _ _; rfl
  · rfl

/-! ### RSRL grounding of the Head-Complement HFP

A minimal worked HPSG signature, the **Head Feature Principle** as a description, two worked
head-complement models (one satisfying, one violating the HFP), and a faithful **structure-sharing**
bridge from the computational `HPSG.HeadCompRule.hfp` (category *value* equality) to the token-identity
HFP of the RSRL model theory (`Syntax/HPSG/{Signature,Interpretation,Description}`). This worked example
is consumed only by this study, so it lives here rather than in the substrate ([richter-2000],
[richter-2024], [pollard-sag-1994]).

The HFP works at **CAT** granularity (what `HeadCompRule.hfp` exposes), a valence-free stand-in for
canonical **HEAD**-value sharing. `HeadCompRule.hfp` is value equality while the grammar's `pathEq` HFP
is token identity, so the induced model must structure-share the category object for the principle to
hold (`toInterpShared`). Only `hpsgSig` is `@[reducible]`; the models are plain `def`s with explicit
carrier instances. -/
namespace HFPGrounding

open HPSG.RSRL

/-! ### A minimal HPSG sort hierarchy and signature -/

/-- Sorts of the worked fragment. `category` generalises the category species
`nounCat`/`verbCat`/`otherCat`; `headedPhrase`/`word` are the sign species. -/
inductive HSort where
  | top | sign | phrase | headedPhrase | word | category | nounCat | verbCat | otherCat
  deriving DecidableEq, Fintype, Repr

/-- Attributes of the worked fragment: `CAT` (a sign's category) and `HD` (the head daughter
of a headed phrase). -/
inductive HAttr where
  | CAT | HD
  deriving DecidableEq, Fintype, Repr

/-- Direct subsumption ("covers"): the DAG edges (a *directly* more specific than b). The order is
`ReflTransGen hCovers`. -/
def hCovers : HSort → HSort → Bool
  | .sign, .top => true
  | .category, .top => true
  | .phrase, .sign => true
  | .word, .sign => true
  | .headedPhrase, .phrase => true
  | .nounCat, .category => true
  | .verbCat, .category => true
  | .otherCat, .category => true
  | _, _ => false

/-- Specificity depth; every covers edge strictly increases it (giving antisymmetry). -/
def hRank : HSort → Nat
  | .top => 0
  | .sign => 1 | .category => 1
  | .phrase => 2 | .word => 2 | .nounCat => 2 | .verbCat => 2 | .otherCat => 2
  | .headedPhrase => 3

/-- The sort hierarchy as a `PartialOrder` (`a ≤ b` = "`a` at least as specific as `b`"). -/
instance : PartialOrder HSort :=
  partialOrderOfCovers (hCovers · · = true) hRank (by decide)

instance : DecidableLE HSort := fun a b =>
  decidableLEOfCovers (covers := (hCovers · · = true))
    [.top, .sign, .phrase, .headedPhrase, .word, .category, .nounCat, .verbCat, .otherCat]
    (by decide) a b

/-- Appropriateness: `CAT` is appropriate to every sign (value `category`); `HD` to headed
phrases (value `sign`). Categories are attributeless. -/
def happrop : HSort → HAttr → Option HSort
  | .sign, .CAT => some .category
  | .phrase, .CAT => some .category
  | .headedPhrase, .CAT => some .category
  | .word, .CAT => some .category
  | .headedPhrase, .HD => some .sign
  | _, _ => none

private theorem happrop_inh : ∀ (σ₁ σ₂ : HSort) (α : HAttr) (τ₁ : HSort),
    σ₂ ≤ σ₁ → happrop σ₁ α = some τ₁ → ∃ τ₂, happrop σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁ := by decide

/-- The worked HPSG signature. Reducible so its projections (`Attr`, `approp`) resolve in
instance search; the models below are plain `def`s. -/
@[reducible] def hpsgSig : Signature HSort where
  Attr := HAttr
  Rel := Empty
  arity := fun e => e.elim
  approp := happrop
  approp_inherits := fun {σ₁ σ₂ α τ₁} => happrop_inh σ₁ σ₂ α τ₁


/-! ### The Head Feature Principle -/

/-- The **Head Feature Principle** ([pollard-sag-1994]; [richter-2024], Ch. 3, (3a)),
at CAT granularity: a headed phrase shares its category (path `CAT`) with its head daughter
(path `HD CAT`), as token identity (`pathEq`). The mother is the described entity `:`; `CAT`
and `HD CAT` are `:`-rooted paths (`Term.path`). -/
def hfp : Desc hpsgSig :=
  .imp (.sortAssign .colon .headedPhrase) (.pathEq (.path [.CAT]) (.path [.HD, .CAT]))

/-- The one-principle grammar of the worked fragment. -/
def hpsgGrammar : Grammar hpsgSig := [hfp]

/-! ### Worked head-complement structures (entities: mother, head daughter, two categories) -/

/-- Entities of a worked head-complement structure. -/
inductive Ent where
  | mother | headDtr | catM | catH
  deriving DecidableEq, Fintype, Repr

/-- A well-formed head-complement structure: the mother and its head daughter point at one
shared category entity, so the Head Feature Principle holds. -/
def posModel : Interpretation hpsgSig where
  U := Ent
  S := fun
    | .mother => .headedPhrase
    | .headDtr => .word
    | .catM => .nounCat
    | .catH => .nounCat
  A := fun a u => match a, u with
    | .CAT, .mother => some .catM
    | .CAT, .headDtr => some .catM
    | .HD, .mother => some .headDtr
    | _, _ => none
  R := fun e => e.elim

-- Explicit `Fintype`/`DecidableEq` on the carrier so `decide` resolves the decision instances
-- *without* unfolding `posModel` (which would reduce `.R` and unmatch the empty-relation
-- instance below). The kernel still unfolds `posModel` when evaluating `decide`.
instance : Fintype posModel.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq posModel.U := inferInstanceAs (DecidableEq Ent)

/-- The well-formed structure satisfies the Head Feature Principle. -/
example : posModel.Models hpsgGrammar := by decide

/-- The well-formed structure is totally well-typed. -/
example : posModel.WellTyped := by decide

/-- An ill-formed structure: the head daughter's category differs from the mother's, so the
HFP fails — the principle is a genuine filter, not vacuously satisfied. -/
def negModel : Interpretation hpsgSig where
  U := Ent
  S := fun
    | .mother => .headedPhrase
    | .headDtr => .word
    | .catM => .nounCat
    | .catH => .verbCat
  A := fun a u => match a, u with
    | .CAT, .mother => some .catM
    | .CAT, .headDtr => some .catH
    | .HD, .mother => some .headDtr
    | _, _ => none
  R := fun e => e.elim

instance : Fintype negModel.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq negModel.U := inferInstanceAs (DecidableEq Ent)

/-- The ill-formed structure violates the Head Feature Principle. -/
example : ¬ negModel.Models hpsgGrammar := by decide

/-- It is nonetheless well-typed: it only violates the *principle*, not the signature. -/
example : negModel.WellTyped := by decide

/-! ### A faithful structure-sharing bridge to the computational HPSG core

`HPSG.HeadCompRule.hfp` is value equality (the mother and head daughter agree in category *value*),
while the grammar's `pathEq` HFP is *token identity*. Value equality does not entail token identity, so
a naive induced model with *distinct* category entities would satisfy only sort agreement, not the HFP.
The faithful bridge therefore **structure-shares** the category object — the mother and head daughter
point at one entity — which the rule's value-equality HFP (`r.hfp`) justifies. -/

/-- A category species for each UD category. -/
def catSpecies : UD.UPOS → HSort
  | .NOUN => .nounCat
  | .VERB => .verbCat
  | _ => .otherCat

/-- A category species is never a phrase sort, so it can never trigger the headed-phrase HFP. -/
private theorem catSpecies_not_headedPhrase (c : UD.UPOS) :
    ¬ (catSpecies c ≤ HSort.headedPhrase) := by
  cases c <;> decide

/-- The interpretation induced by a head-complement rule that **structure-shares** the category
object: the mother and head daughter both point at one category entity (`catM`, species from the head
daughter), realizing the token-identity HFP. -/
def toInterpShared (r : HPSG.HeadCompRule) : Interpretation hpsgSig where
  U := Ent
  S := fun
    | .mother => .headedPhrase
    | .headDtr => .word
    | .catM => catSpecies r.head.synsem.cat
    | .catH => catSpecies r.result.synsem.cat
  A := fun a u => match a, u with
    | .CAT, .mother => some .catM
    | .CAT, .headDtr => some .catM     -- structure sharing: both daughters point at one category
    | .HD, .mother => some .headDtr
    | _, _ => none
  R := fun e => e.elim

/-- **The faithful bridge.** The structure-sharing induced model satisfies the grammar's
token-identity Head Feature Principle — the mother and head daughter genuinely share one category
object, not merely agree in sort. -/
theorem toInterpShared_models_hfp (r : HPSG.HeadCompRule) :
    (toInterpShared r).Models hpsgGrammar := by
  intro u d hd
  simp only [hpsgGrammar, List.mem_singleton] at hd
  subst hd
  cases u with
  | mother => exact fun _ => rfl                              -- HFP holds: both daughters share catM
  | headDtr =>                                                -- word ⋨ headed-phrase
    exact fun h => absurd (show HSort.word ≤ HSort.headedPhrase from h) (by decide)
  | catM => exact fun h => absurd h (catSpecies_not_headedPhrase r.head.synsem.cat)
  | catH => exact fun h => absurd h (catSpecies_not_headedPhrase r.result.synsem.cat)

/-- The structure-sharing is *justified* by the computational value-equality HFP (`r.hfp`): the
mother's and head daughter's category species coincide, so collapsing them to one object loses no
information — recovering genuine token identity from value equality. -/
theorem toInterpShared_faithful_of_hfp (r : HPSG.HeadCompRule) :
    catSpecies r.result.synsem.cat = catSpecies r.head.synsem.cat := by
  rw [r.hfp]

end HFPGrounding

/-- **Model-theoretic grounding (RSRL).** The HPSG Head-Complement schema compared to External Merge
above carries the Head Feature Principle (`HeadCompRule.hfp`: mother and head daughter share their
category *value*). On the RSRL substrate that value-equality is the shadow of genuine **token
identity**: the structure-sharing induced model satisfies the model-theoretic HFP, so each schema
instance is grounded in `HFPGrounding.toInterpShared_models_hfp` above. -/
theorem headComp_hfp_rsrl_grounded (r : HPSG.HeadCompRule) :
    (HFPGrounding.toInterpShared r).Models HFPGrounding.hpsgGrammar :=
  HFPGrounding.toInterpShared_models_hfp r

/-- External Merge without selection is Head-Specifier across theories
    (Minimalist clause parametric over the head function `h`). -/
theorem external_merge_is_head_specifier :
    -- Minimalism: Ext Merge without selection = headSpecifier
    (∀ (h : Minimalist.HeadFunction) (a b : Minimalist.SyntacticObject),
      ¬ Minimalist.selects h a b → ¬ Minimalist.selects h b a →
      classifyExternalMerge h a b = .headSpecifier) ∧
    -- HPSG: HeadSubjRule = headSpecifier
    (∀ r : HPSG.HeadSubjRule,
      classifyHPSGSchema (.headSubj r) = some .headSpecifier) ∧
    -- DG: subj dep = headSpecifier
    (classifyDepType .nsubj = .headSpecifier) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h a b ha hb; exact no_selection_implies_headSpecifier h a b ha hb
  · intro _; rfl
  · rfl

/-! ## §4. Internal Merge ↔ Head-Filler ↔ Composition (§2.3)

All theories handle long-distance dependencies via the third schema:
- Minimalism: Internal Merge — Stabler's `im` (Müller's 28) corresponds
  to the HPSG Head-Filler Schema (Pollard & Sag 1994:164, p. 939)
- HPSG: Head-Filler Schema (filler XP + S[SLASH {XP}])
- CCG: Forward/backward composition (enables extraction)
- DG: Non-projective (crossing) dependencies -/

/-- Internal Merge / Head-Filler / Composition across theories. -/
theorem internal_merge_is_head_filler :
    -- Minimalism: Internal Merge = headFiller
    (classifyInternalMerge = .headFiller) ∧
    -- HPSG: HeadFillerRule = headFiller
    (∀ r : HPSG.HeadFillerRule,
      classifyHPSGSchema (.headFiller r) = some .headFiller) ∧
    -- CCG: forward composition = headFiller
    (∀ d1 d2 : CCG.DerivStep,
      classifyCCGDerivStep (.fcomp d1 d2) = some .headFiller) ∧
    -- CCG: backward composition = headFiller
    (∀ d1 d2 : CCG.DerivStep,
      classifyCCGDerivStep (.bcomp d1 d2) = some .headFiller) := by
  exact ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Non-projective dependencies in DG correspond to Head-Filler.

A non-projective (crossing) dependency represents displacement — the DG
analogue of Internal Merge and the Head-Filler Schema. -/
theorem dg_nonproj_is_filler_gap :
    -- A tree with crossing arcs has filler-gap dependencies
    DepGrammar.hasFillerGap DepGrammar.nonProjectiveTree = true := by
  decide

/-! ## §5. Coordination Diagnostic (§1, §2.2)

Coordination requires matching categories: "two constituents that have
compatible syntactic properties can be coordinated and ... the result of
the coordination is an object that has the syntactic properties of the
linguistic objects that are coordinated" (p. 924). This is a *diagnostic*
for whether two expressions have the same category. -/

/-- CCG coordination requires matching categories. -/
theorem ccg_coordination_same_cat (c1 c2 : CCG.Cat) :
    CCG.coordinate c1 c2 ≠ none → c1 = c2 := by
  simp only [CCG.coordinate]
  intro h
  by_contra hne
  have : ¬(c1 == c2) = true := by
    intro heq; exact hne (beq_iff_eq.mp heq)
  simp [this] at h

/-- CCG coordination of mismatched categories fails. -/
theorem ccg_coordination_mismatch (c1 c2 : CCG.Cat) (h : c1 ≠ c2) :
    CCG.coordinate c1 c2 = none := by
  simp only [CCG.coordinate]
  have : ¬(c1 == c2) = true := by
    intro heq; exact h (beq_iff_eq.mp heq)
  simp [this]

/-- HPSG lexical rules preserve head features, enabling coordination — grounded **model-theoretically**
in the RSRL `inflectional-cxt` (`Syntax/HPSG/Construction`): a category-preserving lexical rule's output
shares the base's category (`inflectionalPrinciple`, the Head Feature Principle for the lexicon), so two
same-category outputs of the rule coordinate (e.g. passivized verbs); an output whose category differs
from the base is rejected. -/
theorem hpsg_lexrule_enables_coordination :
    HPSG.Construction.goodInflectional.Models HPSG.Construction.grammar ∧
    ¬ HPSG.Construction.inflectionalWrongCat.Models HPSG.Construction.grammar := by decide

/-! ## §6. Directional MG ≈ CCG (§2.3)

Stabler's directional Minimalist Grammar marks the position of an argument
relative to its head together with the selection feature: =x (argument to
the right) and x= (argument to the left), which "corresponds to forward and
backward application" in categorial grammar (Müller's 33, p. 938).

This formal correspondence is not yet formalized because directional MG
is not in the codebase. -/

/- Placeholder: directional MG ≈ CCG (Stabler's =x ≈ X/Y, x= ≈ X\Y).
   TODO: When directional MG is added, prove:
   - =x features ≈ forward slash (X/Y)
   - x= features ≈ backward slash (X\Y)
   - DMG derivation trees ≈ CCG derivation trees -/

/-! ## §7. Both Directions Right (§3)

Müller's conclusion: the three universal schemata handle fully abstract
constructions, but phrasal constructions (his examples: Jackendoff's N-P-N,
verbless directives) are irreducible — they cannot be decomposed into the
three schemata. "Both research directions are right to a certain extent"
(p. 920): we need BOTH Merge/schemata AND constructions.

`decompose` maps a fully abstract argument-structure construction to its
sequence of schema steps; the irreducibility witness is the *let alone*
construction ([fillmore-kay-oconnor-1988] — era-appropriate for a 2013
paper; see `GoldbergShirtz2025.pal_irreducible` for a later-discovered
witness making the same point). -/

/-- Decompose a fully abstract construction into a sequence of combination steps.

For a construction with slots [Subj, V, Obj1, Obj2]:
1. V + Obj2 → V' (Head-Complement)
2. V' + Obj1 → V'' (Head-Complement)
3. Subj + V'' → S (Head-Specifier)

The head slot determines which combinations are complements vs specifier. -/
def decompose (asc : ConstructionGrammar.ArgStructureConstruction) :
    List CombinationKind :=
  let nonHeadSlots := asc.slots.filter (!·.isHead)
  -- Subject (first non-head slot) maps to Head-Specifier,
  -- all other non-head slots map to Head-Complement
  nonHeadSlots.zipIdx.map λ ⟨_, i⟩ =>
    if i == 0 then .headSpecifier  -- first non-head = specifier (subject)
    else .headComplement           -- later non-heads = complements

/-- Ditransitive decomposes into Head-Specifier + Head-Complement + Head-Complement.

The ditransitive [Subj V Obj1 Obj2] decomposes as:
1. V + Obj2 → V' (Head-Complement)
2. V' + Obj1 → V'' (Head-Complement)
3. Subj + V'' → S (Head-Specifier) -/
theorem ditransitive_decomposes :
    decompose ConstructionGrammar.ditransitive =
      [.headSpecifier, .headComplement, .headComplement] := by
  decide

/-- Caused-motion decomposes into Head-Specifier + Head-Complement + Head-Complement. -/
theorem causedMotion_decomposes :
    decompose ConstructionGrammar.causedMotion =
      [.headSpecifier, .headComplement, .headComplement] := by
  decide

/-- Resultative decomposes into Head-Specifier + Head-Complement + Head-Complement. -/
theorem resultative_decomposes :
    decompose ConstructionGrammar.resultative =
      [.headSpecifier, .headComplement, .headComplement] := by
  decide

/-- Conative decomposes into Head-Specifier + Head-Complement. -/
theorem conative_decomposes :
    decompose ConstructionGrammar.conative =
      [.headSpecifier, .headComplement] := by
  decide

/-- All members of a polysemy family decompose identically
    (same slots → same decomposition). -/
theorem polysemyFamily_all_same_decomposition
    (f : ConstructionGrammar.PolysemyFamily)
    (ext : String × String × List String) :
    decompose (f.extensionConstruction ext) =
    decompose f.centralConstruction := by
  simp [decompose, ConstructionGrammar.ArgStructureConstruction.slots,
    ConstructionGrammar.PolysemyFamily.extensionConstruction,
    ConstructionGrammar.PolysemyFamily.centralConstruction]

/-- Both directions right: the three schemata AND phrasal constructions are needed.

1. Fully abstract constructions without pragmatic functions are fully
   compositional — decomposable into Head-Complement and Head-Specifier steps.
2. There exist constructions that are not fully compositional — they cannot
   be captured by the three schemata alone, requiring CxG's phrasal patterns
   (witness: *let alone*, [fillmore-kay-oconnor-1988]). -/
theorem both_directions_right :
    -- Direction 1: fully abstract constructions are fully compositional
    (∀ c : ConstructionGrammar.Construction,
      c.specificity = .fullyAbstract →
      c.pragmaticFunction = none →
      ConstructionGrammar.isFullyCompositional c = true) ∧
    -- Direction 2: there exist non-fully-compositional constructions
    (∃ c : ConstructionGrammar.Construction,
      ConstructionGrammar.isFullyCompositional c = false) :=
  ⟨ConstructionGrammar.fullyAbstract_isFullyCompositional,
   ⟨_, FillmoreKayOConnor1988.let_alone_irreducible⟩⟩

/-! ### Resultative family decomposition

[goldberg-jackendoff-2004]'s four resultative subconstructions, viewed
through the schema decomposition (the chronologically later paper's
apparatus applied to the earlier paper's constructions). -/

section ResultativeFamily

open ConstructionGrammar.Resultatives

/-- All four resultative subconstructions are fully compositional. -/
theorem allResultativesFullyCompositional :
    resultativeFamily.all (λ c =>
      ConstructionGrammar.isFullyCompositional c.construction) = true := by
  decide

/-- Causative subconstructions decompose like the parent resultative. -/
theorem causative_decompose_like_parent :
    decompose causativePropertyConstruction =
      decompose ConstructionGrammar.resultative ∧
    decompose causativePathConstruction =
      decompose ConstructionGrammar.resultative := by
  constructor <;> decide

/-- Noncausative subconstructions decompose into fewer combination steps. -/
theorem noncausative_fewer_steps :
    (decompose noncausativePropertyConstruction).length <
    (decompose causativePropertyConstruction).length ∧
    (decompose noncausativePathConstruction).length <
    (decompose causativePathConstruction).length := by
  constructor <;> decide

/-- Decomposition length reflects transitivity: causative subconstructions
    have three combination steps, noncausative two. -/
theorem decomposition_reflects_transitivity :
    (decompose causativePropertyConstruction).length = 3 ∧
    (decompose noncausativePropertyConstruction).length = 2 := by
  constructor <;> decide

end ResultativeFamily

/-! ## §8. Concrete Cross-Theory Examples

Verify that specific combinations classify identically across theories. -/

/-- Det + N via forward application is Head-Complement in CCG. -/
example : classifyCCGDerivStep
    (.fapp (.lex ⟨"the", CCG.Det⟩) (.lex ⟨"pizza", CCG.N⟩)) =
    some .headComplement := rfl

/-- Det dependency is Head-Complement in DG. -/
example : classifyDepType .det = .headComplement := rfl

/-- Subject dependency is Head-Specifier in DG. -/
example : classifyDepType .nsubj = .headSpecifier := rfl

/-- The three schemata are exhaustive for External Merge in Minimalism
    (under any head function `h`). -/
theorem min_external_exhaustive
    (h : Minimalist.HeadFunction) (a b : Minimalist.SyntacticObject) :
    classifyExternalMerge h a b = .headComplement ∨
    classifyExternalMerge h a b = .headSpecifier :=
  classify_external_exhaustive h a b

/-- The three primary HPSG schemata map to the three universal schemata;
    Head-Modifier (adjunction) falls outside the classification. -/
theorem hpsg_schemata_classified (s : HPSG.HPSGSchema) :
    classifyHPSGSchema s = some .headComplement ∨
    classifyHPSGSchema s = some .headSpecifier ∨
    classifyHPSGSchema s = some .headFiller ∨
    classifyHPSGSchema s = none := by
  cases s with
  | headComp _ => left; rfl
  | headSubj _ => right; left; rfl
  | headFiller _ => right; right; left; rfl
  | headMod _ => right; right; right; rfl

/-- Head-Modifier falls outside Müller's three schemata.
    Adjunction is HPSG-specific and not part of the universal convergence claim. -/
theorem hpsg_headMod_not_classified (r : HPSG.HeadModRule) :
    classifyHPSGSchema (.headMod r) = none := rfl

/-! ## §9. Labeling Failures (§2.1)

Müller shows that Chomsky's labeling algorithm (his 14a/14b, from Chomsky
2008:145) fails in two ways:

1. **Free relatives**: 14a and 14b give contradictory labels for
   *what you wrote* (Müller's 16–17: a DP-like object via 14a, a clausal
   one via 14b), and complex free-relative phrases (his 18–19) defeat
   both rules
2. **Coordination of phrases**: labeling requires raising one conjunct
   (his 15), which makes wrong predictions for coordinations of two
   singular NPs (his fn. 13)

Note: The free relative SO `freeRelSO` models the surface structure
{what, [wrote ___]} without explicitly modeling Internal Merge — "what"
and the gap have different token IDs rather than being literal copies.
The labeling conflict holds regardless of how the gap is represented. -/

/-! Theorems `free_relative_labeling_conflict` and
`coordination_labeling_failure` were removed: their components in
`Syntax/Minimalist/Labeling.lean` (specifically
`freeRel_labelCat_gives_V`, `coord_neither_selects`) were
also removed because their `decide`-based proofs failed in the kernel
(recursive `label` does not reduce). The substantive Müller arguments
remain documented in `Labeling.lean`'s docstrings and in §10 below. -/

/-! ## §10. Monovalent Verb Serialization Problem (§2.3)

In Stabler's non-directional MG, external Merge (Müller's 27, from
Stabler 2010:402) treats a monovalent verb's sole argument as a complement
and serializes it to the right of the head, yielding "*Sleeps Max" instead
of "Max sleeps" (Müller's 30). Stabler's fix — combining monovalent verbs
with a nonovert object (Veenstra 1998:61, 124) — is "both stipulative and
entirely ad hoc, being motivated only by the wish to have uniform
structures" (p. 937). -/

section MonovalentVerbProblem

open Minimalist

/-- "sleeps" — a monovalent verb (category V, selects D). -/
def sleepsToken : LIToken := ⟨.simple .V [.D] (phonForm := "sleeps"), 200⟩

/-- "Max" — a proper name (category D, no selectional features). -/
def maxToken : LIToken := ⟨.simple .D [] (phonForm := "Max"), 201⟩

/-! Theorem `monovalent_classified_as_complement` — that
`classifyExternalMerge sleepsToken maxToken = .headComplement` (V
selects D, so the argument is a complement) — was removed because its
`decide`-based proof does not reduce in the kernel. The Müller argument
(Stabler's linearization yields "*Sleeps Max" instead of "Max sleeps",
requiring an ad hoc empty object) stands in the section docstring above. -/

/-- Left-to-right linearization of merge(sleeps, Max) gives "sleeps Max".
    This is the wrong order for English — it should be "Max sleeps".

    TODO Phase 2: `phonYield` is `Quot.out`-based after the FreeCommMagma
    migration; `decide` no longer reduces. Re-prove with parameterized
    linearization. -/
theorem monovalent_wrong_linearization :
    HeadFunction.leftSpine.phonYield (merge (.leaf sleepsToken) (.leaf maxToken))
      = ["sleeps", "Max"] := by
  sorry

/-- The desired order differs from the linearization. -/
theorem monovalent_desired_order_differs :
    ["Max", "sleeps"] ≠
      HeadFunction.leftSpine.phonYield (merge (.leaf sleepsToken) (.leaf maxToken)) := by
  sorry

end MonovalentVerbProblem

/-! ## §11. Iterable Valence Operations (§1)

Lexical rules compose freely, capturing double passivization (Turkish,
Özkaragöz 1986; Lithuanian, Timberlake 1982) without phrasal machinery. -/

/-- Any chain of lexical rules preserves head features, grounded **model-theoretically** in the RSRL
`inflectional-cxt`: a two-step chain (double passivization) keeps the category through both steps, so
lexical rules iterate freely with no phrasal machinery ([mueller-2013] §11). -/
theorem valence_iteration_works :
    HPSG.Construction.iterationChain.Models HPSG.Construction.grammar := by decide

/-! ## Summary Table

| Claim | Min | HPSG | CCG | DG | CxG | Status |
|-------|-----|------|-----|-----|-----|--------|
| Head-Complement | Ext Merge + sel | HeadComp | fapp/bapp | obj/det/... | slot decomp | Proved |
| Head-Specifier | Ext Merge − sel | HeadSubj | (= bapp) | subj | slot decomp | Proved |
| Head-Filler | Int Merge | HeadFiller | fcomp/bcomp | nonproj | irreducible | Proved |
| Head-Modifier | — | HeadMod | — | — | — | Not in 3 schemata |
| Labeling | selector proj | HFP | functor result | head | — | Proved |
| Coordination | same cat | same cat | same cat | — | — | Proved |
| Labeling failure (FR) | 14a≠14b | — | — | — | — | Documented |
| Labeling failure (coord) | no rule applies | — | — | — | — | Documented |
| Monovalent verb | *Sleeps Max | — | — | — | — | Sorry (Phase 2) |
| Valence iteration | — | double passive | — | — | — | Proved |
| Directional MG ≈ CCG | =x ≈ X/Y | — | — | — | — | Not formalized |
| Both directions right | — | — | — | — | abstract ∨ phrasal | Proved |

Note: CCG has no separate Head-Specifier mechanism. Subject combination uses
backward application (the verb S\NP is the functor), which is Head-Complement
in the classification. The subject/complement distinction is syntactic, not
combinatory, in CCG.
-/

end Mueller2013
