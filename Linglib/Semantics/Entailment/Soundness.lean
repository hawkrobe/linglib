import Linglib.Core.Logic.NaturalLogic
import Linglib.Semantics.Entailment.AntiAdditivity

/-!
# Soundness of the projectivity calculus

Semantic grounding for [icard-2012]'s projectivity machinery: `NLRelation`
gets its lattice content (`Holds`, his Definition 1.2 — non-exclusive
equations, so `⊑` is plain `≤`), and a signature is *sound* for a function
(`EntailmentSig.SoundFor`) when the function projects every relation as the
signature's `project` row says (his Lemma 2.5). The characterization
theorems discharge each row from the property family in
`Semantics.Entailment.AntiAdditivity` — the additive-family rows need the
`IsCompletely*` unit conditions, exactly as Icard's tables assume; the
soundness proofs go through over bounded lattices, not just his Boolean
lattices.

`SoundFor.comp` and `soundFor_contextProjectivity` certify
`EntailmentSig.compose` and path projection against function composition
(his Lemma 2.7 and Proposition 2.10): study-file locality computations over
the enum become corollaries of facts about actual context functions.

## Main declarations

- `NLRelation.Holds`: lattice content of the seven relations;
- `EntailmentSig.SoundFor`: σ's projection row is sound for `f`;
- `soundFor_mono_iff`, `soundFor_anti_iff`: the monotone rows, as iffs;
- `soundFor_additive` … `soundFor_antiAddMult`: the algebraic rows, from
  `IsCompletely*` hypotheses (sound direction; the converses fail —
  projection rows are class-maximal, not function-characterizing);
- `SoundFor.comp`: soundness composes along `EntailmentSig.compose`;
- `soundFor_contextProjectivity`: soundness folds along a signature path.

## Two flagged divergences (enum-level, not touched here)

- `project` gives `.all` and `.addMult` identical rows, so
  `soundFor_all_iff_addMult` holds by `Iff.rfl`; in [icard-2012] the
  identity class is additive-and-multiplicative (his ⊕⊞) while • ("all
  functions") projects everything to `#` and is absorbing. linglib's
  `.all` plays ⊕⊞'s role under `project`/`compose` but sits at the bottom
  of `Refines` — semantically the bottom reading is wrong (morphisms are
  not antitone), which is why no `SoundFor`-monotonicity along `Refines`
  is stated.
- `NLRelation.Refines` puts `.equiv` below all seven relations; under the
  implication reading ([icard-2012] §1) `≡` does not refine `^`, `|`, or
  `⌣`. `Holds` follows the paper, not the enum order.
-/

namespace Core.NaturalLogic

open Semantics.Entailment.AntiAdditivity

/-! ### Lattice content of the relations -/

/-- The lattice content of a natural-logic relation ([icard-2012]
Definition 1.2): non-exclusive equations over a bounded lattice. `negation`
is complementhood (cf. mathlib's `IsCompl`); `forward` is non-strict `≤`
(the enum comments' `⊂` follows MacCartney's exclusive reading, which the
projectivity tables do not need). -/
def NLRelation.Holds {α : Type*} [Lattice α] [BoundedOrder α] :
    NLRelation → α → α → Prop
  | .equiv => fun x y => x = y
  | .forward => fun x y => x ≤ y
  | .reverse => fun x y => y ≤ x
  | .negation => fun x y => x ⊓ y = ⊥ ∧ x ⊔ y = ⊤
  | .alternation => fun x y => x ⊓ y = ⊥
  | .cover => fun x y => x ⊔ y = ⊤
  | .independent => fun _ _ => True

/-! ### Soundness of a signature for a function -/

section SoundFor

variable {α β γ : Type*} [Lattice α] [BoundedOrder α] [Lattice β]
  [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- A signature σ is **sound for** `f` when `f` projects every relation as
σ's row of the projection table says ([icard-2012] Lemma 2.5: every
φ-function projects `R` to `[R]^φ`). -/
def EntailmentSig.SoundFor (σ : EntailmentSig) (f : α → β) : Prop :=
  ∀ (R : NLRelation) (x y : α), R.Holds x y →
    (EntailmentSig.project R σ).Holds (f x) (f y)

/-- The `.mono` row is sound for exactly the monotone functions. -/
theorem soundFor_mono_iff {f : α → β} :
    EntailmentSig.SoundFor .mono f ↔ Monotone f := by
  constructor
  · intro h x y hxy
    exact h .forward x y hxy
  · intro h R x y hR
    cases R with
    | equiv => exact congrArg f hR
    | forward => exact h hR
    | reverse => exact h hR
    | negation | alternation | cover | independent => trivial

/-- The `.anti` row is sound for exactly the antitone functions. -/
theorem soundFor_anti_iff {f : α → β} :
    EntailmentSig.SoundFor .anti f ↔ Antitone f := by
  constructor
  · intro h x y hxy
    exact h .forward x y hxy
  · intro h R x y hR
    cases R with
    | equiv => exact congrArg f hR
    | forward => exact h hR
    | reverse => exact h hR
    | negation | alternation | cover | independent => trivial

/-- The `.additive` row is sound for completely additive functions. -/
theorem soundFor_additive {f : α → β} (h : IsCompletelyAdditive f) :
    EntailmentSig.SoundFor .additive f := by
  obtain ⟨hadd, htop⟩ := h
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact hadd.monotone hR
  | reverse => exact hadd.monotone hR
  | negation => show f x ⊔ f y = ⊤; rw [← hadd x y, hR.2]; exact htop
  | alternation => trivial
  | cover => show f x ⊔ f y = ⊤; rw [← hadd x y, hR]; exact htop
  | independent => trivial

/-- The `.mult` row is sound for completely multiplicative functions. -/
theorem soundFor_mult {f : α → β} (h : IsCompletelyMultiplicative f) :
    EntailmentSig.SoundFor .mult f := by
  obtain ⟨hmult, hbot⟩ := h
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact hmult.monotone hR
  | reverse => exact hmult.monotone hR
  | negation => show f x ⊓ f y = ⊥; rw [← hmult x y, hR.1]; exact hbot
  | alternation => show f x ⊓ f y = ⊥; rw [← hmult x y, hR]; exact hbot
  | cover => trivial
  | independent => trivial

/-- The `.antiAdd` row is sound for completely anti-additive functions. -/
theorem soundFor_antiAdd {f : α → β} (h : IsCompletelyAntiAdditive f) :
    EntailmentSig.SoundFor .antiAdd f := by
  obtain ⟨haa, htop⟩ := h
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact haa.antitone hR
  | reverse => exact haa.antitone hR
  | negation => show f x ⊓ f y = ⊥; rw [← haa x y, hR.2]; exact htop
  | alternation => trivial
  | cover => show f x ⊓ f y = ⊥; rw [← haa x y, hR]; exact htop
  | independent => trivial

/-- The `.antiMult` row is sound for completely anti-multiplicative
functions. -/
theorem soundFor_antiMult {f : α → β} (h : IsCompletelyAntiMultiplicative f) :
    EntailmentSig.SoundFor .antiMult f := by
  obtain ⟨ham, hbot⟩ := h
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact ham.antitone hR
  | reverse => exact ham.antitone hR
  | negation => show f x ⊔ f y = ⊤; rw [← ham x y, hR.1]; exact hbot
  | alternation => show f x ⊔ f y = ⊤; rw [← ham x y, hR]; exact hbot
  | cover => trivial
  | independent => trivial

/-- The `.addMult` row (preserve everything) is sound for morphisms:
completely additive and completely multiplicative functions. -/
theorem soundFor_addMult {f : α → β} (hadd : IsCompletelyAdditive f)
    (hmult : IsCompletelyMultiplicative f) :
    EntailmentSig.SoundFor .addMult f := by
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact hadd.1.monotone hR
  | reverse => exact hadd.1.monotone hR
  | negation =>
      exact ⟨by show f x ⊓ f y = ⊥; rw [← hmult.1 x y, hR.1]; exact hmult.2,
             by show f x ⊔ f y = ⊤; rw [← hadd.1 x y, hR.2]; exact hadd.2⟩
  | alternation => show f x ⊓ f y = ⊥; rw [← hmult.1 x y, hR]; exact hmult.2
  | cover => show f x ⊔ f y = ⊤; rw [← hadd.1 x y, hR]; exact hadd.2
  | independent => trivial

/-- The `.antiAddMult` row is sound for anti-morphisms: completely
anti-additive and completely anti-multiplicative functions. This is the
sentential-negation row — the semantic content of "double negation is a
morphism". -/
theorem soundFor_antiAddMult {f : α → β} (haa : IsCompletelyAntiAdditive f)
    (ham : IsCompletelyAntiMultiplicative f) :
    EntailmentSig.SoundFor .antiAddMult f := by
  intro R x y hR
  cases R with
  | equiv => exact congrArg f hR
  | forward => exact haa.1.antitone hR
  | reverse => exact haa.1.antitone hR
  | negation =>
      exact ⟨by show f x ⊓ f y = ⊥; rw [← haa.1 x y, hR.2]; exact haa.2,
             by show f x ⊔ f y = ⊤; rw [← ham.1 x y, hR.1]; exact ham.2⟩
  | alternation => show f x ⊔ f y = ⊤; rw [← ham.1 x y, hR]; exact ham.2
  | cover => show f x ⊓ f y = ⊥; rw [← haa.1 x y, hR]; exact haa.2
  | independent => trivial

/-- `.all` and `.addMult` have definitionally identical projection rows —
the flagged enum-level duplicate. -/
theorem soundFor_all_iff_addMult {f : α → β} :
    EntailmentSig.SoundFor .all f ↔ EntailmentSig.SoundFor .addMult f :=
  Iff.rfl

/-- The `.all` row is sound for morphisms (via the `.addMult` duplicate). -/
theorem soundFor_all {f : α → β} (hadd : IsCompletelyAdditive f)
    (hmult : IsCompletelyMultiplicative f) :
    EntailmentSig.SoundFor .all f :=
  soundFor_all_iff_addMult.mpr (soundFor_addMult hadd hmult)

/-! ### Composition and paths -/

/-- **Soundness composes along `EntailmentSig.compose`** ([icard-2012]
Lemma 2.7 + Proposition 2.10): if ψ is sound for the outer function and φ
for the inner one, `ψ * φ` is sound for the composite. This is the theorem
that certifies the enum-level `compose` table against actual context
functions. -/
theorem EntailmentSig.SoundFor.comp {ψ φ : EntailmentSig} {f : β → γ}
    {g : α → β} (hf : ψ.SoundFor f) (hg : φ.SoundFor g) :
    (ψ * φ).SoundFor (f ∘ g) := by
  intro R x y hR
  have h := hf (EntailmentSig.project R φ) (g x) (g y) (hg R x y hR)
  rwa [projection_composition] at h

/-- The identity context is sound for `.all` (vacuously: `.all` preserves
every relation, and so does `id`). -/
theorem soundFor_all_id : EntailmentSig.SoundFor .all (id : α → α) :=
  fun _ _ _ hR => hR

/-- **Path soundness**: a path of (signature, context) pairs, each sound,
yields a context sound for `contextProjectivity` of the signature path —
the semantic counterpart of [icard-2012] Definition 2.9's marking
algorithm. Signatures are listed outermost-first, matching
`contextProjectivity`. -/
theorem soundFor_contextProjectivity :
    ∀ (l : List (EntailmentSig × (α → α))),
      (∀ p ∈ l, p.1.SoundFor p.2) →
      (EntailmentSig.contextProjectivity (l.map Prod.fst)).SoundFor
        ((l.map Prod.snd).foldr (· ∘ ·) id)
  | [], _ => soundFor_all_id
  | p :: l, h => by
      have hhead : p.1.SoundFor p.2 := h p (List.mem_cons_self ..)
      have htail := soundFor_contextProjectivity l
        (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simpa [EntailmentSig.contextProjectivity, List.prod_cons, List.map_cons,
        List.foldr_cons] using
        hhead.comp htail

end SoundFor

/-! ### Worked instance: double negation is a morphism, semantically

`pnot` is completely anti-additive and completely anti-multiplicative, so
the `.antiAddMult` row is sound for it; composing it with itself certifies
the enum fact `◇⊟ ∘ ◇⊟ = ⊕⊞` against the actual function `pnot ∘ pnot`. -/

section PnotInstance

open Semantics.Entailment

theorem pnot_isCompletelyAntiAdditive : IsCompletelyAntiAdditive pnot :=
  ⟨pnot_isAntiAdditive, by show (Set.univ : Set World)ᶜ = ∅; exact Set.compl_univ⟩

theorem pnot_isCompletelyAntiMultiplicative :
    IsCompletelyAntiMultiplicative pnot :=
  ⟨pnot_isAntiMultiplicative, by show (∅ : Set World)ᶜ = Set.univ; exact Set.compl_empty⟩

/-- Negation realizes the anti-morphism row. -/
theorem pnot_soundFor_antiAddMult :
    EntailmentSig.SoundFor .antiAddMult pnot :=
  soundFor_antiAddMult pnot_isCompletelyAntiAdditive
    pnot_isCompletelyAntiMultiplicative

/-- Double negation realizes the morphism row — the composed-signature
fact `◇⊟ ∘ ◇⊟ = ⊕⊞`, certified semantically rather than by enum table
lookup. -/
example : EntailmentSig.SoundFor .addMult (pnot ∘ pnot) :=
  pnot_soundFor_antiAddMult.comp pnot_soundFor_antiAddMult

end PnotInstance

end Core.NaturalLogic
