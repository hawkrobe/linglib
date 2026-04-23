import Mathlib.Data.Set.Basic

/-!
# Implicature: Cross-Mechanism Spine
@cite{grice-1975} @cite{horn-1972} @cite{gazdar-1979} @cite{sauerland-2004}
@cite{chierchia-fox-spector-2012} @cite{bar-lev-fox-2020}

Defines the central `Implicature W` type — the cross-mechanism representation
of a pragmatic inference. Every parallel mechanism in the library
(neo-Gricean Standard Recipe, EXH with Innocent Exclusion / Inclusion,
RSA recursion, IBR fixed point) can produce values of this type, enabling:

1. **Cross-mechanism agreement theorems** — e.g. that the Sauerland
   secondary procedure agrees with `exhIE` for non-FC cases (per
   @cite{chierchia-fox-spector-2012} §3) and characteristically diverges
   for free choice (per @cite{bar-lev-fox-2020}).
2. **Mechanism-independent diagnostics** — `Implicature/Diagnostics.lean`
   states Grice's tests (cancellability, reinforceability, calculability,
   non-detachability) over the `Implicature` type so they apply uniformly
   to neo-Gricean, EXH-derived, and RSA-derived inferences.
3. **Empirical comparison** — head-to-head experiments in the modern
   literature (cf. @cite{cremers-wilcox-spector-2023}) ask which
   mechanism best predicts observed inferences. The `mechanism` field
   tracks provenance so these comparisons can be formalized.

## Design choices

The structure carries four fields and deliberately omits a "trigger"
field. Lexical / structural triggers are study-file concerns; baking
them into the spine would couple `Implicature` to either `Word`,
`Tree`, or `Alternatives.AlternativeSource`, none of which is
appropriate at this level. Wrapping structures in study files can add
trigger metadata if needed.

The `Mechanism` enum lists the canonical derivations in the
contemporary literature; new mechanisms (graph-based, dynamic, etc.)
can be added without disrupting consumers, since pattern-matches
typically fall into a default branch.

## Naming

Following `Filter.Filter`-style mathlib precedent: the central struct
`Implicature` is declared at the root, while the supporting enums
(`Implicature.Kind`, `Implicature.Mechanism`) and helper definitions
live under `namespace Implicature`. The existing per-file sub-namespaces
(`Implicature.Markedness`, `Implicature.Scales`, …) coexist because
Lean permits a type and a namespace to share a name.
-/

/--
Taxonomic classification of pragmatic inferences.

The post-Grice consensus distinguishes:

- **scalar** — derived from a Horn scale; canonical *some* ⇝ *not all*
  (@cite{horn-1972}, @cite{sauerland-2004})
- **freeChoice** — distributive inference from disjunction under a
  modal: ◇(A ∨ B) ⇝ ◇A ∧ ◇B (@cite{kamp-1973}, @cite{zimmermann-2000},
  @cite{fox-2007})
- **ignorance** — speaker-uncertainty inference; "the primary
  implicature" of @cite{sauerland-2004}, going back to
  @cite{gazdar-1979} epistemic implicature
- **clausal** — ¬K(p) ∧ ¬K(q) from "p or q" (@cite{gazdar-1979})
- **manner** — marked-form-implicates-marked-meaning, the
  R-principle / M-principle (@cite{horn-1984}, @cite{levinson-2000}
  ch. 2)
- **conventional** — lexically encoded non-at-issue content; *but*,
  *therefore*, expressives (@cite{grice-1975}, @cite{potts-2005})
-/
inductive ImplicatureKind where
  | scalar
  | freeChoice
  | ignorance
  | clausal
  | manner
  | conventional
  deriving DecidableEq, Repr

/--
Is this kind a *conversational* implicature (as opposed to a conventional
one)?

Grice's primary distinction. Conversational implicatures are calculable
from the cooperative principle and pass the standard diagnostics
(cancellability, reinforceability, non-detachability); conventional
implicatures fail at least cancellability.
-/
def ImplicatureKind.isConversational : ImplicatureKind → Prop
  | .conventional => False
  | _ => True

instance : DecidablePred ImplicatureKind.isConversational
  | .conventional => isFalse not_false
  | .scalar | .freeChoice | .ignorance | .clausal | .manner =>
      isTrue trivial


/--
The derivation mechanism that produced an implicature.

Tracking provenance lets cross-mechanism agreement and disagreement
theorems be stated. The canonical mechanisms in the contemporary
literature:

- **neoGricean** — Standard Recipe; Quantity-driven competition over
  alternatives (@cite{geurts-2010}, @cite{sauerland-2004})
- **exhIE** — Innocent Exclusion (@cite{fox-2007})
- **exhII** — Innocent Inclusion (@cite{bar-lev-fox-2020})
- **exhIEII** — combined IE+II, the canonical post-2020 EXH
  (@cite{bar-lev-fox-2020})
- **rsa** — Bayesian listener-speaker recursion
  (@cite{frank-goodman-2012}, @cite{goodman-stuhlmuller-2013})
- **ibr** — Iterated Best Response game-theoretic fixed point
  (@cite{franke-2011})
- **lexical** — the inference is encoded in a lexical entry; no
  pragmatic derivation is required (e.g. conventional implicatures
  per @cite{potts-2005})
-/
inductive ImplicatureMechanism where
  | neoGricean
  | exhIE
  | exhII
  | exhIEII
  | rsa
  | ibr
  | lexical
  deriving DecidableEq, Repr

/--
A pragmatic inference, parameterized by a world type `W`.

Every value carries:
- `kind`      — taxonomic classification
- `content`   — the inferred proposition (`W → Prop`)
- `altsUsed`  — the alternative set that drove derivation (the
  Horn scale, the structural-alternative closure, the LU lexicon, ...)
- `mechanism` — provenance, recording which derivation produced it

Two `Implicature W` values agree iff they predict the same content;
see `Implicature.Agree` below. The cross-mechanism bridge files
(`Implicature/Exh.lean`, the α→∞ limit theorems in `RSA/Limits.lean`)
state agreement results in this form.
-/
structure Implicature (W : Type*) where
  /-- Taxonomic classification (scalar / freeChoice / ignorance / ...). -/
  kind : ImplicatureKind
  /-- The inferred proposition. -/
  content : W → Prop
  /-- The alternative set that drove derivation. -/
  altsUsed : Set (W → Prop)
  /-- The derivation mechanism that produced this inference. -/
  mechanism : ImplicatureMechanism

namespace Implicature

variable {W : Type*}

/-- Is this inference a conversational implicature? Lifts
`ImplicatureKind.isConversational` to `Implicature`. -/
def isConversational (i : Implicature W) : Prop :=
  i.kind.isConversational

instance (i : Implicature W) : Decidable i.isConversational :=
  inferInstanceAs (Decidable i.kind.isConversational)

/--
Two implicatures **agree** iff they predict the same content at every
world.

This is the load-bearing relation for cross-mechanism comparison: a
typical bridge theorem has the shape

```
theorem sauerland_agrees_with_exhIE (φ : W → Prop) (alts : Set (W → Prop))
    (h : nonFreeChoice alts) :
    Agree (Implicature.fromSauerland φ alts)
          (Implicature.fromExhIE φ alts)
```

For free choice, the analogous theorem characteristically *fails* —
that non-equivalence is itself a result (per
@cite{bar-lev-fox-2020}).
-/
def Agree (i j : Implicature W) : Prop :=
  ∀ w, i.content w ↔ j.content w

@[refl] theorem Agree.refl (i : Implicature W) : Agree i i :=
  fun _ => Iff.rfl

@[symm] theorem Agree.symm {i j : Implicature W} (h : Agree i j) : Agree j i :=
  fun w => (h w).symm

theorem Agree.trans {i j k : Implicature W}
    (hij : Agree i j) (hjk : Agree j k) : Agree i k :=
  fun w => (hij w).trans (hjk w)

end Implicature
