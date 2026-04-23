import Mathlib.Data.Set.Basic

/-!
# Implicature: Cross-Mechanism Spine
@cite{grice-1975} @cite{horn-1972} @cite{gazdar-1979} @cite{sauerland-2004}
@cite{chierchia-fox-spector-2012} @cite{bar-lev-fox-2020}
@cite{frank-goodman-2012} @cite{goodman-stuhlmuller-2013}

Defines the central `Implicature W S` type — the cross-mechanism
representation of a pragmatic inference, parameterized by a **world type
`W`** and a **strength type `S`**.

## Why polymorphic in `S`?

The ontology of "what an implicature is" is contested in the literature:

- The **discrete / grammaticalist tradition** (@cite{sauerland-2004},
  @cite{chierchia-2004}, @cite{fox-2007}, @cite{bar-lev-fox-2020})
  treats an implicature as a discrete proposition — instantiated by
  `S := Prop`.
- The **graded / Bayesian tradition** (@cite{frank-goodman-2012},
  @cite{goodman-stuhlmuller-2013}, @cite{bergen-levy-goodman-2016})
  treats interpretation as a posterior shift; "the implicature" is a
  change in degrees of belief, not a discrete proposition. Instantiated
  by `S := ℝ≥0` or similar graded type.
- **Trivalent** accounts (presupposition-bearing, partial) instantiate
  with `S := Truth3`.

Parameterizing rather than committing lets each mechanism use its
native output type. The categorical Gricean diagnostics
(`Diagnostics.lean`) are then specialized to `S = Prop` — they're an
artifact of the discrete ontology and don't generalize to ℝ-valued
contents. Cross-mechanism comparison between, say, RSA and Sauerland
requires explicit projection (thresholding a posterior), which is itself
a contestable empirical claim that should be formalized as such, not
hidden in a coercion.

## Default `S := Prop`

Most consumers want categorical implicatures. The default keeps
existing call sites unchanged: `Implicature W` means `Implicature W Prop`.

## Bridge architecture

Cross-mechanism agreement theorems (in sibling files) state results in
terms of `Agree`, the pointwise content-equality relation. For
`S = Prop`, this collapses to the iff version under propositional
extensionality.

## Naming

Following `Filter.Filter`-style mathlib precedent: the central struct
`Implicature` is declared at the root, while supporting enums
(`ImplicatureKind`, `ImplicatureMechanism`) and helper definitions live
under `namespace Implicature`. The existing per-file sub-namespaces
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
theorems be stated. Different mechanisms naturally produce different
strength types (the `S` parameter of `Implicature`):

- **neoGricean** / **exhIE** / **exhII** / **exhIEII** — discrete
  outputs (`S := Prop`)
- **rsa** — graded posterior (`S := ℝ≥0` or similar)
- **ibr** — discrete fixed-point output (`S := Prop`)
- **lexical** — discrete; encoded in the lexical entry (`S := Prop`)

The mechanism field tracks provenance regardless of strength type.

Citations:
- **neoGricean** — Standard Recipe (@cite{geurts-2010},
  @cite{sauerland-2004})
- **exhIE** — Innocent Exclusion (@cite{fox-2007})
- **exhII** — Innocent Inclusion (@cite{bar-lev-fox-2020})
- **exhIEII** — combined IE+II, the canonical post-2020 EXH
  (@cite{bar-lev-fox-2020})
- **rsa** — Bayesian listener-speaker recursion
  (@cite{frank-goodman-2012}, @cite{goodman-stuhlmuller-2013})
- **ibr** — Iterated Best Response (@cite{franke-2011})
- **lexical** — encoded in lexical entries (@cite{potts-2005})
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
A pragmatic inference, parameterized by:
- **`W`** — the world type
- **`S`** — the strength type (default `Prop` for the discrete /
  Gricean / grammaticalist ontology; instantiate with `ℝ≥0` for
  graded / RSA-style; with `Truth3` for trivalent)

Every value carries:
- `kind`      — taxonomic classification
- `content`   — the inferred per-world strength (`W → S`)
- `altsUsed`  — the alternative set that drove derivation
- `mechanism` — provenance, recording which derivation produced it

The `S` parameter encodes a real theoretical commitment: see the file
docstring. For `S = Prop`, `content` is a discrete proposition and the
Gricean diagnostics in `Diagnostics.lean` apply directly. For
`S = ℝ≥0` (RSA), the diagnostics require an interpretive projection.
-/
structure Implicature (W : Type*) (S : Type := Prop) where
  /-- Taxonomic classification (scalar / freeChoice / ignorance / ...). -/
  kind : ImplicatureKind
  /-- The inferred per-world strength. For `S = Prop`, a discrete
  proposition; for graded `S` (e.g. `ℝ≥0`), a probability or score. -/
  content : W → S
  /-- The alternative set that drove derivation. -/
  altsUsed : Set (W → S)
  /-- The derivation mechanism that produced this inference. -/
  mechanism : ImplicatureMechanism

namespace Implicature

variable {W : Type*} {S : Type}

/-- Is this inference a conversational implicature? Lifts
`ImplicatureKind.isConversational` to `Implicature`. Polymorphic in
the strength type: classification doesn't depend on content. -/
def isConversational (i : Implicature W S) : Prop :=
  i.kind.isConversational

instance (i : Implicature W S) : Decidable i.isConversational :=
  inferInstanceAs (Decidable i.kind.isConversational)

/--
Two implicatures **agree** iff they assign the same strength to every
world.

For the default `S = Prop`, this is `∀ w, i.content w = j.content w`,
which collapses to the iff version under propositional extensionality.
For `S = ℝ`, it's literal numeric equality of the per-world scores.

Bridge theorems state cross-mechanism agreement in this form. Two
implicatures with different `mechanism` fields can `Agree` (the
canonical Sauerland ≡ exhIE result for non-FC cases per
@cite{chierchia-fox-spector-2012} §3) or characteristically *fail* to
agree (the FC non-equivalence per @cite{bar-lev-fox-2020}).
-/
def Agree (i j : Implicature W S) : Prop :=
  ∀ w, i.content w = j.content w

@[refl] theorem Agree.refl (i : Implicature W S) : Agree i i :=
  fun _ => rfl

@[symm] theorem Agree.symm {i j : Implicature W S}
    (h : Agree i j) : Agree j i :=
  fun w => (h w).symm

theorem Agree.trans {i j k : Implicature W S}
    (hij : Agree i j) (hjk : Agree j k) : Agree i k :=
  fun w => (hij w).trans (hjk w)

end Implicature
