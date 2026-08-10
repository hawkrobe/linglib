/-!
# Causative and implicative verb features

Per-verb-entry taxonomies for causal verb classification: the force-dynamic
`Causative` classification and the [karttunen-1971] `Implicative` polarity.

`Causative`'s five-way `cause`/`make`/`force`/`enable`/`prevent` split extends
the three-way force-dynamic taxonomy of [wolff-2003] (CAUSE / ENABLE / PREVENT)
by subdividing CAUSE into counterfactual dependence (`cause`), direct
sufficient guarantee (`make`), and coercive sufficiency (`force`) —
distinctions [talmy-1988] discusses without crystallizing as named primitives.
The `AssertsSufficiency`/`AssertsNecessity` classification follows
[nadathur-lauer-2020]'s sufficiency/necessity decomposition and is
characterized against the truth-conditional dispatch in
`Semantics/Causation/Interpretation.lean` (`Causative.toSemantics`). Rival
taxonomies carve causatives differently — [comrie-1989]'s
lexical/morphological/syntactic scale, [shibatani-pardeshi-2002]'s directness
continuum, [pylkkanen-2008]'s Cause-head theory — and are formalized in the
studies that consume them.

`Implicative` fixes [karttunen-1971]'s binary positive/negative bipartition;
the finer nine-way entailment matrix of [nairn-condoravdi-karttunen-2006] and
[karttunen-2012] is not encoded here. Implicatives differ structurally from
causatives ([nadathur-2023-implicatives]): causatives predicate causation
directly, while implicatives assert a prerequisite whose causal link to the
complement is presupposed. `Semantics/Causation/Implicative.lean` carries that
account.
-/

namespace Features

/-! ### Force-dynamic causatives -/

/-- Force-dynamic classification of causative verbs by the causal mechanism
the verb lexicalizes. `Causative.toSemantics` (in
`Semantics/Causation/Interpretation.lean`) maps each variant to its truth
conditions. -/
inductive Causative where
  /-- Counterfactual dependence: removing the cause blocks the effect (*cause*). -/
  | cause
  /-- Direct sufficient guarantee: adding the cause ensures the effect (*make*). -/
  | make
  /-- Coercive sufficiency: the causer overcomes the causee's resistance (*force*). -/
  | force
  /-- Permissive: the causer removes a barrier so the effect can occur (*let*). -/
  | enable
  /-- Blocking: the causer adds a barrier so the effect cannot occur (*prevent*). -/
  | prevent
  deriving DecidableEq, Repr

namespace Causative

/-- The variant asserts causal sufficiency ([nadathur-lauer-2020]): `make`,
`force`, and `enable` share sufficiency truth conditions
(`AssertsSufficiency.toSemantics_eq`). -/
def AssertsSufficiency : Causative → Prop
  | .make | .force | .enable => True
  | .cause | .prevent => False

instance : DecidablePred AssertsSufficiency := fun b => by
  cases b <;> unfold AssertsSufficiency <;> infer_instance

/-- The variant asserts causal necessity ([nadathur-lauer-2020]): only `cause`,
whose truth conditions are counterfactual dependence
(`AssertsNecessity.toSemantics_eq`). -/
def AssertsNecessity : Causative → Prop
  | .cause => True
  | _ => False

instance : DecidablePred AssertsNecessity := fun b => by
  cases b <;> unfold AssertsNecessity <;> infer_instance

/-- The variant encodes coercion: `force` lexicalizes overcoming the causee's
resistance, distinguishing it from `make` despite shared truth conditions. -/
def IsCoercive : Causative → Prop
  | .force => True
  | _ => False

instance : DecidablePred IsCoercive := fun b => by
  cases b <;> unfold IsCoercive <;> infer_instance

/-- The variant encodes permission: `enable` lexicalizes removing a barrier,
distinguishing it from `make` despite shared truth conditions. -/
def IsPermissive : Causative → Prop
  | .enable => True
  | _ => False

instance : DecidablePred IsPermissive := fun b => by
  cases b <;> unfold IsPermissive <;> infer_instance

end Causative

/-! ### Implicative polarity -/

/-- [karttunen-1971] polarity for implicative verbs: positive implicatives
entail their complement, negative implicatives entail its negation. -/
inductive Implicative where
  /-- The verb entails its complement (*manage*, *remember*). -/
  | positive
  /-- The verb entails the negation of its complement (*fail*, *forget*). -/
  | negative
  deriving DecidableEq, Repr

namespace Implicative

/-- The polarity entails the complement rather than its negation. -/
def EntailsComplement : Implicative → Prop
  | .positive => True
  | .negative => False

instance : DecidablePred EntailsComplement := fun i => by
  cases i <;> unfold EntailsComplement <;> infer_instance

end Implicative

end Features
