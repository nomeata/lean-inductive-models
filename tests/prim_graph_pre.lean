/- **Arm G on an input that brings its own prelude.** `prim_graph.lean` is the
   same arm on a file that declares only `Eq`, so everything the graph route
   needs is spliced there; this is the control that says an input's own
   constants beat a spliced one, and that they are **checked** rather than
   assumed.

   Four things the arm reaches for, and this file has all four:

   * `PSigma` — the value is paired with its graph proof, never chosen bare.
   * `Nonempty` — `Classical.choice`'s own domain, and the reason the arm names
     it at all. It is **not** a basis primitive: it is a non-recursive,
     small-eliminating `Prop`, so the Church route models it like anything
     else, and it has a model in this file's output beside its declaration.
   * `Classical.choice` — the one axiom the arm asserts. `Modelgen.ensureChoice`
     compares an input's own against Lean's statement with `isDefEq`.
   * `funext` — Lean's own development, from the quotient and `Quot.sound`,
     written out exactly as `funext_binder.lean` writes it. `Ac`'s recursive
     field has binders, so `Graph.unique`'s congruence transports along one.

   **Three of the four are reused and the fourth is not**, and the fourth is
   the export's doing rather than the tool's: `ensureFunext` is asked lazily,
   at the point the model is generated, and `lean4export` emits `Ac.rec` before
   this file's own `funext` — nothing in `Ac` mentions it, so nothing orders it
   earlier. So the report's one splice line for `Ac` reads
   `Ac._model.funext` and names nothing else. That a *declared* `funext`
   ahead of the model is used instead is `funext_binder.lean`'s claim, on the
   same [`Modelgen.ensureFunext`]; what this file measures is `PSigma`,
   `Nonempty` and `Classical.choice`, all three of which the replay does reach
   in time, and the `isDefEq` check `Modelgen.ensureChoice` puts the input's
   own axiom through. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

structure PSigma {α : Sort u} (β : α → Sort v) where
  fst : α
  snd : β fst

inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α

axiom Classical.choice {α : Sort u} : Nonempty α → α

init_quot

axiom Quot.sound : {α : Sort u} → {r : α → α → Prop} → {a b : α} → r a b →
  Eq (Quot.mk r a) (Quot.mk r b)

theorem congrArg {α : Sort u} {β : Sort v} {a b : α} (f : α → β) (h : Eq a b) :
    Eq (f a) (f b) :=
  Eq.rec (motive := fun x _ => Eq (f a) (f x)) (Eq.refl (f a)) h

theorem funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : (x : α) → Eq (f x) (g x)) : Eq f g :=
  congrArg
    (fun (q : Quot (fun (a b : (x : α) → β x) => (x : α) → Eq (a x) (b x))) (x : α) =>
      Quot.lift (fun (a : (x : α) → β x) => a x)
        (fun a b (hab : (x : α) → Eq (a x) (b x)) => hab x) q)
    (Quot.sound h)

inductive Ac {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Ac r y) : Ac r x
