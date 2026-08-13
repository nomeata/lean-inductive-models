/- The W core, as a module, so that `lean4export` can emit it and `lean-inductive-models`
can splice it. `--#export` lists the six roots and the exporter takes their
transitive closure — which is what makes this a fragment of ~250 declarations
rather than the whole of `Init`.

**One construction, two instantiations.** The core below is generic in `K`,
`B' : K → Type u` and `tg : A → K`. The tagged and untagged W are that one
core at `K := Nat, tg := PSigma'.fst`
and at `K := A, tg := id`. `K : Type w` and not `K : Type` for exactly that
reason, and widening it cost no proof change at all: `Edge`, `PTree` and `W`
land at `Type (max w u)`, which normalises to `Type u` at `w := 0` and at
`w := u` alike.

**The last two roots are not part of the construction**; they are the
`DecidableEq K` each instantiation needs, and **the closure of the other four
cannot reach either**, because all four take the instance as a *parameter*.

* `instDecidableEqNat` is the tagged one's. `K := Nat` is the tag type because
  `Nat` is already shared with the input by the
  splice, so it costs no new fragment inductive. Without this root a generator
  would have to mint an enumeration inductive per declaration and prove its
  decidable equality, which `Iso.requires` would then oblige the run to model.
* `WT.decEqAll` is the untagged one's, and it is `Classical.propDecidable`. It
  takes the export from 163 records to 208 — **45 more**, of which exactly one
  is an inductive (`Nonempty`) and one an axiom (`Classical.choice`). Those two
  are why `Test.lean`'s `w_core` row asserts that `Nonempty` models, and why
  `Modelgen.wCoreShared` gained both names beside `propext` and `Iff`.

Both are exported, and which a target takes is `Modelgen.tagFactored`'s answer:
the tagged column stays at `[propext, Quot.sound]` and only a declaration that
*needs* the untagged instantiation pays `Classical.choice`. -/

--#export WT.W WT.sup WT.Wrec WT.Wrec_iota instDecidableEqNat WT.decEqAll

universe u v w

namespace WT

-- Half the lemmas below need `DecidableEq K` and half do not, and they are
-- interleaved by what they depend on rather than by that. Splitting the
-- section in two to satisfy the linter would order the file by an instance
-- rather than by the construction.
set_option linter.unusedSectionVars false

/-! `K` is the constructor tag — `Fin k` in the generator, and the only type
whose equality this construction decides. `A` is the full label, tag plus that
constructor's non-recursive fields. `B'` is the branch type **per tag**, which
is item E's precondition made into a signature: there is nowhere to put a
dependence on the label's data.

Every binder below is written out rather than taken from a `section variable`.
`W` has to take `B'` **explicitly** — `W tg` does not determine it, since `tg`
mentions only `A` and `K` — and once one definition needs it explicit, mixing
the two through section variables is more confusing than the repetition. -/

/-- One step of a path: which constructor-tag, and which of its branches. -/
abbrev Edge (K : Type w) (B' : K → Type u) : Type (max w u) := Σ t : K, B' t

/-- A raw tree: a partial labelling of paths. The label at a path is the
**whole** `A`, so nothing about the constructor's data is lost by recording
only the tag on the path itself. -/
abbrev PTree (K : Type w) (B' : K → Type u) (A : Type u) : Type (max w u) :=
  List (Edge K B') → Option A

variable {K : Type w} {A : Type u} {B' : K → Type u}

def subt (t : PTree K B' A) (x : Edge K B') : PTree K B' A := fun p => t (x :: p)

def nowhere : PTree K B' A := fun _ => none

/-- One step of unfolding whose least fixpoint is "is a well-founded tree". The
third clause — subtrees hanging off a *tag* other than the node's own are
empty — is what makes `canon` provable. It quantifies over tags rather than
labels. -/
def Step (tg : A → K) (S : PTree K B' A → Prop) (t : PTree K B' A) : Prop :=
  ∃ a : A, t [] = some a ∧ (∀ b : B' (tg a), S (subt t ⟨tg a, b⟩)) ∧
    ∀ x : Edge K B', x.1 ≠ tg a → subt t x = nowhere

theorem Step.mono {tg : A → K} {S S' : PTree K B' A → Prop} (hss : ∀ u, S u → S' u)
    {t : PTree K B' A} (h : Step tg S t) : Step tg S' t := by
  obtain ⟨a, h1, h2, h3⟩ := h
  exact ⟨a, h1, fun b => hss _ (h2 b), h3⟩

/-- Knaster–Tarski least fixpoint, impredicatively. -/
def Good (tg : A → K) (t : PTree K B' A) : Prop :=
  ∀ S : PTree K B' A → Prop, (∀ u, Step tg S u → S u) → S t

theorem Good.pre {tg : A → K} {t : PTree K B' A} (h : Step tg (Good tg) t) : Good tg t :=
  fun S hS => hS t (Step.mono (fun _u hu => hu S hS) h)

theorem Good.post {tg : A → K} {t : PTree K B' A} (h : Good tg t) : Step tg (Good tg) t :=
  h (Step tg (Good tg)) (fun _u hu => Step.mono (fun _v hv => Good.pre hv) hu)

/-- The carrier. `B'` is explicit because nothing else determines it. -/
def W (B' : K → Type u) (tg : A → K) : Type (max w u) := {t : PTree K B' A // Good tg t}

/-- The raw tree of a node labelled `a` with children `f`.

The guard is `x.1 = tg a` at the tag type, so `DecidableEq K` discharges it;
guarding at the full label type would instead require a decision procedure
there. Everything downstream costs what it costs because of this one line. -/
def mk [DecidableEq K] (tg : A → K) (a : A) (f : B' (tg a) → PTree K B' A) :
    PTree K B' A
  | [] => some a
  | x :: p => if h : x.1 = tg a then f (h ▸ x.2) p else none

variable [DecidableEq K] {tg : A → K}

theorem mk_nil (a : A) (f : B' (tg a) → PTree K B' A) : mk tg a f [] = some a := rfl

theorem mk_sub (a : A) (f : B' (tg a) → PTree K B' A) (b : B' (tg a)) :
    subt (mk tg a f) ⟨tg a, b⟩ = f b := by
  funext p; simp [subt, mk]

theorem mk_ne (a : A) (f : B' (tg a) → PTree K B' A) (x : Edge K B') (h : x.1 ≠ tg a) :
    subt (mk tg a f) x = nowhere := by
  funext p; simp [subt, mk, nowhere, h]

def sup (a : A) (f : B' (tg a) → W B' tg) : W B' tg :=
  ⟨mk tg a (fun b => (f b).1),
   Good.pre ⟨a, rfl, fun b => by rw [mk_sub]; exact (f b).2, fun x hx => mk_ne _ _ x hx⟩⟩

theorem isSome_root (w : W B' tg) : (w.1 []).isSome := by
  obtain ⟨a, ha, _, _⟩ := w.2.post
  rw [ha]; rfl

def root (w : W B' tg) : A := (w.1 []).get (isSome_root w)

theorem root_spec (w : W B' tg) : w.1 [] = some (root w) := (Option.some_get _).symm

theorem root_eq {w : W B' tg} {a : A} (h : w.1 [] = some a) : root w = a := by
  rw [root_spec] at h; exact Option.some.inj h

theorem good_sub (w : W B' tg) (b : B' (tg (root w))) :
    Good tg (subt w.1 ⟨tg (root w), b⟩) := by
  obtain ⟨a, ha, hk, _⟩ := w.2.post
  have hra : root w = a := root_eq ha
  subst hra; exact hk b

def kids (w : W B' tg) (b : B' (tg (root w))) : W B' tg :=
  ⟨subt w.1 ⟨tg (root w), b⟩, good_sub w b⟩

theorem canon (w : W B' tg) : w = sup (root w) (kids w) := by
  apply Subtype.ext
  obtain ⟨a, ha, _, hm⟩ := w.2.post
  have hra : root w = a := root_eq ha
  subst hra
  funext p
  match p with
  | [] => exact ha
  | ⟨x1, x2⟩ :: p =>
    by_cases h : x1 = tg (root w)
    · subst h
      show w.1 (⟨tg (root w), x2⟩ :: p)
          = subt (mk tg (root w) (fun b => (kids w b).1)) ⟨tg (root w), x2⟩ p
      rw [mk_sub]
      rfl
    · have := congrFun (hm ⟨x1, x2⟩ h) p
      show w.1 (⟨x1, x2⟩ :: p) = mk tg (root w) (fun b => (kids w b).1) (⟨x1, x2⟩ :: p)
      rw [show w.1 (⟨x1, x2⟩ :: p) = subt w.1 ⟨x1, x2⟩ p from rfl, this]
      simp [mk, nowhere, h]

theorem root_sup (a : A) (f : B' (tg a) → W B' tg) : root (sup a f) = a := root_eq rfl

theorem kids_eq' (w : W B' tg) (f : B' (tg (root w)) → W B' tg) (hw : w = sup (root w) f)
    (b : B' (tg (root w))) : kids w b = f b := by
  apply Subtype.ext
  have h1 : w.val = (sup (root w) f).val := congrArg Subtype.val hw
  show subt w.1 ⟨tg (root w), b⟩ = (f b).1
  rw [h1]
  exact mk_sub (root w) (fun b => (f b).val) b

/-- Induction (small motive) is immediate from the fixpoint. -/
theorem Wind {P : W B' tg → Prop}
    (h : ∀ (a : A) (f : B' (tg a) → W B' tg), (∀ b, P (f b)) → P (sup a f)) : ∀ w, P w := by
  have key : ∀ t : PTree K B' A, Good tg t → ∀ ht : Good tg t, P ⟨t, ht⟩ := by
    intro t hg
    refine hg (fun t => ∀ ht : Good tg t, P ⟨t, ht⟩) ?_
    intro u hu ht
    obtain ⟨a, ha, hk, _hm⟩ := hu
    have hra : root (⟨u, ht⟩ : W B' tg) = a := root_eq ha
    have hP : ∀ b : B' (tg (root (⟨u, ht⟩ : W B' tg))), P (kids ⟨u, ht⟩ b) := by
      intro b
      have : kids (⟨u, ht⟩ : W B' tg) b
          = ⟨subt u ⟨tg (root ⟨u, ht⟩), b⟩, good_sub _ b⟩ := rfl
      rw [this]
      subst hra
      exact hk b _
    exact (canon (⟨u, ht⟩ : W B' tg)).symm ▸ h _ _ hP
  intro w
  exact key w.1 w.2 w.2

/-- The immediate-subtree relation. -/
def Sub (w' w : W B' tg) : Prop := ∃ b : B' (tg (root w)), w' = kids w b

theorem kids_cast (w : W B' tg) (a : A) (f : B' (tg a) → W B' tg) (hw : w = sup a f)
    (hra : root w = a) (b : B' (tg (root w))) :
    kids w b = f (cast (congrArg (fun z => B' (tg z)) hra) b) := by
  subst hra
  exact kids_eq' w f hw b

theorem kids_sup (a : A) (f : B' (tg a) → W B' tg) (b : B' (tg (root (sup a f)))) :
    kids (sup a f) b = f (cast (congrArg (fun z => B' (tg z)) (root_sup a f)) b) :=
  kids_cast (sup a f) a f rfl (root_sup a f) b

theorem sub_wf : ∀ w : W B' tg, Acc (Sub (B' := B') (tg := tg)) w := by
  refine Wind ?_
  intro a f ih
  refine Acc.intro _ ?_
  rintro w' ⟨b, rfl⟩
  rw [kids_sup]
  exact ih _

theorem cast_symm_cancel {α β : Sort v} (h1 : β = α) (h2 : α = β) (x : β) :
    cast h2 (cast h1 x) = x := by
  cases h2; rfl

section Rec
variable {C : W B' tg → Sort v}
  (F : (a : A) → (f : B' (tg a) → W B' tg) → ((b : B' (tg a)) → C (f b)) → C (sup a f))

/-- The large recursor, by well-founded recursion on `Sub`. -/
def Wrec : (w : W B' tg) → C w :=
  WellFounded.fix ⟨sub_wf⟩ fun w ih =>
    cast (congrArg C (canon w).symm) (F (root w) (kids w) fun b => ih (kids w b) ⟨b, rfl⟩)

theorem Wrec_unfold (w : W B' tg) :
    Wrec F w = cast (congrArg C (canon w).symm)
      (F (root w) (kids w) fun b => Wrec F (kids w b)) :=
  WellFounded.fix_eq _ _ _

theorem Wrec_key (w : W B' tg) (a : A) (f : B' (tg a) → W B' tg) (h : w = sup a f) :
    cast (congrArg C h) (Wrec F w) = F a f (fun b => Wrec F (f b)) := by
  have hra : root w = a := by rw [h]; exact root_sup a f
  subst hra
  have hf : kids w = f := by
    funext b; exact kids_eq' w f h b
  subst hf
  rw [Wrec_unfold]
  exact cast_symm_cancel _ _ _

theorem Wrec_iota (a : A) (f : B' (tg a) → W B' tg) :
    Wrec F (sup a f) = F a f (fun b => Wrec F (f b)) :=
  Wrec_key F (sup a f) a f rfl

end Rec

/-- **`DecidableEq` at any type at all**, and the untagged arm's entire price.
`K := A` with `tg := id` needs the guard `x.1 = a` decided at the *label*, and
nothing decides it — so it is `Classical.propDecidable`, and every constant
downstream of it carries `Classical.choice`. The tagged arm passes
`instDecidableEqNat` instead and stays at `[propext, Quot.sound]`; the two
columns are the whole reason both roots are exported. -/
noncomputable def decEqAll (α : Sort u) : DecidableEq α :=
  fun a b => Classical.propDecidable (a = b)

end WT
