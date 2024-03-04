import Mathlib.Init.Control.Lawful
import Mathlib.Order.SetNotation
import Std.Classes.LawfulMonad

/-!
## Notation and lemmas for `SatisfiesM`
-/

namespace SatisfiesM

scoped notation3 "∀ˢ "(...)" in "f", "r:(scoped p => SatisfiesM p f) => r

end SatisfiesM

variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable {α β : Type}

lemma SatisfiesM.unit_bind {p : α → Prop} {x : m Unit} {y : m α} (h : SatisfiesM p y) :
    SatisfiesM p (do x; y) := by
  apply SatisfiesM.bind_pre
  apply SatisfiesM.of_true
  intro _
  exact h

-- DO NOT SUBMIT: Hmm, not sure if this is even true.
-- On reflection I think it isn't true: `pure` doesn't need to be injective in a LawfulMonad.
/-
@[simp] lemma pure_iff {p : α → Prop} {x : α} : SatisfiesM (m := m) p (pure x) ↔ p x := by
  constructor
  · intro ⟨n, h⟩
    simp only [map_eq_pure_bind] at h
-/

lemma SatisfiesM.lazyPure {p : α → Prop} {f : Unit → α} (h : p (f ())) :
    SatisfiesM p (IO.lazyPure f) :=
  SatisfiesM.pure h

def allProps (x : m α) (y : α) : Prop := ∀ p : α → Prop, SatisfiesM p x → p y

lemma SatisfiesM.and {p q : α → Prop} {x : m α} (px : SatisfiesM p x) (qx : SatisfiesM q x) :
    SatisfiesM (fun y ↦ p y ∧ q y) x := by
  sorry
  --rcases px with ⟨y,py⟩
  --rcases qx with ⟨z,qz⟩

lemma SatisfiesM.allProps (x : m α) : SatisfiesM (allProps x) x := by
  sorry

def enrich {x : m α} : m {y : α // allProps x y} := by
  refine (fun y ↦ ⟨y, fun p h ↦ ?_⟩) <$> x
  sorry

def BaseIO.asTask' (x : BaseIO α) : BaseIO (Task (BaseIO α)) := do
  let s := { p : α → Prop | SatisfiesM p x }
  let t ← BaseIO.asTask x
  sorry
  --return t.map BaseIO.ofExcept

-- DO NOT SUBMIT: Move elsewhere
def IO.asTask' (x : IO α) : IO (Task (IO α)) := do
  let t ← IO.asTask x
  return t.map IO.ofExcept

-- DO NOT SUBMIT
/-
lemma _root_.BaseIO.askTask_def (x : BaseIO α) (prio : Task.Priority) :
    BaseIO.asTask x prio = Task.pure <$> x := by
  with_unfolding_all rfl

lemma _root_.IO.asTask_map' (f : α → β) (x : IO α) :
    IO.asTask' (f <$> x) = (IO.asTask' x >>= fun t ↦ return t.map (fun y ↦ f <$> y)) := by
  simp? [IO.asTask', IO.asTask, EIO.asTask]

end SatisfiesM

-- DO NOT SUBMIT: Move elsewhere
lemma asTask' {p : α → Prop} {x : IO α} (h : SatisfiesM p x) :
    ∀ˢ t in IO.asTask' x, ∀ˢ y in t.get, p y := by
  rcases h with ⟨q,e⟩
  simp? [←e, IO.asTask', IO.asTask, EIO.asTask]
  apply SatisfiesM.bind_pre
  simp?
  rw [BaseIO.asTask]
-/
