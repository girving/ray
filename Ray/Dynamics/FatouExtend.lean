module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Bound

/-!
## Extending Fatou coordinates and parametrisations by the dynamics

Two generic extensions, used for parabolic Fatou coordinates:

1. `basinExt`: if `g` maps an open `P` into itself and `Φ (g z) = Φ z + 1` on `P`, then `Φ z = Φ (g^[n] z) - n`
   extends `Φ` to the basin `{z | ∃ n, g^[n] z ∈ P}`, analytically if `g` and `Φ` are.
2. `paramExt`: if `V` is open, closed under `ζ ↦ ζ - 1`, reaches every point (`∀ ζ, ∃ n, ζ - n ∈ V`), and
   `g (Ψ (ζ - 1)) = Ψ ζ` on `V`, then `Ψ ζ = g^[n] (Ψ (ζ - n))` extends `Ψ` to an entire function with
   `g (Ψ ζ) = Ψ (ζ + 1)`, for entire `g`.

Neither depends on how `Φ` or `Ψ` were built.
-/

open Classical
open Filter
open Set
open scoped Topology

variable {g Φ Ψ : ℂ → ℂ} {P V : Set ℂ}

/-- Iterates of an entire function are entire -/
lemma iterate_analyticAt (ga : ∀ z, AnalyticAt ℂ g z) (n : ℕ) (z : ℂ) : AnalyticAt ℂ g^[n] z := by
  induction n generalizing z with
  | zero => exact analyticAt_id
  | succ n ih => rw [Function.iterate_succ]; exact (ih (g z)).comp (ga z)

/-!
### The basin extension
-/

/-- The points whose orbit enters `P` -/
@[expose] public def basin (g : ℂ → ℂ) (P : Set ℂ) : Set ℂ := {z | ∃ n, g^[n] z ∈ P}

/-- `Φ` extended along orbits: `Φ (g^[n] z) - n` for the first `n` with `g^[n] z ∈ P` -/
@[expose] public noncomputable def basinExt (g Φ : ℂ → ℂ) (P : Set ℂ) (z : ℂ) : ℂ :=
  if h : ∃ n, g^[n] z ∈ P then Φ (g^[Nat.find h] z) - Nat.find h else 0

public lemma subset_basin : P ⊆ basin g P := fun _ m ↦ ⟨0, m⟩

public lemma isOpen_basin (gc : Continuous g) (Po : IsOpen P) : IsOpen (basin g P) := by
  have : basin g P = ⋃ n, g^[n] ⁻¹' P := by ext z; simp [basin]
  rw [this]
  exact isOpen_iUnion fun n ↦ Po.preimage (gc.iterate n)

public lemma mapsTo_basin (gP : MapsTo g P P) : MapsTo g (basin g P) (basin g P) := by
  rintro z ⟨n, m⟩
  exact ⟨n, by rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']; exact gP m⟩

lemma iter_eqn (gP : MapsTo g P P) (e : ∀ z ∈ P, Φ (g z) = Φ z + 1) {z : ℂ} (m : z ∈ P) (n : ℕ) :
    Φ (g^[n] z) = Φ z + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', e _ ((gP.iterate n) m), ih]; push_cast; ring

/-- Any entry time gives the same value -/
public lemma basinExt_eq_of (gP : MapsTo g P P) (e : ∀ z ∈ P, Φ (g z) = Φ z + 1) {z : ℂ} {n : ℕ}
    (m : g^[n] z ∈ P) : basinExt g Φ P z = Φ (g^[n] z) - n := by
  have h : ∃ n, g^[n] z ∈ P := ⟨n, m⟩
  simp only [basinExt, h, ↓reduceDIte]
  have le : Nat.find h ≤ n := Nat.find_min' h m
  have hn : g^[n] z = g^[n - Nat.find h] (g^[Nat.find h] z) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel le]
  rw [hn, iter_eqn gP e (Nat.find_spec h), Nat.cast_sub le]
  ring

public lemma basinExt_eq (gP : MapsTo g P P) (e : ∀ z ∈ P, Φ (g z) = Φ z + 1) {z : ℂ} (m : z ∈ P) :
    basinExt g Φ P z = Φ z := by
  simpa using basinExt_eq_of (n := 0) gP e m

/-- The extension still satisfies Abel's equation -/
public lemma basinExt_eqn (gP : MapsTo g P P) (e : ∀ z ∈ P, Φ (g z) = Φ z + 1) {z : ℂ}
    (m : z ∈ basin g P) : basinExt g Φ P (g z) = basinExt g Φ P z + 1 := by
  obtain ⟨n, m⟩ := m
  have m' : g^[n] (g z) ∈ P := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']; exact gP m
  rw [basinExt_eq_of gP e m', basinExt_eq_of gP e m, ← Function.iterate_succ_apply,
    Function.iterate_succ_apply', e _ m]
  ring

/-- The extension is analytic on the basin -/
public lemma basinExt_analytic (ga : ∀ z, AnalyticAt ℂ g z) (Po : IsOpen P) (gP : MapsTo g P P)
    (e : ∀ z ∈ P, Φ (g z) = Φ z + 1) (Φa : AnalyticOnNhd ℂ Φ P) :
    AnalyticOnNhd ℂ (basinExt g Φ P) (basin g P) := by
  rintro z ⟨n, m⟩
  have c : ContinuousAt g^[n] z := (iterate_analyticAt ga n z).continuousAt
  have ev : ∀ᶠ y in 𝓝 z, g^[n] y ∈ P := c.preimage_mem_nhds (Po.mem_nhds m)
  refine (((Φa _ m).comp (iterate_analyticAt ga n z)).sub (analyticAt_const (v := (n : ℂ)))).congr ?_
  filter_upwards [ev] with y my
  exact (basinExt_eq_of gP e my).symm

/-!
### The entire extension of a parametrisation
-/

/-- `Ψ` extended by `g^[n] (Ψ (ζ - n))` for the first `n` with `ζ - n ∈ V` -/
@[expose] public noncomputable def paramExt (g Ψ : ℂ → ℂ) (V : Set ℂ) (ζ : ℂ) : ℂ :=
  if h : ∃ n : ℕ, ζ - n ∈ V then g^[Nat.find h] (Ψ (ζ - Nat.find h)) else 0

/-- Any `n` with `ζ - n ∈ V` gives the same value -/
public lemma paramExt_eq_of (Vl : ∀ ζ ∈ V, ζ - 1 ∈ V) (e : ∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) {ζ : ℂ} {n : ℕ}
    (m : ζ - n ∈ V) : paramExt g Ψ V ζ = g^[n] (Ψ (ζ - n)) := by
  have h : ∃ n : ℕ, ζ - n ∈ V := ⟨n, m⟩
  simp only [paramExt, h, ↓reduceDIte]
  set N := Nat.find h
  have le : N ≤ n := Nat.find_min' h m
  -- `g^[N + j] (Ψ (ζ - (N + j)))` is constant in `j`, and `ζ - (N + j) ∈ V`
  have step : ∀ j : ℕ, ζ - ((N + j : ℕ) : ℂ) ∈ V ∧
      g^[N + j] (Ψ (ζ - ((N + j : ℕ) : ℂ))) = g^[N] (Ψ (ζ - N)) := by
    intro j
    induction j with
    | zero => exact ⟨by simpa using Nat.find_spec h, rfl⟩
    | succ j ih =>
      have m1 : ζ - ((N + (j + 1) : ℕ) : ℂ) = ζ - ((N + j : ℕ) : ℂ) - 1 := by push_cast; ring
      refine ⟨by rw [m1]; exact Vl _ ih.1, ?_⟩
      rw [← ih.2, m1, show N + (j + 1) = (N + j) + 1 by ring, Function.iterate_succ_apply, e _ ih.1]
  have := (step (n - N)).2
  rw [Nat.add_sub_cancel' le] at this
  exact this.symm

public lemma paramExt_eq (Vl : ∀ ζ ∈ V, ζ - 1 ∈ V) (e : ∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) {ζ : ℂ}
    (m : ζ ∈ V) : paramExt g Ψ V ζ = Ψ ζ := by
  simpa using paramExt_eq_of (n := 0) Vl e (by simpa using m)

/-- The extension semiconjugates translation to `g`: `g (Ψ ζ) = Ψ (ζ + 1)` -/
public lemma paramExt_eqn (Vl : ∀ ζ ∈ V, ζ - 1 ∈ V) (e : ∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ)
    (reach : ∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) (ζ : ℂ) : paramExt g Ψ V (ζ + 1) = g (paramExt g Ψ V ζ) := by
  obtain ⟨n, m⟩ := reach ζ
  have m' : ζ + 1 - ((n + 1 : ℕ) : ℂ) ∈ V := by push_cast; rwa [add_sub_add_right_eq_sub]
  rw [paramExt_eq_of Vl e m', paramExt_eq_of Vl e m, Function.iterate_succ_apply']
  congr 2; push_cast; ring_nf

/-- The extension is entire -/
public lemma paramExt_analytic (ga : ∀ z, AnalyticAt ℂ g z) (Vo : IsOpen V) (Vl : ∀ ζ ∈ V, ζ - 1 ∈ V)
    (e : ∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) (reach : ∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) (Ψa : AnalyticOnNhd ℂ Ψ V)
    (ζ : ℂ) : AnalyticAt ℂ (paramExt g Ψ V) ζ := by
  obtain ⟨n, m⟩ := reach ζ
  have sa : AnalyticAt ℂ (fun ξ : ℂ ↦ ξ - n) ζ := analyticAt_id.sub analyticAt_const
  have ev : ∀ᶠ ξ : ℂ in 𝓝 ζ, ξ - (n : ℂ) ∈ V := sa.continuousAt.preimage_mem_nhds (Vo.mem_nhds m)
  refine ((iterate_analyticAt ga n _).comp ((Ψa _ m).comp (f := fun ξ : ℂ ↦ ξ - n) sa)).congr ?_
  filter_upwards [ev] with ξ mξ
  exact (paramExt_eq_of Vl e mξ).symm
