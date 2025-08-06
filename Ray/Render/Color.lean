import Interval.Floating.Floor
import Interval.Interval.Basic
import Interval.Interval.Conversion
import Interval.Interval.Mul
import Interval.Interval.Scale

/-!
## Approximate colors

We define the infinite precision `Color` type, and a finite precision `Color32` type
with an `Approx Color32 Color` instance.
-/

open Set

/-- RGBA colors -/
structure Color (α : Type) where
  r : α
  g : α
  b : α
  a : α
  deriving DecidableEq

variable {α β : Type}

lemma Color.ext_iff (x y : Color α) : x = y ↔ x.r = y.r ∧ x.g = y.g ∧ x.b = y.b ∧ x.a = y.a := by
  induction x; induction y; simp only [mk.injEq]

-- Componentwise operations
instance [Zero α] : Zero (Color α) where zero := ⟨0, 0, 0, 0⟩
instance [Neg α] : Neg (Color α) where neg x := ⟨-x.r, -x.g, -x.b, -x.a⟩
instance [Add α] : Add (Color α) where add x y := ⟨x.r + y.r, x.g + y.g, x.b + y.b, x.a + y.a⟩
instance [Sub α] : Sub (Color α) where sub x y := ⟨x.r - y.r, x.g - y.g, x.b - y.b, x.a - y.a⟩
instance [SMul α β] : SMul α (Color β) where smul s c := ⟨s • c.r, s • c.g, s • c.b, s • c.a⟩

-- Definition lemmas (unfortunate duplication here)
lemma Color.zero_def [Zero α] : (0 : Color α) = ⟨0, 0, 0, 0⟩ := rfl
lemma Color.neg_def [Neg α] (x : Color α) : -x = ⟨-x.r, -x.g, -x.b, -x.a⟩ := rfl
lemma Color.add_def [Add α] (x y : Color α) :
    x + y = ⟨x.r + y.r, x.g + y.g, x.b + y.b, x.a + y.a⟩ := rfl
lemma Color.sub_def [Sub α] (x y : Color α) :
    x - y = ⟨x.r - y.r, x.g - y.g, x.b - y.b, x.a - y.a⟩ := rfl
lemma Color.smul_def [SMul α β] (s : α) (x : Color β) : s • x = ⟨s•x.r, s•x.g, s•x.b, s•x.a⟩ := rfl

/-- Colors form an additive monoid -/
instance [AddMonoid α] : AddMonoid (Color α) where
  add_assoc _ _ _ := by simp only [Color.add_def, add_assoc]
  zero_add _ := by simp only [Color.add_def, Color.zero_def, zero_add]
  add_zero _ := by simp only [Color.add_def, Color.zero_def, add_zero]
  nsmul n x := ⟨n • x.r, n • x.g, n • x.b, n • x.a⟩
  nsmul_zero := by intro x; simp only [zero_smul, Color.zero_def]
  nsmul_succ := by intro n x; simp only [succ_nsmul, Color.add_def]

/-- Colors form a `SubNegMonoid` -/
instance [SubNegMonoid α] : SubNegMonoid (Color α) where
  sub_eq_add_neg _ _ := by
    simp only [Color.add_def, Color.neg_def, Color.sub_def, sub_eq_add_neg]
  zsmul n x := ⟨n • x.r, n • x.g, n • x.b, n • x.a⟩
  zsmul_zero' := by intro x; simp only [zero_zsmul, Color.zero_def]
  zsmul_succ' := by
    intro n x
    simp only [Color.add_def, Color.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply SubNegMonoid.zsmul_succ'
  zsmul_neg' := by
    intro n x
    simp only [Color.neg_def, Color.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply SubNegMonoid.zsmul_neg'

/-- Colors form an additive group -/
instance [AddGroup α] : AddGroup (Color α) where
  neg_add_cancel _ := by
    simp only [Color.add_def, Color.neg_def, neg_add_cancel, Color.zero_def]

/-- Conversion from `Color ℚ → Color ℝ`.
    We should make this general, but `ℚ → ℝ` is all we need for now. -/
@[coe] def Color.coe (c : Color ℚ) : Color ℝ :=
  ⟨c.r, c.g, c.b, c.a⟩

/-- Conversion from `Color ℚ → Color ℝ`.
    We should make this general, but `ℚ → ℝ` is all we need for now. -/
instance : Coe (Color ℚ) (Color ℝ) where
  coe c := Color.coe c

/-- `c[i]` for `i < 4` -/
instance : GetElem (Color α) (Fin 4) α (fun _ _ ↦ True) where
  getElem c i _ := match i with
  | 0 => c.r
  | 1 => c.g
  | 2 => c.b
  | 3 => c.a

-- `c[i]` simplification lemmas
@[simp] lemma Color.get_0 (c : Color UInt8) : c[(0 : Fin 4)] = c.r := rfl
@[simp] lemma Color.get_1 (c : Color UInt8) : c[(1 : Fin 4)] = c.g := rfl
@[simp] lemma Color.get_2 (c : Color UInt8) : c[(2 : Fin 4)] = c.b := rfl
@[simp] lemma Color.get_3 (c : Color UInt8) : c[(3 : Fin 4)] = c.a := rfl
open Fin.NatCast in @[simp] lemma Color.get_0' (c : Color UInt8) : c[((0 : ℕ) : Fin 4)] = c.r := rfl
open Fin.NatCast in @[simp] lemma Color.get_1' (c : Color UInt8) : c[((1 : ℕ) : Fin 4)] = c.g := rfl
open Fin.NatCast in @[simp] lemma Color.get_2' (c : Color UInt8) : c[((2 : ℕ) : Fin 4)] = c.b := rfl
open Fin.NatCast in @[simp] lemma Color.get_3' (c : Color UInt8) : c[((3 : ℕ) : Fin 4)] = c.a := rfl

/-!
### Quantized colors

We divide the interval `Icc 0 1` into 256 regions, map our 256 quantized `UInt8` values to the
centers of these regions, and place an approximation interval around each one.  We allow some
overlap to make the task easier.
-/

/-- Approximation interval radius.  With this error, quantized colors that aren't `nan`
    differ from the optimal `UInt8` value by at most `1`. -/
@[irreducible] def color_error : ℚ := 3 / 256

/-- Halved approximation radius -/
@[irreducible] def half_color_error : Interval := .ofRat (color_error / 2)

/-- We define `nan` as red for now, even if it's a bit specific -/
instance : Nan (Color UInt8) where
  nan := ⟨255, 0, 0, 255⟩

/-- Approximation midpoint for a color channel -/
noncomputable def UInt8.color (v : UInt8) : ℝ :=
  (v.toNat + 1/2) / 256

@[irreducible] def UInt8.approx' (v : UInt8) : Set ℝ :=
  let c : ℝ := v.color
  let e := color_error / 2
  Icc (c - e) (c + e)

/-- Approximation interval around a color channel, of width `color_error` -/
instance : Approx UInt8 ℝ where
  approx v := v.approx'

lemma UInt8.approx_def (v : UInt8) : Approx.approx v =
    let c : ℝ := v.color
    let e := color_error / 2
    Icc (c - e) (c + e) := by
  simp only [Approx.approx]
  rw [approx']

/-- Componentwise approximation for `Color` -/
@[irreducible] def Color.approx' [Approx α β] (c : Color α) : Set (Color β) :=
  {e : Color β | e.r ∈ approx c.r ∧ e.g ∈ approx c.g ∧ e.b ∈ approx c.b ∧ e.a ∈ approx c.a}

/-- `Color α` approximates componentwise, after a single nan -/
instance : Approx (Color UInt8) (Color ℝ) where
  approx c := if c = nan then univ else c.approx'

lemma Color.approx_uint8_def (c : Color UInt8) :
    approx c = if c = nan then univ else {e : Color ℝ |
      e.r ∈ approx c.r ∧ e.g ∈ approx c.g ∧ e.b ∈ approx c.b ∧ e.a ∈ approx c.a} := by
  simp only [Approx.approx]
  rw [approx']
  simp only [Approx.approx]

@[simp] lemma Color.approx_nan : approx (nan : Color UInt8) = univ := rfl

/-- `Color Interval` approximates purely componentwise -/
instance : Approx (Color Interval) (Color ℝ) where
  approx c := c.approx'

lemma Color.approx_interval_def (c : Color Interval) :
    approx c = {e : Color ℝ |
      e.r ∈ approx c.r ∧ e.g ∈ approx c.g ∧ e.b ∈ approx c.b ∧ e.a ∈ approx c.a} := by
  simp only [Approx.approx]
  rw [approx']
  simp only [Approx.approx]

/-- Send `none` to `univ` -/
instance : Approx (Option UInt8) ℝ where
  approx v := match v with
    | none => univ
    | some v => approx v

@[simp] lemma approx_none : approx (none : Option UInt8) = univ := rfl
@[simp] lemma approx_some (v : UInt8) : approx (some v) = approx v := rfl

/-- Roughly what `Color ℝ` a `Color UInt8` corresponds to -/
noncomputable def Color.val (c : Color UInt8) : Color ℝ :=
  ⟨c.r.color, c.g.color, c.b.color, c.a.color⟩

/-- Untrusted quantized interval -/
@[irreducible] def Interval.untrusted_quantize (x : Interval) : UInt8 :=
  let n := (((x.lo.add x.hi false).scaleB 7).add (.ofRat (1/2) false) false).floor
  (max 0 (min 255 n)).n.toUInt64.toUInt8

/-- Unquantize back to an interval midpoint.  This is exact.  -/
@[irreducible] def UInt8.unquantize (v : UInt8) : Floating :=
  (Floating.ofNat (2*v.toNat + 1) false).scaleB (-9)

/-- `UInt8.unquantize` is exact, if isn't nan (it never is, but we won't prove that) -/
@[simp] lemma UInt8.val_unquantize {v : UInt8} (n : v.unquantize ≠ nan) :
    v.unquantize.val = v.toNat / 256 + 1 / 512 := by
  rw [unquantize] at n ⊢
  have lt : 2 * v.toNat + 1 < 2^63 := by have h := v.toNat_lt; norm_num only at h ⊢; omega
  have e9 : ((-9 : Int64) : ℤ) = -9 := by decide
  simp only [Floating.val_scaleB n, Floating.val_ofNat' lt, e9, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, Int.reduceNeg, zpow_neg, add_mul, one_div]
  ring_nf

/-- Quantize an interval approximating a `[0,1]` value into a `UInt8` -/
@[irreducible] def Interval.quantize (x : Interval) : Option UInt8 :=
  -- Determine the best result
  let c := x.untrusted_quantize
  -- Check if we're accurate enough
  let m := c.unquantize
  let lo := m.sub half_color_error.lo true
  let hi := m.add half_color_error.lo false
  if lo ≠ nan ∧ hi ≠ nan ∧ lo ≤ x.lo ∧ x.hi ≤ hi then some c else none

/-- `UInt8`s convert to `Floating` exactly -/
@[simp] lemma Floating.val_ofUInt8 (v : UInt8) (up : Bool) :
    (Floating.ofNat v.toNat up).val = v.toNat :=
  Floating.val_ofNat' (lt_trans v.toNat_lt (by norm_num))

/-- `Interval.quantize` is conservative -/
@[approx] lemma Interval.mem_approx_quantize {x' : ℝ} {x : Interval} (xm : x' ∈ approx x) :
    x' ∈ approx x.quantize := by
  rw [quantize]
  generalize hc : x.untrusted_quantize = c
  generalize hl : c.unquantize.sub half_color_error.lo true = lo
  generalize hh : c.unquantize.add half_color_error.lo false = hi
  simp only [ne_eq, Floating.val_le_val]
  by_cases n : lo = nan ∨ hi = nan
  · rcases n with n | n; all_goals simp [n]
  rcases not_or.mp n with ⟨n0,n1⟩
  simp only [n0, not_false_eq_true, n1, true_and]
  have mn : c.unquantize ≠ nan := by rw [←hl] at n0; exact (Floating.ne_nan_of_sub n0).1
  by_cases g : lo.val ≤ x.lo.val ∧ x.hi.val ≤ hi.val
  · have xn : x ≠ nan := by
      contrapose g
      simp only [ne_eq, not_not] at g
      simp only [g, lo_nan, hi_nan, Floating.val_nan_le, and_true, not_le, ←Floating.val_lt_val]
      exact Floating.nan_lt n0
    simp only [g, and_self, ↓reduceIte, UInt8.approx_def, approx_some]
    simp only [Rat.cast_div, Rat.cast_ofNat, mem_Icc, tsub_le_iff_right, UInt8.color, add_div]
    simp only [approx, lo_eq_nan, xn, ↓reduceIte, mem_Icc] at xm
    have e : half_color_error.lo.val ≤ color_error / 2 := by
      rw [half_color_error]
      apply lo_le (by native_decide)
      have e : (color_error : ℝ) / 2 = (color_error / 2 : ℚ) := by
        simp only [Rat.cast_div, Rat.cast_ofNat]
      rw [e]; approx
    simp only [←hl, ←hh] at n0 n1 mn g
    have le_lo := Floating.le_sub n0
    have le_hi := Floating.add_le n1
    simp only [UInt8.val_unquantize mn, tsub_le_iff_right, hl, hh] at le_lo le_hi g ⊢
    exact ⟨by linarith, by linarith⟩
  · simp only [g, ↓reduceIte, approx_none, mem_univ]

/-- Turn an `Interval` color into a `UInt8` color -/
@[irreducible] def Color.quantize (c : Color Interval) : Color UInt8 :=
  match (c.r.quantize, c.g.quantize, c.b.quantize, c.a.quantize) with
  | (some r, some g, some b, some a) => ⟨r, g, b, a⟩
  | _ => nan

/-- `Color.quantize` is conservative -/
@[approx] lemma Color.mem_approx_quantize {c' : Color ℝ} {c : Color Interval} (cm : c' ∈ approx c) :
    c' ∈ approx c.quantize := by
  unfold quantize
  generalize hr : c.r.quantize = r
  generalize hg : c.g.quantize = g
  generalize hb : c.b.quantize = b
  generalize ha : c.a.quantize = a
  match r with
  | none => simp only [approx_nan, mem_univ]
  | some r =>
    match g with
    | none => simp only [approx_nan, mem_univ]
    | some g =>
    match b with
    | none => simp only [approx_nan, mem_univ]
    | some b =>
      match a with
      | none => simp only [approx_nan, mem_univ]
      | some a =>
        simp only [approx, mem_ite_univ_left]
        intro _
        simp only [approx] at cm; simp only [approx', mem_setOf_eq] at cm
        rcases cm with ⟨m0, m1, m2, m3⟩
        simp only [approx', mem_setOf_eq, ←approx_some, ←hr, ←hg, ←hb, ←ha,
          Interval.mem_approx_quantize, m0, m1, m2, m3, true_and]

/-!
### Color construction utilities
-/

/-- Map a color componentwise -/
def Color.map (f : α → β) (c : Color α) : Color β :=
  ⟨f c.r, f c.g, f c.b, f c.a⟩

/-- Linear interpolation between two colors -/
def lerp [SMul α β] [Add β] [Sub β] (t : α) (x y : β) : β :=
  x + t • (y - x)

/-- `ℚ → Interval` for `Color` -/
@[irreducible] def Color.ofRat (c : Color ℚ) : Color Interval :=
  c.map .ofRat

/-!
### Approximation lemmas
-/

variable {α' β' : Type}
variable [Approx α α'] [Approx β β']

/-- `neg` approximates itself, for `Interval` and `ℝ` -/
noncomputable instance : ApproxNeg (Color Interval) (Color ℝ) where
  approx_neg x := by
    intro a m
    simp only [mem_neg] at m
    simpa only [Color.approx_interval_def, Color.neg_def, mem_setOf_eq, Interval.approx_neg,
      mem_neg] using m

/-- `+` approximates itself, for `Interval` and `ℝ` -/
noncomputable instance : ApproxAdd (Color Interval) (Color ℝ) where
  approx_add x y := by
    intro a m
    simp only [mem_add] at m
    rcases m with ⟨x',xm,y',ym,e⟩
    simp only [Color.add_def, approx, ←e] at xm ym ⊢
    simp only [Color.approx', mem_setOf_eq] at xm ym ⊢
    rcases xm with ⟨x0, x1, x2, x3⟩
    rcases ym with ⟨y0, y1, y2, y3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals exact mem_approx_add (by assumption) (by assumption)

/-- `-` approximates itself, for `Interval` and `ℝ` -/
noncomputable instance : ApproxSub (Color Interval) (Color ℝ) where
  approx_sub x y := by
    intro a m
    simp only [mem_sub] at m
    rcases m with ⟨x',xm,y',ym,e⟩
    simp only [Color.sub_def, approx, ← e] at xm ym ⊢
    simp only [Color.approx', mem_setOf_eq] at xm ym ⊢
    rcases xm with ⟨x0, x1, x2, x3⟩
    rcases ym with ⟨y0, y1, y2, y3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals exact mem_approx_sub (by assumption) (by assumption)

noncomputable instance : ApproxAddGroup (Color Interval) (Color ℝ) where

/-- `•` approximates itself, for `Interval` and `ℝ` -/
noncomputable instance : ApproxSMul Interval (Color Interval) ℝ (Color ℝ) where
  mem_approx_smul {s' x' s x} sm xm := by
    simp only [Color.smul_def, smul_eq_mul, approx] at xm ⊢
    simp only [Color.approx', mem_setOf_eq] at xm ⊢
    rcases xm with ⟨m0, m1, m2, m3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals exact mem_approx_mul (by assumption) (by assumption)

/-- `lerp` approximates itself -/
@[approx] lemma mem_approx_lerp [Add β] [Sub β] [AddGroup β'] [SMul α β] [SMul α' β']
    [ApproxAdd β β'] [ApproxSub β β'] [ApproxSMul α β α' β']
    {t' : α'} {x' y' : β'} {t : α} {x y : β}
    (tm : t' ∈ approx t) (xm : x' ∈ approx x) (ym : y' ∈ approx y) :
    lerp t' x' y' ∈ approx (lerp t x y) := by
  rw [lerp, lerp]
  approx

/-- `Color.ofRat` is conservative -/
@[approx] lemma Color.mem_approx_ofRat {c : Color ℚ} : ↑c ∈ approx (Color.ofRat c) := by
  simp only [coe, approx, ofRat, map]
  simp only [approx', mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply Interval.approx_ofRat
