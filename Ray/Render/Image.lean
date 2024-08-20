import Interval.Misc.Array
import Ray.Render.Color
import Ray.Render.Grid

/-!
## Images: 2D arrays of colors

We build these on top of `ByteArray` for speed.
-/

open Set

/-- Packed array of `Color UInt8` -/
structure Image where
  /-- Packed RGBA bytes, corresponding to `Color UInt88888888`.
      These are in `y`-major order from top to bottom, to match libpng,
      though the accessors use correct `x`-major bottom-to-top order. -/
  data : ByteArray
  /-- Width -/
  width : ℕ
  /-- Height -/
  height : ℕ
  /-- `data` is the right size -/
  size_eq : data.size = height * width * 4

namespace Image

/-!
### Image access
-/

/-- The internal index of `(x,y,0)` -/
@[irreducible] def base (w h x y : ℕ) : ℕ := ((h - 1 - y) * w + x) * 4

/-- `base + c` is valid for `c < 4` -/
@[irreducible] def base_le {w h x y : ℕ} (xw : x < w) (yh : y < h) :
    base w h x y + 4 ≤ h * w * 4 := by
  rw [base]
  have hy : h - 1 - y ≤ h - 1 := by omega
  refine le_trans (add_le_add_right (Nat.mul_le_mul_right _ (add_le_add (Nat.mul_le_mul_right _
    hy) (Nat.le_pred_of_lt xw))) _) ?_
  have le0 : 1 ≤ w := by omega
  have le1 : 1 ≤ h := by omega
  simp only [Nat.pred_eq_sub_one, ← add_one_mul, add_assoc, Nat.sub_add_cancel le0,
    Nat.sub_add_cancel le1, le_refl]

/-- Get a pixel -/
@[irreducible] def get (i : Image) (x : Fin i.width) (y : Fin i.height) : Color UInt8 :=
  let b := base i.width i.height x y
  have lt : b + 4 ≤ i.data.size := by rw [i.size_eq]; exact base_le x.prop y.prop
  ⟨i.data[b]'(by omega),
   i.data[b + 1]'(by omega),
   i.data[b + 2]'(by omega),
   i.data[b + 3]'(by omega)⟩

/-- Get a pixel -/
@[irreducible] def get? (i : Image) (x y : ℕ) : Option (Color UInt8) :=
  if h : x < i.width ∧ y < i.height then
  some (i.get ⟨x, h.1⟩ ⟨y, h.2⟩) else none

/-!
### Build packed color arrays

This is a bit fiddly since we have to directly interface with `ByteArray`
-/

/-- Append a bunch of colors to a `ByteArray` -/
def push_colors (f : ℕ → Color UInt8) (n o : ℕ) (d : ByteArray) : ByteArray :=
  if n = 0 then d else
  let c := f o
  push_colors f (n-1) (o+1) ((((d.push c.r).push c.g).push c.b).push c.a)

/-- `push_colors` has the right size -/
@[simp] lemma size_push_colors (f : ℕ → Color UInt8) (n o : ℕ) (d : ByteArray) :
    (push_colors f n o d).size = d.size + n * 4 := by
  induction' n with n h generalizing d o
  · simp only [Nat.zero_eq, push_colors, ↓reduceIte, zero_mul, add_zero]
  · rw [push_colors]
    simp only [Nat.succ_eq_add_one, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
      add_tsub_cancel_right, h, ByteArray.size_push]
    omega

/-- `push_colors` fills in the right values, `get!` version -/
lemma get!_push_colors (f : ℕ → Color UInt8) (n o : ℕ) (d : ByteArray) (k : ℕ)
    (lt : k < d.size + n * 4) :
    (push_colors f n o d).get! k = (if k < d.size then d.get! k else
      (f (o + (k - d.size) / 4))[((k - d.size : ℕ) : Fin 4)]) := by
  induction' n with n h generalizing d o
  · simp only [Nat.zero_eq, zero_mul, add_zero] at lt
    simp only [Nat.zero_eq, push_colors, ↓reduceIte, lt, ↓reduceIte]
  · simp only [ByteArray.getElem_eq_get!, ByteArray.getElemNat_eq_get!] at h ⊢
    rw [push_colors]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_succ_eq_sub, tsub_zero, dite_eq_ite]
    simp only [Nat.succ_eq_add_one, add_one_mul, ← add_assoc] at lt
    rw [h]
    · simp only [ByteArray.size_push, dite_eq_ite, ByteArray.get!_push, add_assoc]
      norm_num
      by_cases e0 : k = d.size;     · simp [e0]
      by_cases e1 : k = d.size + 1; · simp [e1]
      by_cases e2 : k = d.size + 2; · simp [e2]
      by_cases e3 : k = d.size + 3; · simp [e3]
      simp only [← ne_eq] at e0 e1 e2 e3
      by_cases lt0 : k < d.size
      · have lt1 : k < d.size + 1 := by omega
        have lt2 : k < d.size + 2 := by omega
        have lt3 : k < d.size + 3 := by omega
        have lt4 : k < d.size + 4 := by omega
        simp only [lt0, lt1, lt2, lt3, lt4, if_true]
      · have ge : d.size + 4 ≤ k := by omega
        have e0 : o + (1 + (k - (d.size + 4)) / 4) = o + (k - d.size) / 4 := by omega
        have e1 : k - d.size = k - (d.size + 4) + 4 := by omega
        simp only [not_lt.mpr ge, ↓reduceIte, Nat.succ_eq_add_one, e0, e1, lt0, Nat.cast_add,
          Fin.natCast_self, add_zero]
    · simp only [ByteArray.size_push]
      omega

/-- `push_colors` fills in the right values, `get` version -/
lemma get_push_colors (f : ℕ → Color UInt8) (n o : ℕ) (d : ByteArray)
    (k : Fin (push_colors f n o d).size) :
    (push_colors f n o d)[k] = (if h : k < d.size then d[k]'h else
      (f (o + (k - d.size) / 4))[((k - d.size : ℕ) : Fin 4)]) := by
  simp only [Fin.getElem_fin, ByteArray.getElemNat_eq_get!, dite_eq_ite]
  apply get!_push_colors; convert k.prop; simp only [size_push_colors]

/-!
### Build packed color arrays in parallel
-/

-- Termination for `parallel_colors`
lemma n0_lt_n {n chunk : ℕ} (h : ¬n ≤ max 1 chunk) : n / 2 < n := by
  simp only [le_max_iff] at h; omega
lemma n1_lt_n {n chunk : ℕ} (h : ¬n ≤ max 1 chunk) : n - n / 2 < n := by
  simp only [le_max_iff] at h; omega

/-- Build a color array out of a function, parallelizing down to chunks of size `≤ chunk` -/
def parallel_colors' (f : ℕ → Color UInt8) (n o chunk : ℕ) : ByteArray :=
  if n ≤ max 1 chunk then
    push_colors f n o (.mkEmpty n)
  else
    let n0 := n / 2
    let t0 := Task.spawn (fun _ ↦ parallel_colors' f n0 o chunk)
    let t1 := Task.spawn (fun _ ↦ parallel_colors' f (n - n0) (o + n0) chunk)
    t0.get ++ t1.get
termination_by n decreasing_by
  · exact n0_lt_n (by assumption)
  · exact n1_lt_n (by assumption)

/-- Build a color array out of a function, parallelizing down to chunks of size `≤ chunk` -/
def parallel_colors (f : ℕ → Color UInt8) (n chunk : ℕ) : ByteArray :=
  parallel_colors' f n 0 chunk

/-- `parallel_colors'` has the right size -/
@[simp] lemma size_parallel_colors' (f : ℕ → Color UInt8) (n o chunk : ℕ) :
    (parallel_colors' f n o chunk).size = n * 4 := by
  induction' n using Nat.strong_induction_on with n i generalizing o
  rw [parallel_colors']
  by_cases h : n ≤ max 1 chunk
  · simp only [h, if_true, size_push_colors, ByteArray.size_mkEmpty, zero_add]
  · simp only [h, if_false, Task.spawn, ByteArray.size_append, i _ (n0_lt_n h), i _ (n1_lt_n h)]
    omega

/-- `parallel_colors'` fills in the right values, `get!` version -/
lemma get!_parallel_colors' (f : ℕ → Color UInt8) (n o chunk : ℕ) (k : ℕ) (lt : k < n * 4) :
    (parallel_colors' f n o chunk).get! k = (f (o + k/4))[(k : Fin 4)] := by
  have four : ((4 : ℕ) : Fin 4) = 0 := by decide
  induction' n using Nat.strong_induction_on with n i generalizing o k
  rw [parallel_colors']
  by_cases h : n ≤ max 1 chunk
  · simp only [h, if_true, Task.spawn]
    rw [get!_push_colors]
    · simp only [ByteArray.size_mkEmpty, not_lt_zero', ↓reduceIte, tsub_zero]
    · simpa only [ByteArray.size_mkEmpty, zero_add]
  · simp only [h, if_false, Task.spawn, ByteArray.get!_append, size_parallel_colors']
    simp only [le_max_iff, not_or, not_le] at h
    by_cases c : k < n/2 * 4
    · simp only [c, ↓reduceIte]
      rw [i _ (by omega) _ _ (by omega)]
    · simp only [c, ↓reduceIte]
      rw [i]
      · have ke : o + n / 2 + (k - n / 2 * 4) / 4 = o + k / 4 := by omega
        rw [Nat.cast_sub (by omega), Nat.cast_mul, four, mul_zero, sub_zero, ke]
      · omega
      · omega

/-- `parallel_colors` has the right size -/
@[simp] lemma size_parallel_colors (f : ℕ → Color UInt8) (n chunk : ℕ) :
    (parallel_colors f n chunk).size = n * 4 := by
  simp only [parallel_colors, size_parallel_colors']

/-- `parallel_colors` fills in the right values, `get!` version -/
lemma get!_parallel_colors (f : ℕ → Color UInt8) (n chunk : ℕ) (k : ℕ) (lt : k < n * 4) :
    (parallel_colors f n chunk).get! k = (f (k/4))[(k : Fin 4)] := by
  simp only [parallel_colors, zero_add, get!_parallel_colors' f n 0 chunk k lt]

/-!
### Image construction
-/

/-- Build an image in parallel -/
@[irreducible] def ofFn (w h chunk : ℕ) (f : ℕ → ℕ → Color UInt8) : Image :=
  ⟨parallel_colors (fun i ↦ f (i % w) (h - 1 - i / w)) (h * w) chunk, w, h, by
    simp only [size_parallel_colors, zero_add]⟩

@[simp] lemma width_ofFn (f : ℕ → ℕ → Color UInt8) (w h chunk : ℕ) :
    (ofFn w h chunk f).width = w := by rw [ofFn]
@[simp] lemma height_ofFn (f : ℕ → ℕ → Color UInt8) (w h chunk : ℕ) :
    (ofFn w h chunk f).height = h := by rw [ofFn]

@[simp] lemma get_ofFn (f : ℕ → ℕ → Color UInt8) (w h chunk : ℕ)
    (x : Fin (ofFn w h chunk f).width) (y : Fin (ofFn w h chunk f).height) :
    (ofFn w h chunk f).get x y = f x y := by
  rw [get]
  simp only [ByteArray.getElemNat_eq_get!]
  have xw := x.prop
  have yh := y.prop
  simp only [width_ofFn, height_ofFn, Color.ext_iff] at xw yh ⊢
  have w0 : 0 < w := by omega
  have yh' : y ≤ h - 1 := by omega
  have m0 : ∀ x : Fin 4, (x * 4 : Fin 4) = 0 := by
    intro x
    have e : (4 : Fin 4) = 0 := rfl
    simp only [e, mul_zero]
  have f0 : 0 < 4 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals {
    nth_rw 1 [ofFn]
    simp only
    rw [get!_parallel_colors]
    · simp [base, add_comm _ (x : ℕ), Nat.add_mul_div_right _ _ w0, Nat.div_eq_of_lt xw,
        Nat.sub_sub_self yh', Nat.mod_eq_of_lt xw, m0, add_comm (_ * 4),
        Nat.add_mul_div_right _ _ f0]
    · have le := base_le xw yh
      omega }

/-!
### Image construction on a `Grid`
-/

def ofGrid (g : Grid) (chunk : ℕ) (f : ℚ × ℚ → Color UInt8) : Image :=
  ofFn g.n.1 g.n.2 chunk (fun i j ↦ f (g.center (i,j)))

/-!
### Image analysis
-/

/-- Find indices that satisfy a predicate -/
def find (i : Image) (f : ℕ → ℕ → Color UInt8 → Bool) : Array (ℕ × ℕ) :=
  Fin.foldl i.height (fun (r : Array (ℕ × ℕ)) y ↦
    Fin.foldl i.width (fun (r : Array (ℕ × ℕ)) x ↦
      if f x y (i.get x y) then r.push ⟨x,y⟩ else r) r) #[]

/-- Find grid centers that satisfy a predicate -/
def find_grid (i : Image) (g : Grid) (f : ℚ × ℚ → Color UInt8 → Bool) : Array (ℚ × ℚ) :=
  (i.find fun x y c ↦ f (g.center (x,y)) c).map g.center
