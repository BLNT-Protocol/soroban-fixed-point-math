import Mathlib

namespace SorobanFixedPointMath

/-!
This module models the observable checked arithmetic semantics of the signed
Soroban `I256` operations used by the fixed-point implementation. Values are
represented by mathematical integers; `none` represents the host error raised
when an exact result is outside the signed 256-bit range.
-/

namespace I256

def minValue : ℤ := -(2 ^ 255)

def maxValue : ℤ := 2 ^ 255 - 1

def InRange (x : ℤ) : Prop := minValue ≤ x ∧ x ≤ maxValue

instance (x : ℤ) : Decidable (InRange x) := by
  unfold InRange
  infer_instance

theorem minValue_lt_zero : minValue < 0 := by
  norm_num [minValue]

theorem zero_le_maxValue : 0 ≤ maxValue := by
  norm_num [maxValue]

theorem zero_inRange : InRange 0 := by
  constructor
  · exact minValue_lt_zero.le
  · exact zero_le_maxValue

theorem one_inRange : InRange 1 := by
  norm_num [InRange, minValue, maxValue]

/-- The checked-result behavior shared by Soroban's signed arithmetic host functions. -/
def checked (x : ℤ) : Option ℤ := if InRange x then some x else none

def add (x y : ℤ) : Option ℤ := checked (x + y)

def sub (x y : ℤ) : Option ℤ := checked (x - y)

def mul (x y : ℤ) : Option ℤ := checked (x * y)

theorem checked_eq_some {x : ℤ} (h : InRange x) : checked x = some x := by
  simp [checked, h]

theorem checked_eq_none {x : ℤ} (h : ¬InRange x) : checked x = none := by
  simp [checked, h]

theorem add_eq_some {x y : ℤ} (h : InRange (x + y)) : add x y = some (x + y) := by
  exact checked_eq_some h

theorem sub_eq_some {x y : ℤ} (h : InRange (x - y)) : sub x y = some (x - y) := by
  exact checked_eq_some h

theorem mul_eq_some {x y : ℤ} (h : InRange (x * y)) : mul x y = some (x * y) := by
  exact checked_eq_some h

theorem checked_eq_some_iff {x y : ℤ} : checked x = some y ↔ InRange x ∧ x = y := by
  by_cases h : InRange x
  · simp [checked, h]
  · simp [checked, h]

/-- Rust signed division truncated toward zero, specialized to a natural denominator. -/
def truncDiv (x : ℤ) (d : ℕ) : ℤ :=
  if x < 0 ∧ x % (d : ℤ) ≠ 0 then x / (d : ℤ) + 1 else x / (d : ℤ)

/-- Checked positive-denominator division used by the fixed-point implementation. -/
def div (x : ℤ) (d : ℕ) : Option ℤ :=
  if d = 0 then none else checked (truncDiv x d)

/-- Checked Euclidean remainder used by the fixed-point implementation. -/
def remEuclid (x : ℤ) (d : ℕ) : Option ℤ :=
  if d = 0 then none else checked (x % (d : ℤ))

theorem truncDiv_of_nonneg {x : ℤ} {d : ℕ} (hx : 0 ≤ x) : truncDiv x d = x / (d : ℤ) := by
  simp [truncDiv, not_lt_of_ge hx]

theorem truncDiv_of_neg_of_mod_ne {x : ℤ} {d : ℕ}
    (hx : x < 0) (hmod : x % (d : ℤ) ≠ 0) :
    truncDiv x d = x / (d : ℤ) + 1 := by
  simp [truncDiv, hx, hmod]

theorem truncDiv_of_mod_eq_zero {x : ℤ} {d : ℕ} (hmod : x % (d : ℤ) = 0) :
    truncDiv x d = x / (d : ℤ) := by
  simp [truncDiv, hmod]

/-- The model is Lean's truncating signed division for every positive denominator. -/
theorem truncDiv_eq_tdiv (x : ℤ) {d : ℕ} (hd : 0 < d) :
    truncDiv x d = x.tdiv (d : ℤ) := by
  have hdzpos : (0 : ℤ) < d := by exact_mod_cast hd
  rw [Int.tdiv_eq_ediv]
  simp only [Int.sign_eq_one_of_pos hdzpos, Int.dvd_iff_emod_eq_zero]
  by_cases hx : 0 ≤ x
  · simp [truncDiv, hx]
  · have hxneg : x < 0 := lt_of_not_ge hx
    by_cases hm : x % (d : ℤ) = 0
    · simp [truncDiv, hx, hxneg, hm]
    · simp [truncDiv, hx, hxneg, hm]

theorem ediv_ge_self_of_neg {x : ℤ} {d : ℕ} (hx : x < 0) (hd : 0 < d) :
    x ≤ x / (d : ℤ) := by
  have hdzpos : (0 : ℤ) < d := by exact_mod_cast hd
  apply (Int.le_ediv_iff_mul_le hdzpos).2
  have hd1 : (1 : ℤ) ≤ d := hdzpos
  have hfactor : 0 ≤ (d : ℤ) - 1 := sub_nonneg.mpr hd1
  have hproduct := mul_nonpos_of_nonpos_of_nonneg hx.le hfactor
  nlinarith

/-- Division by a positive natural cannot increase an `I256` magnitude past its input. -/
theorem ediv_inRange {x : ℤ} {d : ℕ} (hx : InRange x) (hd : 0 < d) :
    InRange (x / (d : ℤ)) := by
  have hdzpos : (0 : ℤ) < d := by exact_mod_cast hd
  by_cases hx0 : 0 ≤ x
  · have hq0 : 0 ≤ x / (d : ℤ) := Int.ediv_nonneg hx0 hdzpos.le
    have hqx : x / (d : ℤ) ≤ x := Int.ediv_le_self _ hx0
    exact ⟨le_trans minValue_lt_zero.le hq0, le_trans hqx hx.2⟩
  · have hxneg : x < 0 := lt_of_not_ge hx0
    have hq0 : x / (d : ℤ) ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg hxneg.le hdzpos
    exact ⟨le_trans hx.1 (ediv_ge_self_of_neg hxneg hd),
      le_trans hq0 zero_le_maxValue⟩

/-- Truncating positive-denominator division cannot escape the signed 256-bit range. -/
theorem truncDiv_inRange {x : ℤ} {d : ℕ} (hx : InRange x) (hd : 0 < d) :
    InRange (truncDiv x d) := by
  by_cases hx0 : 0 ≤ x
  · rw [truncDiv_of_nonneg hx0]
    exact ediv_inRange hx hd
  · have hxneg : x < 0 := lt_of_not_ge hx0
    by_cases hm : x % (d : ℤ) = 0
    · rw [truncDiv_of_mod_eq_zero hm]
      exact ediv_inRange hx hd
    · rw [truncDiv_of_neg_of_mod_ne hxneg hm]
      have hdzpos : (0 : ℤ) < d := by exact_mod_cast hd
      have hqneg : x / (d : ℤ) < 0 := Int.ediv_neg_of_neg_of_pos hxneg hdzpos
      constructor
      · have hxq := ediv_ge_self_of_neg hxneg hd
        have hqsucc : x / (d : ℤ) ≤ x / (d : ℤ) + 1 := by omega
        exact le_trans hx.1 (le_trans hxq hqsucc)
      · exact le_trans (by omega) zero_le_maxValue

theorem div_eq_some {x : ℤ} {d : ℕ} (hx : InRange x) (hd : 0 < d) :
    div x d = some (truncDiv x d) := by
  simp [div, Nat.ne_of_gt hd, checked_eq_some (truncDiv_inRange hx hd)]

/-- A Euclidean remainder fits whenever its positive denominator fits below `I256::MAX`. -/
theorem emod_inRange (x : ℤ) {d : ℕ} (hd : 0 < d) (hdmax : (d : ℤ) ≤ maxValue) :
    InRange (x % (d : ℤ)) := by
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hdzpos : (0 : ℤ) < d := by exact_mod_cast hd
  have hmod0 := Int.emod_nonneg x hdz
  have hmodlt := Int.emod_lt_of_pos x hdzpos
  exact ⟨le_trans minValue_lt_zero.le hmod0, by omega⟩

theorem remEuclid_eq_some (x : ℤ) {d : ℕ} (hd : 0 < d)
    (hdmax : (d : ℤ) ≤ maxValue) :
    remEuclid x d = some (x % (d : ℤ)) := by
  simp [remEuclid, Nat.ne_of_gt hd, checked_eq_some (emod_inRange x hd hdmax)]

end I256

end SorobanFixedPointMath
