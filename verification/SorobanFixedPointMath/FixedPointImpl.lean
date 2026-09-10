import SorobanFixedPointMath.Rounding
import SorobanFixedPointMath.I256

namespace SorobanFixedPointMath

/-!
These definitions mirror the positive-denominator paths of `src/i256.rs`. The
Rust implementation first performs signed division truncated toward zero, then
uses the Euclidean remainder to correct that quotient to mathematical floor or
ceiling. The execution models preserve the source operation order.
-/

namespace FixedPointImpl

/-- The value returned by `mul_div_floor` after its checked operations succeed. -/
def mulDivFloorValue (x y : ℤ) (d : ℕ) : ℤ :=
  let r := x * y
  if r < 0 then
    I256.truncDiv r d - if 0 < r % (d : ℤ) then 1 else 0
  else
    I256.truncDiv r d

/-- The value returned by `mul_div_ceil` after its checked operations succeed. -/
def mulDivCeilValue (x y : ℤ) (d : ℕ) : ℤ :=
  let r := x * y
  if r = 0 ∨ r < 0 then
    I256.truncDiv r d
  else
    I256.truncDiv r d + if 0 < r % (d : ℤ) then 1 else 0

/-- Checked execution model of the positive-denominator `mul_div_floor` path. -/
def mulDivFloor (x y : ℤ) (d : ℕ) : Option ℤ := do
  let r ← I256.mul x y
  if r < 0 then
    let remainder ← I256.remEuclid r d
    let q ← I256.div r d
    I256.sub q (if 0 < remainder then 1 else 0)
  else
    I256.div r d

/-- Checked execution model of the positive-denominator `mul_div_ceil` path. -/
def mulDivCeil (x y : ℤ) (d : ℕ) : Option ℤ := do
  let r ← I256.mul x y
  if r = 0 ∨ r < 0 then
    I256.div r d
  else
    let remainder ← I256.remEuclid r d
    let q ← I256.div r d
    I256.add q (if 0 < remainder then 1 else 0)

/-- Model of `fixed_mul_floor(x, y, denominator)` for a positive denominator. -/
def fixedMulFloor (x y : ℤ) (denominator : ℕ) : Option ℤ :=
  mulDivFloor x y denominator

/-- Model of `fixed_mul_ceil(x, y, denominator)` for a positive denominator. -/
def fixedMulCeil (x y : ℤ) (denominator : ℕ) : Option ℤ :=
  mulDivCeil x y denominator

/-- Model of `fixed_div_floor(x, y, denominator)`, which computes `x * denominator / y`. -/
def fixedDivFloor (x : ℤ) (y : ℕ) (denominator : ℤ) : Option ℤ :=
  mulDivFloor x denominator y

/-- Model of `fixed_div_ceil(x, y, denominator)`, which computes `x * denominator / y`. -/
def fixedDivCeil (x : ℤ) (y : ℕ) (denominator : ℤ) : Option ℤ :=
  mulDivCeil x denominator y

/-- The floor implementation reduces to Euclidean integer division. -/
theorem mulDivFloorValue_eq_ediv (x y : ℤ) {d : ℕ} (hd : 0 < d) :
    mulDivFloorValue x y d = x * y / (d : ℤ) := by
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hmod0 : 0 ≤ x * y % (d : ℤ) := Int.emod_nonneg _ hdz
  by_cases hr : x * y < 0
  · by_cases hm : 0 < x * y % (d : ℤ)
    · simp [mulDivFloorValue, hr, hm, I256.truncDiv, ne_of_gt hm]
    · have hm0 : x * y % (d : ℤ) = 0 := le_antisymm (le_of_not_gt hm) hmod0
      simp [mulDivFloorValue, hr, hm, I256.truncDiv, hm0]
  · simp [mulDivFloorValue, hr, I256.truncDiv]

/-- The ceiling implementation is Euclidean division plus one exactly for a nonzero remainder. -/
theorem mulDivCeilValue_eq_ediv_add_indicator (x y : ℤ) {d : ℕ} (hd : 0 < d) :
    mulDivCeilValue x y d =
      x * y / (d : ℤ) + if 0 < x * y % (d : ℤ) then 1 else 0 := by
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hmod0 : 0 ≤ x * y % (d : ℤ) := Int.emod_nonneg _ hdz
  by_cases hr0 : x * y = 0
  · simp [mulDivCeilValue, hr0, I256.truncDiv]
  · by_cases hr : x * y < 0
    · by_cases hm : 0 < x * y % (d : ℤ)
      · simp [mulDivCeilValue, hr0, hr, hm, I256.truncDiv, ne_of_gt hm]
      · have hm0 : x * y % (d : ℤ) = 0 := le_antisymm (le_of_not_gt hm) hmod0
        simp [mulDivCeilValue, hr0, hr, hm, I256.truncDiv, hm0]
    · have hrpos : 0 < x * y := lt_of_le_of_ne (le_of_not_gt hr) (Ne.symm hr0)
      simp [mulDivCeilValue, hr0, hr, hrpos, I256.truncDiv]

/-- A successful checked product is enough to keep the floor result in range. -/
theorem mulDivFloorValue_inRange {x y : ℤ} {d : ℕ}
    (hprod : I256.InRange (x * y)) (hd : 0 < d) :
    I256.InRange (mulDivFloorValue x y d) := by
  rw [mulDivFloorValue_eq_ediv x y hd]
  exact I256.ediv_inRange hprod hd

/-- A successful checked product is enough to keep the ceiling result in range. -/
theorem mulDivCeilValue_inRange {x y : ℤ} {d : ℕ}
    (hprod : I256.InRange (x * y)) (hd : 0 < d) :
    I256.InRange (mulDivCeilValue x y d) := by
  rw [mulDivCeilValue_eq_ediv_add_indicator x y hd]
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hdzpos : (0 : ℤ) < d := by exact_mod_cast hd
  have hmod0 : 0 ≤ x * y % (d : ℤ) := Int.emod_nonneg _ hdz
  by_cases hm : 0 < x * y % (d : ℤ)
  · simp only [if_pos hm]
    by_cases hr : x * y < 0
    · have hqneg : x * y / (d : ℤ) < 0 := Int.ediv_neg_of_neg_of_pos hr hdzpos
      have hprodq := I256.ediv_ge_self_of_neg hr hd
      constructor
      · exact le_trans hprod.1 (by omega)
      · exact le_trans (by omega) I256.zero_le_maxValue
    · have hr0 : 0 ≤ x * y := le_of_not_gt hr
      have hq0 : 0 ≤ x * y / (d : ℤ) := Int.ediv_nonneg hr0 hdzpos.le
      have hdecomp : x * y % (d : ℤ) + (d : ℤ) * (x * y / (d : ℤ)) = x * y :=
        Int.emod_add_ediv (x * y) (d : ℤ)
      have hd1 : (1 : ℤ) ≤ d := hdzpos
      have hmul : x * y / (d : ℤ) ≤ (d : ℤ) * (x * y / (d : ℤ)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hq0]
      exact ⟨le_trans I256.minValue_lt_zero.le (by omega),
        le_trans (by omega) hprod.2⟩
  · simp only [if_neg hm]
    simpa using I256.ediv_inRange hprod hd

/-- Under the checked product and denominator bounds, the floor path cannot trap. -/
theorem mulDivFloor_eq_some {x y : ℤ} {d : ℕ}
    (hprod : I256.InRange (x * y)) (hd : 0 < d)
    (hdmax : (d : ℤ) ≤ I256.maxValue) :
    mulDivFloor x y d = some (mulDivFloorValue x y d) := by
  unfold mulDivFloor
  rw [I256.mul_eq_some hprod]
  simp
  by_cases hr : x * y < 0
  · rw [if_pos hr, I256.remEuclid_eq_some (x * y) hd hdmax]
    simp
    rw [I256.div_eq_some hprod hd]
    simp
    rw [I256.sub_eq_some]
    · simp [mulDivFloorValue, hr]
    · simpa [mulDivFloorValue, hr] using mulDivFloorValue_inRange hprod hd
  · rw [if_neg hr, I256.div_eq_some hprod hd]
    simp [mulDivFloorValue, hr]

/-- Under the checked product and denominator bounds, the ceiling path cannot trap. -/
theorem mulDivCeil_eq_some {x y : ℤ} {d : ℕ}
    (hprod : I256.InRange (x * y)) (hd : 0 < d)
    (hdmax : (d : ℤ) ≤ I256.maxValue) :
    mulDivCeil x y d = some (mulDivCeilValue x y d) := by
  unfold mulDivCeil
  rw [I256.mul_eq_some hprod]
  simp
  by_cases hr : (x = 0 ∨ y = 0) ∨ x * y < 0
  · rw [if_pos hr, I256.div_eq_some hprod hd]
    simp [mulDivCeilValue, hr]
  · rw [if_neg hr, I256.remEuclid_eq_some (x * y) hd hdmax]
    simp
    rw [I256.div_eq_some hprod hd]
    simp
    rw [I256.add_eq_some]
    · simp [mulDivCeilValue, hr]
    · simpa [mulDivCeilValue, hr] using mulDivCeilValue_inRange hprod hd

/-- Euclidean division plus a remainder indicator is rational ceiling. -/
theorem ediv_add_indicator_eq_ceil (r : ℤ) {d : ℕ} (hd : 0 < d) :
    r / (d : ℤ) + (if 0 < r % (d : ℤ) then 1 else 0) =
      ⌈(r : ℚ) / (d : ℚ)⌉ := by
  rw [Rat.ceil_intCast_div_natCast]
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hdzpos : (0 : ℤ) < d := by exact_mod_cast hd
  have hdecomp : r % (d : ℤ) + (d : ℤ) * (r / (d : ℤ)) = r :=
    Int.emod_add_ediv r (d : ℤ)
  have hmod0 : 0 ≤ r % (d : ℤ) := Int.emod_nonneg _ hdz
  have hmodlt : r % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos _ hdzpos
  by_cases hm : 0 < r % (d : ℤ)
  · have hnegdiv :
        (-r) / (d : ℤ) = -(r / (d : ℤ)) - 1 := by
      exact ((Int.ediv_emod_unique'' (a := -r) (b := (d : ℤ))
        (r := (d : ℤ) - r % (d : ℤ)) (q := -(r / (d : ℤ)) - 1) hdz).2 ⟨by
          calc
            (d : ℤ) - r % (d : ℤ) + (d : ℤ) * (-(r / (d : ℤ)) - 1) =
                -(r % (d : ℤ) + (d : ℤ) * (r / (d : ℤ))) := by ring
            _ = -r := by rw [hdecomp], by
          constructor
          · omega
          · rw [abs_of_pos hdzpos]
            omega⟩).1
    simp [hm, hnegdiv, add_comm]
  · have hm0 : r % (d : ℤ) = 0 := le_antisymm (le_of_not_gt hm) hmod0
    have hnegdiv : (-r) / (d : ℤ) = -(r / (d : ℤ)) := by
      exact ((Int.ediv_emod_unique'' (a := -r) (b := (d : ℤ))
        (r := 0) (q := -(r / (d : ℤ))) hdz).2 ⟨by
          simp only [hm0, zero_add] at hdecomp
          nlinarith, by
          constructor
          · norm_num
          · rw [abs_of_pos hdzpos]
            exact hdzpos⟩).1
    simp [hm, hnegdiv]

/-- The positive-denominator `I256` multiplication/floor algorithm has exact floor semantics. -/
theorem mulDivFloorValue_isFloor (x y : ℤ) {d : ℕ} (hd : 0 < d) :
    IsFloor (mulDivFloorValue x y d) (((x * y : ℤ) : ℝ) / (d : ℝ)) := by
  have h := floor_isFloor (((x * y : ℤ) : ℝ) / (d : ℝ))
  have hfloor : ⌊((x * y : ℤ) : ℝ) / (d : ℝ)⌋ = x * y / (d : ℤ) := by
    rw [show ((x * y : ℤ) : ℝ) / (d : ℝ) =
        (((x * y : ℤ) : ℚ) / (d : ℚ) : ℚ) by norm_cast,
      Rat.floor_cast, Rat.floor_intCast_div_natCast]
  rw [hfloor] at h
  rwa [mulDivFloorValue_eq_ediv x y hd]

/-- The positive-denominator `I256` multiplication/ceiling algorithm has exact ceiling semantics. -/
theorem mulDivCeilValue_isCeil (x y : ℤ) {d : ℕ} (hd : 0 < d) :
    IsCeil (mulDivCeilValue x y d) (((x * y : ℤ) : ℝ) / (d : ℝ)) := by
  have h := ceil_isCeil (((x * y : ℤ) : ℝ) / (d : ℝ))
  have hceil : ⌈((x * y : ℤ) : ℝ) / (d : ℝ)⌉ =
      ⌈((x * y : ℤ) : ℚ) / (d : ℚ)⌉ := by
    rw [show ((x * y : ℤ) : ℝ) / (d : ℝ) =
        (((x * y : ℤ) : ℚ) / (d : ℚ) : ℚ) by norm_cast,
      Rat.ceil_cast]
  rw [hceil, ← ediv_add_indicator_eq_ceil (x * y) hd,
    ← mulDivCeilValue_eq_ediv_add_indicator x y hd] at h
  exact h

/-- The checked floor implementation succeeds and refines mathematical floor. -/
theorem mulDivFloor_refines {x y : ℤ} {d : ℕ}
    (hprod : I256.InRange (x * y)) (hd : 0 < d)
    (hdmax : (d : ℤ) ≤ I256.maxValue) :
    ∃ result,
      mulDivFloor x y d = some result ∧
      IsFloor result (((x * y : ℤ) : ℝ) / (d : ℝ)) := by
  exact ⟨mulDivFloorValue x y d, mulDivFloor_eq_some hprod hd hdmax,
    mulDivFloorValue_isFloor x y hd⟩

/-- The checked ceiling implementation succeeds and refines mathematical ceiling. -/
theorem mulDivCeil_refines {x y : ℤ} {d : ℕ}
    (hprod : I256.InRange (x * y)) (hd : 0 < d)
    (hdmax : (d : ℤ) ≤ I256.maxValue) :
    ∃ result,
      mulDivCeil x y d = some result ∧
      IsCeil result (((x * y : ℤ) : ℝ) / (d : ℝ)) := by
  exact ⟨mulDivCeilValue x y d, mulDivCeil_eq_some hprod hd hdmax,
    mulDivCeilValue_isCeil x y hd⟩

theorem fixedMulFloor_refines {x y : ℤ} {denominator : ℕ}
    (hprod : I256.InRange (x * y)) (hd : 0 < denominator)
    (hdmax : (denominator : ℤ) ≤ I256.maxValue) :
    ∃ result,
      fixedMulFloor x y denominator = some result ∧
      IsFloor result (((x * y : ℤ) : ℝ) / (denominator : ℝ)) :=
  mulDivFloor_refines hprod hd hdmax

theorem fixedMulCeil_refines {x y : ℤ} {denominator : ℕ}
    (hprod : I256.InRange (x * y)) (hd : 0 < denominator)
    (hdmax : (denominator : ℤ) ≤ I256.maxValue) :
    ∃ result,
      fixedMulCeil x y denominator = some result ∧
      IsCeil result (((x * y : ℤ) : ℝ) / (denominator : ℝ)) :=
  mulDivCeil_refines hprod hd hdmax

theorem fixedDivFloor_refines {x denominator : ℤ} {y : ℕ}
    (hprod : I256.InRange (x * denominator)) (hy : 0 < y)
    (hymax : (y : ℤ) ≤ I256.maxValue) :
    ∃ result,
      fixedDivFloor x y denominator = some result ∧
      IsFloor result (((x * denominator : ℤ) : ℝ) / (y : ℝ)) :=
  mulDivFloor_refines hprod hy hymax

theorem fixedDivCeil_refines {x denominator : ℤ} {y : ℕ}
    (hprod : I256.InRange (x * denominator)) (hy : 0 < y)
    (hymax : (y : ℤ) ≤ I256.maxValue) :
    ∃ result,
      fixedDivCeil x y denominator = some result ∧
      IsCeil result (((x * denominator : ℤ) : ℝ) / (y : ℝ)) :=
  mulDivCeil_refines hprod hy hymax

end FixedPointImpl

end SorobanFixedPointMath
