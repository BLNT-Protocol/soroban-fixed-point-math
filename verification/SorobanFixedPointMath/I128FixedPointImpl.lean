import SorobanFixedPointMath.FixedPointImpl
import SorobanFixedPointMath.I128

namespace SorobanFixedPointMath

/-!
These definitions mirror the positive-denominator paths of the `FixedPoint for
i128` implementation in `src/i128.rs`. Unlike the Soroban `I256` path, an
out-of-range intermediate product returns `none`; there is no widening retry.
-/

namespace I128FixedPointImpl

/-- The mathematical result value is shared with the source-independent signed algorithm. -/
abbrev mulDivFloorValue := FixedPointImpl.mulDivFloorValue

abbrev mulDivCeilValue := FixedPointImpl.mulDivCeilValue

/-- Checked execution model of the positive-denominator `i128` floor path. -/
def mulDivFloor (x y : ℤ) (d : ℕ) : Option ℤ := do
  let r ← I128.mul x y
  if r < 0 then
    let remainder ← I128.remEuclid r d
    let q ← I128.div r d
    I128.sub q (if 0 < remainder then 1 else 0)
  else
    I128.div r d

/-- Checked execution model of the positive-denominator `i128` ceiling path. -/
def mulDivCeil (x y : ℤ) (d : ℕ) : Option ℤ := do
  let r ← I128.mul x y
  if r = 0 ∨ r < 0 then
    I128.div r d
  else
    let remainder ← I128.remEuclid r d
    let q ← I128.div r d
    I128.add q (if 0 < remainder then 1 else 0)

def fixedMulFloor (x y : ℤ) (denominator : ℕ) : Option ℤ :=
  mulDivFloor x y denominator

def fixedMulCeil (x y : ℤ) (denominator : ℕ) : Option ℤ :=
  mulDivCeil x y denominator

def fixedDivFloor (x : ℤ) (y : ℕ) (denominator : ℤ) : Option ℤ :=
  mulDivFloor x denominator y

def fixedDivCeil (x : ℤ) (y : ℕ) (denominator : ℤ) : Option ℤ :=
  mulDivCeil x denominator y

/-- A successful checked product is enough to keep the floor result in `i128` range. -/
theorem mulDivFloorValue_inRange {x y : ℤ} {d : ℕ}
    (hprod : I128.InRange (x * y)) (hd : 0 < d) :
    I128.InRange (mulDivFloorValue x y d) := by
  change I128.InRange (FixedPointImpl.mulDivFloorValue x y d)
  rw [FixedPointImpl.mulDivFloorValue_eq_ediv x y hd]
  exact I128.ediv_inRange hprod hd

/-- A successful checked product is enough to keep the ceiling result in `i128` range. -/
theorem mulDivCeilValue_inRange {x y : ℤ} {d : ℕ}
    (hprod : I128.InRange (x * y)) (hd : 0 < d) :
    I128.InRange (mulDivCeilValue x y d) := by
  change I128.InRange (FixedPointImpl.mulDivCeilValue x y d)
  rw [FixedPointImpl.mulDivCeilValue_eq_ediv_add_indicator x y hd]
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hdzpos : (0 : ℤ) < d := by exact_mod_cast hd
  have hmod0 : 0 ≤ x * y % (d : ℤ) := Int.emod_nonneg _ hdz
  by_cases hm : 0 < x * y % (d : ℤ)
  · simp only [if_pos hm]
    by_cases hr : x * y < 0
    · have hqneg : x * y / (d : ℤ) < 0 := Int.ediv_neg_of_neg_of_pos hr hdzpos
      have hprodq := I128.ediv_ge_self_of_neg hr hd
      constructor
      · exact le_trans hprod.1 (by omega)
      · exact le_trans (by omega) I128.zero_le_maxValue
    · have hr0 : 0 ≤ x * y := le_of_not_gt hr
      have hq0 : 0 ≤ x * y / (d : ℤ) := Int.ediv_nonneg hr0 hdzpos.le
      have hdecomp : x * y % (d : ℤ) + (d : ℤ) * (x * y / (d : ℤ)) = x * y :=
        Int.emod_add_ediv (x * y) (d : ℤ)
      have hd1 : (1 : ℤ) ≤ d := hdzpos
      have hmul : x * y / (d : ℤ) ≤ (d : ℤ) * (x * y / (d : ℤ)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hq0]
      exact ⟨le_trans I128.minValue_lt_zero.le (by omega),
        le_trans (by omega) hprod.2⟩
  · simp only [if_neg hm]
    simpa using I128.ediv_inRange hprod hd

/-- Under the checked product and denominator bounds, the `i128` floor path succeeds. -/
theorem mulDivFloor_eq_some {x y : ℤ} {d : ℕ}
    (hprod : I128.InRange (x * y)) (hd : 0 < d)
    (hdmax : (d : ℤ) ≤ I128.maxValue) :
    mulDivFloor x y d = some (mulDivFloorValue x y d) := by
  unfold mulDivFloor
  rw [I128.mul_eq_some hprod]
  simp
  by_cases hr : x * y < 0
  · rw [if_pos hr, I128.remEuclid_eq_some (x * y) hd hdmax]
    simp
    rw [I128.div_eq_some hprod hd]
    simp
    rw [I128.sub_eq_some]
    · simp [mulDivFloorValue, FixedPointImpl.mulDivFloorValue, hr, I128.truncDiv]
    · simpa [mulDivFloorValue, FixedPointImpl.mulDivFloorValue,
        I128.truncDiv, hr] using mulDivFloorValue_inRange hprod hd
  · rw [if_neg hr, I128.div_eq_some hprod hd]
    simp [mulDivFloorValue, FixedPointImpl.mulDivFloorValue, hr, I128.truncDiv]

/-- Under the checked product and denominator bounds, the `i128` ceiling path succeeds. -/
theorem mulDivCeil_eq_some {x y : ℤ} {d : ℕ}
    (hprod : I128.InRange (x * y)) (hd : 0 < d)
    (hdmax : (d : ℤ) ≤ I128.maxValue) :
    mulDivCeil x y d = some (mulDivCeilValue x y d) := by
  unfold mulDivCeil
  rw [I128.mul_eq_some hprod]
  simp
  by_cases hr : (x = 0 ∨ y = 0) ∨ x * y < 0
  · rw [if_pos hr, I128.div_eq_some hprod hd]
    simp [mulDivCeilValue, FixedPointImpl.mulDivCeilValue, hr, I128.truncDiv]
  · rw [if_neg hr, I128.remEuclid_eq_some (x * y) hd hdmax]
    simp
    rw [I128.div_eq_some hprod hd]
    simp
    rw [I128.add_eq_some]
    · simp [mulDivCeilValue, FixedPointImpl.mulDivCeilValue, hr, I128.truncDiv]
    · simpa [mulDivCeilValue, FixedPointImpl.mulDivCeilValue,
        I128.truncDiv, hr] using mulDivCeilValue_inRange hprod hd

/-- An `i128` phantom overflow is observable as `none`, matching `checked_mul` and `?`. -/
theorem mulDivFloor_eq_none_of_product_out_of_range {x y : ℤ} {d : ℕ}
    (hprod : ¬I128.InRange (x * y)) :
    mulDivFloor x y d = none := by
  unfold mulDivFloor
  rw [I128.mul_eq_none hprod]
  rfl

theorem mulDivCeil_eq_none_of_product_out_of_range {x y : ℤ} {d : ℕ}
    (hprod : ¬I128.InRange (x * y)) :
    mulDivCeil x y d = none := by
  unfold mulDivCeil
  rw [I128.mul_eq_none hprod]
  rfl

/-- A zero denominator returns `none` after a successful product, as in `checked_div`. -/
theorem mulDivFloor_eq_none_of_zero_denominator {x y : ℤ}
    (hprod : I128.InRange (x * y)) :
    mulDivFloor x y 0 = none := by
  unfold mulDivFloor
  rw [I128.mul_eq_some hprod]
  simp [I128.remEuclid, I128.div]

theorem mulDivCeil_eq_none_of_zero_denominator {x y : ℤ}
    (hprod : I128.InRange (x * y)) :
    mulDivCeil x y 0 = none := by
  unfold mulDivCeil
  rw [I128.mul_eq_some hprod]
  simp [I128.remEuclid, I128.div]

/-- The successful positive-denominator `i128` floor path has exact floor semantics. -/
theorem mulDivFloor_refines {x y : ℤ} {d : ℕ}
    (hprod : I128.InRange (x * y)) (hd : 0 < d)
    (hdmax : (d : ℤ) ≤ I128.maxValue) :
    ∃ result,
      mulDivFloor x y d = some result ∧
      IsFloor result (((x * y : ℤ) : ℝ) / (d : ℝ)) := by
  exact ⟨mulDivFloorValue x y d, mulDivFloor_eq_some hprod hd hdmax,
    FixedPointImpl.mulDivFloorValue_isFloor x y hd⟩

/-- The successful positive-denominator `i128` ceiling path has exact ceiling semantics. -/
theorem mulDivCeil_refines {x y : ℤ} {d : ℕ}
    (hprod : I128.InRange (x * y)) (hd : 0 < d)
    (hdmax : (d : ℤ) ≤ I128.maxValue) :
    ∃ result,
      mulDivCeil x y d = some result ∧
      IsCeil result (((x * y : ℤ) : ℝ) / (d : ℝ)) := by
  exact ⟨mulDivCeilValue x y d, mulDivCeil_eq_some hprod hd hdmax,
    FixedPointImpl.mulDivCeilValue_isCeil x y hd⟩

theorem fixedMulFloor_refines {x y : ℤ} {denominator : ℕ}
    (hprod : I128.InRange (x * y)) (hd : 0 < denominator)
    (hdmax : (denominator : ℤ) ≤ I128.maxValue) :
    ∃ result,
      fixedMulFloor x y denominator = some result ∧
      IsFloor result (((x * y : ℤ) : ℝ) / (denominator : ℝ)) :=
  mulDivFloor_refines hprod hd hdmax

theorem fixedMulCeil_refines {x y : ℤ} {denominator : ℕ}
    (hprod : I128.InRange (x * y)) (hd : 0 < denominator)
    (hdmax : (denominator : ℤ) ≤ I128.maxValue) :
    ∃ result,
      fixedMulCeil x y denominator = some result ∧
      IsCeil result (((x * y : ℤ) : ℝ) / (denominator : ℝ)) :=
  mulDivCeil_refines hprod hd hdmax

theorem fixedDivFloor_refines {x denominator : ℤ} {y : ℕ}
    (hprod : I128.InRange (x * denominator)) (hy : 0 < y)
    (hymax : (y : ℤ) ≤ I128.maxValue) :
    ∃ result,
      fixedDivFloor x y denominator = some result ∧
      IsFloor result (((x * denominator : ℤ) : ℝ) / (y : ℝ)) :=
  mulDivFloor_refines hprod hy hymax

theorem fixedDivCeil_refines {x denominator : ℤ} {y : ℕ}
    (hprod : I128.InRange (x * denominator)) (hy : 0 < y)
    (hymax : (y : ℤ) ≤ I128.maxValue) :
    ∃ result,
      fixedDivCeil x y denominator = some result ∧
      IsCeil result (((x * denominator : ℤ) : ℝ) / (y : ℝ)) :=
  mulDivCeil_refines hprod hy hymax

end I128FixedPointImpl

end SorobanFixedPointMath
