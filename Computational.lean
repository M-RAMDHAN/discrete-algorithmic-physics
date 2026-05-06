/- ============================================================
   DAP Computational Verification Module
   Extensive computational testing across algorithms
   All theorems verified by native_decide or rfl only
   ============================================================ -/

import DAP.Basic

namespace DAP

/- ----------------------------------------------------------
   This module provides extensive computational verification
   of DAP properties using Lean 4's native_decide and rfl.
   No sorry or admit is used anywhere in this file.
   ---------------------------------------------------------- -/

/-- Hard Collatz numbers: notoriously difficult test cases -/
def hardNumbers : List Nat :=
  [27, 31, 41, 47, 63, 71, 73, 97, 107, 871, 6171, 35647, 35649]

/-- Verification: 27 reaches 1 -/
lemma verify_27 : reachesOne 27 1000 = true := by native_decide

/-- Verification: 31 reaches 1 -/
lemma verify_31 : reachesOne 31 1000 = true := by native_decide

/-- Verification: 41 reaches 1 -/
lemma verify_41 : reachesOne 41 1000 = true := by native_decide

/-- Verification: 47 reaches 1 -/
lemma verify_47 : reachesOne 47 1000 = true := by native_decide

/-- Verification: 63 reaches 1 -/
lemma verify_63 : reachesOne 63 1000 = true := by native_decide

/-- Verification: 71 reaches 1 -/
lemma verify_71 : reachesOne 71 1000 = true := by native_decide

/-- Verification: 73 reaches 1 -/
lemma verify_73 : reachesOne 73 1000 = true := by native_decide

/-- Verification: 97 reaches 1 -/
lemma verify_97 : reachesOne 97 1000 = true := by native_decide

/-- Verification: 107 reaches 1 -/
lemma verify_107 : reachesOne 107 1000 = true := by native_decide

/-- Verification: 871 reaches 1 -/
lemma verify_871 : reachesOne 871 2000 = true := by native_decide

/-- Verification: 6171 reaches 1 -/
lemma verify_6171 : reachesOne 6171 3000 = true := by native_decide

/-- Verification: 35647 reaches 1 -/
lemma verify_35647 : reachesOne 35647 5000 = true := by native_decide

/-- Verification: 35649 reaches 1 -/
lemma verify_35649 : reachesOne 35649 5000 = true := by native_decide

/-- D/U ratio verification: all tested numbers exceed threshold -/
lemma du_ratio_27 : descentRatio 27 1000 > gravityThreshold 3 := by native_decide
lemma du_ratio_31 : descentRatio 31 1000 > gravityThreshold 3 := by native_decide
lemma du_ratio_41 : descentRatio 41 1000 > gravityThreshold 3 := by native_decide
lemma du_ratio_47 : descentRatio 47 1000 > gravityThreshold 3 := by native_decide
lemma du_ratio_63 : descentRatio 63 1000 > gravityThreshold 3 := by native_decide
lemma du_ratio_71 : descentRatio 71 1000 > gravityThreshold 3 := by native_decide
lemma du_ratio_73 : descentRatio 73 1000 > gravityThreshold 3 := by native_decide
lemma du_ratio_97 : descentRatio 97 1000 > gravityThreshold 3 := by native_decide
lemma du_ratio_107 : descentRatio 107 1000 > gravityThreshold 3 := by native_decide
lemma du_ratio_871 : descentRatio 871 2000 > gravityThreshold 3 := by native_decide
lemma du_ratio_6171 : descentRatio 6171 3000 > gravityThreshold 3 := by native_decide

/-- Popcount depletion verification -/
lemma popcount_27_start : popcount 27 = 4 := by rfl

/-- Popcount of powers of 2 is 1 -/
lemma popcount_pow2_8 : popcount 8 = 1 := by rfl
lemma popcount_pow2_16 : popcount 16 = 1 := by rfl
lemma popcount_pow2_32 : popcount 32 = 1 := by rfl

/-- Popcount of 1 is 1 -/
lemma popcount_1_eq_1 : popcount 1 = 1 := by rfl

/-- Bit density of powers of 2 is minimal -/
lemma bit_density_8 : bitDensity 8 = 1.0 / 4.0 := by native_decide
lemma bit_density_16 : bitDensity 16 = 1.0 / 5.0 := by native_decide

/-- Gravity threshold is approximately 1.585 for 3n+1 -/
lemma gravity_threshold_approx : gravityThreshold 3 = 1.585 := by native_decide

/-- Verification that numbers 1-20 all reach 1 -/
lemma reach_1 : reachesOne 1 100 = true := by native_decide
lemma reach_2 : reachesOne 2 100 = true := by native_decide
lemma reach_3 : reachesOne 3 100 = true := by native_decide
lemma reach_4 : reachesOne 4 100 = true := by native_decide
lemma reach_5 : reachesOne 5 100 = true := by native_decide
lemma reach_6 : reachesOne 6 100 = true := by native_decide
lemma reach_7 : reachesOne 7 100 = true := by native_decide
lemma reach_8 : reachesOne 8 100 = true := by native_decide
lemma reach_9 : reachesOne 9 100 = true := by native_decide
lemma reach_10 : reachesOne 10 100 = true := by native_decide
lemma reach_11 : reachesOne 11 100 = true := by native_decide
lemma reach_12 : reachesOne 12 100 = true := by native_decide
lemma reach_13 : reachesOne 13 100 = true := by native_decide
lemma reach_14 : reachesOne 14 100 = true := by native_decide
lemma reach_15 : reachesOne 15 100 = true := by native_decide
lemma reach_16 : reachesOne 16 100 = true := by native_decide
lemma reach_17 : reachesOne 17 100 = true := by native_decide
lemma reach_18 : reachesOne 18 100 = true := by native_decide
lemma reach_19 : reachesOne 19 100 = true := by native_decide
lemma reach_20 : reachesOne 20 100 = true := by native_decide

/-- D/U ratios all above threshold for numbers 1-20 -/
lemma du_above_1 : descentRatio 1 100 > gravityThreshold 3 := by native_decide
lemma du_above_2 : descentRatio 2 100 > gravityThreshold 3 := by native_decide
lemma du_above_3 : descentRatio 3 100 > gravityThreshold 3 := by native_decide
lemma du_above_4 : descentRatio 4 100 > gravityThreshold 3 := by native_decide
lemma du_above_5 : descentRatio 5 100 > gravityThreshold 3 := by native_decide
lemma du_above_6 : descentRatio 6 100 > gravityThreshold 3 := by native_decide
lemma du_above_7 : descentRatio 7 100 > gravityThreshold 3 := by native_decide
lemma du_above_8 : descentRatio 8 100 > gravityThreshold 3 := by native_decide
lemma du_above_9 : descentRatio 9 100 > gravityThreshold 3 := by native_decide
lemma du_above_10 : descentRatio 10 100 > gravityThreshold 3 := by native_decide
lemma du_above_11 : descentRatio 11 100 > gravityThreshold 3 := by native_decide
lemma du_above_12 : descentRatio 12 100 > gravityThreshold 3 := by native_decide
lemma du_above_13 : descentRatio 13 100 > gravityThreshold 3 := by native_decide
lemma du_above_14 : descentRatio 14 100 > gravityThreshold 3 := by native_decide
lemma du_above_15 : descentRatio 15 100 > gravityThreshold 3 := by native_decide
lemma du_above_16 : descentRatio 16 100 > gravityThreshold 3 := by native_decide
lemma du_above_17 : descentRatio 17 100 > gravityThreshold 3 := by native_decide
lemma du_above_18 : descentRatio 18 100 > gravityThreshold 3 := by native_decide
lemma du_above_19 : descentRatio 19 100 > gravityThreshold 3 := by native_decide
lemma du_above_20 : descentRatio 20 100 > gravityThreshold 3 := by native_decide

/-- 5n+1 step verification -/
lemma step_5n1_1 : generalizedStep 5 1 1 = 6 := by rfl
lemma step_5n1_3 : generalizedStep 5 1 3 = 16 := by rfl
lemma step_5n1_5 : generalizedStep 5 1 5 = 26 := by rfl

/-- 7n+1 step verification -/
lemma step_7n1_1 : generalizedStep 7 1 1 = 8 := by rfl
lemma step_7n1_3 : generalizedStep 7 1 3 = 22 := by rfl

/-- 9n+1 step verification -/
lemma step_9n1_1 : generalizedStep 9 1 1 = 10 := by rfl
lemma step_9n1_3 : generalizedStep 9 1 3 = 28 := by rfl

/-- 3n-1 step verification -/
lemma step_3nm1_5 : step3nm1 5 = 14 := by rfl
lemma step_3nm1_7 : step3nm1 7 = 20 := by rfl

/-- Collatz step function verification -/
lemma collatz_1 : collatzStep 1 = 4 := by rfl
lemma collatz_2 : collatzStep 2 = 1 := by rfl
lemma collatz_3 : collatzStep 3 = 10 := by rfl
lemma collatz_4 : collatzStep 4 = 2 := by rfl
lemma collatz_5 : collatzStep 5 = 16 := by rfl

/-- Trailing zeros verification -/
lemma tz_1 : countTrailingZeros 1 = 0 := by rfl
lemma tz_2 : countTrailingZeros 2 = 1 := by rfl
lemma tz_4 : countTrailingZeros 4 = 2 := by rfl
lemma tz_8 : countTrailingZeros 8 = 3 := by rfl
lemma tz_16 : countTrailingZeros 16 = 4 := by rfl

/-- Gravity thresholds for different multipliers -/
lemma gt_3 : gravityThreshold 3 = 1.585 := by native_decide
lemma gt_5 : gravityThreshold 5 = 2.322 := by native_decide
lemma gt_7 : gravityThreshold 7 = 2.807 := by native_decide
lemma gt_9 : gravityThreshold 9 = 3.170 := by native_decide

end DAP
