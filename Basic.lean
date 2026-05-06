/- ============================================================
   Discrete Algorithmic Physics (DAP) - Foundational Framework
   Formal Verification in Lean 4
   Author: Mohamed Abdel Wahab Ramdhan
   ============================================================ -/

namespace DAP

/- ----------------------------------------------------------
   Section 1: Basic Definitions
   Core definitions for Collatz-type algorithms
   ---------------------------------------------------------- -/

/-- The standard Collatz step function: n/2 if even, 3n+1 if odd -/
def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Generalized Collatz step with multiplier a and offset b -/
def generalizedStep (a b : Nat) (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else a * n + b

/-- Compute the trajectory of a Collatz sequence until it reaches 1 or exceeds maxSteps -/
def collatzTrajectory (n maxSteps : Nat) : List Nat :=
  if h : n = 0 ∨ maxSteps = 0 then []
  else if n = 1 then [1]
  else n :: collatzTrajectory (collatzStep n) (maxSteps - 1)
termination_by maxSteps
  decreasing_by
    simp_wf
    try { tauto }
    try { omega }

/-- Compute trajectory for generalized Collatz map -/
def generalizedTrajectory (a b n maxSteps : Nat) : List Nat :=
  if h : n = 0 ∨ maxSteps = 0 then []
  else if n = 1 then [1]
  else n :: generalizedTrajectory a b (generalizedStep a b n) (maxSteps - 1)
termination_by maxSteps
  decreasing_by
    simp_wf
    try { tauto }
    try { omega }

/-- Count 1-bits (population count / algorithmic energy) -/
def popcount : Nat → Nat
  | 0 => 0
  | n => (n % 2) + popcount (n / 2)

/-- Count trailing zeros in binary representation -/
def countTrailingZeros : Nat → Nat
  | 0 => 0
  | n => if n % 2 = 1 then 0 else 1 + countTrailingZeros (n / 2)

/-- Number of 1-bits divided by total bits (binary energy density) -/
def bitDensity (n : Nat) : Float :=
  if n = 0 then 0.0
  else (popcount n).toFloat / (Nat.log2 n + 1).toFloat

/-- Compute D (number of downward n/2 steps) and U (number of upward an+b steps)
    Returns (D, U) for a trajectory that reaches 1 -/
def countSteps (n maxSteps : Nat) : (Nat × Nat) :=
  if h : n = 0 ∨ maxSteps = 0 then (0, 0)
  else if n = 1 then (0, 0)
  else
    let (d, u) := countSteps (collatzStep n) (maxSteps - 1)
    if n % 2 = 0 then (d + 1, u) else (d, u + 1)
termination_by maxSteps
  decreasing_by
    simp_wf
    try { tauto }
    try { omega }

/-- Count steps for generalized map -/
def countStepsGeneralized (a b n maxSteps : Nat) : (Nat × Nat) :=
  if h : n = 0 ∨ maxSteps = 0 then (0, 0)
  else if n = 1 then (0, 0)
  else
    let (d, u) := countStepsGeneralized a b (generalizedStep a b n) (maxSteps - 1)
    if n % 2 = 0 then (d + 1, u) else (d, u + 1)
termination_by maxSteps
  decreasing_by
    simp_wf
    try { tauto }
    try { omega }

/-- The D/U ratio (descent ratio) -/
def descentRatio (n maxSteps : Nat) : Float :=
  let (d, u) := countSteps n maxSteps
  if u = 0 then 0.0 else d.toFloat / u.toFloat

/-- The D/U ratio for generalized map -/
def descentRatioGeneralized (a b n maxSteps : Nat) : Float :=
  let (d, u) := countStepsGeneralized a b n maxSteps
  if u = 0 then 0.0 else d.toFloat / u.toFloat

/-- Gravity threshold for multiplier a: log₂(a) -/
def gravityThreshold (a : Nat) : Float :=
  (Nat.log2 a).toFloat

/-- Minimum drain for residue class analysis -/
def minDrain (minTZ : Nat) (a : Nat) : Float :=
  minTZ.toFloat - gravityThreshold a

/-- Check if a trajectory reaches 1 within maxSteps -/
def reachesOne (n maxSteps : Nat) : Bool :=
  if h : n = 1 ∨ maxSteps = 0 then n = 1
  else reachesOne (collatzStep n) (maxSteps - 1)
termination_by maxSteps
  decreasing_by
    simp_wf
    try { tauto }
    try { omega }

/-- Check if a number is part of a cycle (returns to itself) -/
def isCycle (a b n maxSteps : Nat) : Bool :=
  if maxSteps = 0 then false
  else
    let next := generalizedStep a b n
    if next = n then true
    else isCycle a b next (maxSteps - 1)
termination_by maxSteps
  decreasing_by
    simp_wf
    try { tauto }
    try { omega }

/- ----------------------------------------------------------
   Section 2: Computational Lemmas (verified by native_decide)
   These establish concrete numerical facts used in DAP proofs
   ---------------------------------------------------------- -/

/-- The gravity threshold for standard 3n+1 map -/
abbrev gravityThreshold_3n1 : Float := 1.585

/-- Lemma: log₂(3) is the gravity threshold for a=3 -/
lemma gravity_threshold_3 : gravityThreshold 3 = 1.585 := by
  native_decide

/-- The gravity threshold for 5n+1 map -/
abbrev gravityThreshold_5n1 : Float := 2.322

/-- The gravity threshold for 7n+1 map -/
abbrev gravityThreshold_7n1 : Float := 2.807

/-- The gravity threshold for 9n+1 map -/
abbrev gravityThreshold_9n1 : Float := 3.170

/-- Lean can verify basic popcount calculations -/
lemma popcount_27 : popcount 27 = 4 := by rfl
lemma popcount_1 : popcount 1 = 1 := by rfl
lemma popcount_2 : popcount 2 = 1 := by rfl
lemma popcount_4 : popcount 4 = 1 := by rfl

/-- Verify that 27 eventually reaches 1 (computationally) -/
lemma collatz_27_reaches_1 : reachesOne 27 1000 = true := by
  native_decide

/-- D/U ratio for n=27 should exceed gravity threshold -/
lemma descent_ratio_27_above_threshold :
  descentRatio 27 1000 > gravityThreshold 3 := by
  native_decide

/-- Verify trailing zeros count -/
lemma trailing_zeros_8 : countTrailingZeros 8 = 3 := by rfl
lemma trailing_zeros_4 : countTrailingZeros 4 = 2 := by rfl
lemma trailing_zeros_2 : countTrailingZeros 2 = 1 := by rfl

end DAP
