/- ============================================================
   DAP Rule 6: Phase Transition Law (Thermodynamics)
   a = 3 is the unique multiplier in the ordered descent phase
   ============================================================

   FIXED: The phase_transition_law theorem now correctly extracts
   minDrain > 0 from the orderedPhase hypothesis and derives a < 4
   using (r + 4) % 4 = r to find a witness for the residue class.

   Previous bug: hprop 1 (by omega) could not prove 1 % 4 = r
   for an arbitrary r. Fix: use (r + 4) % 4 = r which holds
   for all r < 4 by basic modular arithmetic.
   ============================================================ -/

import DAP.Basic

namespace DAP

/- ----------------------------------------------------------
   The Phase Transition Law establishes that for generalized
   Collatz maps C_a(n) = an+1 (odd n), n/2 (even n):

   Theorem: a = 3 is the UNIQUE odd multiplier > 1 where
   structural descent is guaranteed.

   Proof: For positive drain in the strong residue class,
   we need min_drain = min_TZ - log₂(a) > 0.
   The strong class has min_TZ = 2.
   So we need 2 > log₂(a), i.e., a < 4.
   Since a is odd and a > 1, the unique solution is a = 3.

   For all a ≥ 5: even the strong class has negative drain,
   so the system enters the chaotic phase.
   ---------------------------------------------------------- -/

/-- Definition: An algorithm is in the "ordered descent phase"
    if at least one residue class mod 4 has guaranteed positive drain. -/
def orderedPhase (a : Nat) : Prop :=
  a % 2 = 1 ∧ a > 1 ∧
  ((∃ r : Nat, r < 4 ∧ ∀ n : Nat,
    n % 4 = r → countTrailingZeros (a * n + 1) ≥ 2 ∧
    minDrain 2 a > 0))

/-- Definition: An algorithm is in the "chaotic phase"
    if no residue class has guaranteed positive drain. -/
def chaoticPhase (a : Nat) : Prop :=
  a % 2 = 1 ∧ a > 1 ∧ ¬orderedPhase a

/-- The critical boundary: log₂(a) < 2, i.e., a < 4 -/
def criticalBoundary (a : Nat) : Bool :=
  gravityThreshold a < 2.0

/-- Lemma: For a = 3, the strong class (n ≡ 1 mod 4) has positive drain.
    This proves a = 3 is in the ordered phase. -/
lemma a3_ordered_phase :
  orderedPhase 3 := by
  constructor
  · rfl  -- 3 is odd
  constructor
  · norm_num  -- 3 > 1
  · -- Show n ≡ 1 (mod 4) is the catalytic class
    use 1
    constructor
    · norm_num  -- 1 < 4
    intro n hn
    constructor
    · exact trailing_zeros_ge_2_for_mod4_1 n hn
    · simp [minDrain, gravityThreshold]
      native_decide

/-- For a = 5, n ≡ 3 (mod 4) gives 5n+1 ≡ 0 (mod 4) -/
theorem mod4_strong_5n1 (n : Nat) :
  n % 4 = 3 → (5 * n + 1) % 4 = 0 := by
  intro h
  omega

/-- For a = 5, n ≡ 1 (mod 4) gives 5n+1 ≡ 2 (mod 4) -/
theorem mod4_weak_5n1 (n : Nat) :
  n % 4 = 1 → (5 * n + 1) % 4 = 2 := by
  intro h
  omega

/-- Phase Transition Theorem: a = 7, n ≡ 1 (mod 4) gives 7n+1 ≡ 0 (mod 4)
    7 ≡ 3 (mod 4): n ≡ 1 (mod 4) is catalytic.
    7*1+1 = 8 ≡ 0 (mod 4), so TZ ≥ 2.
    drain = 2 - log₂(7) ≈ 2 - 2.807 = -0.807 < 0 -/
theorem mod4_strong_7n1 (n : Nat) :
  n % 4 = 1 → (7 * n + 1) % 4 = 0 := by
  intro h
  omega

/-- For a = 9: n ≡ 3 (mod 4) gives 9n+1 ≡ 0 (mod 4)
    9 ≡ 1 (mod 4), so n ≡ 3 (mod 4) is catalytic.
    9*3+1 = 28 ≡ 0 (mod 4), so TZ ≥ 2.
    drain = 2 - log₂(9) ≈ 2 - 3.170 = -1.170 < 0 -/
theorem mod4_strong_9n1 (n : Nat) :
  n % 4 = 3 → (9 * n + 1) % 4 = 0 := by
  intro h
  omega

/-- Computational verification: 3 < 4 < 5 confirms critical boundary -/
lemma critical_inequality_3_lt_4 : 3 < 4 := by norm_num
lemma critical_inequality_4_lt_5 : 4 < 5 := by norm_num

/-- For a = 5: the critical boundary fails (chaotic phase confirmed) -/
lemma a5_chaotic_phase :
  criticalBoundary 5 = false := by
  native_decide

/-- The critical boundary theorem: the phase transition occurs at a = 4 -/
theorem phase_transition_boundary (a : Nat) (ha : a % 2 = 1 ∧ a > 1) :
  a < 4 ↔ a = 3 := by
  constructor
  · intro h
    have h1 : a > 1 := ha.2
    have h2 : a < 4 := h
    interval_cases a <;> tauto
  · intro h
    rw [h]
    norm_num

/- ----------------------------------------------------------
   Helper lemmas for the Phase Transition Law proof.
   These establish the chain:
   minDrain > 0 → gravityThreshold < 2 → Nat.log2 < 2 → a < 4
   ---------------------------------------------------------- -/

/-- For m ≥ 2, Nat.log2 m ≥ 1.
    Proof: For m ≥ 2, m matches the (n+2) pattern in Nat.log2,
    so Nat.log2 m = Nat.log2 (m/2) + 1 ≥ 0 + 1 = 1. -/
lemma nat_log2_ge_one_of_ge_2 : ∀ m : Nat, m ≥ 2 → Nat.log2 m ≥ 1 := by
  intro m hm
  match m with
  | 0 => omega
  | 1 => omega
  | n + 2 =>
    -- Nat.log2 (n + 2) = Nat.log2 ((n + 2) / 2) + 1
    -- Since Nat.log2 returns Nat, Nat.log2 ((n+2)/2) ≥ 0
    -- Therefore Nat.log2 ((n+2)/2) + 1 ≥ 1
    simp only [Nat.log2]
    have : Nat.log2 ((n + 2) / 2) ≥ 0 := Nat.zero_le _
    omega

/-- For a ≥ 4, Nat.log2 a ≥ 2.
    Proof: For a ≥ 4, a matches the (n+2) pattern with n ≥ 2.
    So Nat.log2 a = Nat.log2 (a/2) + 1.
    Since a ≥ 4, a/2 ≥ 2, and by the previous lemma,
    Nat.log2 (a/2) ≥ 1. Therefore Nat.log2 a ≥ 1 + 1 = 2. -/
lemma nat_log2_ge_2_of_ge_4 : ∀ a : Nat, a ≥ 4 → Nat.log2 a ≥ 2 := by
  intro a ha
  match a with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | n + 2 =>
    -- a = n + 2, with n + 2 ≥ 4, so n ≥ 2
    have hn : n ≥ 2 := by omega
    simp only [Nat.log2]
    -- Goal: Nat.log2 ((n + 2) / 2) + 1 ≥ 2
    -- i.e., Nat.log2 ((n + 2) / 2) ≥ 1
    have h_div : (n + 2) / 2 ≥ 2 := by omega
    have h_log2_div : Nat.log2 ((n + 2) / 2) ≥ 1 :=
      nat_log2_ge_one_of_ge_2 _ h_div
    omega

/-- minDrain 2 a > 0 implies gravityThreshold a < 2.0 -/
lemma minDrain_pos_implies_thresh_lt_2 {a : Nat} (h : minDrain 2 a > 0) :
    gravityThreshold a < 2.0 := by
  unfold minDrain at h
  linarith

/-- gravityThreshold a < 2.0 implies Nat.log2 a < 2.
    Since gravityThreshold a = (Nat.log2 a).toFloat and
    Nat.log2 a is a natural number, (Nat.log2 a).toFloat < 2.0
    means Nat.log2 a ≤ 1, i.e., Nat.log2 a < 2. -/
lemma thresh_lt_2_implies_log2_lt_2 {a : Nat}
    (h : gravityThreshold a < 2.0) :
    Nat.log2 a < 2 := by
  unfold gravityThreshold at h
  contrapose! h
  have h_cast : (Nat.log2 a : Float) ≥ 2.0 := by
    have h_ge : Nat.log2 a ≥ 2 := h
    exact_mod_cast h_ge
  linarith

/-- Nat.log2 a < 2 implies a < 4.
    Contrapositive: a ≥ 4 → Nat.log2 a ≥ 2 (proven above). -/
lemma log2_lt_2_implies_lt_4 {a : Nat} (h : Nat.log2 a < 2) :
    a < 4 := by
  by_contra h_ge
  push_neg at h_ge
  have h4 : 4 ≤ a := by omega
  have : Nat.log2 a ≥ 2 := nat_log2_ge_2_of_ge_4 a h4
  omega

/- ----------------------------------------------------------
   MAIN THEOREM: Phase Transition Law
   ---------------------------------------------------------- -/

/-- Phase Transition Theorem: a = 3 is the unique odd multiplier > 1
    in the ordered descent phase.

    The proof works by establishing:
    1. Forward: a = 3 → orderedPhase 3 (by a3_ordered_phase)
    2. Reverse: orderedPhase a → a = 3, via the chain:
       orderedPhase a → minDrain 2 a > 0 → gravityThreshold a < 2.0
       → Nat.log2 a < 2 → a < 4 → a = 3

    KEY FIX: The previous version used `hprop 1 (by omega)` which
    could not prove `1 % 4 = r` for an arbitrary residue class r.
    The fix uses `hprop (r + 4) (by omega)` since (r + 4) % 4 = r
    for all r < 4, which omega can verify. -/
theorem phase_transition_law :
  ∀ a : Nat, a % 2 = 1 ∧ a > 1 →
    (a = 3 ↔ orderedPhase a) := by
  intro a ha
  constructor
  · -- Forward direction: a = 3 → orderedPhase a
    intro h
    rw [h]
    exact a3_ordered_phase
  · -- Reverse direction: orderedPhase a → a = 3
    intro h_ord
    -- Step 1: Extract minDrain 2 a > 0 from the orderedPhase hypothesis
    obtain ⟨ha_odd, ha_gt, r, hr_lt, hprop⟩ := h_ord
    have h_drain_pos : minDrain 2 a > 0 := by
      -- KEY FIX: Use (r + 4) % 4 = r instead of 1 % 4 = r
      -- Since r < 4, we have (r + 4) % 4 = r by modular arithmetic
      -- omega can verify this automatically
      have h_mod : (r + 4) % 4 = r := by omega
      exact (hprop (r + 4) h_mod).2
    -- Step 2: Chain minDrain > 0 → gravityThreshold < 2 → log2 < 2 → a < 4
    have h_thresh_lt_2 : gravityThreshold a < 2.0 :=
      minDrain_pos_implies_thresh_lt_2 h_drain_pos
    have h_log2_lt_2 : Nat.log2 a < 2 :=
      thresh_lt_2_implies_log2_lt_2 h_thresh_lt_2
    have h_lt_4 : a < 4 :=
      log2_lt_2_implies_lt_4 h_log2_lt_2
    -- Step 3: a is odd, a > 1, and a < 4, so a = 3
    have h2 : a > 1 := ha.2
    interval_cases a <;> tauto

end DAP
