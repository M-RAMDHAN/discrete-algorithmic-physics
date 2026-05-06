/- ============================================================
   DAP Rule 7: Catalytic Reversal Law (Chemistry)
   The algorithmic analog of molecular chirality
   ============================================================ -/

import DAP.Basic

namespace DAP

/- ----------------------------------------------------------
   The Catalytic Reversal Law establishes that when the
   multiplier a changes parity class modulo 4, the catalytic
   residue class reverses:

   For a ≡ 3 (mod 4): n ≡ 1 (mod 4) is catalytic (TZ ≥ 2)
   For a ≡ 1 (mod 4): n ≡ 3 (mod 4) is catalytic (TZ ≥ 2)

   This is the algorithmic analog of molecular chirality:
   the same structural mechanism, but mirrored.
   ---------------------------------------------------------- -/

/-- For a ≡ 3 (mod 4) and n ≡ 1 (mod 4): (an+1) ≡ 0 (mod 4) -/
theorem catalytic_a3_n1 (a n : Nat) :
  a % 4 = 3 → n % 4 = 1 → (a * n + 1) % 4 = 0 := by
  intros ha hn
  have h1 : a % 4 = 3 := ha
  have h2 : n % 4 = 1 := hn
  have h3 : a * n % 4 = 3 := by
    simp [Nat.mul_mod, h1, h2]
  omega

/-- For a ≡ 1 (mod 4) and n ≡ 3 (mod 4): (an+1) ≡ 0 (mod 4) -/
theorem catalytic_a1_n3 (a n : Nat) :
  a % 4 = 1 → n % 4 = 3 → (a * n + 1) % 4 = 0 := by
  intros ha hn
  have h1 : a % 4 = 1 := ha
  have h2 : n % 4 = 3 := hn
  have h3 : a * n % 4 = 3 := by
    simp [Nat.mul_mod, h1, h2]
  omega

/-- For a ≡ 3 (mod 4) and n ≡ 3 (mod 4): (an+1) ≡ 2 (mod 4) -/
theorem inhibitory_a3_n3 (a n : Nat) :
  a % 4 = 3 → n % 4 = 3 → (a * n + 1) % 4 = 2 := by
  intros ha hn
  have h1 : a % 4 = 3 := ha
  have h2 : n % 4 = 3 := hn
  have h3 : a * n % 4 = 1 := by
    simp [Nat.mul_mod, h1, h2]
  omega

/-- For a ≡ 1 (mod 4) and n ≡ 1 (mod 4): (an+1) ≡ 2 (mod 4) -/
theorem inhibitory_a1_n1 (a n : Nat) :
  a % 4 = 1 → n % 4 = 1 → (a * n + 1) % 4 = 2 := by
  intros ha hn
  have h1 : a % 4 = 1 := ha
  have h2 : n % 4 = 1 := hn
  have h3 : a * n % 4 = 1 := by
    simp [Nat.mul_mod, h1, h2]
  omega

/-- Definition: The catalytic residue class for multiplier a -/
def catalyticClass (a : Nat) : Nat :=
  if a % 4 = 3 then 1
  else if a % 4 = 1 then 3
  else 0  -- undefined for even a

/-- Definition: The inhibitory residue class for multiplier a -/
def inhibitoryClass (a : Nat) : Nat :=
  if a % 4 = 3 then 3
  else if a % 4 = 1 then 1
  else 0  -- undefined for even a

/-- Catalytic Reversal Theorem: the catalytic class reverses
    when a changes parity mod 4 -/
theorem catalytic_reversal (a : Nat) (ha : a % 2 = 1 ∧ a > 1) :
  (a % 4 = 3 → catalyticClass a = 1 ∧ inhibitoryClass a = 3) ∧
  (a % 4 = 1 → catalyticClass a = 3 ∧ inhibitoryClass a = 1) := by
  constructor
  · intro ha3
    simp [catalyticClass, inhibitoryClass, ha3]
  · intro ha1
    simp [catalyticClass, inhibitoryClass, ha1]

/-- For a = 3 (≡ 3 mod 4): catalytic is n ≡ 1 -/
lemma catalytic_3 : catalyticClass 3 = 1 := by rfl
lemma inhibitory_3 : inhibitoryClass 3 = 3 := by rfl

/-- For a = 5 (≡ 1 mod 4): catalytic is n ≡ 3 -/
lemma catalytic_5 : catalyticClass 5 = 3 := by rfl
lemma inhibitory_5 : inhibitoryClass 5 = 1 := by rfl

/-- For a = 7 (≡ 3 mod 4): catalytic is n ≡ 1 -/
lemma catalytic_7 : catalyticClass 7 = 1 := by rfl
lemma inhibitory_7 : inhibitoryClass 7 = 3 := by rfl

/-- For a = 9 (≡ 1 mod 4): catalytic is n ≡ 3 -/
lemma catalytic_9 : catalyticClass 9 = 3 := by rfl
lemma inhibitory_9 : inhibitoryClass 9 = 1 := by rfl

/-- The reversal is confirmed: for a=3 vs a=5, the classes swap -/
theorem reversal_3_vs_5 :
  catalyticClass 3 = inhibitoryClass 5 ∧
  inhibitoryClass 3 = catalyticClass 5 := by
  constructor <;> rfl

/-- Verified in Lean 4: the 3n-1 map has its catalytic class
    at n ≡ 3 (mod 4) (because 3 ≡ 3 mod 4, catalytic is n ≡ 1,
    but wait -- for 3n-1 the offset is -1, not +1)
    
    For 3n-1 with n ≡ 3 (mod 4): 3*3-1 = 8 ≡ 0 (mod 4)
    This is why 3n-1 has ordered behavior too! -/
theorem mod4_3nm1_catalytic (n : Nat) :
  n % 4 = 3 → (3 * n - 1) % 4 = 0 := by
  intro h
  have h1 : n % 4 = 3 := h
  have h2 : 3 * n % 4 = 1 := by
    omega
  omega

/-- For 3n-1, n ≡ 1 (mod 4): 3*1-1 = 2 ≡ 2 (mod 4) -/
theorem mod4_3nm1_inhibitory (n : Nat) :
  n % 4 = 1 → (3 * n - 1) % 4 = 2 := by
  intro h
  have h1 : n % 4 = 1 := h
  have h2 : 3 * n % 4 = 3 := by
    omega
  omega

/-- The 3n-1 map is the "mirror image" of 3n+1 -/
theorem mirror_3n1_vs_3nm1 :
  catalyticClass 3 = 1 ∧
  (∀ n : Nat, n % 4 = 1 → (3 * n + 1) % 4 = 0) ∧
  (∀ n : Nat, n % 4 = 3 → (3 * n - 1) % 4 = 0) := by
  constructor
  · rfl
  constructor
  · intro n hn
    exact mod4_catalytic_3n1 n hn
  · intro n hn
    exact mod4_3nm1_catalytic n hn

end DAP
