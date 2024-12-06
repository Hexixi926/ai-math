-- This module serves as the root of the `Foo` library.
-- Import modules here that should be built as part of the library.
import «Foo».Basic
import «Foo».Minif2fImport



-- Prob 1
example (f : ℝ → ℝ) (h1 : f 0 = 0) (h2 : ∀ x : ℝ, f (2 * x) = Real.sin x + f x) :
f 1 < 1 :=
by
  sorry

-- Prob 2
def find_co_prime_larger_than_aux : ℕ → ℕ → ℕ
| 0, _  => 0
| (m + 1), n =>
  if Nat.gcd (n + 1) 105 = 1 then
    n + 1
  else
    find_co_prime_larger_than_aux m (n + 1)

def find_co_prime_larger_than (n : ℕ) : ℕ :=
  find_co_prime_larger_than_aux 105 n

def seq : ℕ → ℕ
| 0 => 0
| n + 1 => find_co_prime_larger_than (seq n)

example : seq 1000 = 2186 :=
by
  sorry

-- Prob 3
example (a b c : ℝ) (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) :
  (Real.sqrt (a^2 + a * b + b^2)
   + Real.sqrt (b^2 + b * c + c^2)
   + Real.sqrt (c^2 + c * a + a^2))
  ≤ Real.sqrt (5 * (a^2 + b^2 + c^2) + 4 * (a * b + b * c + c * a)) :=
by
  sorry


-- Prob 4
def seq2 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| 3 => 3
| n + 1 => seq2 n + 2 * seq2 (n - 1) + seq2 (n - 2)

example (m : ℕ) (hm : m > 0) :
  ∃ n : ℕ, m ∣ seq2 n :=
by
  sorry

-- Prob 5
def f (xset : Finset ℝ) (x : ℝ) : ℝ :=
  xset.prod (λ root => x - root)
def in_interval (x : ℝ) : Prop :=
  x ≤ 1 ∧ x ≥ -1
example (xset : Finset ℝ) (a b : ℝ) (h_xset : ∀ x ∈ xset, in_interval x) (ha : a > -1 ∧ a < 0) (hb : b > 0 ∧ b < 1) :
  min (abs (f xset a)) (abs (f xset b)) < 1 :=
by
  sorry






-- Proving 1
theorem theorem_5fdfb072_cf0d_4e11_bd2a_0934958add04 (a : ℝ) (h : a = 10) :
Real.sqrt (10 * 4 * 3 * 3) = 6 * Real.sqrt 10 :=
by {
    have thirtysix : (4 : ℝ) * (3 : ℝ) * (3 : ℝ)  = (6 : ℝ) * (6 : ℝ)
      := by norm_num
    simp [thirtysix ,mul_assoc, Real.mul_self_sqrt]
    rw [mul_comm]
}

-- Proving 2
theorem theorem_394a1998_91a8_40a3_80d4_d8426d461b0c (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b + 1 / (a * b) = 6) :
(a + 1) * (b + 1) ≥ 2 :=
by {
    let t := a * b
    have a_plus_b_nonneg : 0 ≤ a+b := by {
      apply le_of_lt
      exact Right.add_pos' ha hb
    }
    have am_gm : a+b ≥ 2 * Real.sqrt (a*b) := by {
    simp
    apply nonneg_le_nonneg_of_sq_le_sq a_plus_b_nonneg
    ring_nf
    rw [Real.sq_sqrt]
    rw [← sub_nonneg]
    have : a*b*2 + a^2 + b^2 - a*b*4 = (a-b)^2 := by {
      ring_nf
      rw [this]
      exact sq_nonneg (a - b)
      assumption
    }
    have h0 : (a+1) * (b+1) ≥ t + 2 * Real.sqrt t + 1 := by {
    calc
      (a+1) * (b+1)
        = a*b + (a+b) + 1 := by ring_nf
      _ ≥ (a*b) + (2*Real.sqrt (a*b)) + 1 := by simp [am_gm]
      _ = t + 2*Real.sqrt t + 1 := by ring_nf
    }
    have h1 : t + 1 / t = 6 := by {exact hab}
    have h2 : t = 6 - 1/t := by {linarith}
    have t_eq : (t - 3)^2 = 8 := by {
      calc
          (t-3)^2
            = (t^2-6*t+1) + 8 := by ring_nf
          _ = 8 := by {
            simp [hab]
            field_simp at hab
            calc
              t^2-6*t+1 = (t*t+1) - (6*t) := by ring_nf
              _ = (6*t) - (6*t) := by rw [hab]
              _ = 0 := by ring_nf
            }
    }
    have value_t : t = 3 + Real.sqrt 8 ∨ t = 3 - Real.sqrt 8 := by {
      by_cases h: t-3 ≥ 0
      case pos =>
          left
          calc
              t = (t-3) + 3 := by ring_nf
              _ = Real.sqrt ((t-3)^2) + 3 := by rw [Real.sqrt_sq h]
              _ = Real.sqrt 8 + 3 := by simp [t_eq]
              _ = 3 + Real.sqrt 8 := by simp [add_comm]
      case neg =>
          right
          apply le_of_not_ge at h
          calc
              t = (t - 3) + 3 := by ring_nf
              _ = - Real.sqrt ( (3-t)^2) + 3 := by {
                  rw [Real.sqrt_sq]
                  ring_nf
                  simp [h]
                  simp at h
                  exact h
              }
              _ = - Real.sqrt ((t-3)^2)+3 := by ring_nf
              _ = - Real.sqrt 8 + 3 := by simp [t_eq]
              _ = 3 - Real.sqrt 8 := by {
                  simp [add_comm]
                  ring_nf
              }
    }
    cases val_x with
  | inl val_x_1 => {
    rw [val_x_1]
    simp_quadratic_ineq
    exact Real.sqrt_nonneg 8
  }
  | inr val_x_2 => {
    rw [val_x_2]
    simp_quadratic_ineq
  }
}
}
-- Proving 3
open BigOperators
theorem theorem_1abfa71b_2e7e_4b59_9af1_cb16f6cafea1 (i k : ℕ) (h₁ : k ≤ i) :
(∑ n in Finset.Icc k i, Nat.choose n k) = Nat.choose (i + 1) (k + 1) :=
by {exact Nat.sum_Icc_choose i k}


-- Proving 4
theorem theorem_f000e48f_6f30_408a_ac91_493fff4521d6 (f : ℕ → ℕ) (hf: f 1 = 1) (hf1: ∀ m n: ℕ, f (m + n) = f m + f n + m * n):
∀ n:ℕ, f n = n  * (n + 1) / 2 :=
by {
    have hf2 : ∀ m, f (m + 1) = f m + 1 + m :=
        λ m => by rw [hf1 m 1, hf, mul_one]
    intro n
    induction n with
    | zero => {
        specialize hf1 0 1
        simp at hf1
        exact hf1
    }
    | succ n0 hfn0 => {
        rw [hf2 n0, hfn0, Nat.succ_eq_add_one]
        have hhh (n:ℕ): 2 * ((n*(n+1)) / 2) = n * (n+1) := by
        {
            refine Nat.mul_div_cancel' ?this.H
            refine Nat.dvd_of_mod_eq_zero ?this.H.H
            induction n with
            | zero => simp
            | succ n1 even_n1 => {
                rw [Nat.succ_eq_add_one, mul_add, add_mul, add_assoc, Nat.add_mod, even_n1 ]
                simp
                rw [← mul_two]
                simp
            }
        }
        have hh (n : ℕ ): n * (n + 1)  + 2 * (1 + n)  = (n + 1) * (n + 2) := by ring
        specialize hh n0
        rw [← hhh n0, ← hhh (n0 + 1) ] at hh
        linarith
    }
}



-- Proving 5
theorem theorem_337c29d8_7fce_47e8_97d8_b2489b8c61d5 (a : ℝ) :
(a^3 - a + 2)^2 > 4 * a^2 * (a^2 + 1) * (a - 2) :=
by {
    have h1 : (a^3 - a + 2)^2 - 4 * a^2 * (a^2 + 1) * (a - 2) > 0 := by
      {calc (a^3 - a + 2)^2 - 4 * a^2 * (a^2 + 1) * (a - 2)
       _ = ((a - 2) *  a^2) * ((a - 2) *  a^2) + 2 * a^4 + 5 * a^2 + (2*a - 1) * (2*a - 1) + 3 := by ring_nf
       _ > 0 := by nlinarith }
    linarith
}

















-- -- induction n with
--             -- | zero => simp
--             -- | succ n1 hhhn1 => {
--             --     rw [Nat.succ_eq_add_one, mul_add, add_mul]
--             --     calc 2 * ((n1 * (n1 + 1) + 1 * (n1 + 1) + (n1 + 1) * 1) / 2)
--             --       = 2 * ((n1 * (n1 + 1) + 2 * (n1 + 1)) / 2) := by ring_nf
--             --     _ = 2 * ((n1 * (n1 + 1) / 2 + (n1 + 1))) := by rw[Nat.add_mul_div_left]

--             -- }

-- example (a b : ℝ) (h: a - b > 0) : a > b  := by linarith
-- variable (α : Type) (a b c d : α)
-- variable (hab : a = b) (hcb : c = b) (hcd : c = d)

-- example : a = d :=
--   Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

-- example (a : ℝ) : 2 * a^4 + 5 * a^2 + (2 * a - 1) * (2 * a - 1) + 3 > 0 := by {
--   nlinarith
-- }

-- example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
--   induction x, y using Nat.mod.inductionOn with
--   | ind x y h₁ ih =>
--     rw [Nat.mod_eq_sub_mod h₁.2]
--     exact ih h
--   | base x y h₁ =>
--     have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
--     match this with
--     | Or.inl h₁ => exact absurd h h₁
--     | Or.inr h₁ =>
--       have hgt : y > x := Nat.gt_of_not_le h₁
--       rw [← Nat.mod_eq_of_lt hgt] at hgt
--       assumption



-- def coprime_with_105 (n : ℕ) : Prop :=
-- Nat.gcd n 105 = 1

-- example (n0 : ℕ) : n0 * (n0 + 1) / 2 = (n0 + 1) * n0 / 2 :=
-- by {rw [mul_comm n0 (n0 + 1)]}
