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


-- Prob 3
example (a b c : ℝ) (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) :
  (Real.sqrt (a^2 + a * b + b^2)
   + Real.sqrt (b^2 + b * c + c^2)
   + Real.sqrt (c^2 + c * a + a^2))
  ≤ Real.sqrt (5 * (a^2 + b^2 + c^2) + 4 * (a * b + b * c + c * a)) :=
by
  sorry


-- Prob 4
def seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| 3 => 3
| n + 1 => seq n + 2 * seq (n - 1) + seq (n - 2)

example (m : ℕ) (hm : m > 0) :
  ∃ n : ℕ, m ∣ seq n :=
by
  sorry

-- Prob 5

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

-- Proving 3

-- Proving 4

-- Proving 5
theorem theorem_337c29d8_7fce_47e8_97d8_b2489b8c61d5 (a : ℝ) :
(a^3 - a + 2)^2 > 4 * a^2 * (a^2 + 1) * (a - 2) :=
by {
    have h3 : (((a - 2) *  a^2) * ((a - 2) *  a^2) + 2 * a^4 + 5 * a^2 + (2*a - 1) * (2*a - 1) + 3) > 0 := by
      { nlinarith }
    have h1 : (a^3 - a + 2)^2 - 4 * a^2 * (a^2 + 1) * (a - 2) > 0
      {calc (a^3 - a + 2)^2 - 4 * a^2 * (a^2 + 1) * (a - 2)
       = ((a - 2) *  a^2) * ((a - 2) *  a^2) + (2 * a^4 + 5 * a^2 + (2*a - 1) * (2*a - 1) + 3) := by ring
       > 0 := by exact h3 }


}

example (a b : ℝ) (h: a - b > 0) : a > b  := by linarith
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

example (a : ℝ) : 2 * a^4 + 5 * a^2 + (2 * a - 1) * (2 * a - 1) + 3 > 0 := by {
  nlinarith
}
