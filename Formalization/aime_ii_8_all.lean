import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0

def PropertySet : Set ℕ := {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)}

theorem P2026AIMEII_8_bad : ∃ (P2026AIMEII_8_answer : Nat), ((IsLeast PropertySet) P2026AIMEII_8_answer) := by
  refine ⟨sInf PropertySet, ?_⟩
  have h : PropertySet.Nonempty := ⟨490, 20, 14, by norm_num [PropertySet]⟩
  exact ⟨Nat.sInf_mem h, fun y hy => Nat.sInf_le hy⟩

theorem P2026AIMEII_8_good : ∃ (P2026AIMEII_8_answer : Nat), ((IsLeast PropertySet) P2026AIMEII_8_answer) := by
  use (245 : Nat)
  sorry
