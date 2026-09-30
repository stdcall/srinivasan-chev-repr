import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.Group

namespace Srinivasan

/-- Equality of Lang-map values is exactly the fixed-point condition on
the right quotient. This proves the fibre/coset calculation; it does not
prove finiteness of rational points or surjectivity of the Lang map. -/
theorem lang_fibre_iff {G : Type*} [Group G] (F : G →* G) (x y : G) :
    x * (F x)⁻¹ = y * (F y)⁻¹ ↔ F (y⁻¹ * x) = y⁻¹ * x := by
  constructor
  · intro h
    have hx : x = y * (F y)⁻¹ * F x := by
      calc
        x = x * (F x)⁻¹ * F x := by group
        _ = y * (F y)⁻¹ * F x := by rw [h]
    calc
      F (y⁻¹ * x) = (F y)⁻¹ * F x := by simp
      _ = y⁻¹ * (y * (F y)⁻¹ * F x) := by group
      _ = y⁻¹ * x := by rw [← hx]
  · intro h
    have hf : (F y)⁻¹ * F x = y⁻¹ * x := by simpa using h
    calc
      x * (F x)⁻¹ = y * (y⁻¹ * x) * (F x)⁻¹ := by group
      _ = y * ((F y)⁻¹ * F x) * (F x)⁻¹ := by rw [← hf]
      _ = y * (F y)⁻¹ := by group

end Srinivasan

#print axioms Srinivasan.lang_fibre_iff
