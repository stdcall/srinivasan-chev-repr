import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-!
Chapter I, Bruhat refinement: the group-theoretic uniqueness step.

H is the restricted unipotent factor U ∩ w U⁻ w⁻¹, K is the Borel
subgroup on the right. The hypothesis says H ∩ w K w⁻¹ = {1}.
That structural intersection statement follows from opposite root
subgroups in the algebraic-group argument; it is NOT proved here.

This lemma establishes uniqueness of the pair in h w k under that
intersection hypothesis. It does not establish existence of Bruhat
factorizations, uniqueness of the Weyl group element, or splitting
the Borel factor as a torus factor times a unipotent factor.
-/
namespace Srinivasan

variable {G : Type*} [Group G]

theorem bruhat_factor_unique (H K : Subgroup G) (w : G)
    (h_inter : ∀ g ∈ H, w⁻¹ * g * w ∈ K → g = 1)
    (h₁ h₂ k₁ k₂ : G) (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (heq : h₁ * w * k₁ = h₂ * w * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have hrel : w⁻¹ * (h₂⁻¹ * h₁) * w = k₂ * k₁⁻¹ := by
    calc
      w⁻¹ * (h₂⁻¹ * h₁) * w =
          w⁻¹ * h₂⁻¹ * (h₁ * w * k₁) * k₁⁻¹ := by group
      _ = w⁻¹ * h₂⁻¹ * (h₂ * w * k₂) * k₁⁻¹ := by rw [heq]
      _ = k₂ * k₁⁻¹ := by group
  have hone : h₂⁻¹ * h₁ = 1 :=
    h_inter _ (H.mul_mem (H.inv_mem hh₂) hh₁)
      (hrel ▸ K.mul_mem hk₂ (K.inv_mem hk₁))
  have hsame : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by group
      _ = h₂ := by rw [hone, mul_one]
  have ksame : k₁ = k₂ := by
    apply mul_left_cancel (a := h₂ * w)
    simpa [hsame] using heq
  exact ⟨hsame, ksame⟩

end Srinivasan

#print axioms Srinivasan.bruhat_factor_unique
