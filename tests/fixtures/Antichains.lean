import Mathlib.Order.Antichain
import Mathlib.Data.Finset.Basic

namespace AntichainExamples

theorem finite_family (𝒜 : Finset (Finset ℕ))
    (h : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset ℕ))) :
    IsAntichain (· ⊆ ·) (𝒜 : Set (Finset ℕ)) := h

theorem arbitrary_relation (r : Finset ℕ → Finset ℕ → Prop) (ℱ : Set (Finset ℕ))
    (h : IsAntichain r ℱ) : IsAntichain r ℱ := h

theorem different_arguments (ℬ : Set (Finset ℕ))
    (h : IsAntichain (fun s _ : Finset ℕ => s ⊆ s) ℬ) :
    IsAntichain (fun s _ : Finset ℕ => s ⊆ s) ℬ := h

theorem distinct_binders (K 𝕜 : Type) (𝒜 𝒜₁ : K → 𝕜) (h : 𝒜 = 𝒜₁) : 𝒜 = 𝒜₁ := h

theorem other_subset (c : HasSubset (Finset ℕ)) (ℱ : Set (Finset ℕ))
    (h : IsAntichain (@HasSubset.Subset _ c) ℱ) : IsAntichain (@HasSubset.Subset _ c) ℱ := h

end AntichainExamples
