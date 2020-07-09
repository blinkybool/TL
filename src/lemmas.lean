import definitions
import wellformedness
import tactic.tidy

namespace TT

lemma eq_sound {Γ} {A : type} {a₁ a₂ : term} (eq : ⊨ (a₁ ≃[A] a₂)) (φ : term) : entails Γ ⊤ (φ⁅a₁⁆) → entails Γ ⊤ (φ⁅a₂⁆) :=
by sorry

lemma reverse_extensionality (A : type) : ⊨ (∀' (𝒫 A) $ ∀' (𝒫 A) $ (↑1 ≃[𝒫 A] ↑0) ⟹ (∀' A ((↑0 ∈ ↑2) ⇔ (↑0 ∈ ↑1)))) :=
by sorry

open entails

variables {φ ψ : term}
variable {Γ : context}

lemma meta.from_ent {p} {wfP : WF [] Ω p} : entails Γ φ ψ  → entails Γ p φ → entails Γ p ψ :=
  λ _ _, (by {apply cut φ, tidy})

lemma meta.to_ent (wfφ : WF Γ Ω φ) : (∀ p, entails Γ p φ → entails Γ p ψ) → entails Γ φ ψ :=
  λ h, h φ (axm wfφ)

lemma meta.from_imp {p} : entails Γ p (φ ⟹ ψ) → (entails Γ p φ → entails Γ p ψ) :=
  λ imp hpφ, (begin
    apply cut (p ⋀ φ),
    apply and_intro,
      apply axm, exact WF.entails_left imp,
      exact hpφ,
    exact imp_to_and imp,
  end)

end TT