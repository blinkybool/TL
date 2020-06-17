import TL
import tactic.tidy

namespace TT

open proof


variables p q r φ ψ : term
variable {Γ : context}

lemma from_meta_imp (_ : WF Γ Ω φ) (_ : WF Γ Ω ψ) : (proof Γ ⊤ φ → proof Γ ⊤ ψ) → proof Γ φ ψ
  := sorry

lemma to_meta_imp : proof Γ φ ψ  → proof Γ ⊤ φ → proof Γ ⊤ ψ :=
  by {intros, apply proof.cut _ φ _, tidy}

lemma from_imp {Γ : context} : proof Γ ⊤ (q ⟹ r) → proof Γ q r :=
begin
  intro h₁,
  apply proof.cut _ (⊤ ⋀ q) _,
  apply_rules easy_proofs,
  repeat {
    apply @WF.imp_left _ q r,
    exact WF.proof_right _ _ h₁
  },
  exact proof.imp_to_and h₁,
end

lemma to_imp {Γ : context} : proof Γ q r → proof Γ ⊤ (q ⟹ r) :=
begin
  intro h₁,
  apply proof.and_to_imp,
  apply proof.cut _ q _,
  apply proof.and_right _ ⊤ _,
  apply proof.axm,
  apply WF.and,
  exact WF.top,
  apply WF.proof_left q r,
  tidy
end
lemma proof.or_inl (wfq : WF Γ Ω q) (prfp :proof Γ ⊤ p) : proof Γ ⊤ (p ⋁ q) :=
  by {apply proof.cut _ p _, assumption, apply proof.or_left _ q, apply proof.axm, apply_rules [WF.or, WF.proof_right]}
lemma proof.or_inr (wfq : WF Γ Ω p) (prfp :proof Γ ⊤ q) : proof Γ ⊤ (p ⋁ q) :=
  by {apply proof.cut _ q _, assumption, apply proof.or_right _ q, apply proof.axm, apply_rules [WF.or, WF.proof_right]}

lemma proof_of_and_left (_ : WF Γ Ω p) (_ : WF Γ Ω q) : proof Γ (p ⋀ q) p :=
  by {intros, apply proof.and_left _ p q, apply proof.axm, apply WF.and, tidy}
lemma proof_of_and_right (_ : WF Γ Ω p) (_ : WF Γ Ω q) : proof Γ (p ⋀ q) q :=
  by {apply proof.and_right _ p q, apply proof.axm, apply WF.and, tidy}

example (_ : WF Γ Ω p) (_ : WF Γ Ω q) : proof Γ (p ⋀ q) (q ⋀ p) :=
begin
  apply proof.and_intro,
  apply proof_of_and_right,
  tidy,
  apply proof_of_and_left,
  tidy
end

namespace proof
open term

lemma eq_sound {A : type} {a₁ a₂ : term} (eq : ⊨ (a₁ ≃[A] a₂)) (φ ψ : term) : proof Γ ⊤ ⁅φ // a₁⁆ → proof Γ ⊤ ⁅φ // a₂⁆ :=
  by sorry

lemma reverse_extensionality (A : type) : ⊨ (∀' (𝒫 A) $ ∀' (𝒫 A) $ (𝟙 ≃[𝒫 A] 𝟘) ⟹ (∀' A ((𝟘 ∈ 𝟙) ⇔ (𝟘 ∈ 𝟚)))) :=
begin
  apply proof.all_intro 𝒫 A,
  apply proof.all_intro 𝒫 A,
  apply to_imp,
  apply from_meta_imp,
  any_goals {apply_rules WF_rules; refl},
  intro h,
  sorry
end



end proof


end TT