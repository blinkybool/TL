import definitions
import wellformedness
import tactic

namespace TT

variables p q r φ ψ : term
variable {Γ : context}

lemma from_imp {Γ : context} : entails Γ ⊤ (q ⟹ r) → entails Γ q r :=
begin
  intro h₁,
  apply entails.cut _ (⊤ ⋀ q) _,
  apply_rules [entails.and_intro, entails.vac, entails.axm];
    { apply @WF.imp_left _ q r,
      exact WF.proof_right h₁
    },
  exact entails.imp_to_and h₁,
end

lemma to_imp {Γ : context} : entails Γ q r → entails Γ ⊤ (q ⟹ r) :=
begin
  intro h₁,
  apply_rules [entails.and_to_imp, entails.cut _ q _, entails.and_right _ ⊤ _, entails.axm],
  WF_prover,
  apply WF.proof_left h₁,
end
lemma entails.or_inl (wfq : WF Γ Ω q) (prfp :entails Γ ⊤ p) : entails Γ ⊤ (p ⋁ q) :=
  by {apply entails.cut _ p _, assumption, apply entails.or_left _ q, apply entails.axm, apply_rules [WF.or, WF.proof_right]}
lemma entails.or_inr (wfq : WF Γ Ω p) (prfp :entails Γ ⊤ q) : entails Γ ⊤ (p ⋁ q) :=
  by {apply entails.cut _ q _, assumption, apply entails.or_right _ q, apply entails.axm, apply_rules [WF.or, WF.proof_right]}

lemma proof_of_and_left (_ : WF Γ Ω p) (_ : WF Γ Ω q) : entails Γ (p ⋀ q) p :=
  by {intros, apply entails.and_left _ p q, apply entails.axm, apply WF.and, tidy}
lemma proof_of_and_right (_ : WF Γ Ω p) (_ : WF Γ Ω q) : entails Γ (p ⋀ q) q :=
  by {apply entails.and_right _ p q, apply entails.axm, apply WF.and, tidy}

example (_ : WF Γ Ω p) (_ : WF Γ Ω q) : entails Γ (p ⋀ q) (q ⋀ p) :=
begin
  apply entails.and_intro,
  apply proof_of_and_right,
  tidy,
  apply proof_of_and_left,
  tidy
end

lemma eq_sound {A : type} {a₁ a₂ : term} (eq : ⊨ (a₁ ≃[A] a₂)) (φ : term) : entails Γ ⊤ ⁅φ // a₁⁆ → entails Γ ⊤ ⁅φ // a₂⁆ :=
by sorry

lemma reverse_extensionality (A : type) : ⊨ (∀' (𝒫 A) $ ∀' (𝒫 A) $ (↑1 ≃[𝒫 A] ↑0) ⟹ (∀' A ((↑0 ∈ ↑2) ⇔ (↑0 ∈ ↑1)))) :=
begin
  apply entails.all_intro 𝒫 A,
  apply entails.all_intro 𝒫 A,
  apply to_imp,
  apply from_meta_imp,
  any_goals {apply_rules WF_rules; refl},
  intro h,
  sorry
end

def is_star {Γ : context} {a : term} : WF Γ 𝟙 a → entails Γ ⊤ (a ≃[𝟙] ⁎) :=
begin
  intro wfa,
  apply entails.sub 𝟙 a ⊤ (↑0 ≃[𝟙] ⁎),
  assumption,
  have : (⊤ : term) = ^ ⊤, by rw WF.lift_closed; exact WF.top,
  rw this,
  apply entails.all_elim,
  rw ←list.nil_append Γ,
  apply entails.weakening,
  exact entails.star_unique
end

local notation `[]` := list.nil

lemma phi_ent_phi_and_top (h : WF [] Ω φ): φ ⊨ (φ ⋀ ⊤) :=
begin
  apply entails.and_intro,
  apply entails.axm,
  exact h,
  apply entails.vac,
  exact h
end

section meta_conversion

lemma ent_to_meta {p} {wfP : WF [] Ω p} : entails Γ φ ψ  → entails Γ p φ → entails Γ p ψ :=
  λ _ _, (by {apply entails.cut _ φ _, tidy})

lemma meta_to_ent (wfφ : WF Γ Ω φ) : (∀ p, entails Γ p φ → entails Γ p ψ) → entails Γ φ ψ :=
  λ h, h φ (entails.axm wfφ)

end meta_conversion



end TT