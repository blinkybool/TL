import definitions
import wellformedness
import tactic

namespace TT
namespace entails
open entails

variables p q r φ ψ : term
variable {Γ : context}

lemma hyp_and_left (_ : WF Γ Ω p) (_ : WF Γ Ω q) : entails Γ (p ⋀ q) p :=
  by {intros, apply entails.and_left _ p q, apply entails.axm, apply WF.and, tidy}
lemma hyp_and_right (_ : WF Γ Ω p) (_ : WF Γ Ω q) : entails Γ (p ⋀ q) q :=
  by {apply entails.and_right _ p q, apply entails.axm, apply WF.and, tidy}

lemma from_imp {p q}: entails Γ ⊤ (p ⟹ q) → entails Γ p q :=
begin
  intro h₁, 
  have : WF Γ Ω (p ⟹ q), from WF.entails_right h₁,
  have wfp : WF Γ Ω p, from WF.imp_left _ _ this,
  have wfq : WF Γ Ω q, from WF.imp_right _ _ this,
  apply cut (⊤ ⋀ p),
    { apply_rules and_intro,
        { exact vac wfp },
        { exact axm wfp}
    },
    { exact imp_to_and h₁ }
end

lemma to_imp {p q} : entails Γ p q → entails Γ ⊤ (p ⟹ q) :=
begin
  intro h₁,
  apply_rules [and_to_imp, cut p, and_right _ ⊤ _, axm],
  WF_prover,
  exact WF.entails_left h₁,
end

lemma or_intro_left (p q) : WF Γ Ω p → WF Γ Ω q → entails Γ p (p ⋁ q) :=
  by intros wfp wfq;apply hyp_or_left;apply axm;WF_prover
lemma or_intro_right (p q) : WF Γ Ω p → WF Γ Ω q → entails Γ q (p ⋁ q) :=
  by intros wfp wfq;apply hyp_or_right;apply axm;WF_prover

def is_star {a : term} : WF Γ 𝟙 a → entails Γ ⊤ (a ≃[𝟙] ⁎) :=
begin
  intro wfa,
  apply @sub _ ⊤ (↑0 ≃[𝟙] ⁎) _ _ wfa,
  have lift_top : (⊤ : term) = ^⊤, by refl,
  rw lift_top,
  apply all_elim,
  have nil_context : Γ = ([] ++ Γ ++ []), by simp,
  rw nil_context,
  have lift_0_top : (⊤ : term) = lift Γ.length 0 ⊤, by simp,
  rw lift_0_top,
  have lift_0_forall : (∀' 𝟙 (↑0 ≃[𝟙] ⁎)) = lift Γ.length 0 (∀' 𝟙 (↑0 ≃[𝟙] ⁎)), by simp; constructor,
  rw lift_0_forall,
  apply weakening,
  exact star_unique
end

lemma meta_all_sub {A φ a} : WF Γ A a → entails Γ ⊤ (∀' A φ) → entails Γ ⊤ (φ⁅a⁆) :=
begin
  intros wfa ent_all,
  have : (⊤ : term) =  ⊤⁅a⁆, by refl, rw this,
  apply sub _ _ wfa,
  have : (⊤ : term) = ^ ⊤, by refl, rw this,
  exact all_elim ent_all
end

lemma all_sub {A φ a} : WF (A :: Γ) Ω φ → entails (A::Γ) (^ (∀' A φ)) (φ⁅a⁆) :=
begin
  intro wf,
  apply cut φ,
    { apply_rules [all_elim, axm], WF_prover },
    {
      induction wf; sorry
     }
end


end entails


end TT