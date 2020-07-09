import definitions
import category
import entails

namespace TT
open entails

def entails_eq (A : type) (a₁ a₂ : tset A) := ⊨ (a₁ ≃ a₂)

section equivalence_relation

  variable A : type

  theorem entails_eq_refl : reflexive (entails_eq A) :=
  by intro; apply_rules [all_intro, and_intro, to_imp, axm, WF_rules]; refl

  theorem entails_eq_symm : symmetric (entails_eq A) :=
  begin
    intros a₁ a₂ H,
    apply entails.all_intro,
    apply entails.and_intro,
    apply entails.and_right _ ((↑a₁ ∈ ↑0) ⟹ (↑a₂ ∈ ↑0)) _,
    apply entails.all_elim, sorry,
    -- exact H,
    apply entails.and_left _ _ ((↑a₂ ∈ ↑0) ⟹ (↑a₁ ∈ ↑0)),
    apply entails.all_elim,
    sorry,
    -- exact H,
  end

  theorem entails_eq_trans : transitive (entails_eq A) := sorry

  theorem entails_eq_equiv : equivalence (entails_eq A) :=
    ⟨entails_eq_refl A, entails_eq_symm A, entails_eq_trans A⟩

end equivalence_relation

section setoid

  def TT.setoid (A : type) : setoid (tset A) := 
    {r := entails_eq A, iseqv := entails_eq_equiv A}

  local attribute [instance] TT.setoid

  variable A : type

  def tsetoid := quotient (TT.setoid A)

  def to_tsetoid := quot.mk (entails_eq A)

  def coe_tset_tsetoid : has_coe (tset A) (tsetoid A) := ⟨to_tsetoid A⟩
  local attribute [instance] coe_tset_tsetoid

  def elem_maker {A : type} (a : term) (wf : WF [] A a) : tsetoid A → Prop :=
    quotient.lift (λ α : tset A, ⊨ a ∈ α) (begin
      intros α₁ α₂ heq,
      simp,
      constructor,
      intro h,

      sorry, sorry
    end)
    
  def tset.star_singleton : tsetoid 𝟙 :=
    by {apply to_tsetoid, apply tset.mk _ ⟦𝟙 | ⊤⟧, apply WF.comp, exact WF.top}

end setoid

section

  variables {A B : type}

  def AB_setoid : setoid (tset (A 𝕏 B)) := TT.setoid (A 𝕏 B)

  local attribute [instance] AB_setoid

  def lifted_is_subset_of_terms {A B : type} : tset A → tset B → tsetoid (A 𝕏 B) → Prop := 
    λ α β, (
      quotient.lift 
        (λ F : tset (A 𝕏 B), ⊨ F ⊆ α 𝕏 β)
        (begin
          intros F₁ F₂ heq,
          simp,
          constructor; sorry
        end)
    )

end

end TT