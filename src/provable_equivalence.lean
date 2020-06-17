import TL
import category

namespace TT

  variable A : type

  def proof_eq (a₁ a₂ : tset A) := ⊨ (a₁ ≃[A] a₂)

  section equivalence_relation

  theorem proof_eq_refl : reflexive (proof_eq A) :=
  begin
    intro a,
    unfold proof_eq,
    apply proof.all_intro 𝒫 A,
    apply proof.and_intro,
    all_goals {
        apply to_imp,
        apply proof.axm,
        apply_rules WF_rules,
        apply WF.lift,
        exact a.property,
        refl
      }
  end

  theorem proof_eq_symm : symmetric (proof_eq A) :=
  begin
    intros a₁ a₂ H,
    apply proof.all_intro 𝒫 A,
    apply proof.and_intro,
    apply proof.and_right _ ((↑a₁ ∈ 𝟘) ⟹ (↑a₂ ∈ 𝟘)) _,
    apply proof.all_elim, sorry,
    -- exact H,
    apply proof.and_left _ _ ((↑a₂ ∈ 𝟘) ⟹ (↑a₁ ∈ 𝟘)),
    apply proof.all_elim,
    sorry,
    -- exact H,
  end

  theorem proof_eq_trans : transitive (proof_eq A) := sorry

  theorem proof_eq_equiv : equivalence (proof_eq A) :=
    ⟨proof_eq_refl A, proof_eq_symm A, proof_eq_trans A⟩

  end equivalence_relation

  definition TT.setoid : setoid (closed_term A) := 
    {r := proof_eq A, iseqv := proof_eq_equiv A}

  #check TT.setoid

  local attribute [instance] TT.setoid

  def tset := quotient (TT.setoid (𝒫 A))

  def to_tset := quot.mk (proof_eq (𝒫 A))

  def coe_term_tset : has_coe (closed_term 𝒫 A) (tset A) := ⟨to_tset A⟩
  local attribute [instance] coe_term_tset

  def elem_maker {A : type} (a : closed_term A) : tset A → Prop :=
    quotient.lift (λ α : closed_term (𝒫 A), ⊨ a ∈ α) (begin
      intros α₁ α₂ heq,
      simp,
      constructor,
      intro h,

      sorry, sorry
    end)
    
  def tset.star_singleton : tset Unit :=
    by {apply to_tset, apply closed_term.mk _ ⟦Unit | ⊤⟧, apply WF.comp, exact WF.top}


  variables {A B : type}

  def AB_setoid : setoid (closed_term (𝒫 (A ×× B))) := TT.setoid (𝒫 (A ×× B))

  local attribute [instance] AB_setoid

  def term_is_subset_of_terms {A B : type} (α : closed_term 𝒫 A) (β : closed_term 𝒫 B) (F : closed_term 𝒫 (A××B)) : Prop :=
    ⊨ F ⊆[𝒫 A] (@term_prod A B α β)

  def lifted_is_subset_of_terms {A B : type} : tset A → tset B → tset (A ×× B) → Prop := 
    λ α β, (
      quotient.lift  (λ F : closed_term (𝒫 (A ×× B)), term_is_subset_of_terms α β F) (begin
        intros F₁ F₂ heq,
        simp,
        unfold term_is_subset_of_terms,
        constructor; sorry
      end)
    )

end TT