import definitions
import wellformedness
import tactic

namespace TT
namespace entails
open entails

variable {Γ : context}
variables {H K : term} -- an abitrary hypotheses
variables {p q r φ ψ : term}

example {Γ p q r} : entails Γ q q → WF Γ Ω ((p ⋀ ⊤) ⋁ r) → WF Γ Ω (r ⟹ (p ⋁ q)) :=
begin
  intros entq wfpq,
  WF_prover,
end

lemma absurd {wfp : WF Γ Ω p}: entails Γ H ⊥ → entails Γ H p :=
  λ entf, cut _ entf (abs wfp)

lemma add_hyp : WF Γ Ω H → entails Γ ⊤ p → entails Γ H p :=
  λ wfH entp, cut ⊤ (vac wfH) entp

lemma and_hyp_right : WF Γ Ω H → entails Γ K p → entails Γ (H ⋀ K) p :=
  λ wfH entp, by refine cut K (and_right (axm _)) entp; WF_prover

lemma and_hyp_left : WF Γ Ω H → entails Γ K p → entails Γ (K ⋀ H) p :=
  λ wfH entp, by refine cut K (and_left (axm _)) entp; WF_prover

lemma hyp_and_iff_imp : entails Γ (p ⋀ q) r ↔ entails Γ p (q ⟹ r) := ⟨and_to_imp, imp_to_and⟩

lemma ent_to_meta_imp : entails Γ p q → entails Γ H p → entails Γ H q :=
  λ _ _, cut p (by assumption) (by assumption)

lemma imp_iff_ent : entails Γ ⊤ (p ⟹ q) ↔ entails Γ p q :=
begin
  split,
    { intro ent, 
      apply cut (⊤ ⋀ p),
        { apply_rules [and_intro, vac, axm]; WF_prover},
        { exact imp_to_and ent } },
    { intro ent,
      cases (WF.entails_terms ent) with wfp wfq,
      apply_rules [and_to_imp, cut p],
      refine and_right (axm _); WF_prover }
end

lemma to_meta_imp : entails Γ H (p ⟹ q) → entails Γ H p → entails Γ H q :=
begin
  intros ent_pq entp,
  apply cut (H ⋀ p),
  apply and_intro _ entp,
    {apply axm; WF_prover}, 
  exact imp_to_and ent_pq
end

lemma to_meta_iff : entails Γ H (p ⇔ q) → (entails Γ H p ↔ entails Γ H q) :=
begin
  intro ent_iff,
  split;apply to_meta_imp, exact and_left ent_iff, exact and_right ent_iff, 
end

lemma hyp_true_to_meta_iff : entails Γ ⊤ (p ⇔ q) → (entails Γ H p ↔ entails Γ H q) :=
begin
  intro ent_iff,
  split, apply to_meta_imp,
  apply cut _ (vac _),
  exact and_left ent_iff, exact and_right ent_iff, 
end

lemma meta_and : entails Γ H (p ⋀ q) ↔ (entails Γ H p ∧ entails Γ H q) :=
  ⟨λ entpq, ⟨and_left entpq, and_right entpq⟩, λ ⟨entp, entq⟩, and_intro entp entq⟩

lemma hyp_and_left {wfp : WF Γ Ω p} {wfq : WF Γ Ω q} : entails Γ (p ⋀ q) p :=
  and_left (axm (by WF_prover))
lemma hyp_and_right {wfp : WF Γ Ω p} {wfq : WF Γ Ω q} : entails Γ (p ⋀ q) p :=
  and_left (axm (by WF_prover))

lemma and_comm : entails Γ H (p ⋀ q) → entails Γ H (q ⋀ p) :=
  λ entpq, and_intro (and_right entpq) (and_left entpq)

lemma and_assoc : entails Γ H (p ⋀ q ⋀ r) ↔ entails Γ H ((p ⋀ q) ⋀ r) :=
 by iterate 4 {rw meta_and}; tidy

lemma or_intro_left {wfq : WF Γ Ω q} : entails Γ H p → entails Γ H (p ⋁ q) :=
  λ entp, by apply cut p entp; apply hyp_or_left; apply axm;WF_prover
lemma or_intro_right {wfp : WF Γ Ω p} : entails Γ H q → entails Γ H (p ⋁ q) :=
  λ entq, by apply cut q entq; apply hyp_or_right; apply axm;WF_prover

lemma or_comm : entails Γ H (p ⋁ q) → entails Γ H (q ⋁ p) :=
  λ entpq,
  begin
    apply cut _ entpq,
    apply hyp_or,
    refine or_intro_right (axm _); WF_prover,
    refine or_intro_left (axm _); WF_prover
  end

lemma imp_trans (q) : entails Γ H (p ⟹ q) → entails Γ H (q ⟹ r) → entails Γ H (p ⟹ r) :=
begin
  intros ent_pq ent_qr,
  rw ←hyp_and_iff_imp at *,
  refine cut (H ⋀ q) _ ent_qr,
  refine and_intro hyp_and_left ent_pq; WF_prover,
end

lemma imp_refl {wfH : WF Γ Ω H} {wfp : WF Γ Ω p} : entails Γ H (p ⟹ p) :=
  by { refine add_hyp _ _, WF_prover, rw imp_iff_ent, refine axm _; WF_prover }

lemma iff_intro : entails Γ H (p ⟹ q) → entails Γ H (q ⟹ p) → entails Γ H (p ⇔ q) :=
  λ entpq entqp, and_intro entpq entqp 

lemma iff_elim : entails Γ H (p ⇔ q) ↔ (entails Γ H (p ⟹ q) ∧ entails Γ H (q ⟹ p)) :=
  by rw ←meta_and; refl 

lemma iff_elim_mp : entails Γ H (p ⇔ q) → entails Γ H (p ⟹ q) :=
  by rw iff_elim; tidy

lemma iff_elim_mpr : entails Γ H (p ⇔ q) → entails Γ H (q ⟹ p) :=
  by rw iff_elim; tidy

lemma iff_refl {wfH : WF Γ Ω H} {wfp : WF Γ Ω p} : entails Γ H (p ⇔ p) :=
  by apply and_intro; refine imp_refl; WF_prover

lemma iff_trans (q) : entails Γ H (p ⇔ q) → entails Γ H (q ⇔ r) → entails Γ H (p ⇔ r) :=
  λ entpq entqr, by { rw iff_elim at *, split; apply imp_trans q; tidy }

lemma iff_symm : entails Γ H (p ⇔ q) → entails Γ H (q ⇔ p) := entails.and_comm

lemma hyp_of_iff (φ ψ) (ent_iff : entails Γ ⊤ (φ ⇔ ψ)) : entails Γ φ K ↔ entails Γ ψ K :=
begin
  split;
  {intro entψ, apply cut _ _ entψ,
  rw ←imp_iff_ent,
  rw iff_elim at ent_iff,
  tidy,}
end

lemma closed_weakening : entails [] p q → entails Γ p q :=
begin
  intro entpq,
  have modΓ : Γ = [] ++ Γ ++ [], simp,
  have modp : p = lift Γ.length 0 p, rw WF.lift_closed p; WF_prover,
  have modq : q = lift Γ.length 0 q, rw WF.lift_closed q; WF_prover,
  rw [modΓ, modp, modq],
  exact weakening [] Γ [] entpq
end

lemma lift {A} : entails Γ p q → entails (A::Γ) (^p) (^q) :=
  by convert weakening [] [A] Γ; tidy

lemma all_to_spec {A a} {wfa : WF Γ A a} (φ) : entails Γ H (∀' A φ) → entails Γ H (φ⁅a⁆) :=
begin
  intros ent_all,
  apply cut _ ent_all,
  suffices : entails (A::Γ) (^ (∀' A φ)) φ, { convert sub A wfa this; simp },
  apply_rules [all_elim, axm]; WF_prover
end

lemma spec_to_ex {A a} {wfa : WF Γ A a} {wfφ : WF (A :: Γ) Ω φ} : entails Γ H (φ⁅a⁆) → entails Γ H (∃' A φ) :=
begin
  intro ent_spec,
  apply cut _ ent_spec,
  suffices : entails (A::Γ) φ (^ (∃' A φ)), { convert sub A wfa this; simp},
  apply_rules [ex_elim, axm]; WF_prover
end

lemma is_star {wfH : WF Γ Ω H} (s : term) {wfs : WF Γ 𝟙 s} : entails Γ H (s ≃[𝟙] ⁎) :=
  by refine (add_hyp wfH $ all_to_spec (↑0 ≃[𝟙] ⁎) (closed_weakening star_unique)); WF_prover 

lemma elem_iff_spec {A} {wfH : WF Γ Ω H} {wfφ : WF (A::Γ) Ω φ} : entails Γ ⊤ (∀' A $ (↑0 ∈[A] ^(⟦A | φ⟧)) ⇔ φ) := comp wfφ

lemma eq_elem {A} (a₁ a₂ α) {wfα : WF Γ (𝒫 A) α} (ent_eq : entails Γ H (a₁ ≃[A] a₂)) : entails Γ H (a₁ ∈[A] α) ↔ entails Γ H (a₂ ∈[A] α) :=
  by convert to_meta_iff (all_to_spec _ ent_eq); simp <|> WF_prover

lemma eq_sub {A} (a₁ a₂ φ) (ent_eq : entails Γ H (a₁ ≃[A] a₂)) (wfφ : WF (A::Γ) Ω φ) : entails Γ H (φ⁅a₁⁆) ↔ entails Γ H (φ⁅a₂⁆) :=
begin
  rw [←elem_iff_spec, ←elem_iff_spec], any_goals {WF_prover},
  apply eq_elem; WF_prover
end

lemma intro_eq {wfH : WF Γ Ω H} {A} {α₁ α₂} {wfα₁ : WF Γ (𝒫 A) α₁} {wfα₂ : WF Γ (𝒫 A) α₂} : entails Γ H (∀' A ((↑0 ∈[A] ^α₁) ⇔ (↑0 ∈[A] ^α₂))) → entails Γ H (α₁ ≃[𝒫 A] α₂) :=
  to_meta_imp (add_hyp wfH (by { convert all_to_spec _ (all_to_spec _ (closed_weakening extensionality)), any_goals {simp}, all_goals {WF_prover}}))

lemma prop_eq_iff {wfH : WF Γ Ω H} {φ ψ} {wfφ : WF Γ Ω φ} {wfψ : WF Γ Ω ψ} : entails Γ H (φ ⇔ ψ) ↔ entails Γ H (φ ≃[Ω] ψ) :=
begin
  split,
    { apply to_meta_imp, apply add_hyp wfH,
      convert all_to_spec _ (all_to_spec _ (closed_weakening prop_ext)); {simp <|> WF_prover} },
    { intro ent_eq,
      convert (eq_sub φ ψ ((^φ) ⇔ ↑0) ent_eq _).1, simp, tidy, refine a iff_refl, all_goals {WF_prover; refl} }
end

lemma eq_elim_elems {A} {α₁ α₂} {a} {wfa : WF Γ A a} {ent_eq : entails Γ H (α₁ ≃[𝒫 A] α₂)} : entails Γ H (a ∈[A] α₁) ↔ entails Γ H (a ∈[A] α₂) :=
  by {convert eq_sub α₁ α₂ (^a ∈[A] ↑0) ent_eq _, simp, simp, WF_prover, apply WF.lift_once, assumption}

lemma elem_product {d A B} {wfH : WF Γ Ω H} : WF Γ (A 𝕏 B) d → entails Γ H (∃[A,B] $ (^(^d)) ≃[A 𝕏 B] ⟪↑1,↑0⟫) :=
λ wfd, add_hyp wfH (by {convert (all_to_spec _ (closed_weakening pair_rep)); WF_prover})



lemma ex_ent_ex_of_var {A} : entails (A::Γ) p q → entails Γ (∃' A p) (∃' A q) :=
begin
  intro entpq,
  refine ex_intro (cut q entpq (ex_elim (axm _))); WF_prover
end

end entails

end TT