import definitions
import tactic

def foo : ℕ := 3


@[user_attribute]
meta def WF_rules : user_attribute :=
{ name := `WF_rules,
  descr := "lemmas usable to prove Well Formedness" }

namespace TT


open list
local notation l₁ ++ l₂ := list.append l₁ l₂

variables {Γ Δ : list type}
variables {A B Ω' : type}
-- Ω' is just a fake/variable version of Ω so we don't need to bother proving
-- that it must be Ω itself.'
variables {p q r φ a b α : term}

attribute [WF_rules]
WF.star WF.top WF.bot WF.and WF.or WF.imp WF.elem WF.pair WF.var WF.comp WF.all WF.ex


lemma WF.and_elim  : WF Γ Ω' (p ⋀ q) → WF Γ Ω' p ∧ WF Γ Ω' q := by {intro h, cases h, tidy}
lemma WF.or_elim   : WF Γ Ω' (p ⋁ q) → WF Γ Ω' p ∧ WF Γ Ω' q := by {intro h, cases h, tidy}
lemma WF.imp_elim  : WF Γ Ω' (p ⟹ q) → WF Γ Ω' p ∧ WF Γ Ω' q := by {intro h, cases h, tidy}
lemma WF.pair_elim : WF Γ (A 𝕏 B) ⟪a,b⟫ → WF Γ A a ∧ WF Γ B b := by {intro h, cases h, tidy}
lemma WF.comp_elim : WF Γ (𝒫 A) ⟦A | φ⟧ → WF (A::Γ) Ω φ := by {intro h, cases h, tidy}
lemma WF.all_elim  : WF Γ Ω' (∀' A φ) → WF (A::Γ) Ω' φ := by {intro h, cases h, tidy}
lemma WF.ex_elim   : WF Γ Ω' (∃' A φ) → WF (A::Γ) Ω' φ := by {intro h, cases h, tidy}

lemma WF.eq_elim {Γ} {a₁ a₂} {A} : WF Γ Ω (a₁ ≃[A] a₂) → WF Γ A a₁ ∧ WF Γ A a₂ := sorry

@[WF_rules]
lemma WF.iff : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⇔ q) := by intros; apply_rules WF_rules

@[WF_rules]
lemma WF.lift (K Δ Γ : context) (A : type) (a : term) : WF (K ++ Γ) A a → WF (K ++ Δ ++ Γ) A (lift (length Δ) (length K) a) :=
begin
  intro wfa,
  -- generalize_hyp e : K ++ Γ = Γ' at wfa,
  induction' wfa; simp * at *,
  any_goals {apply_rules WF_rules;refl},
  any_goals {apply_rules WF_rules; {exact ih_wfa Δ <|> exact ih_wfa_1 Δ}},
  case WF.var : {
    split_ifs, sorry,
      {
        apply WF.var,
        rw ←x, simp at h, sorry,
      }
  },
  iterate 3 {sorry},
end

@[WF_rules]
lemma WF.lift_once {Γ A a B} : WF Γ A a → WF (B :: Γ) A (^a) :=
  by {intros, apply WF.lift [] [B] Γ, assumption}

@[WF_rules]
lemma WF.eq {Γ} {a₁ a₂} {A} : WF Γ A a₁ → WF Γ A a₂ → WF Γ Ω (a₁ ≃[A] a₂) :=
  by {intros; apply_rules WF_rules; refl}

lemma WF.drop {Γ A a B} : WF (B :: Γ) A (^a) → WF Γ A a := sorry

@[simp]
lemma WF.lift_closed {A d} (a : term) : WF [] A a → lift d 0 a = a :=
begin
  suffices : ∀ G A a, WF G A a → lift d (list.length G) a = a,
  { exact this _ _ _ },
  introv wf,
  induction wf; simp * at *,
  exact if_neg (not_le_of_gt (list.nth_eq_some.1 wf_a).fst)
end

lemma WF.add_context {Γ Δ : list type} {A a}: WF Γ A a → WF (Γ ++ Δ) A a :=
begin
  intro wf,
  induction wf,
  case WF.var : Γ A n eq {
    apply WF.var, erw nth_append, assumption, exact (nth_eq_some.mp eq).fst 
  },
  all_goals {apply_rules WF_rules}
end

lemma WF.closed_add_context {Γ a A} : WF [] A a → WF Γ A a :=
  by {intro wf, rw ←nil_append Γ, exact WF.add_context wf}

lemma WF.subst {Γ B b p} : WF Γ B b → WF (B :: Γ) Ω p → WF Γ Ω (p⁅b⁆) := sorry

lemma WF.entails_terms {Γ} {p q} : entails Γ p q → WF Γ Ω p ∧ WF Γ Ω q :=
begin
  intro ent,
  induction ent,
  case sub        : Γ p q b B wfb ent ih {
    suffices : ∀ p, WF (B :: Γ) Ω p → WF Γ Ω (p⁅b⁆), from ⟨this p ih.1, this q ih.2⟩,
    intros _ wfp, exact WF.subst wfb wfp
  },
  any_goals {split; cases ent_ih.1; cases ent_ih.2; apply_rules WF_rules; tidy},
  any_goals {split;apply_rules WF_rules;refl},
  any_goals {split; simp * at *;apply_rules WF_rules;refl},
  case all_intro : Γ p φ A entφ ih { split, apply WF.drop ih.1, apply_rules WF_rules; tidy},
  case ex_intro : Γ p φ A entφ ih { split, apply_rules WF_rules; tidy, apply WF.drop ih.2,},
end

lemma WF.entails_left  {Γ p q} : entails Γ p q → WF Γ Ω p :=
  λ ent, (WF.entails_terms ent).1
lemma WF.entails_right {Γ p q} : entails Γ p q → WF Γ Ω q :=
  λ ent, (WF.entails_terms ent).2

end TT

open tactic

meta def decompose_WF : expr → expr → tactic expr
| _ `(TT.WF _ _ TT.term.star) := tactic.failed
| _ `(TT.WF _ _ TT.term.top) := tactic.failed
| _ `(TT.WF _ _ TT.term.bot) := tactic.failed
| h `(TT.WF _ _ (TT.term_eq _ _ _)) := mk_app `TT.WF.eq_elim [h]
| h `(TT.WF _ _ (TT.term.and _ _)) := mk_app `TT.WF.and_elim [h]
| h `(TT.WF _ _ (TT.term.or _ _)) := mk_app `TT.WF.or_elim [h]
| h `(TT.WF _ _ (TT.term.imp _ _)) := mk_app `TT.WF.imp_elim [h]
| h `(TT.WF _ _ (TT.term.pair _ _)) := mk_app `TT.WF.pair_elim [h]
| h `(TT.WF _ _ (TT.term.comp _ _)) := mk_app `TT.WF.comp_elim [h]
| h `(TT.WF _ _ (TT.term.all _ _)) := mk_app `TT.WF.all_elim [h]
| h `(TT.WF _ _ (TT.term.ex _ _)) := mk_app `TT.WF.ex_elim [h]
| h `(TT.entails _ _ _) := mk_app `TT.WF.entails_terms [h]
| _ _ := tactic.failed

meta def decompose_list_WFs : list expr → tactic unit
| [] := skip
| (h::t) :=
  do
    H ← infer_type h,
    (decompose_WF h H >>= cases >>= list.mmap' (λ name_wfs, decompose_list_WFs name_wfs.2)) <|> skip,
    decompose_list_WFs t

meta def tactic.interactive.decompose_WFs : tactic unit :=
  local_context >>= decompose_list_WFs

meta def tactic.interactive.WF_prover : tactic unit :=
  do `[tactic.interactive.decompose_WFs <|> skip, apply_rules WF_rules]

namespace TT

example {Γ p q r} : entails Γ q q → WF Γ Ω ((p ⋀ ⊤) ⋁ r) → WF Γ Ω (r ⟹ (p ⋁ q)) :=
begin
  intros entq wfpq,
  WF_prover,
end

end TT