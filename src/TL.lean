/-
Definitions of a type theory

Author: Billy Price
-/

import data.finset
import tactic.tidy
namespace TT

inductive type : Type
| Unit | Omega | Prod (A B : type)| Pow (A : type)

notation `Ω` := type.Omega
def Unit := type.Unit
infix `××`:max := type.Prod
notation `𝒫`A :max := type.Pow A

def context := list type

inductive term : Type
| star : term
| top  : term
| bot  : term
| and  : term → term → term
| or   : term → term → term
| imp  : term → term → term
| elem : term → term → term
| pair : term → term → term
| var  : ℕ → term
| comp : type → term → term
| all  : type → term → term
| ex   : type → term → term

open term

-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * 
-- Notation and derived operators 
-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * 

notation `𝟘` := term.var 0
notation `𝟙` := term.var 1
notation `𝟚` := term.var 2
notation `𝟛` := term.var 3
notation `𝟜` := term.var 4
notation `𝟝` := term.var 5

notation `⁎` := term.star    -- input \asterisk
notation `⊤` := term.top     --       \top
notation `⊥` := term.bot     -- input \bot
infixr ` ⟹ `:60 := term.imp -- input \==>
infixr ` ⋀ ` :70 := term.and -- input \And or \bigwedge
infixr ` ⋁ ` :59 := term.or  -- input \Or or \bigvee

def not (p : term) := p ⟹ ⊥
prefix `∼`:max := not -- input \~

def iff (p q: term) := (p ⟹ q) ⋀ (q ⟹ p)
infix ` ⇔ `:60 := iff -- input \<=>

infix ∈ := term.elem
infix ∉ := λ a α, not (term.elem a α)
notation `⟦ ` A ` | ` φ ` ⟧` := term.comp A φ

notation `⟪` a `,` b `⟫` := term.pair a b 

notation `∀'` := term.all
notation `∃'` := term.ex


section substitution

  @[simp]
  def lift_d (d : ℕ) : ℕ → term → term
  | k ⁎          := ⁎
  | k ⊤          := ⊤
  | k ⊥          := ⊥
  | k (p ⋀ q)    := (lift_d k p) ⋀ (lift_d k q)
  | k (p ⋁ q)    := (lift_d k p) ⋁ (lift_d k q)
  | k (p ⟹ q)   := (lift_d k p) ⟹ (lift_d k q)
  | k (a ∈ α)    := (lift_d k a) ∈ (lift_d k α)
  | k ⟪a,b⟫      := ⟪lift_d k a, lift_d k b⟫
  | k (var m)    := if m≥k then var (m+d) else var m
  | k ⟦A | φ⟧     :=   ⟦A | lift_d (k+1) φ⟧
  | k (∀' A φ)   := ∀' A $ lift_d (k+1) φ
  | k (∃' A φ)   := ∃' A $ lift_d (k+1) φ

  @[simp]
  def lift := lift_d 1 0

  @[simp]
  def subst : ℕ → term → term → term
  | n x ⁎          := ⁎
  | n x ⊤          := ⊤
  | n x ⊥          := ⊥
  | n x (p ⋀ q)    := (subst n x p) ⋀ (subst n x q)
  | n x (p ⋁ q)    := (subst n x p) ⋁ (subst n x q)
  | n x (p ⟹ q)  := (subst n x p) ⟹ (subst n x q)
  | n x (a ∈ α)    := (subst n x a) ∈ (subst n x α)
  | n x ⟪a,c⟫      := ⟪subst n x a, subst n x c⟫
  | n x (var m)    := if n=m then x else var m
  | n x ⟦ A | φ ⟧   :=    ⟦A | subst (n+1) (lift x) φ⟧
  | n x (∀' A φ)     := ∀' A (subst (n+1) (lift x) φ)
  | n x (∃' A φ)     := ∃' A (subst (n+1) (lift x) φ)

  notation  `⁅` φ ` // `  b `⁆` := subst 0 b φ

  #reduce ⁅𝟘 // ⊤ ⋀ ⊥⁆
  #reduce ⁅ 𝟙 // ⊤ ⋀ ⊥⁆

end substitution

def eq (A:type) (a₁ a₂ : term) : term := ∀' (𝒫 A) $ ((lift a₁) ∈ 𝟘) ⇔ ((lift a₂) ∈ 𝟘)
notation a ` ≃[`:max A `] `:0 b := eq A a b

#check eq Unit 𝟘 𝟘

def singleton (A : type) (a : term) := ⟦A | (lift a) ≃[A] 𝟘⟧

def ex_unique (A : type) (φ : term) : term :=
  ∃' A (⟦A | φ⟧ ≃[𝒫 A] (singleton A 𝟘))
prefix `∃!'`:2 := ex_unique

def subseteq (A : type) (α : term) (β : term) : term :=
  ∀' A (𝟘 ∈ (lift α)) ⟹ (𝟘 ∈ (lift β))
notation a ` ⊆[`:max A `] `:0 b := subseteq A a b

def term_prod (A B : type) (α β : term) : term :=
  ⟦ A ×× B | ∃' A (∃' B ((𝟙 ∈ α) ⋀ (𝟘 ∈ β) ⋀ (𝟚 ≃[A××B] ⟪𝟙,𝟘⟫)))⟧
-- notation α ` ××[`:max A,B `] `:0 β := term_prod A B α β


@[simp]
lemma subst.subseteq {x n α β A}: subst n x (α ⊆[A] β) = (subst n x α) ⊆[A] (subst n x β) :=
  sorry

-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
open term

@[user_attribute]
meta def WF_rules : user_attribute :=
{ name := `TT.WF_rules,
  descr := "lemmas usable to prove Well Formedness" }

inductive WF : context → type → term → Prop
| star {Γ}         : WF Γ Unit ⁎
| top  {Γ}         : WF Γ Ω ⊤
| bot  {Γ}         : WF Γ Ω ⊥
| and  {Γ p q}     : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⋀ q)
| or   {Γ p q}     : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⋁ q)
| imp  {Γ p q}     : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⟹ q)
| elem {Γ A a α}   : WF Γ A a → WF Γ (𝒫 A) α → WF Γ Ω (a ∈ α)
| pair {Γ A B a b} : WF Γ A a → WF Γ B b → WF Γ (A ×× B) ⟪a,b⟫
| var  {Γ A n}     : list.nth Γ n = some A → WF Γ A (var n)
| comp {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ (𝒫 A) ⟦A | φ⟧
| all  {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ Ω (∀' A φ)
| ex   {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ Ω (∃' A φ)

attribute [TT.WF_rules] WF.star WF.top WF.bot WF.and WF.or WF.imp WF.elem WF.pair WF.var WF.comp WF.all WF.ex

section

variables {Γ Δ : context}
variables {p q r φ a b α : term}
variables {A B Ω' : type}
-- Ω' is just a fake/variable version of Ω so we don't need to bother proving
-- that it must be Ω itself.'

meta def WF_prover : tactic unit := do `[intro h, cases h, assumption]

lemma WF.and_left   : WF Γ Ω' (p ⋀ q) → WF Γ Ω' p := by WF_prover
lemma WF.and_right  : WF Γ Ω' (p ⋀ q) → WF Γ Ω' q := by WF_prover
lemma WF.or_left    : WF Γ Ω' (p ⋁ q) → WF Γ Ω' p := by WF_prover
lemma WF.or_right   : WF Γ Ω' (p ⋁ q) → WF Γ Ω' q := by WF_prover
lemma WF.imp_left   : WF Γ Ω' (p ⟹ q) → WF Γ Ω' p := by WF_prover
lemma WF.imp_right  : WF Γ Ω' (p ⟹ q) → WF Γ Ω' q := by WF_prover
lemma WF.pair_left  : WF Γ (A ×× B) ⟪a,b⟫ → WF Γ A a := by WF_prover
lemma WF.pair_right : WF Γ (A ×× B) ⟪a,b⟫ → WF Γ B b := by WF_prover
lemma WF.comp_elim  : WF Γ (𝒫 A) ⟦A | φ⟧ → WF (A::Γ) Ω φ := by WF_prover
lemma WF.all_elim   : WF Γ Ω' (∀' A φ) → WF (A::Γ) Ω' φ := by WF_prover
lemma WF.ex_elim    : WF Γ Ω' (∀' A φ) → WF (A::Γ) Ω' φ := by WF_prover
@[TT.WF_rules] lemma WF.iff_intro : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⇔ q) :=
begin
  intros,
  apply_rules WF_rules,
end
lemma iff_elim : WF Γ Ω' (p ⇔ q) → WF Γ Ω' p ∧ WF Γ Ω' q :=
  by {intro h, refine and.intro _ _;{cases h, cases h_a, assumption}}

local notation l₁ ++ l₂ := list.append l₁ l₂
open list


lemma WF.lift_d (K Δ Γ : context) (A : type) (a : term) : WF (K ++ Γ) A a → WF (K ++ Δ ++ Γ) A (lift_d (length Δ) (length K) a) :=
begin
  intro wfa,
  generalize_hyp e : K ++ Γ = Γ' at wfa,
  induction wfa generalizing K,
  case WF.all  : Γ' A' ψ wfψ ih {subst e, constructor, refine ih (A' :: K) _, refl},
  case WF.ex   : Γ' A' ψ wfψ ih {subst e, constructor, refine ih (A' :: K) _, refl},
  case WF.comp : Γ' A' ψ wfψ ih {subst e, constructor, refine ih (A' :: K) _, refl},
  case WF.var  : Γ' A' n h₁ 
  {
    subst e,simp,
    split_ifs with h₂,
      apply WF.var,
      rw ←h₁,
      rw nth_le_nth,
      rw nth_le_nth,
    repeat {sorry}
  },
  repeat {sorry},
end

lemma WF.lift {Γ A a B} : WF Γ A a → WF (B :: Γ) A (lift a) :=
  by {intros, apply WF.lift_d [] [B] Γ, assumption}

@[TT.WF_rules]
lemma WF.eq_intro {Γ} {a₁ a₂} (A : type) : WF Γ A a₁ → WF Γ A a₂ → WF Γ Ω (a₁ ≃[A] a₂) :=
begin
  intros,
  apply WF.all,
  apply WF.iff_intro;{apply WF.elem, apply WF.lift, assumption, apply WF.var; refl}
end

lemma WF.lift_closed {a A} : WF [] A a → lift a = a :=
begin
  suffices : ∀ G A a, WF G A a → lift_d 1 (list.length G) a = a,
  { exact this _ _ _ },
  introv wf,
  induction wf; simp * at *,
  exact if_neg (not_le_of_gt (list.nth_eq_some.1 wf_a).fst)
end

lemma lift_zero_does_nothing {k} {a : term} : lift_d 0 k a = a :=
  by induction a generalizing k;simp *

lemma WF.list_d_closed {a A d} : WF [] A a → lift_d d 0 a = a :=
begin
  intro wf,
  induction d,
  case nat.zero : {induction a; apply lift_zero_does_nothing,},
  sorry
end

lemma WF.closed_with_context {Γ a A} : WF [] A a → WF Γ A a :=
begin
  intro wf,
  induction Γ,
  assumption,
  sorry
end

end

section proofs

inductive proof : context → term → term → Prop
| axm        {Γ} {φ}       : WF Γ Ω φ → proof Γ φ φ
| vac        {Γ} {φ}       : WF Γ Ω φ → proof Γ φ ⊤
| abs        {Γ} {φ}       : WF Γ Ω φ → proof Γ ⊥ φ
| and_intro  {Γ} {p q r}   : proof Γ p q → proof Γ p r → proof Γ p (q ⋀ r)
| and_left   {Γ} (p q r)   : proof Γ p (q ⋀ r) → proof Γ p q
| and_right  {Γ} (p q r)   : proof Γ p (q ⋀ r) → proof Γ p r
| or_intro   {Γ} {p q r}   : proof Γ p r → proof Γ q r → proof Γ (p ⋁ q) r
| or_left    {Γ} (p q r)   : proof Γ (p ⋁ q) r → proof Γ p r
| or_right   {Γ} (p q r)   : proof Γ (p ⋁ q) r → proof Γ q r
| imp_to_and {Γ} {p q r}   : proof Γ p (q ⟹ r) → proof Γ (p ⋀ q) r
| and_to_imp {Γ} {p q r}   : proof Γ (p ⋀ q) r → proof Γ p (q ⟹ r)
| weakening  {Γ} {φ ψ Δ}   : proof Γ φ ψ → proof (list.append Γ Δ) φ ψ
| cut        {Γ} (φ c ψ)   : proof Γ φ c → proof Γ c ψ → proof Γ φ ψ
| all_elim   {Γ} {p φ A}   : proof Γ p (∀' A φ) → proof (A::Γ) p φ
| all_intro  {Γ} {p φ} (A) : proof (A::Γ) p φ → proof Γ p (∀' A φ)
| ex_elim    {Γ} {p φ A}   : proof Γ p (∃' A φ) → proof (A::Γ) p φ
| ex_intro   {Γ} {p φ} (A) : proof (A::Γ) p φ → proof Γ p (∃' A φ)
| extensionality {A}       : proof [] ⊤ $ ∀' (𝒫 A) $ ∀' (𝒫 A) $ (∀' A ((𝟘 ∈ 𝟚) ⇔ (𝟘 ∈ 𝟙))) ⟹ (𝟚 ≃[A] 𝟙)
| prop_ext                 : proof [] ⊤ $ ∀' Ω $ ∀' Ω (𝟙 ⇔ 𝟘) ⟹ (𝟙 ≃[Ω] 𝟘)
| star_unique              : proof [] ⊤ $ ∀' Unit (𝟘 ≃[Unit] ⁎)
| pair_exists_rep {A B}    : proof [] ⊤ $ ∀' (A ×× B) $ ∃' A $ ∃' B $ 𝟚 ≃[A ×× B] ⟪𝟙,𝟘⟫
| pair_distinct_rep {A B}  : proof [] ⊤ $ ∀' A $ ∀' B $ ∀' A $ ∀' B $ (⟪𝟛,𝟙⟫ ≃[A××B] ⟪𝟚,𝟘⟫) ⟹ (𝟛 ≃[A] 𝟚 ⋀ 𝟙 ≃[B] 𝟘)
| sub      {Γ} (B) (φ ψ b) : WF Γ B b → proof (B::Γ) φ ψ → proof Γ (⁅φ // b⁆) (⁅ψ // b⁆)
| comp     {Γ} (A) (φ)     : WF (A::Γ) Ω φ → proof Γ ⊤ (∀' A (𝟘 ∈ ⟦A | φ⟧) ⇔ (⁅φ // 𝟘⁆))

@[user_attribute]
meta def easy_proofs : user_attribute :=
{ name := `TT.easy_proofs,
  descr := "Easy proofs" }

attribute [TT.easy_proofs] proof.axm proof.vac proof.abs proof.and_intro proof.or_intro


prefix `⊨`:1 := proof [] ⊤
infix ` ⊨ `:50 := proof []
notation φ ` ⊨[` Γ:(foldr `,` (h t, list.cons h t) list.nil) `] ` ψ := proof Γ φ ψ
notation `⊨[` Γ:(foldr `,` (h t, list.cons h t) list.nil) `] ` ψ := proof Γ ⊤ ψ

section
  variables p q φ ψ : term

  #reduce   ⊨ (p ⋁ ∼p)  -- proof [] ⊤ (or p (imp p ⊥))
  #reduce q ⊨ (p ⋁ ∼p)  -- proof [] q (or p (imp p ⊥))
  #reduce   ⊨[Ω,Unit] p -- proof [Ω,Unit] ⊤ p
  #reduce q ⊨[Ω,Unit] p -- proof [Ω,Unit] q p
end 

end proofs

namespace WF
variable {Γ : context}
variables p q φ ψ : term
lemma proof_left  : proof Γ φ ψ → WF Γ Ω φ := sorry
lemma proof_right : proof Γ φ ψ → WF Γ Ω ψ := sorry

end WF


end TT