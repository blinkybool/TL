/-
Definitions of a type theory

Author: Billy Price
-/

import data.finset
namespace TT

inductive type : Type
| Unit | Omega | Prod (A B : type)| Pow (A : type)

notation `Ω` := type.Omega
def Unit := type.Unit
infix `××`:max := type.Prod
prefix 𝒫 :max := type.Pow

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
| comp : term → term
| all  : term → term
| ex   : term → term

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
notation `⟦` φ `⟧` := term.comp φ

notation `⟪` a `,` b `⟫` := term.pair a b 

prefix `∀'`:1 := term.all 
prefix `∃'`:2 := term.ex

def eq (a₁ a₂ : term) : term := ∀' (a₁ ∈ 𝟘) ⇔ (a₂ ∈ 𝟘)
infix `≃` :50 := eq

def singleton (a : term) := ⟦a ≃ (𝟘)⟧

def ex_unique (φ : term) : term :=
  ∃' ⟦φ⟧ ≃ singleton (𝟛)
prefix `∃!'`:2 := ex_unique

def subseteq (α : term) (β : term) : term :=
  ∀' (𝟘 ∈ α) ⟹ (𝟘 ∈ β)
infix ⊆ := subseteq

def set_prod {A B : type} (α β : term) : term :=
  ⟦∃' ∃' (𝟙 ∈ α) ⋀ (𝟘 ∈ β) ⋀ (𝟛 ≃ ⟪𝟚,𝟙⟫)⟧

-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
open term


section wellformedness

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
  | comp {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ (𝒫 A) ⟦φ⟧
  | all  {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ Ω (∀' φ)
  | ex   {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ Ω (∃' φ)


  variable {Γ : context}
  variables p q r φ a b α : term
  variables {A B Ω' : type}
  -- Ω' is just a fake/variable version of Ω so we don't need to bother proving
  -- that it must be Ω itself.

  local notation `ez` := by {intro h, cases h, assumption}
  lemma WF.and_left   : WF Γ Ω' (p ⋀ q) → WF Γ Ω' p               := ez
  lemma WF.and_right  : WF Γ Ω' (p ⋀ q) → WF Γ Ω' q               := ez
  lemma WF.or_left    : WF Γ Ω' (p ⋁ q) → WF Γ Ω' p               := ez
  lemma WF.or_right   : WF Γ Ω' (p ⋁ q) → WF Γ Ω' q               := ez
  lemma WF.imp_left   : WF Γ Ω' (p ⟹ q) → WF Γ Ω' p             := ez
  lemma WF.imp_right  : WF Γ Ω' (p ⟹ q) → WF Γ Ω' q             := ez
  lemma WF.pair_left  : WF Γ (A ×× B) ⟪a,b⟫ → WF Γ A a            := ez
  lemma WF.pair_right : WF Γ (A ×× B) ⟪a,b⟫ → WF Γ B b            := ez
  lemma WF.comp_elim  : WF Γ (𝒫 A) (⟦φ⟧) → WF (A::Γ) Ω φ          := ez
  lemma WF.all_elim   : WF Γ Ω' (∀' φ) → ∃ A:type, WF (A::Γ) Ω' φ :=
    by {intro h, cases h, constructor, assumption}
  lemma WF.ex_elim    : WF Γ Ω' (∀' φ) → ∃ A:type, WF (A::Γ) Ω' φ :=
    by {intro h, cases h, constructor, assumption}
  lemma WF.iff_intro : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⇔ q) :=
    by {intros h₁ h₂, apply WF.and, all_goals {apply WF.imp, assumption, assumption}}
  lemma WF.iff_elim : WF Γ Ω' (p ⇔ q) → WF Γ Ω' p ∧ WF Γ Ω' q :=
    by {intro h, apply and.intro, all_goals {cases h, cases h_a, assumption}}
  lemma WF.eq_intro {Γ} {a₁ a₂} (A : type) : WF ((𝒫 A) :: Γ) A a₁ → WF ((𝒫 A) :: Γ) A a₂ → WF Γ Ω (a₁ ≃ a₂) :=
    by {intros h₁ h₂, apply WF.all, apply WF.iff_intro, all_goals {apply WF.elem, assumption, apply WF.var, simp}}

end wellformedness

section substitution

  def lift (d : ℕ) : ℕ → term → term
  | k ⁎          := ⁎
  | k ⊤          := ⊤
  | k ⊥          := ⊥
  | k (p ⋀ q)    := (lift k p) ⋀ (lift k q)
  | k (p ⋁ q)    := (lift k p) ⋁ (lift k q)
  | k (p ⟹ q)   := (lift k p) ⟹ (lift k q)
  | k (a ∈ α)    := (lift k a) ∈ (lift k α)
  | k ⟪a,b⟫      := ⟪lift k a, lift k b⟫
  | k (var m)    := if m≥k then var (m+d) else var m
  | k ⟦φ⟧         :=    ⟦lift (k+1) φ⟧
  | k (∀' φ)     := ∀' lift (k+1) φ
  | k (∃' φ)     := ∃' lift (k+1) φ

  def subst_nth : ℕ → term → term → term
  | n x ⁎          := ⁎
  | n x ⊤          := ⊤
  | n x ⊥          := ⊥
  | n x (p ⋀ q)    := (subst_nth n x p) ⋀ (subst_nth n x q)
  | n x (p ⋁ q)    := (subst_nth n x p) ⋁ (subst_nth n x q)
  | n x (p ⟹ q)  := (subst_nth n x p) ⟹ (subst_nth n x q)
  | n x (a ∈ α)    := (subst_nth n x a) ∈ (subst_nth n x α)
  | n x ⟪a,c⟫      := ⟪subst_nth n x a, subst_nth n x c⟫
  | n x (var m)    := if n=m then x else var m
  | n x ⟦φ⟧         :=    ⟦subst_nth (n+1) (lift 1 0 x) φ⟧
  | n x (∀' φ)     := ∀' (subst_nth (n+1) (lift 1 0 x) φ)
  | n x (∃' φ)     := ∃' (subst_nth (n+1) (lift 1 0 x) φ)

  def subst := subst_nth 0

  notation  φ `⁅` b `⁆` := subst b φ

  #reduce 𝟘⁅⊤ ⋀ ⊥⁆
  #reduce 𝟙⁅⊤ ⋀ ⊥⁆

end substitution

section proofs

  inductive proof : context → term → term → Prop
  | axm        {Γ φ}         : WF Γ Ω φ → proof Γ φ φ
  | vac        {Γ φ}         : WF Γ Ω φ → proof Γ φ ⊤
  | abs        {Γ φ}         : WF Γ Ω φ → proof Γ ⊥ φ
  | and_intro  {Γ p q r}     : proof Γ p q → proof Γ p r → proof Γ p (q ⋀ r)  
  | and_left   {Γ} (p q r)   : proof Γ p (q ⋀ r) → proof Γ p q
  | and_right  {Γ} (p q r)   : proof Γ p (q ⋀ r) → proof Γ p r
  | or_intro   {Γ p q r}     : proof Γ p r → proof Γ q r → proof Γ (p ⋁ q) r  
  | or_left    {Γ} (p q r)   : proof Γ (p ⋁ q) r → proof Γ p r
  | or_right   {Γ} (p q r)   : proof Γ (p ⋁ q) r → proof Γ q r
  | imp_to_and {Γ p q r}     : proof Γ p (q ⟹ r) → proof Γ (p ⋀ q) r
  | and_to_imp {Γ p q r}     : proof Γ (p ⋀ q) r → proof Γ p (q ⟹ r)
  | weakening  {Γ φ ψ B}     : proof Γ φ ψ → proof (list.concat Γ B) φ ψ
  | cut        {Γ} (φ c ψ)   : proof Γ φ c → proof Γ c ψ → proof Γ φ ψ
  | all_elim   {Γ p φ B}     : proof Γ p (∀' φ) → proof (B::Γ) p φ
  | all_intro  {Γ p φ} (B)   : proof (B::Γ) p φ → proof Γ p (∀' φ)
  | ex_elim    {Γ p φ B}     : proof Γ p (∃' φ) → proof (B::Γ) p φ
  | ex_intro   {Γ p φ B}     : proof (B::Γ) p φ → proof Γ p (∃' φ)
  | ext                      : proof [] ⊤ $ ∀' ∀' (∀' (𝟘 ∈ 𝟚) ⇔ (𝟘 ∈ 𝟙)) ⟹ (𝟙 ≃ 𝟘)
  | prop_ext                 : proof [] ⊤ ∀' ∀' (𝟙 ⇔ 𝟘) ⟹ (𝟚 ≃ 𝟙)
  | star_unique              : proof [] ⊤ ∀' (𝟙 ≃ ⁎)
  | pair_exists_rep          : proof [] ⊤ ∀' ∃' ∃' 𝟚 ≃ ⟪𝟙,𝟘⟫
  | pair_distinct_rep        : proof [] ⊤ ∀' ∀' ∀' ∀' (⟪𝟜,𝟚⟫ ≃ ⟪𝟛,𝟙⟫) ⟹ (𝟜 ≃ 𝟛 ⋀ 𝟚 ≃ 𝟙)
  | apply      {Γ B} (φ ψ b) : WF Γ B b → proof (B::Γ) φ ψ → proof Γ (φ⁅b⁆) (ψ⁅b⁆)
  | comp       {Γ φ A}       : WF (A::A::Γ) Ω φ → proof Γ ⊤ (∀' (𝟘 ∈ ⟦φ⟧) ⇔ (φ⁅𝟙⁆))

  prefix ⊢ := proof [] ⊤
  infix ` ⊢ `:50 := proof []
  notation φ ` ⊢[` Γ:(foldr `,` (h t, list.cons h t) list.nil) `] ` ψ := proof Γ φ ψ
  notation `⊢[` Γ:(foldr `,` (h t, list.cons h t) list.nil) `] ` ψ := proof Γ ⊤ ψ

  variables p q : term

  #reduce   ⊢ (p ⋁ ∼p)  -- proof [] ⊤ (or p (imp p ⊥))
  #reduce q ⊢ (p ⋁ ∼p)  -- proof [] q (or p (imp p ⊥))
  #reduce   ⊢[Ω,Unit] p -- proof [Ω,Unit] ⊤ p
  #reduce q ⊢[Ω,Unit] p -- proof [Ω,Unit] q p

  variable {Γ : context}
  variables φ ψ : term

  lemma WF.proof_left  : proof Γ φ ψ → WF Γ Ω φ := sorry
  lemma WF.proof_right : proof Γ φ ψ → WF Γ Ω ψ := sorry

end proofs

end TT