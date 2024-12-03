
import EffectCompiler.STLC_Sum.Basic
import EffectCompiler.STLC_Sum.SmallStep
import EffectCompiler.STLC_Sum.TypeSafety

import Mathlib.Data.Set.Basic

open Relation


set_option maxHeartbeats 320000

namespace STLC_Sum

def ISmallStep : Γ ⊢ A → Γ ⊢ A → Prop := fun t t' => t' ⟶ₛ t
infix : 30 " ₛ⟵ " => ISmallStep
def sn : Γ ⊢ A → Prop := Acc (ISmallStep)

inductive snr : Γ ⊢ A → Γ ⊢ A → Prop where
  | ξ_p₁ : snr ab ab' → snr (.p₁ ab) (.p₁ ab')
  | ξ_p₂ : snr ab ab' → snr (.p₂ ab) (.p₂ ab')
  | β_p₁ : sn b → snr (.p₁ (.pair a b)) a
  | β_p₂ : sn a → snr (.p₂ (.pair a b)) b
  | ξ_app : {f f' : Γ ⊢ (A ⇒ B)} → snr f f' → sn x → snr (.app f x) (.app f' x)
  | β_app : sn x → snr (.app (.lam _ f) x) f[[x]]₀
  | ξ_case : snr m m' → snr (.case m a b) (.case m' a b)
  | β_case₁ : sn x → sn b → snr (.case (.inl x) a b) a[[x]]₀
  | β_case₂ : sn x → sn a → snr (.case (.inr x) a b) b[[x]]₀
infix : 30 " ⟶sn " => snr

def sn_of_normal : Normal t → sn t :=
  fun hn_t => Acc.intro t
  fun t' htt' => (Normal.not_progress hn_t t' htt').elim
def sn_of_neutral : Neutral t → sn t :=
  fun hne_t => Acc.intro t
  fun t' htt' => (Neutral.not_progress hne_t t' htt').elim

-- instance (priority:=high) : WellFoundedRelation {t : Γ ⊢ A // sn t} where
--   rel := fun t t' => t.1 ₛ⟵ t'.1
--   wf := .intro fun ⟨t, ht⟩ => by
--     let f : {t : Γ ⊢ A // sn t} → Γ ⊢ A := (fun t => t.1)
--     let rel := InvImage ISmallStep f
--     have : (fun t t' => t.1 ₛ⟵ t'.1) = rel := by
--       simp [InvImage]
--     rw [this]
--     apply InvImage.accessible f
--     assumption

-- mutual
-- inductive SNe : Γ ⊢ A → Prop where
--   | var : SNe (.var x)
--   | p₁ : SNe ab → SNe (.p₁ ab)
--   | p₂ : SNe ab → SNe (.p₂ ab)
--   | app : SNe f → SN x → SNe (.app f x)
-- inductive SN : Γ ⊢ A → Prop where
--   | unit : SN .unit
--   | pair : SN a → SN b → SN (.pair a b)
--   | lam : SN e → SN (.lam _ e)
--   | exp : SNR t t' → SN t' → SN t
--   | sne : SNe t → SN t
-- inductive SNR : Γ ⊢ A → Γ ⊢ A → Prop
--   | ξ_p₁ : SNR ab ab' → SNR (.p₁ ab) (.p₁ ab')
--   | ξ_p₂ : SNR ab ab' → SNR (.p₂ ab) (.p₂ ab')
--   | β_p₁ : SN a → SNR (.p₁ (.pair a b)) a
--   | β_p₂ : SN b → SNR (.p₂ (.pair a b)) b
--   | ξ_app : {f f' : Γ ⊢ (A ⇒ B)} → SNR f f' → (x : Γ ⊢ A) → SNR (.app f x) (.app f' x)
--   | β_app : SN x → SNR (.app (.lam _ f) x) f[[x]]₀
-- end
-- infix : 30 " ⟶SN " => SNR

namespace sn

def inv : sn t → t ⟶* t' → sn t' := by
  intro hsn_t htt'
  induction htt' using ReflTransGen.head_induction_on with
  | refl => exact hsn_t
  | head htt'' _ ih =>
  apply ih
  apply Acc.inv
  assumption
  assumption

def pair : sn a → sn b → sn (.pair a b) := by
  intro hsn_a hsn_b
  induction hsn_a generalizing b
  case intro a ha iha =>
  induction hsn_b generalizing a
  case intro b hb ihb =>
  constructor
  intro hab' habab'
  cases habab' with
  | ξ_PAIR₁ haa' =>
    apply iha
    assumption
    constructor
    intro b' hbb'
    exact hb b' hbb'
  | ξ_PAIR₂ hbb' =>
    apply ihb
    assumption
    assumption
    assumption
def p₁ : sn ab → sn (.p₁ ab) := by
  intro hsn
  induction hsn with
  | intro ab ih₁ ih₂ =>
  constructor
  intro t' htt'
  cases htt' with
  | ξ_P₁ habab' =>
    apply ih₂
    assumption
  | β_P₁ =>
    constructor
    intro a hta
    have := ih₂ _ (.ξ_PAIR₁ hta)
    apply Acc.inv this
    exact .β_P₁
def p₂ : sn ab → sn (.p₂ ab) := by
  intro hsn
  induction hsn with
  | intro ab ih₁ ih₂ =>
  constructor
  intro t' htt'
  cases htt' with
  | ξ_P₂ habab' =>
    apply ih₂
    assumption
  | β_P₂ =>
    constructor
    intro a hta
    have := ih₂ _ (.ξ_PAIR₂ hta)
    apply Acc.inv this
    exact .β_P₂
def lam : sn e → sn (.lam _ e) := by
  intro hsn_e
  induction hsn_e with
  | intro e _ ih =>
  constructor
  intro t' htt'
  cases htt' with
  | ξ_LAM hee' =>
  apply ih
  assumption

def app_lemma : sn e[[x]]₀ → sn e := by
  generalize h : e[[x]]₀ = t
  intro hsn
  induction hsn generalizing e
  case intro t _ ih =>
  constructor
  intro e' hee'
  apply ih
  rw [←h]
  exact SmallStep.ξσ hee'
  rfl

def wh_app : sn x → sn e[[x]]₀ → sn ((.lam _ e) @ x) := by
  intro hsn_x
  intro hsn_ex
  have hsn_e := app_lemma hsn_ex
  induction hsn_x generalizing e
  case intro e _ ihx =>
  induction hsn_e generalizing x
  case intro e he ihe =>
  constructor
  intro t' htt'
  cases htt' with
  | ξ_APP₁ hff' =>
    cases hff' with
    | ξ_LAM hee' =>
    apply ihe
    assumption
    assumption
    apply Acc.inv
    assumption
    exact SmallStep.ξσ hee'
  | ξ_APP₂ hxx' =>
    apply ihx
    assumption
    apply inv
    assumption
    apply MultiStep.ξσ'
    {
      intro B y
      cases y with
      | zero =>
        simp [Subst.cons]
        apply ReflTransGen.head
        assumption
        exact .refl
      | succ y =>
        simp [Subst.cons]
        exact .refl
    }
    constructor
    intro e' hee'
    apply he
    assumption
  | β_APP =>
    assumption

def inl : sn a → sn (.inl (B:=B) a) := sorry
def inr : sn b → sn (.inr (A:=A) b) := sorry
def case : sn m → sn a → sn b → sn (.case m a b) := sorry

namespace Subterm

def p₁ : sn (.p₁ ab) → sn ab := by
  generalize h : STLC_Sum.Term.p₁ ab = t
  intro hsn
  induction hsn generalizing ab
  case intro t _ ih =>
  constructor
  intro t' htt'
  apply ih
  rw [←h]
  exact .ξ_P₁ htt'
  rfl

def p₂ : sn (.p₂ ab) → sn ab := by
  generalize h : STLC_Sum.Term.p₂ ab = t
  intro hsn
  induction hsn generalizing ab
  case intro t _ ih =>
  constructor
  intro t' htt'
  apply ih
  rw [←h]
  exact .ξ_P₂ htt'
  rfl

def pair : sn (.pair a b) → sn a ∧ sn b := by
  generalize h : STLC_Sum.Term.pair a b = t
  intro hsn_t
  induction hsn_t generalizing a b
  case intro t h ih =>
  constructor
  {
    constructor
    intro a' haa'
    subst t
    apply (ih (.pair a' b) (.ξ_PAIR₁ haa') rfl).1
  }
  {
    constructor
    intro b' hbb'
    subst t
    apply (ih (.pair a b') (.ξ_PAIR₂ hbb') rfl).2
  }

def app : sn (f @ x) → sn f ∧ sn x := by
  generalize h : f @ x = t
  intro hsn
  induction hsn generalizing f x
  case intro t h ih =>
  subst t
  constructor
  constructor
  intro f' hff'
  exact (ih (f' @ x) (.ξ_APP₁ hff') rfl).1
  constructor
  intro x' hxx'
  apply (ih (f @ x') (.ξ_APP₂ hxx') rfl).2

def lam : sn (.lam B e) → sn e := by
  generalize h : STLC_Sum.Term.lam B e = t
  intro hsn
  induction hsn generalizing e
  case intro t h ih =>
  constructor
  intro e' hee'
  subst t
  apply ih (.lam B e') (.ξ_LAM hee') rfl

end Subterm


def confluence : {t t₁ t₂ : Γ ⊢ A} → t ⟶sn t₁ → t ⟶ₛ t₂ → t₁ = t₂ ∨ ∃ t' : Γ ⊢ A, (t₁ ⟶* t') ∧ (t₂ ⟶sn t') := by
  intro t t₁ t₂ htt₁ htt₂
  induction htt₁ with
  | ξ_p₁ habab' ih =>
    cases htt₂ with
    | ξ_P₁ habab'' =>
      cases ih habab'' with
      | inl h =>
        apply Or.inl
        rw [h]
      | inr h =>
        apply Or.inr
        have ⟨ab'', _, _⟩ := h
        exists .p₁ ab''
        constructor
        apply MultiStep.ξ_p₁
        assumption
        constructor
        assumption
    | β_P₁ => contradiction
  | ξ_p₂ habab' ih =>
    cases htt₂ with
    | ξ_P₂ habab'' =>
      cases ih habab'' with
      | inl h =>
        apply Or.inl
        rw [h]
      | inr h =>
        apply Or.inr
        have ⟨ab'', _, _⟩ := h
        exists .p₂ ab''
        constructor
        apply MultiStep.ξ_p₂
        assumption
        constructor
        assumption
    | β_P₂ => contradiction
  | β_p₁ hsn_b =>
    cases htt₂ with
    | ξ_P₁ habab'' =>
      rename_i ab''
      cases ab''
      case pair a'' b'' =>
        cases habab'' with
        | ξ_PAIR₁ haa'' => exact Or.inr ⟨a'', .head haa'' .refl, .β_p₁ hsn_b⟩
        | ξ_PAIR₂ hbb'' => exact Or.inr ⟨_, .refl, .β_p₁ (sn.inv hsn_b (.head hbb'' .refl))⟩
      repeat contradiction
    | β_P₁ => exact Or.inl rfl
  | β_p₂ hsn_a =>
    cases htt₂ with
    | ξ_P₂ habab'' =>
      rename_i ab''
      cases ab''
      case pair a'' b'' =>
        cases habab'' with
        | ξ_PAIR₁ haa'' => exact Or.inr ⟨_, .refl, .β_p₂ (sn.inv hsn_a (.head haa'' .refl))⟩
        | ξ_PAIR₂ hbb'' => exact Or.inr ⟨b'', .head hbb'' .refl, .β_p₂ hsn_a⟩
      repeat contradiction
    | β_P₂ => exact Or.inl rfl
  | ξ_app hff' hsn_x ih =>
    rename_i x f f'
    cases htt₂ with
    | ξ_APP₁ hff'' =>
      cases ih hff'' with
      | inl h =>
        apply Or.inl
        rw [h]
      | inr h =>
        apply Or.inr
        have ⟨f'', hff'', _⟩ := h
        exists f'' @ x
        constructor
        apply MultiStep.ξ_app₁
        assumption
        constructor
        assumption
        assumption
    | ξ_APP₂ hxx' =>
      rename_i x'
      apply Or.inr
      exists f' @ x'
      constructor
      apply ReflTransGen.head _ .refl
      exact .ξ_APP₂ hxx'
      constructor
      assumption
      exact sn.inv hsn_x (.head hxx' .refl)
    | β_APP  => contradiction
  | β_app hsn_x =>
    rename_i x e
    cases htt₂ with
    | ξ_APP₁ hff' =>
      rename_i f'
      cases f'
      case lam _ e' =>
        cases hff' with
        | ξ_LAM hee' =>
          apply Or.inr
          exists e'[[x]]₀
          constructor
          apply MultiStep.ξσ
          apply ReflTransGen.head
          assumption
          constructor
          constructor
          assumption
      repeat contradiction
    | ξ_APP₂ hxx' =>
      rename_i x x'
      apply Or.inr
      exists e[[x']]₀
      constructor
      apply MultiStep.ξσ'
      intro B y
      cases y with
      | zero =>
        apply ReflTransGen.head
        assumption
        constructor
      | succ y => constructor
      constructor
      exact sn.inv hsn_x (.head hxx' .refl)
    | β_APP => exact Or.inl rfl
  | ξ_case hmm' ih =>
    rename_i D B C m m' a b
    cases htt₂ with
    | ξ_CASE₁ hmm'' =>
      cases ih hmm'' with
      | inl h =>
        rw [←h]
        apply Or.inl
        rfl
      | inr h =>
        apply Or.inr
        have ⟨m'', _, _⟩:= h
        exists .case m'' a b
        constructor
        apply MultiStep.ξ_case₁
        assumption
        constructor
        assumption
    | ξ_CASE₂ haa' =>
      rename_i a'
      apply Or.inr
      exists .case m' a' b
      constructor
      apply MultiStep.ξ_case₂
      apply ReflTransGen.head _ .refl
      assumption
      constructor
      assumption
    | ξ_CASE₃ hbb' =>
      rename_i b'
      apply Or.inr
      exists .case m' a b'
      constructor
      apply MultiStep.ξ_case₃
      apply ReflTransGen.head _ .refl
      assumption
      constructor
      assumption
    | β_CASE₁ => contradiction
    | β_CASE₂ => contradiction
  | β_case₁ hsn_x hsn_b =>
    rename_i D B x C b a
    cases htt₂ with
    | ξ_CASE₁ hmm' =>
      rename_i m'
      cases m'
      any_goals contradiction
      apply Or.inr
      rename_i x'
      exists a[[x']]₀
      constructor
      {
        apply MultiStep.ξσ'
        intro E y
        cases y with
        | zero =>
          simp [Subst.cons]
          cases hmm'
          apply ReflTransGen.head
          assumption
          rfl
        | succ y =>
          simp [Subst.cons]
          apply ReflTransGen.refl
      }
      {
        constructor
        cases hmm'
        apply inv
        assumption
        apply ReflTransGen.head
        assumption
        exact ReflTransGen.refl
        assumption
      }
    | ξ_CASE₂ haa' =>
      rename_i a'
      apply Or.inr
      exists a'[[x]]₀
      constructor
      apply MultiStep.ξσ
      apply ReflTransGen.head
      assumption
      constructor
      constructor
      assumption
      assumption
    | ξ_CASE₃ hbb' =>
      rename_i b'
      apply Or.inr
      exists a[[x]]₀
      constructor
      constructor
      constructor
      assumption
      apply inv
      assumption
      apply ReflTransGen.head
      assumption
      constructor
    | β_CASE₁ =>
      apply Or.inl
      rfl
  | β_case₂ hsn_m hsn_a =>
    rename_i D B x C a b
    cases htt₂ with
    | ξ_CASE₁ hmm' =>
      rename_i m'
      cases m'
      any_goals contradiction
      apply Or.inr
      rename_i x'
      exists b[[x']]₀
      constructor
      {
        apply MultiStep.ξσ'
        intro E y
        cases y with
        | zero =>
          simp [Subst.cons]
          cases hmm'
          apply ReflTransGen.head
          assumption
          rfl
        | succ y =>
          simp [Subst.cons]
          apply ReflTransGen.refl
      }
      {
        constructor
        cases hmm'
        apply inv
        assumption
        apply ReflTransGen.head
        assumption
        exact ReflTransGen.refl
        assumption
      }
    | ξ_CASE₂ haa' =>
      rename_i a'
      apply Or.inr
      exists b[[x]]₀
      constructor
      constructor
      constructor
      assumption
      apply inv
      assumption
      apply ReflTransGen.head
      assumption
      constructor
    | ξ_CASE₃ hbb' =>
      rename_i b'
      apply Or.inr
      exists b'[[x]]₀
      constructor
      apply MultiStep.ξσ
      apply ReflTransGen.head
      assumption
      constructor
      constructor
      assumption
      assumption
    | β_CASE₂ =>
      apply Or.inl
      rfl

def closed_backward_lemma : sn f → sn x → f ⟶sn f' → sn (f' @ x) → sn (f @ x) := by
  intro hsn_f hsn_x hff' hsn_t'
  induction hsn_f generalizing x f'
  case intro f hf ihf =>
  induction hsn_x generalizing f f'
  case intro x hx ihx =>
  constructor
  intro t' htt'
  cases htt' with
  | ξ_APP₁ hff'' =>
    cases confluence hff' hff'' with
    | inl h =>
      subst f'
      assumption
    | inr h =>
      let ⟨φ, hf'φ, _⟩ := h
      have : sn (φ @ x) := sn.inv hsn_t' (MultiStep.ξ_app₁ hf'φ)
      apply ihf
      assumption
      constructor
      intro x' hxx''
      exact hx _ hxx''
      assumption
      assumption
  | ξ_APP₂ hxx' =>
    apply ihx
    assumption
    intro f'' hff''
    exact hf _ hff''
    exact ihf
    assumption
    exact sn.inv hsn_t' (.head (.ξ_APP₂ hxx') .refl)
  | β_APP => contradiction


def closed_backward : t ⟶sn t' → sn t' → sn t
  | .ξ_p₁ habab', hsn_t' =>
    p₁ (closed_backward habab' (Subterm.p₁ hsn_t'))
  | .ξ_p₂ habab', hsn_t' =>
    p₂ (closed_backward habab' (Subterm.p₂ hsn_t'))
  | .β_p₁ hsn_b, hsn_t' =>
    p₁ (pair hsn_t' hsn_b)
  | .β_p₂ hsn_a, hsn_t' =>
    p₂ (pair hsn_a hsn_t')
  | .ξ_app hff' hsn_x, hsn_t' =>
    closed_backward_lemma (closed_backward hff' (Subterm.app hsn_t').1) hsn_x hff' hsn_t'
  | .β_app hsn_x, hsn_t' =>
    wh_app hsn_x hsn_t'
  | .ξ_case hmm', hsn_t' => sorry
  | .β_case₁ hsn_m' hsn_b, hsn_t' => sorry
  | .β_case₂ hsn_m' hsn_a, hsn_t' => sorry

def ξρ_lemma : t{{ρ}}ᵣ ⟶ₛ s → ∃ t', s = t'{{ρ}}ᵣ ∧ (t ⟶ₛ t') := by
  intro htᵣs
  rename_i Γ A Δ
  induction t generalizing Δ with
  | unit => contradiction
  | var x => contradiction
  | pair a b ih₁ ih₂ =>
    cases htᵣs with
    | ξ_PAIR₁ haᵣa' =>
      have ⟨a', ha'_eq, haa'⟩ := ih₁ haᵣa'
      exists (.pair a' b)
      constructor
      rw [ha'_eq]
      rfl
      constructor
      assumption
    | ξ_PAIR₂ hbᵣb' =>
      have ⟨b', hb'_eq, hbb'⟩ := ih₂ hbᵣb'
      exists (.pair a b')
      constructor
      rw [hb'_eq]
      rfl
      constructor
      assumption
  | p₁ ab ih =>
    cases ab
    case var x => contradiction
    case pair a b =>
      cases htᵣs with
      | ξ_P₁ habab' =>
        have ⟨ab', hab'_eq, habab'⟩ := ih habab'
        exists .p₁ ab'
        constructor
        rw [hab'_eq]
        rfl
        constructor
        assumption
      | β_P₁ =>
        exists a
        constructor
        rfl
        constructor
    all_goals cases htᵣs with
    | ξ_P₁ habab' =>
      have ⟨ab', hab'_eq, habab'⟩ := ih habab'
      exists .p₁ ab'
      constructor
      rw [hab'_eq]
      rfl
      constructor
      assumption
  | p₂ ab ih =>
    cases ab
    case var x => contradiction
    case pair a b =>
      cases htᵣs with
      | ξ_P₂ habab' =>
        have ⟨ab', hab'_eq, habab'⟩ := ih habab'
        exists .p₂ ab'
        constructor
        rw [hab'_eq]
        rfl
        constructor
        assumption
      | β_P₂ =>
        exists b
        constructor
        rfl
        constructor
    all_goals cases htᵣs with
    | ξ_P₂ habab' =>
      have ⟨ab', hab'_eq, habab'⟩ := ih habab'
      exists .p₂ ab'
      constructor
      rw [hab'_eq]
      rfl
      constructor
      assumption
  | lam B e ih =>
    cases htᵣs with
    | ξ_LAM hee' =>
    have ⟨e', heq_e', hee'⟩ := ih hee'
    exists .lam B e'
    constructor
    rw [heq_e']
    rfl
    constructor
    assumption
  | app f x ih₁ ih₂ =>
    cases f with
    | var x' =>
      cases htᵣs with
      | ξ_APP₁ _ => contradiction
      | ξ_APP₂ hxᵣx' =>
        have ⟨x'', heq_x'', hxx''⟩ := ih₂ hxᵣx'
        exists .app (.var x') x''
        constructor
        rw [heq_x'']
        rfl
        constructor
        assumption
    | p₁ ab =>
      cases htᵣs with
      | ξ_APP₁ habᵣab' =>
        have ⟨f', heq_f', hf'⟩ := ih₁ habᵣab'
        exists .app f' x
        constructor
        rw [heq_f']
        rfl
        constructor
        assumption
      | ξ_APP₂ hxᵣx' =>
        have ⟨x', heq_x', hx'⟩ := ih₂ hxᵣx'
        exists .app (.p₁ ab) x'
        constructor
        rw [heq_x']
        rfl
        constructor
        assumption
    | p₂ ab =>
      cases htᵣs with
      | ξ_APP₁ habᵣab' =>
        have ⟨f', heq_f', hf'⟩ := ih₁ habᵣab'
        exists .app f' x
        constructor
        rw [heq_f']
        rfl
        constructor
        assumption
      | ξ_APP₂ hxᵣx' =>
        have ⟨x', heq_x', hx'⟩ := ih₂ hxᵣx'
        exists .app (.p₂ ab) x'
        constructor
        rw [heq_x']
        rfl
        constructor
        assumption
    | lam B e =>
      cases htᵣs with
      | ξ_APP₁ heᵣe' =>
        have ⟨f', heq_f', hf'⟩ := ih₁ heᵣe'
        exists .app f' x
        constructor
        rw [heq_f']
        rfl
        constructor
        assumption
      | ξ_APP₂ hxᵣx' =>
        have ⟨x', heq_x', hx'⟩ := ih₂ hxᵣx'
        exists .app (.lam _ e) x'
        constructor
        rw [heq_x']
        rfl
        constructor
        assumption
      | β_APP =>
        exists e[[x]]₀
        constructor
        show e{{ρ ⁺⁺ (_ : Ty)}}ᵣ[[x{{ρ}}ᵣ]]₀ = e[[x]]₀{{ρ}}ᵣ
        rw [Parallel.ξρ_lemma]
        constructor
    | app f' x' =>
      cases htᵣs with
      | ξ_APP₁ hfᵣf' =>
        have ⟨f', heq_f', hff'⟩ := ih₁ hfᵣf'
        exists .app f' x
        constructor
        rw [heq_f']
        rfl
        constructor
        assumption
      | ξ_APP₂ hxᵣx' =>
        have ⟨x'', heq_x'', hxx''⟩ := ih₂ hxᵣx'
        exists .app (.app f' x') x''
        constructor
        rw [heq_x'']
        rfl
        constructor
        assumption
    | case m a b =>
      cases htᵣs with
      | ξ_APP₁ hfᵣf' =>
        have ⟨f', heq_f', hff'⟩ := ih₁ hfᵣf'
        exists .app f' x
        constructor
        rw [heq_f']
        rfl
        constructor
        assumption
      | ξ_APP₂ hxᵣx' =>
        have ⟨x', heq_x', hx'⟩ := ih₂ hxᵣx'
        exists STLC_Sum.Term.app (.case m a b) x'
        constructor
        rw [heq_x']
        rfl
        constructor
        assumption
  | inl a iha => sorry
  | inr b ihb => sorry
  | case m a b ihm iha ihb => sorry

def ξρ : sn t → sn t{{ρ}}ᵣ := by
  intro hsn_t
  rename_i Γ A Δ
  induction hsn_t generalizing ρ
  case intro t' _ ih =>
  constructor
  intro t''ᵣ ht'ᵣt''ᵣ
  have ⟨t'', heq_t'', ht't''⟩ := ξρ_lemma ht'ᵣt''ᵣ
  rw [heq_t'']
  exact ih t'' ht't''

namespace LogicalRelation

inductive sne : Γ ⊢ A → Prop where
  | var : sne (.var x)
  | p₁ : sne ab → sne (.p₁ ab)
  | p₂ : sne ab → sne (.p₂ ab)
  | app : sne f → sn x → sne (.app f x)
  | case : sne m → sn a → sn b → sne (.case m a b)

inductive sn_closure : {A : Ty} → Set (Γ ⊢ A) → Γ ⊢ A → Prop where
  | p : P t → sn_closure P t
  | sne : sne t → sn_closure P t
  | sn : t ⟶sn t' → sn_closure P t' → sn_closure P t
deriving instance SizeOf for sn_closure

def R : (A : Ty) → Δ ⊢ A → Prop
  | 𝟙, t => sn t
  | A ⊗ B, ab => sn ab ∧ R A (.p₁ ab) ∧ R B (.p₂ ab)
  | A ⇒ B, f => sn f ∧ (∀ Γ, ∀ ρ : Renaming Γ Δ, ∀ x : Γ ⊢ A, R A x → R B (f{{ρ}}ᵣ @ x))
  | A ⨁ B, m => sn m
    ∧ sn_closure ({STLC_Sum.Term.inl a | (a : Δ ⊢ A) (_ : R A a)} ∪ {STLC_Sum.Term.inr b | (b : Δ ⊢ B) (_ : R B b)}) m

def sn_of_R : {A : Ty} → {t : Γ ⊢ A} → R A t → sn t
  | 𝟙, _, hr_t => hr_t
  | _ ⊗ _, _, hr_t => hr_t.1
  | _ ⇒ _, _, hr_t => hr_t.1
  | _ ⨁ _, _, hr_t => hr_t.1

def satisfy (Γ : Context Ty) (σ : Subst Γ Δ) : Prop := ∀ A, ∀ x : Δ ∋ A, R A (σ A x)
local infix : 60 (priority:=high) " ⊨ " => satisfy

def snr.ξρ : t ⟶sn t' → t{{ρ}}ᵣ ⟶sn t'{{ρ}}ᵣ
  | .ξ_p₁ habab' => .ξ_p₁ (snr.ξρ habab')
  | .ξ_p₂ habab' => .ξ_p₂ (snr.ξρ habab')
  | .β_p₁ hsn_b => .β_p₁ (sn.ξρ hsn_b)
  | .β_p₂ hsn_a => .β_p₂ (sn.ξρ hsn_a)
  | .ξ_app hff' hsn_x => .ξ_app (snr.ξρ hff') (sn.ξρ hsn_x)
  | .β_app hsn_x => Parallel.ξρ_lemma ρ _ _ ▸ .β_app (sn.ξρ hsn_x)

def R.ξρ : {A : Ty} → {t : Γ ⊢ A} → R A t →  R A t{{ρ}}ᵣ
  | 𝟙, t, hr_t => sn.ξρ hr_t
  | A ⊗ B, t, hr_t => ⟨sn.ξρ (sn_of_R hr_t), ξρ hr_t.2.1, ξρ hr_t.2.2⟩
  | A ⇒ B, t, hr_t =>
    have h : ∀ (Δ : Context Ty) (ρ' : Renaming Δ _) (x : Δ ⊢ A), R A x → R B (t{{ρ}}ᵣ{{ρ'}}ᵣ @ x) := by
      intro Δ ρ' x hr_x
      rw [←Renaming.ren_comp]
      apply hr_t.2
      assumption
    ⟨sn.ξρ (sn_of_R hr_t), h⟩
  | A ⨁ B, t, hr_t =>
    sorry

def R.closed_backward : {A : Ty} → {t t' : Γ ⊢ A} → t ⟶sn t' → R A t' → R A t
  | 𝟙, _, _, htt', hr_t' => sn.closed_backward htt' hr_t'
  | _ ⊗ _, _, _, htt', hr_t' => ⟨sn.closed_backward htt' (sn_of_R hr_t'), R.closed_backward (.ξ_p₁ htt') hr_t'.2.1, R.closed_backward (.ξ_p₂ htt') hr_t'.2.2⟩
  | A ⇒ B, t, _, htt', hr_t' =>
    have h : ∀(Δ : Context Ty) (ρ : Renaming Δ Γ) (x : Δ ⊢ A), R A x → R B (t{{ρ}}ᵣ @ x) :=
      fun Δ ρ x hr_x =>
      R.closed_backward (.ξ_app (snr.ξρ htt') (sn_of_R hr_x)) (hr_t'.2 Δ ρ x hr_x)
    ⟨sn.closed_backward htt' (sn_of_R hr_t'), h⟩

def R.closed_forward : {A : Ty} → {t t' : Γ ⊢ A} → t ⟶ₛ t' → R A t → R A t' := by
  intro A t t' htt' hr_t
  induction A generalizing Γ with
  | unit =>
    apply Acc.inv hr_t htt'
  | prod A B ih₁ ih₂ =>
    constructor
    apply Acc.inv hr_t.1 htt'
    constructor
    apply ih₁
    constructor
    assumption
    exact hr_t.2.1
    apply ih₂
    constructor
    assumption
    exact hr_t.2.2
  | fn A B _ ih₂ =>
    constructor
    apply Acc.inv hr_t.1 htt'
    intro Δ ρ x hr_x
    apply ih₂
    constructor
    apply SmallStep.ξρ
    assumption
    apply hr_t.2
    assumption

def not_β : Γ ⊢ A → Prop
  | .lam _ _ => false
  | .pair _ _ => false
  | _ => true

def not_β_expansion_closed (P : Γ ⊢ A →  Prop) : Prop := ∀ t, not_β t → (∀ t', t ⟶ₛ t' → P t') → P t

def sne.closed_forward : t ⟶ₛ t' → sne t → sne t' := by
  intro htt' hsne_t
  induction hsne_t with
  | var => contradiction
  | p₁ hsne_ab ih =>
    cases htt' with
    | ξ_P₁ habab' =>
      apply p₁
      apply ih
      assumption
    | β_P₁ => contradiction
  | p₂ hsne_ab ih =>
    cases htt' with
    | ξ_P₂ habab' =>
      apply p₂
      apply ih
      assumption
    | β_P₂ => contradiction
  | app hsne_f hsn_x ih =>
    cases htt' with
    | ξ_APP₁ hff' =>
      apply app
      apply ih
      assumption
      assumption
    | ξ_APP₂ hxx' =>
      apply app
      assumption
      apply sn.inv hsn_x (.head hxx' .refl)
    | β_APP => contradiction
def sn_of_sne_lemma : sne f → sn f → sn x → sn (f @ x) := by
  intro hsne_f hsn_f hsn_x
  induction hsn_f generalizing x
  case intro f hf ihf =>
  induction hsn_x generalizing f
  case intro x hx ihx =>
  constructor
  intro t' htt'
  cases htt' with
  | ξ_APP₁ hff' =>
    rename_i f'
    apply ihf
    assumption
    apply sne.closed_forward
    assumption
    assumption
    constructor
    intro x' hxx'
    exact hx x' hxx'
  | ξ_APP₂ hxx' =>
    rename_i x'
    apply ihx
    assumption
    intro f' hff'
    exact hf f' hff'
    assumption
    assumption
  | β_APP => contradiction

def sn_of_sne : sne t → sn t
  | .var => sn_of_neutral .var
  | .p₁ hsne_ab => p₁ (sn_of_sne hsne_ab)
  | .p₂ hsne_ab => p₂ (sn_of_sne hsne_ab)
  | .app hsne_f hsn_x => sn_of_sne_lemma hsne_f (sn_of_sne hsne_f) hsn_x
def sne.ξρ : sne t → sne t{{ρ}}ᵣ
  | .var => .var
  | .p₁ hsne_ab => .p₁ (ξρ hsne_ab)
  | .p₂ hsne_ab => .p₂ (ξρ hsne_ab)
  | .app hsne_f hsn_x => .app (ξρ hsne_f) (sn.ξρ hsn_x)

def R_of_sne : {A : Ty} → {t : Γ ⊢ A} → sne t → R A t
  | 𝟙, _, hsne_t => sn_of_sne hsne_t
  | _ ⊗ _, _, hsne_t => ⟨sn_of_sne hsne_t, R_of_sne (.p₁ hsne_t), R_of_sne (.p₂ hsne_t)⟩
  | A ⇒ B, t, hsne_t =>
    have h : ∀ (Δ : Context Ty) (ρ : Renaming Δ Γ) (x : Δ ⊢ A), R A x → R B (t{{ρ}}ᵣ @ x) :=
      fun _ _ _ hr_x =>
      R_of_sne (.app (sne.ξρ hsne_t) (sn_of_R hr_x))
    ⟨sn_of_sne hsne_t, h⟩

def satisfy_extend : Γ ⊨ σ → (Γ; A) ⊨ (σ ⁺⁺ A) :=
  fun h => fun A x =>
  match x with
  | .zero => R_of_sne .var
  | .succ x => by
    simp [PAddAdd.paddadd, Subst.extend]
    show R _ _{{_}}ᵣ
    apply R.ξρ (h _ _)
def satisfy_cons : Γ ⊨ σ → R _ x → Γ ⊨ (σ ::ₛ x) :=
  fun h hsn_x => fun B y =>
  match y with
  | .zero => hsn_x
  | .succ y => h _ y
def satisfy_comp_ren_sub : Δ ⊨ σ → Γ ⊨ (comp_ren_sub ρ σ) :=
  fun h => fun B x =>
  show R B (comp_ren_sub ρ σ B x) from
  show R B (σ B x){{ρ}}ᵣ from
  R.ξρ (h _ x)
def satisfy_id : Γ ⊨ 𝟙ₛΓ :=
  fun B x =>
  show R B (.var x) from
  R_of_sne .var

def R_σ.lemma_case : {σ : Subst Γ Δ} → {m : Δ ⊢ B ⨁ C} → {a : Δ; B ⊢ A} → {b : Δ; C ⊢ A}
  → (h : Γ ⊨ σ) → (ihm : R (B ⨁ C) m{{σ}}ₛ) → (iha : R A a{{σ ⁺⁺ B}}ₛ) → (ihb : R A b{{σ ⁺⁺ C}}ₛ)
  → (R_σ_B : ∀ a b, R B b → R A a{{σ ::ₛ b}}ₛ)
  → (R_σ_C : ∀ a b, R C b → R A a{{σ ::ₛ b}}ₛ)
  → R A (.case m a b){{σ}}ₛ :=
  fun {σ m a b} h ihm iha ihb R_σ_B R_σ_C =>
  match ihm.2 with
  | .p p =>
    match p with
    | .inl ⟨a, ha, ham⟩ => by
      simp [Term.subst]
      rw [←ham]
      apply R.closed_backward
      apply snr.β_case₁
      apply sn_of_R
      assumption
      apply sn_of_R
      assumption
      simp [Term.subs]
      rw [←Subst.comp_refl, Subst.extend_id_cons_eq_cons]
      -- apply R_σ _ (satisfy_cons h ha)
      apply R_σ_B _ _ ha
    | .inr ⟨b, hb, hbm⟩ => by
      simp [Term.subst]
      rw [←hbm]
      apply R.closed_backward
      apply snr.β_case₂
      apply sn_of_R
      assumption
      apply sn_of_R
      assumption
      simp [Term.subs]
      rw [←Subst.comp_refl, Subst.extend_id_cons_eq_cons]
      apply R_σ_C _ _ hb
  | .sne hsne_m => R_of_sne (sne.case hsne_m (sn_of_R iha) (sn_of_R ihb))
  | .sn hmm' (t':=m') hsn_m' => R.closed_backward (.ξ_case hmm') sorry
    -- R.closed_backward (.ξ_case hmm') (R_of_sne (sne.case (_) (sn_of_R iha) (sn_of_R ihb)))
def R_σ : (t : Δ ⊢ A) → Γ ⊨ σ → R A t{{σ}}ₛ
  | .unit, h => sn_of_normal .unit
  | .var x, h => h _ x
  | .pair a b, h =>
    have iha := R_σ a h
    have ihb := R_σ b h
    ⟨sn.pair (sn_of_R iha) (sn_of_R ihb), R.closed_backward (.β_p₁ (sn_of_R ihb)) iha, R.closed_backward (.β_p₂ (sn_of_R iha)) ihb⟩
  | .p₁ ab, h =>
    have ih := R_σ ab h
    ih.2.1
  | .p₂ ab, h =>
    have ih := R_σ ab h
    ih.2.2
  | .lam B e, h =>
    have ih := R_σ e (satisfy_extend h)
    have h : ∀ (Δ : Context Ty) (ρ : Renaming Δ Γ) (x : Δ ⊢ B), R B x → R _ ((STLC_Sum.Term.lam B e){{σ}}ₛ{{ρ}}ᵣ @ x) :=
      fun Δ ρ x hr_x => by
      apply R.closed_backward (.β_app (sn_of_R hr_x)) _
      show R _ e{{σ ⁺⁺ B}}ₛ{{ρ ⁺⁺ B}}ᵣ[[x]]₀
      rw [←«{{comp_ren_sub}}ₛ», ←ext_resp_comp_ren_sub]
      simp [Term.subs]
      rw [←Subst.comp_refl, Subst.extend_id_cons_eq_cons]
      apply R_σ _ (satisfy_cons (satisfy_comp_ren_sub h) hr_x)
    ⟨.lam (sn_of_R ih), h⟩
  | .app f x, h =>
    have ihf := R_σ f h
    have ihx := R_σ x h
    (Renaming.eq_id f{{σ}}ₛ ▸ ihf.2 _ (𝟙ᵣ_) _ ihx : R A (_ @ _))
  | .inl a, h =>
    have ih := R_σ a h
    ⟨sn.inl (sn_of_R ih), by {
      rename_i B C
      simp
      constructor
      simp [Term.subst, Union.union, Set.union]
      apply Or.inl
      exists a{{σ}}ₛ
    }⟩
  | .inr b, h =>
    have ih := R_σ b h
    ⟨sn.inr (sn_of_R ih), by {
      rename_i B C
      simp
      constructor
      simp [Term.subst, Union.union, Set.union]
      apply Or.inr
      exists b{{σ}}ₛ
    }⟩
  | .case (A:=B) (B:=C) m a b, h =>
    have ihm := R_σ m h
    have iha := R_σ a (satisfy_extend h)
    have ihb := R_σ b (satisfy_extend h)
    let rec lem {x a b}: (hsn : sn_closure ({x | ∃ a, ∃ (_ : R B a), a.inl = x} ∪ {x | ∃ b, ∃ (_ : R C b), b.inr = x}) x) → R A (.case x a b)
      | .p p =>
        match p with
        | .inl p => sorry
        | .inr p => sorry
      | .sne _ => sorry
      | .sn hmm' hsn_m' =>
        R.closed_backward (snr.ξ_case hmm') (lem hsn_m')
    termination_by hsn => sizeOf hsn
    decreasing_by {
      simp_wf
      sorry
    }
    lem ihm.2
def Term.R : (t : Γ ⊢ A) → R A t :=
  fun t => Subst.eq_id t ▸ R_σ t satisfy_id

end LogicalRelation

end sn

def Term.sn : (t : Γ ⊢ A) → sn t :=
  fun t => (sn.LogicalRelation.sn_of_R (sn.LogicalRelation.Term.R t))

instance : WellFoundedRelation (Γ ⊢ A) where
  rel := Relation.TransGen ISmallStep
  wf := WellFounded.transGen (WellFounded.intro fun t => t.sn)

def Term.nf : (t : Γ ⊢ A) → Σ t' : Γ ⊢ A, Normal t' :=
  fun t =>
  match t.progress with
  | .step (t':=t') _ => t'.nf
  | .done hnf_t => ⟨t, hnf_t⟩
termination_by t => t
decreasing_by {
  simp_wf
  constructor
  assumption
}

#eval ([[.unit]].nf).1
#eval ([[.lam .unit (.var .zero)]].nf).1
#eval ([[.app (.lam .unit (.var .zero)) .unit]].nf).1
#eval ([[.lam .unit (.app (.lam .unit (.var .zero)) .unit)]].nf).1

end STLC_Sum
