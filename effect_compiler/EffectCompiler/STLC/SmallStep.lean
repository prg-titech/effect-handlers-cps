
import EffectCompiler.STLC.Basic
import EffectCompiler.STLC.Subst

import Mathlib.Logic.Relation
open Relation

namespace STLC

mutual
inductive Normal : Γ ⊢ A → Type
  | unit    : Normal .unit
  | pair    : Normal a → Normal b → Normal (.pair a b)
  | lam     : Normal t → Normal (.lam _ t)
  | neutral : Neutral t → Normal t
inductive Neutral : Γ ⊢ A → Type
  | var     : Neutral (.var x)
  | p₁      : Neutral ab → Neutral (.p₁ ab)
  | p₂      : Neutral ab → Neutral (.p₂ ab)
  | app     : Neutral f → Normal x → Neutral (f @ x)
end

-- mutual
-- def Normal.size : Normal t → Nat
--   | .unit => 1
--   | .pair a b => a.size + b.size + 1
--   | .lam e => e.size + 1
--   | .neutral ne => ne.size + 1
-- def Neutral.size : Neutral t → Nat
--   | .var => 1
--   | .p₁ ab => ab.size + 1
--   | .p₂ ab => ab.size + 1
--   | .app f x => f.size + x.size + 1
-- end

inductive SmallStep : Γ ⊢ A → Γ ⊢ A → Prop
  | ξ_PAIR₁       : SmallStep a a' → SmallStep (.pair a b) (.pair a' b)
  | ξ_PAIR₂       : SmallStep b b' → SmallStep (.pair a b) (.pair a b')
  | ξ_P₁          : SmallStep t t' → SmallStep (.p₁ t) (.p₁ t')
  | ξ_P₂          : SmallStep t t' → SmallStep (.p₂ t) (.p₂ t')
  | ξ_LAM         : SmallStep t t' → SmallStep (.lam _ t) (.lam _ t')
  | ξ_APP₁        : SmallStep f f' → SmallStep (f @ x) (f' @ x)
  | ξ_APP₂        : SmallStep x x' → SmallStep (f @ x) (f @ x')
  | β_P₁          : SmallStep (.p₁ (.pair a b)) a
  | β_P₂          : SmallStep (.p₂ (.pair a b)) b
  | β_APP         : SmallStep ((ƛ _ => e) @ x) e[[x]]₀

infix: 30 " ⟶ₛ " => SmallStep

macro_rules | `(tactic| decreasing_trivial) => `(tactic| simp [Term.size, Normal.size, Neutral.size]; simp_arith; assumption)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| simp [Term.size, Normal.size, Neutral.size])
macro_rules | `(tactic| decreasing_trivial) => `(tactic| simp [Term.size, Normal.size, Neutral.size]; simp_arith)

mutual
theorem Normal.not_progress {Γ} {A} {t : Γ ⊢ A} : (Normal t) → ∀ t', ¬(t ⟶ₛ t')
  | .unit => fun _ _ => by contradiction
  | .pair hvt₁ hvt₂ =>
    fun t ht =>
    match ht with
    | .ξ_PAIR₁ ht₁t₁' => Normal.not_progress hvt₁ _ ht₁t₁'
    | .ξ_PAIR₂ ht₂t₂' => Normal.not_progress hvt₂ _ ht₂t₂'
  | .lam hvt =>
    fun t ht =>
    match ht with
    | .ξ_LAM htt' => Normal.not_progress hvt _ htt'
  | .neutral ne => Neutral.not_progress ne
theorem Neutral.not_progress {Γ} {A} {t : Γ ⊢ A} : (Neutral t) → ∀ t', ¬(t ⟶ₛ t')
  | .var => fun _ _ => by contradiction
  | .p₁ hab =>
    fun t ht =>
    match ht with
    | .ξ_P₁ htt' => Neutral.not_progress hab _ htt'
    | .β_P₁ => by contradiction
  | .p₂ hab =>
    fun t ht =>
    match ht with
    | .ξ_P₂ htt' => Neutral.not_progress hab _ htt'
    | .β_P₂ => by contradiction
  | .app hf hx =>
    fun t ht =>
    match ht with
    | .ξ_APP₁ hff' => Neutral.not_progress hf _ hff'
    | .ξ_APP₂ hxx' => Normal.not_progress hx _ hxx'
    | .β_APP => by contradiction
end
-- termination_by
--   Normal.not_progress t h => (sizeOf t, sizeOf h + 1)
--   Neutral.not_progress t h => (sizeOf t, sizeOf h)

-- inductive MultiStep : Γ ⊢ A → Γ ⊢ A → Prop
--   | refl : MultiStep t t
--   | trans : t ⟶ₛ t' → MultiStep t' t'' → MultiStep t t''
def MultiStep (t t' : Γ ⊢ A) := ReflTransGen SmallStep t t'
infix: 30 " ⟶* " => MultiStep
-- def MultiStep.size : t ⟶* t' → Nat
--   | .refl => 1
--   | .trans _ h' => h'.size + 1 + 1
-- def MultiStep.length : t ⟶* t' → Nat
--   | .refl => 0
--   | .trans _ h' => h'.size + 1

-- def MultiStep.trans' : t ⟶* t' → t' ⟶* t'' → t ⟶* t'' := by
--   intro ms ms'
--   induction ms with
--   | refl => exact ms'
--   | trans h _ ih =>
--   constructor
--   exact h
--   exact ih ms'

-- def MultiStep.trans'' : t ⟶* t' → t' ⟶ₛ t'' → t ⟶* t'' := by
--   intro ms ss
--   induction ms with
--   | refl => exact .trans ss .refl
--   | trans h _ ih =>
--   constructor
--   exact h
--   exact ih ss

inductive Parallel : Γ ⊢ A → Γ ⊢ A → Prop where
  | refl_unit : Parallel .unit .unit
  | refl_var : Parallel (.var x) (.var x)
  | ξ_pair : Parallel a a' → Parallel b b' → Parallel (.pair a b) (.pair a' b')
  | ξ_p₁ : Parallel ab ab' → Parallel (.p₁ ab) (.p₁ ab')
  | ξ_p₂ : Parallel ab ab' → Parallel (.p₂ ab) (.p₂ ab')
  | ξβ_p₁ : Parallel a a' → Parallel (.p₁ (.pair a b)) (a')
  | ξβ_p₂ : Parallel b b' → Parallel (.p₂ (.pair a b)) (b')
  | ξ_lam : Parallel e e' → Parallel (.lam _ e) (.lam _ e')
  | ξ_app : Parallel f f' → Parallel x x' → Parallel (.app f x) (.app f' x')
  | ξβ_app : {e e' : Γ; B ⊢ C} → {x x': Γ ⊢ B} → Parallel e e' → Parallel x x' → Parallel ((.lam B e) @ x) e'[[x']]₀
infix: 30 " ⟹ " => Parallel

-- def Parallel.size : t ⟹ t' → Nat
--   | refl_unit => 1
--   | refl_var => 1
--   | ξ_pair haa' hbb' => haa'.size + hbb'.size + 1
--   | ξ_p₁ habab' => habab'.size + 1
--   | ξ_p₂ habab' => habab'.size + 1
--   | ξβ_p₁ haa' => haa'.size + 1
--   | ξβ_p₂ hbb' => hbb'.size + 1
--   | ξ_lam hee' => hee'.size + 1
--   | ξ_app hff' hxx' => hff'.size + hxx'.size + 1
--   | ξβ_app hee' hxx' => hee'.size + hxx'.size + 1

def Parallel.refl : (t : Γ ⊢ A) → t ⟹ t
  | .unit => .refl_unit
  | .var x => .refl_var
  | .pair a b => .ξ_pair (refl a) (refl b)
  | .p₁ ab => .ξ_p₁ (refl ab)
  | .p₂ ab => .ξ_p₂ (refl ab)
  | .lam _ e => .ξ_lam (refl e)
  | .app f x => .ξ_app (refl f) (refl x)

def «⟹of⟶ₛ» : t ⟶ₛ t' → t ⟹ t'
  | .ξ_PAIR₁ haa' => .ξ_pair («⟹of⟶ₛ» haa') (Parallel.refl _)
  | .ξ_PAIR₂ hbb' => .ξ_pair (Parallel.refl _) («⟹of⟶ₛ» hbb')
  | .ξ_P₁ habab' => .ξ_p₁ («⟹of⟶ₛ» habab')
  | .ξ_P₂ habab' => .ξ_p₂ («⟹of⟶ₛ» habab')
  | .β_P₁ => .ξβ_p₁ (Parallel.refl _)
  | .β_P₂ => .ξβ_p₂ (Parallel.refl _)
  | .ξ_LAM hee' => .ξ_lam («⟹of⟶ₛ» hee')
  | .ξ_APP₁ hff' => .ξ_app («⟹of⟶ₛ» hff') (Parallel.refl _)
  | .ξ_APP₂ hxx' => .ξ_app (Parallel.refl _) («⟹of⟶ₛ» hxx')
  | .β_APP => .ξβ_app (Parallel.refl _) (Parallel.refl _)

def MultiStep.ξ_pair₁ : a ⟶* a' → .pair a b ⟶* .pair a' b :=
  fun haa' => ReflTransGen.lift (Term.pair · b) (fun _ _ => .ξ_PAIR₁) haa'
def MultiStep.ξ_pair₂ : b ⟶* b' → .pair a b ⟶* .pair a b' :=
  fun hbb' => ReflTransGen.lift (Term.pair a) (fun _ _ => .ξ_PAIR₂) hbb'
def MultiStep.ξ_pair : a ⟶* a' → b ⟶* b' → .pair a b ⟶* .pair a' b' :=
  fun haa' hbb' => .trans (MultiStep.ξ_pair₁ haa') (MultiStep.ξ_pair₂ hbb')
def MultiStep.ξ_p₁ : ab ⟶* ab' → .p₁ ab ⟶* .p₁ ab' :=
  fun habab' => ReflTransGen.lift Term.p₁ (fun _ _ => .ξ_P₁) habab'
def MultiStep.ξ_p₂ : ab ⟶* ab' → .p₂ ab ⟶* .p₂ ab' :=
  fun habab' => ReflTransGen.lift Term.p₂ (fun _ _ => .ξ_P₂) habab'
def MultiStep.ξ_lam : e ⟶* e' → .lam _ e ⟶* .lam _ e' :=
  fun hee' => ReflTransGen.lift (Term.lam _) (fun _ _ => .ξ_LAM) hee'
def MultiStep.ξ_app₁ : f ⟶* f' → .app f x ⟶* .app f' x :=
  fun hff' => ReflTransGen.lift (Term.app · _) (fun _ _ => .ξ_APP₁) hff'
def MultiStep.ξ_app₂ : x ⟶* x' → .app f x ⟶* .app f x' :=
  fun hxx' => ReflTransGen.lift (Term.app _) (fun _ _ => .ξ_APP₂) hxx'
def MultiStep.ξ_app : f ⟶* f' → x ⟶* x' → .app f x ⟶* .app f' x' :=
  fun hff' hxx' => .trans (MultiStep.ξ_app₁ hff') (MultiStep.ξ_app₂ hxx')

def «⟶*of⟹» {t t' : Γ ⊢ A} : t ⟹ t' → t ⟶* t'
  | .refl_unit => .refl
  | .refl_var => .refl
  | .ξ_pair haa' hbb' => MultiStep.ξ_pair («⟶*of⟹» haa') («⟶*of⟹» hbb')
  | .ξ_p₁ habab' => MultiStep.ξ_p₁ («⟶*of⟹» habab')
  | .ξ_p₂ habab' => MultiStep.ξ_p₂ («⟶*of⟹» habab')
  | .ξβ_p₁ haa' => .tail (MultiStep.ξ_p₁ (MultiStep.ξ_pair («⟶*of⟹» haa') .refl)) .β_P₁
  | .ξβ_p₂ hbb' => .tail (MultiStep.ξ_p₂ (MultiStep.ξ_pair .refl («⟶*of⟹» hbb'))) .β_P₂
  | .ξ_lam hee' => MultiStep.ξ_lam («⟶*of⟹» hee')
  | .ξ_app hff' hxx' => MultiStep.ξ_app («⟶*of⟹» hff') («⟶*of⟹» hxx')
  | .ξβ_app hee' hxx' => .tail (MultiStep.ξ_app (MultiStep.ξ_lam («⟶*of⟹» hee')) («⟶*of⟹» hxx')) .β_APP

@[reducible, simp]
def Term.cd : Γ ⊢ A → Γ ⊢ A
  | .unit => .unit
  | .var x => .var x
  | .pair a b => .pair a.cd b.cd
  | .p₁ (.pair a _) => a.cd
  | .p₁ ab => .p₁ ab.cd
  | .p₂ (.pair _ b) => b.cd
  | .p₂ ab => .p₂ ab.cd
  | .lam _ e => .lam _ e.cd
  | .app (.lam _ e) x => e.cd[[x.cd]]₀
  | .app f x => .app f.cd x.cd
-- termination_by
--   Term.cd t => t.size
postfix : max "⋆" => Term.cd

def Parallel.ξρ_lemma : (ρ : Renaming Γ Δ) → (t : Δ; B ⊢ A) → (s : Δ ⊢ B) → t[[s]]₀{{ρ}}ᵣ = t{{ρ ⁺⁺ B}}ᵣ[[s{{ρ}}ᵣ]]₀ :=
  fun ρ t s => by
    show t{{𝟙ₛΔ ::ₛ s}}ₛ{{ρ}}ᵣ = t{{ρ ⁺⁺ B}}ᵣ{{𝟙ₛ_ ::ₛ s{{ρ}}ᵣ}}ₛ
    rw [←«{{comp_ren_sub}}ₛ»]
    rw [←«{{comp_sub_ren}}ₛ»]
    congr
    funext C x
    cases x with
    | zero => rfl
    | succ x => rfl
def Parallel.ξρ : t ⟹ t' → t{{ρ}}ᵣ ⟹ t'{{ρ}}ᵣ
  | .refl_unit => .refl_unit
  | .refl_var => .refl_var
  | .ξ_pair haa' hbb' => .ξ_pair (Parallel.ξρ haa') (Parallel.ξρ hbb')
  | .ξ_p₁ habab' => .ξ_p₁ (Parallel.ξρ habab')
  | .ξ_p₂ habab' => .ξ_p₂ (Parallel.ξρ habab')
  | .ξβ_p₁ haa' => .ξβ_p₁ (Parallel.ξρ haa')
  | .ξβ_p₂ hbb' => .ξβ_p₂ (Parallel.ξρ hbb')
  | .ξ_lam hee' => .ξ_lam (Parallel.ξρ hee')
  | .ξ_app hff' hxx' => .ξ_app (Parallel.ξρ hff') (Parallel.ξρ hxx')
  | .ξβ_app (B:=A) hee' (e:=e) (e':=e') hxx' (x:=x) (x':=x') => by
    simp [STLC.Term.rename]
    rw [Parallel.ξρ_lemma]
    exact .ξβ_app (Parallel.ξρ hee') (Parallel.ξρ hxx')

def Parallel.ξσ_lemma₁ {σ σ' : Subst Γ Δ} : (∀ B : Ty, ∀ x : Δ ∋ B, σ B x ⟹ σ' B x) → (∀ B : Ty, ∀ x : Δ; A ∋ B, (σ ⁺⁺ A) B x ⟹ (σ' ⁺⁺ A) B x) :=
  fun h =>
  fun B x =>
  match x with
  | .zero => refl _
  | .succ x => ξρ (h B x)
def Parallel.ξσ_lemma₂ : (σ : Subst Γ Δ) → (t : Δ; B ⊢ A) → (s : Δ ⊢ B) → t[[s]]₀{{σ}}ₛ = t{{σ ⁺⁺ B}}ₛ[[s{{σ}}ₛ]]₀ :=
  fun σ t s => by
    show t{{𝟙ₛΔ ::ₛ s}}ₛ{{σ}}ₛ = t{{σ ⁺⁺ B}}ₛ{{𝟙ₛ_ ::ₛ s{{σ}}ₛ}}ₛ
    rw [←Subst.comp_refl]
    rw [←Subst.comp_refl]
    congr
    funext C x
    cases x with
    | zero => rfl
    | succ x =>
      show Subst.comp σ (𝟙ₛΔ ::ₛ s) C (Member.succ x) = Subst.comp (𝟙ₛΓ ::ₛ s{{σ}}ₛ) (σ ⁺⁺ B) C (Member.succ x)
      show Subst.comp σ (𝟙ₛΔ) C x = Subst.comp (𝟙ₛΓ ::ₛ s{{σ}}ₛ) (σ ⁺ B) C x
      show σ C x = ((σ C x) ⁺ B){{𝟙ₛΓ ::ₛ s{{σ}}ₛ}}ₛ
      let y := σ C x
      show y = y{{𝟙ᵣΓ ⁺ B}}ᵣ{{𝟙ₛΓ ::ₛ s{{σ}}ₛ}}ₛ
      rw [←«{{comp_sub_ren}}ₛ»]
      rw [←Subst.eq_id y]
      congr
      rw [Subst.eq_id y]
def Parallel.ξσ {t t' : Δ ⊢ A} {σ σ' : Subst Γ Δ} : t ⟹ t' → (∀ B : Ty, ∀ x : Δ ∋ B, σ B x ⟹ σ' B x) → t{{σ}}ₛ ⟹ t'{{σ'}}ₛ
  | .refl_unit, h => .refl_unit
  | .refl_var, h => h _ _
  | .ξ_pair haa' hbb', h => .ξ_pair (ξσ haa' h) (ξσ hbb' h)
  | .ξ_p₁ habab', h => .ξ_p₁ (ξσ habab' h)
  | .ξ_p₂ habab', h => .ξ_p₂ (ξσ habab' h)
  | .ξβ_p₁ haa', h => .ξβ_p₁ (ξσ haa' h)
  | .ξβ_p₂ hbb', h => .ξβ_p₂ (ξσ hbb' h)
  | .ξ_lam hee', h => .ξ_lam (ξσ hee' (ξσ_lemma₁ h))
  | .ξ_app hff' hxx', h => .ξ_app (ξσ hff' h) (ξσ hxx' h)
  | .ξβ_app (B:=C) hee' (e:=e) (e':=e') hxx' (x:=x) (x':=x'), h => by
    simp [Term.subst]
    rw [Parallel.ξσ_lemma₂ σ' e' x']
    exact .ξβ_app (ξσ hee' (ξσ_lemma₁ h)) (ξσ hxx' h)

def SmallStep.ξρ : t ⟶ₛ t' → t{{ρ}}ᵣ ⟶ₛ t'{{ρ}}ᵣ
  | .ξ_PAIR₁ haa' => .ξ_PAIR₁ (ξρ haa')
  | .ξ_PAIR₂ hbb' => .ξ_PAIR₂ (ξρ hbb')
  | .ξ_P₁ habab' => .ξ_P₁ (ξρ habab')
  | .ξ_P₂ habab' => .ξ_P₂ (ξρ habab')
  | .β_P₁ => .β_P₁
  | .β_P₂ => .β_P₂
  | .ξ_LAM hee' => .ξ_LAM (ξρ hee')
  | .ξ_APP₁ hff' => .ξ_APP₁ (ξρ hff')
  | .ξ_APP₂ hxx' => .ξ_APP₂ (ξρ hxx')
  | .β_APP => by
    simp [STLC.Term.rename]
    rw [Parallel.ξρ_lemma]
    exact .β_APP
def SmallStep.ξσ : t ⟶ₛ t' → t{{σ}}ₛ ⟶ₛ t'{{σ}}ₛ
  | .ξ_PAIR₁ haa' => .ξ_PAIR₁ (ξσ haa')
  | .ξ_PAIR₂ hbb' => .ξ_PAIR₂ (ξσ hbb')
  | .ξ_P₁ habab' => .ξ_P₁ (ξσ habab')
  | .ξ_P₂ habab' => .ξ_P₂ (ξσ habab')
  | .β_P₁ => .β_P₁
  | .β_P₂ => .β_P₂
  | .ξ_LAM hee' => .ξ_LAM (ξσ hee')
  | .ξ_APP₁ hff' => .ξ_APP₁ (ξσ hff')
  | .ξ_APP₂ hxx' => .ξ_APP₂ (ξσ hxx')
  | .β_APP => by
    simp [Term.subst]
    rw [Parallel.ξσ_lemma₂]
    exact .β_APP

#check 0
def Parallel.confluence {t t' : Γ ⊢ A} : t ⟹ t' → t' ⟹ t⋆ := by
  intro htt'
  induction htt' with
  | refl_unit => constructor
  | refl_var => constructor
  | ξ_pair haa' hbb' iha ihb =>
    simp
    constructor
    assumption
    assumption
  | ξβ_p₁ habab' ih =>
    simp
    assumption
  | ξβ_p₂ habab' ih =>
    simp
    assumption
  | ξ_p₁ habab' ih =>
    rename_i ab ab'
    cases ab
    -- case pair a b => {
    --   simp_all
    --   cases ab'
    --   case pair a' b' => {
    --     apply Parallel.ξβ_p₁
    --     cases ih
    --     assumption
    --   }
      -- all_goals contradiction
    -- }
    all_goals simp_all;
    any_goals constructor; assumption
    {
      cases ab'
      any_goals contradiction
      {
        apply Parallel.ξβ_p₁
        cases ih
        assumption
      }
    }
  | ξ_p₂ habab' ih =>
    rename_i ab ab'
    cases ab
    any_goals simp_all; constructor; assumption
    {
      simp_all
      cases ab'
      any_goals contradiction
      {
        constructor
        cases ih
        assumption
      }
    }
  | ξ_lam hee' ih =>
    rename_i e e'
    simp
    constructor
    assumption
  | ξβ_app hff' hxx' ihf ihx =>
    rename_i f f' x x'
    simp
    apply Parallel.ξσ ihf
    intro B y
    cases y with
    | zero => trivial
    | succ y => constructor
  | ξ_app hff' hxx' ihf ihx =>
    rename_i f f' x x'
    cases f
    any_goals simp_all; constructor; assumption; assumption
    {
      simp_all
      cases f'
      any_goals contradiction
      {
        constructor
        cases ihf
        assumption
        assumption
      }
    }
  -- intro htt'
  -- induction htt' with
  -- | refl_unit => constructor
  -- | refl_var => constructor
  -- | ξ_pair haa' hbb' iha ihb =>
  --   simp
  --   constructor
  --   assumption
  --   assumption
  -- | ξβ_p₁ habab' ih =>
  --   simp
  --   assumption
  -- | ξβ_p₂ habab' ih =>
  --   simp
  --   assumption
  -- | ξ_p₁ habab' ih =>
  --   rename_i ab ab'
  --   cases ab
  --   case pair a b => {
  --     simp_all
  --     cases ab'
  --     case pair a' b' => {
  --       apply Parallel.ξβ_p₁
  --       cases ih
  --       assumption
  --     }
  --     all_goals contradiction
  --   }
  --   all_goals simp_all; constructor; assumption
  -- | ξ_p₂ habab' ih =>
  --   rename_i ab ab'
  --   cases ab
  --   case pair a b => {
  --     simp_all
  --     cases ab'
  --     case pair a' b' => {
  --       constructor
  --       cases ih
  --       assumption
  --     }
  --     all_goals contradiction
  --   }
  --   all_goals simp_all; constructor; assumption
  -- | ξ_lam hee' ih =>
  --   rename_i e e'
  --   simp
  --   constructor
  --   assumption
  -- | ξβ_app hff' hxx' ihf ihx =>
  --   rename_i f f' x x'
  --   simp
  --   apply Parallel.ξσ ihf
  --   intro B y
  --   cases y with
  --   | zero => trivial
  --   | succ y => constructor
  -- | ξ_app hff' hxx' ihf ihx =>
  --   rename_i f f' x x'
  --   cases f
  --   case lam e => {
  --     simp_all
  --     cases f'
  --     case lam e' => {
  --       constructor
  --       cases ihf
  --       assumption
  --       assumption
  --     }
  --     all_goals contradiction
  --   }
  --   all_goals simp_all; constructor; assumption; assumption

inductive MultiParallel : Γ ⊢ A → Γ ⊢ A → Prop where
  | refl : MultiParallel t t
  | trans : Parallel t t' → MultiParallel t' t'' → MultiParallel t t''
infix: 30 " ⟹* " => MultiParallel

def MultiParallel.trans' : t ⟹* t' → t' ⟹* t'' → t ⟹* t'' := by
  intro htt' ht't''
  induction htt' with
  | refl => exact ht't''
  | trans htt'' _ ih =>
  constructor
  exact htt''
  exact ih ht't''
  -- | .refl, ht't'' => ht't''
  -- | .trans (t':=u) htu hut', ht't'' => .trans htu (trans' hut' ht't'')

def «⟹*of⟶*» : t ⟶* t' → t ⟹* t' := by
  intro htt'
  induction htt' using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head htt'' _ ih =>
  constructor
  exact «⟹of⟶ₛ» htt''
  exact ih

def «⟶*of⟹*» : t ⟹* t' → t ⟶* t' := by
  intro htt'
  induction htt' with
  | refl => exact .refl
  | trans htt'' _ ih =>
  apply ReflTransGen.trans
  exact «⟶*of⟹» htt''
  exact ih

def MultiParallel.confluence' : t ⟹* t₁ → t ⟹ t₂ → ∃ t', (t₁ ⟹* t') ∧ (t₂ ⟹* t') := by
  intro htt₁ htt₂
  induction htt₁ generalizing t₂ with
  | refl =>
    exists t₂
    constructor
    constructor
    exact htt₂
    exact .refl
    exact .refl
  | trans htt' ht't₁ ih =>
    have ht'tₛ := Parallel.confluence htt'
    have ht₂tₛ := Parallel.confluence htt₂
    have ⟨s, ht''s, htₛs⟩ := ih ht'tₛ
    exists s
    constructor
    assumption
    constructor
    assumption
    assumption
def MultiParallel.confluence : t ⟹* t₁ → t ⟹* t₂ → ∃ t', (t₁ ⟹* t') ∧ (t₂ ⟹* t') := by
  intro htt₁ htt₂
  induction htt₂ generalizing t₁ with
  | refl =>
    exists t₁
    constructor
    constructor
    assumption
  | trans htt' ht't₂ ih =>
    have ⟨s, ht₁s, ht's⟩ := confluence' htt₁ htt'
    have ⟨u, hsu, ht₂u⟩ := ih ht's
    exists u
    constructor
    apply trans'
    assumption
    assumption
    assumption
def MultiParallel.ξρ : t ⟹* t' → t{{ρ}}ᵣ ⟹* t'{{ρ}}ᵣ := by
  intro htt'
  induction htt' with
  | refl => exact .refl
  | trans htt'' ht''ht' ih =>
  constructor
  apply Parallel.ξρ
  assumption
  exact ih

def SmallStep.confluence {t t₁ t₂ : Γ ⊢ A} : t ⟶ₛ t₁ → t ⟶ₛ t₂ → ∃ t', (t₁ ⟶* t') ∧ (t₂ ⟶* t') :=
  fun htt₁ htt₂ =>
  ⟨t⋆, «⟶*of⟹» (Parallel.confluence («⟹of⟶ₛ» htt₁)), «⟶*of⟹» (Parallel.confluence («⟹of⟶ₛ» htt₂))⟩
def MultiStep.confluence {t t₁ t₂ : Γ ⊢ A} : t ⟶* t₁ → t ⟶* t₂ → ∃ t', (t₁ ⟶* t') ∧ (t₂ ⟶* t') :=
  fun htt₁ htt₂ =>
  have ⟨s, ht₁s, ht₂s⟩ := MultiParallel.confluence («⟹*of⟶*» htt₁) («⟹*of⟶*» htt₂)
  ⟨s, «⟶*of⟹*» ht₁s, «⟶*of⟹*» ht₂s⟩
def MultiStep.normal : Normal nf → (h : Σ' t, nf ⟶* t) → h.1 = nf := by
  intro hnf ⟨t, hnft⟩
  cases hnft using ReflTransGen.head_induction_on with
  | refl => rfl
  | head hnft' ht't =>
    rename_i t'
    have := Normal.not_progress hnf _ hnft'
    contradiction
def MultiStep.confluence_normal : t ⟶* nf → Normal nf → t ⟶* t' → t' ⟶* nf := by
  intro htnf hnf htt'
  have ⟨s, hnfs, ht's⟩:= MultiStep.confluence htnf htt'
  have := MultiStep.normal hnf ⟨s, hnfs⟩
  simp_all

def closed_term {A : Ty} : (.nil ⊢ A) → .nil ⊢ A := id
notation "[[ " t " ]]" => closed_term t


-- def MultiStep.ξ_PAIR₁ : a ⟶* a' → .pair a b ⟶* .pair a' b :=
--   fun haa' =>
--   match haa' with
--   | .refl => .refl
--   | .trans (t':=a'') haa'' ha''a' => .trans (.ξ_PAIR₁ haa'') (MultiStep.ξ_PAIR₁ ha''a')
-- def MultiStep.ξ_PAIR₂ : b ⟶* b' → .pair a b ⟶* .pair a b' :=
--   fun hbb' =>
--   match hbb' with
--   | .refl => .refl
--   | .trans (t':=b'') hbb'' hb''b' => .trans (.ξ_PAIR₂ hbb'') (MultiStep.ξ_PAIR₂ hb''b')
def MultiStep.ξ_APP₂ : x ⟶* x' → .app f x ⟶* .app f x' := by
  intro hxx'
  induction hxx' using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hxx'' hx''x' ih =>
  apply ReflTransGen.head
  exact .ξ_APP₂ hxx''
  exact ih

def Normalizing (t : Γ ⊢ A) (t' : Γ ⊢ A) := PProd (Normal t') (t ⟶* t')
infix : 30 " ⇓ " => Normalizing
def HasNormalForm (t : Γ ⊢ A) := Σ t', t ⇓ t'
postfix : max "⇓" => HasNormalForm

def WN : (A : Ty) → (Δ ⊢ A) → Type
  | 𝟙, t => t⇓
  | A ⊗ B, ab => ab⇓ × WN A (.p₁ ab) × WN B (.p₂ ab)
  | A ⇒ B, f => f⇓ × ∀ Γ, ∀ ρ : Renaming Γ Δ, ∀ x : Γ ⊢ A , WN A x → WN B (f{{ρ}}ᵣ @ x)

def Context.satisfy (Γ : Context Ty) (σ : Subst Γ Δ) : Type := ∀ A, ∀ x : Δ ∋ A, WN A (σ A x)
infix : 60 " ⊨ " => Context.satisfy

def smallstep_preserve_hasnf {t t' : Γ ⊢ A} (htt' : t ⟶ₛ t') : (t⇓ → t'⇓) × (t'⇓ → t⇓) := by
  constructor
  {
    intro ⟨nf, hnf, htnf⟩
    exists nf
    constructor
    exact hnf
    exact MultiStep.confluence_normal htnf hnf (.head htt' .refl)
  }
  {
    intro ⟨nf, hnf, ht'nf⟩
    exists nf
    constructor
    exact hnf
    exact .head htt' ht'nf
  }

def multistep_preserve_hasnf {t t' : Γ ⊢ A} (htt' : t ⟶* t') : (t⇓ → t'⇓) × (t'⇓ → t⇓) := by
  constructor
  {
    intro ⟨nf, hnf, htnf⟩
    exists nf
    constructor
    exact hnf
    exact MultiStep.confluence_normal htnf hnf htt'
  }
  {
    intro ⟨nf, hnf, ht'nf⟩
    exists nf
    constructor
    exact hnf
    exact .trans htt' ht'nf
  }


def hasnf_of_wn : {A : Ty} → {t : Γ ⊢ A} → WN A t → t⇓
  | 𝟙, _, h => h
  | _ ⊗ _, _, h => h.1
  | _ ⇒ _, _, h => h.1
def hasnf.lam : e⇓ → (.lam _ e)⇓ :=
  fun ⟨e', hnf_e', hee'⟩ => ⟨.lam _ e', Normal.lam hnf_e', MultiStep.ξ_lam hee'⟩

def MultiStep.ξρ : t ⟶* t' → t{{ρ}}ᵣ ⟶* t'{{ρ}}ᵣ :=
  fun htt' => «⟶*of⟹*» (MultiParallel.ξρ («⟹*of⟶*» htt'))

def SmallStep.ξσ_lemma {σ σ' : Subst Γ Δ} : (∀ B : Ty, ∀ x : Δ ∋ B, σ B x ⟶* σ' B x) → (∀ B : Ty, ∀ x : Δ; A ∋ B, (σ ⁺⁺ A) B x ⟶* (σ' ⁺⁺ A) B x) :=
  fun h =>
  fun B x =>
  match x with
  | .zero => .refl
  | .succ x => MultiStep.ξρ (h B x)
def SmallStep.ξσ' {σ σ' : Subst Γ Δ} : {t : Δ ⊢ A} → (∀ B : Ty, ∀ x : Δ ∋ B, σ B x ⟶* σ' B x) → t{{σ}}ₛ ⟶* t{{σ'}}ₛ
  | .unit, h => .refl
  | .var x, h => (h _ x)
  | .pair _ _, h => MultiStep.ξ_pair (ξσ' h) (ξσ' h)
  | .p₁ _, h => MultiStep.ξ_p₁ (ξσ' h)
  | .p₂ _, h => MultiStep.ξ_p₂ (ξσ' h)
  | .lam _ _, h => MultiStep.ξ_lam (ξσ' (SmallStep.ξσ_lemma h))
  | .app _ _, h => MultiStep.ξ_app (ξσ' h) (ξσ' h)


def MultiStep.ξσ_lemma₁ {σ σ' : Subst Γ Δ} : (∀ B : Ty, ∀ x : Δ ∋ B, σ B x ⟶* σ' B x) → (∀ B : Ty, ∀ x : Δ; A ∋ B, (σ ⁺⁺ A) B x ⟶* (σ' ⁺⁺ A) B x) :=
  fun h =>
  fun B x =>
  match x with
  | .zero => .refl
  | .succ x => ξρ (h B x)
def MultiStep.ξσ {σ : Subst Γ Δ} : t ⟶* t' → t{{σ}}ₛ ⟶* t'{{σ}}ₛ := by
  intro htt'
  induction htt' using ReflTransGen.head_induction_on with
  | refl => constructor
  | head htt'' ht''t' ih =>
    apply ReflTransGen.head
    apply SmallStep.ξσ
    assumption
    apply ih

def MultiStep.ξσ' {σ σ' : Subst Γ Δ} : {t: Δ ⊢ A} → (∀ B : Ty, ∀ x : Δ ∋ B, σ B x ⟶* σ' B x) → t{{σ}}ₛ ⟶* t{{σ'}}ₛ
  | .unit, h => .refl
  | .var x, h => (h _ x)
  | .pair a b, h => MultiStep.ξ_pair (ξσ' h) (ξσ' h)
  | .p₁ ab, h => MultiStep.ξ_p₁ (ξσ' h)
  | .p₂ ab, h => MultiStep.ξ_p₂ (ξσ' h)
  | .lam B e, h => MultiStep.ξ_lam (ξσ' (ξσ_lemma₁ h))
  | .app f x, h => MultiStep.ξ_app (ξσ' h) (ξσ' h)

def multistep_preserve_sn : {A : Ty} → {t t' : Γ ⊢ A} → t ⟶* t' → WN A t' → WN A t
  | 𝟙, t, t', htt', hsn_t' => (multistep_preserve_hasnf htt').2 (hasnf_of_wn hsn_t')
  | A ⊗ B, t, t', htt', hsn_t' =>
    ⟨(multistep_preserve_hasnf htt').2 (hasnf_of_wn hsn_t'), multistep_preserve_sn (MultiStep.ξ_p₁ htt') hsn_t'.2.1, multistep_preserve_sn (MultiStep.ξ_p₂ htt') hsn_t'.2.2⟩
  | A ⇒ B, t, t', htt', hsn_t' =>
    -- have h' : (x : Γ ⊢ A) → WN A x → WN B (t @ x) :=
    --   fun x hsn_x => multistep_preserve_sn (.ξ_APP₁ htt') (hsn_t'.2 x hsn_x)
    have h' : (Θ : Context Ty) → (ρ : Renaming Θ Γ) → (x : Θ ⊢ A) → WN A x → WN B (t{{ρ}}ᵣ @ x) :=
      fun Θ ρ x hsn_x =>
      have htt'ᵣ:= MultiStep.ξρ (ρ:=ρ) htt'
      have hsn_tᵣ := hsn_t'.2 _ ρ x hsn_x
      multistep_preserve_sn (.ξ_app₁ htt'ᵣ) hsn_tᵣ
    ⟨(multistep_preserve_hasnf htt').2 (hasnf_of_wn hsn_t'), h'⟩

def smallstep_preserve_sn : {A : Ty} → {t t' : Γ ⊢ A} → t ⟶ₛ t' → WN A t' → WN A t :=
  fun htt' hsn_t' => multistep_preserve_sn (.head htt' .refl) hsn_t'

mutual
def renaming_neutral : {t : Γ ⊢ A} → Neutral t → Neutral t{{ρ}}ᵣ
  | .var x, .var => .var
  | .p₁ ab, .p₁ hne_ab => .p₁ (renaming_neutral hne_ab)
  | .p₂ ab, .p₂ hne_ab => .p₂ (renaming_neutral hne_ab)
  | .app f x, .app hnef hnx => .app (renaming_neutral hnef) (renaming_normal hnx)
def renaming_normal : {t : Γ ⊢ A} → Normal t → Normal t{{ρ}}ᵣ
  | .unit, .unit => .unit
  | .pair a b, .pair hna hnb => .pair (renaming_normal hna) (renaming_normal hnb)
  | .lam B e, .lam hne => .lam (renaming_normal hne)
  | _, .neutral ne => .neutral (renaming_neutral ne)
end
-- termination_by
--   renaming_neutral t h => (sizeOf t, sizeOf h)
--   renaming_normal t h => (sizeOf t, sizeOf h + 1)

def wn_of_neutral : {A : Ty} → {t : Γ ⊢ A} → Neutral t → WN A t
  | 𝟙, t, hne_t => ⟨t, Normal.neutral hne_t, .refl⟩
  | A ⊗ B, t, hne_t => ⟨⟨t, Normal.neutral hne_t, .refl⟩, wn_of_neutral (Neutral.p₁ hne_t), wn_of_neutral (Neutral.p₂ hne_t)⟩
  | A ⇒ B, t, hne_t =>
    have h : (Θ : Context Ty) → (ρ : Renaming Θ Γ) → (x : Θ ⊢ A) → WN A x → WN B (t{{ρ}}ᵣ @ x) :=
      fun Θ ρ x hsn_x =>
      have ⟨x', hn_x', hxx'⟩ := hasnf_of_wn hsn_x
      multistep_preserve_sn (MultiStep.ξ_APP₂ hxx') (wn_of_neutral (Neutral.app (renaming_neutral hne_t) hn_x'))
    ⟨⟨t, Normal.neutral hne_t, .refl⟩, h⟩

-- 𝑅
def hasnf_renaming : t⇓ → t{{ρ}}ᵣ⇓ :=
  fun ⟨t', hnf_t', htt'⟩ => ⟨t'{{ρ}}ᵣ, renaming_normal hnf_t', MultiStep.ξρ htt'⟩
def sn_renaming : {A : Ty} → {t : Δ ⊢ A} → (ρ : Renaming Γ Δ) → WN A t → WN A t{{ρ}}ᵣ
  | 𝟙, _, _, hsn_t => hasnf_renaming hsn_t
  | A ⊗ B, t, ρ, hsn_t =>
    ⟨hasnf_renaming hsn_t.1, sn_renaming ρ hsn_t.2.1, sn_renaming ρ hsn_t.2.2⟩
  | A ⇒ C, t, ρ, hsn_t =>
    have h : (Θ : Context Ty) → (ρ' : Renaming Θ Γ) → (x : Θ ⊢ A) → WN A x → WN C (t{{ρ}}ᵣ{{ρ'}}ᵣ @ x) :=
      fun Θ ρ' x hsn_x =>
      show WN C (t{{ρ}}ᵣ{{ρ'}}ᵣ @ x) from
      Renaming.ren_comp ρ' ρ _ ▸ (
        hsn_t.2 Θ (Renaming.comp ρ' ρ) x hsn_x
      )
    ⟨hasnf_renaming hsn_t.1, h⟩

def satisfy_wk : Γ ⊨ σ → Γ; A ⊨ σ ⁺ A :=
  fun h => fun B x => sn_renaming _ (h B x)


def satisfy_extend : Γ ⊨ σ → (Γ; A) ⊨ (σ ⁺⁺ A) :=
  fun h => fun B x =>
  match x with
  | .zero =>
    show WN A (.var .zero) from
    wn_of_neutral .var
  | .succ x =>
    show WN B ((σ ⁺ A) B x) from
    show WN B ((σ B x) ⁺ A) from
    show WN B (σ B x){{𝟙ᵣ_ ⁺ A}}ᵣ from
    sn_renaming _ (h _ x)
def satisfy_cons : Γ ⊨ σ → WN _ x → Γ ⊨ (σ ::ₛ x) :=
  fun h hsn_x => fun B y =>
  match y with
  | .zero => hsn_x
  | .succ y => h _ y
def satisfy_comp_ren_sub : Δ ⊨ σ → Γ ⊨ (comp_ren_sub ρ σ) :=
  fun h => fun B x =>
  show WN B (comp_ren_sub ρ σ B x) from
  show WN B (σ B x){{ρ}}ᵣ from
  sn_renaming ρ (h _ x)
def satisfy_renaming : (ρ : Renaming Γ Δ) → Γ ⊨ SubstOfRenaming ρ :=
  fun ρ => fun B x =>
  show WN B (.var (ρ B x)) from
  wn_of_neutral .var
def Term.wn_σ : {A : Ty} → (t : Δ ⊢ A) → (σ : Subst Γ Δ) → Γ ⊨ σ → WN A t{{σ}}ₛ
  | _, .unit, _, _ => ⟨.unit, .unit, .refl⟩
  | A, .var x, σ, h => h A x
  | A ⊗ B, .pair a b, σ, h =>
    have iha := wn_σ a σ h
    have ihb := wn_σ b σ h
    have ⟨a', hnf_a', haa'⟩ := hasnf_of_wn iha
    have ⟨b', hnf_b', hbb'⟩ := hasnf_of_wn ihb
    ⟨⟨.pair a' b', .pair hnf_a' hnf_b', MultiStep.ξ_pair haa' hbb'⟩, smallstep_preserve_sn .β_P₁ iha, smallstep_preserve_sn .β_P₂ ihb⟩
  | A, .p₁ ab, σ, h =>
    have ih := wn_σ ab σ h
    ih.2.1
  | A, .p₂ ab, σ, h =>
    have ih := wn_σ ab σ h
    ih.2.2
  | A ⇒ B, .lam _ e, σ, h =>
    have hsn_e := wn_σ e (σ ⁺⁺ A) (satisfy_extend h)
    show WN (A ⇒ B) (lam A e{{σ ⁺⁺ A}}ₛ) from
    have h' : (Θ : Context Ty) → (ρ : Renaming Θ Γ) → (x : Θ ⊢ A) → WN A x → WN B ((lam A e{{σ ⁺⁺ A}}ₛ){{ρ}}ᵣ @ x) :=
      fun Θ ρ x hsn_x => by {
        apply smallstep_preserve_sn .β_APP
        show WN B e{{σ ⁺⁺ A}}ₛ{{ρ ⁺⁺ A}}ᵣ{{𝟙ₛ_ ::ₛ x}}ₛ
        rw [←«{{comp_ren_sub}}ₛ», ←ext_resp_comp_ren_sub]
        rw [←Subst.comp_refl, Subst.extend_id_cons_eq_cons]
        have : Θ ⊨ (comp_ren_sub ρ σ ::ₛ x) := satisfy_cons (satisfy_comp_ren_sub h) hsn_x
        exact Term.wn_σ e _ this
      }
    ⟨hasnf.lam (hasnf_of_wn hsn_e), h'⟩
  | B, .app (A:=A) f x, σ, h =>
    have ⟨_, ih⟩ := wn_σ f σ h
    have hsn_x := wn_σ x σ h
    have : WN B (f{{σ}}ₛ @ x{{σ}}ₛ) := Renaming.eq_id f{{σ}}ₛ ▸ ih Γ (𝟙ᵣ_) x{{σ}}ₛ hsn_x
    this

def satisfy_id : Γ ⊨ 𝟙ₛΓ :=
  fun B x =>
  show WN B (.var x) from
  wn_of_neutral .var
def Term.wn : (t : Γ ⊢ A) → WN A t :=
  fun t => Subst.eq_id t ▸ (Term.wn_σ t (𝟙ₛΓ) satisfy_id)
def Term.hasnf : (t : Γ ⊢ A) → t⇓ :=
  fun t => hasnf_of_wn t.wn

#reduce [[.unit]].wn
#reduce [[.lam .unit (.var .zero)]].wn
#reduce [[.app (.lam .unit (.var .zero)) .unit]].wn
#reduce [[.lam .unit (.app (.lam .unit (.var .zero)) .unit)]].wn

#eval (hasnf_of_wn [[.unit]].wn).1
#eval (hasnf_of_wn [[.lam .unit (.var .zero)]].wn).1
#eval (hasnf_of_wn [[.app (.lam .unit (.var .zero)) .unit]].wn).1
#eval (hasnf_of_wn [[.lam .unit (.app (.lam .unit (.var .zero)) .unit)]].wn).1

#reduce (hasnf_of_wn [[.p₁ (.pair .unit .unit)]].wn).1
#eval (hasnf_of_wn [[.app (.p₁ (.pair (.lam 𝟙 (.var .zero)) .unit)) .unit]].wn).1

end STLC
