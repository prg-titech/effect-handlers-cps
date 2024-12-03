
import EffectCompiler.STLC.Basic

import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

namespace STLC

instance : PAdd (Γ ∋ B) Ty (fun A => Γ; A ∋ B) where
  padd x _ := .succ x

def Renaming (Γ Δ : Context Ty) := ∀ (A : Ty), Δ ∋ A → Γ ∋ A
def Subst (Γ Δ : Context Ty) := ∀ (A : Ty), Δ ∋ A → Γ ⊢ A

namespace Renaming

def id  (Γ) : Renaming Γ Γ :=
  fun _ => _root_.id
prefix : 90 "𝟙ᵣ" => id
def wk : Renaming Γ Δ → (A : Ty) → Renaming (Γ; A) Δ :=
  fun ρ _ _ x => .succ (ρ _ x)
instance : PAdd (Renaming Γ Δ) Ty (fun A => Renaming (Γ; A) Δ) where
  padd := wk

def cons : Renaming Γ Δ → Γ ∋ A → Renaming Γ (Δ; A)
  | _, y, _, .zero => y
  | ρ, _, _, .succ x => ρ _ x
infixl : 67 " ::ᵣ " => cons
def extend : Renaming Γ Δ → (A : Ty) → Renaming (Γ ; A) (Δ; A) :=
  fun ρ A => cons (ρ ⁺ A) .zero

instance : PAddAdd (Renaming Γ Δ) Ty (fun A => Renaming (Γ; A) (Δ; A)) where
  paddadd := extend
def comp : Renaming Γ Δ → Renaming Δ Θ → Renaming Γ Θ :=
  fun ρ ρ' => fun A x => ρ A (ρ' A x)

def Member.eq_weak : (σ : Renaming Γ Δ) → (B : Ty) → (x : Δ ∋ A) → (σ ⁺ B) A x = (σ A x) ⁺ B :=
  fun _ _ _ => rfl

@[simp]
def Member.eq_id : (B : Ty) → (x : Δ ∋ A) → (𝟙ᵣΔ) A x = x :=
  fun _ _ => rfl

def Member.eq_id_wk : (B : Ty) → (x : Δ ∋ A) → (𝟙ᵣΔ ⁺ B) A x = x ⁺ B :=
  fun _ _ => rfl

@[simp]
def id_comp : (σ : Renaming Γ Δ) → comp (𝟙ᵣΓ) σ = σ :=
  fun _ => rfl

@[simp]
def eq_cons_wk : (σ : Renaming Γ Δ) → (ρ : Renaming Δ Θ) → (x : Γ ∋ A) → comp (σ ::ᵣ x) (ρ ⁺ A) = comp σ ρ :=
  fun _ _ _ => rfl

@[simp]
def comp_id : (σ : Renaming Γ Δ) → comp σ (𝟙ᵣΔ) = σ := fun _ => rfl

def comp_refl : (σ : Renaming Γ Δ) → (ρ : Renaming Δ Θ) → (x : Θ ∋ A) → (comp σ ρ) A x = σ A (ρ A x) := fun _ _ _ => rfl

def comp_assoc : (γ : Renaming Γ Δ) → (δ : Renaming Δ Θ) → (σ : Renaming Θ Ξ) → comp (comp γ δ) σ = comp γ (comp δ σ) :=
  fun _ _ _ => rfl

instance Ren : Category (Context Ty) where
  Hom := Renaming
  id Γ := 𝟙ᵣΓ
  comp := Renaming.comp

end Renaming


def Term.rename : Δ ⊢ A → Renaming Γ Δ → Γ ⊢ A
  | .unit, _ => .unit
  | .var x, ρ => .var (ρ _ x)
  | .pair a b, ρ => .pair (rename a ρ) (rename b ρ)
  | .p₁ ab, ρ => .p₁ (rename ab ρ)
  | .p₂ ab, ρ => .p₂ (rename ab ρ)
  | .lam B e, ρ => .lam B (rename e (ρ.extend B))
  | .app f x, ρ => .app (rename f ρ) (rename x ρ)
notation : max t "{{" σ "}}ᵣ" => Term.rename t σ

def eq_id_extend : (Γ : Context Ty) → (A : Ty) → 𝟙ᵣΓ ⁺⁺ A = 𝟙ᵣ(Γ; A) :=
  fun _ _ => funext₂
  fun _ x =>
  match x with
  | .zero => rfl
  | .succ _ => rfl

def Renaming.eq_id : (t : Γ ⊢ A) → t{{𝟙ᵣΓ}}ᵣ = t
  | .unit => rfl
  | .var x => congrArg Term.var (Member.eq_id A x)
  | .pair a b => congrArg₂ Term.pair (eq_id a) (eq_id b)
  | .p₁ ab => congrArg Term.p₁ (eq_id ab)
  | .p₂ ab => congrArg Term.p₂ (eq_id ab)
  | .lam C e => congrArg (Term.lam C ·) (Eq.trans (congrArg _ (eq_id_extend Γ C)) (eq_id e))
  | .app f x => congrArg₂ Term.app (eq_id f) (eq_id x)

def Renaming.extend_resp_comp : (ρ : Renaming Γ Δ) → (ρ' : Renaming Δ Θ) → (A : Ty) → (comp ρ ρ') ⁺⁺ A = comp (ρ ⁺⁺ A) (ρ' ⁺⁺ A) :=
  fun _ _ _ => funext₂
  fun _ x =>
  match x with
  | .zero => rfl
  | .succ _ => rfl
def Renaming.ren_comp : (ρ : Renaming Γ Δ) → (ρ' : Renaming Δ Θ) → (t : Θ ⊢ A) → t{{comp ρ ρ'}}ᵣ = t{{ρ'}}ᵣ{{ρ}}ᵣ
  | _, _, .unit => rfl
  | _, _, .var x => rfl
  | ρ, ρ', .pair a b => congrArg₂ Term.pair (ren_comp ρ ρ' a) (ren_comp ρ ρ' b)
  | ρ, ρ', .p₁ ab => congrArg Term.p₁ (ren_comp ρ ρ' ab)
  | ρ, ρ', .p₂ ab => congrArg Term.p₂ (ren_comp ρ ρ' ab)
  | ρ, ρ', .lam B e => congrArg (Term.lam B ·) (Eq.trans (congrArg (e{{·}}ᵣ) (extend_resp_comp ρ ρ' B)) (ren_comp (ρ ⁺⁺ B) (ρ' ⁺⁺ B) e))
  | ρ, ρ', .app f x => congrArg₂ Term.app (ren_comp ρ ρ' f) (ren_comp ρ ρ' x)


def Term.wk : Γ ⊢ A → (B : Ty) → (Γ; B) ⊢ A :=
  fun t B => t.rename (𝟙ᵣ_ ⁺ B)
instance : PAdd (Γ ⊢ B) Ty (fun A => Γ; A ⊢ B) where
  padd := Term.wk

def SubstOfRenaming : Renaming Γ Δ → Subst Γ Δ
  | ρ, A, x => .var (ρ A x)
instance {Γ Δ} : Coe (Renaming Γ Δ) (Subst Γ Δ) where
  coe := SubstOfRenaming
def Subst.id (Γ) : Subst Γ Γ := 𝟙ᵣΓ
prefix : 90 "𝟙ₛ" => Subst.id
def Subst.wk : Subst Γ Δ → (A : Ty) → Subst (Γ; A) Δ :=
  fun σ A B t => (σ B t) ⁺ A
instance : PAdd (Subst Γ Δ) Ty (fun A => Subst (Γ; A) Δ) where
  padd := Subst.wk
@[match_pattern]
def Subst.cons : Subst Γ Δ → Γ ⊢ A → Subst Γ (Δ; A)
  | _, t, _, .zero => t
  | σ, _, B, .succ x => σ B x
infixl : 60 " ::ₛ " => Subst.cons
def Subst.extend : Subst Γ Δ → (A : Ty) → Subst (Γ ; A) (Δ; A) :=
  fun ρ A => Subst.cons (ρ ⁺ A) (.var .zero)
  -- | _, _, _, .zero => .var .zero
  -- | σ, _, _, .succ x => (σ _ x).wk _
-- infixl : 80 " ⁺⁺ " => Subst.extend
instance : PAddAdd (Subst Γ Δ) Ty (fun A => Subst (Γ; A) (Δ; A)) where
  paddadd := Subst.extend

def Term.subst : Δ ⊢ A → Subst Γ Δ → Γ ⊢ A
  | .unit, σ => .unit
  | .var x, σ => σ _ x
  | .pair a b, σ => .pair (subst a σ) (subst b σ)
  | .p₁ ab, σ => .p₁ (subst ab σ)
  | .p₂ ab, σ => .p₂ (subst ab σ)
  | .lam B e, σ => .lam B (subst e (σ ⁺⁺ B))
  | .app f x, σ => .app (subst f σ) (subst x σ)
notation : max t "{{" σ "}}ₛ" => Term.subst t σ

def Subst.comp : Subst Γ Δ → Subst Δ Θ → Subst Γ Θ :=
  fun σ σ' => fun A x => (σ' A x){{σ}}ₛ

def Renaming.comp_sub : Renaming Γ Δ → Subst Δ Θ → Subst Γ Θ :=
  fun ρ σ => fun A x => (σ A x){{ρ}}ᵣ
def Subst.comp_ren : Subst Γ Δ → Renaming Δ Θ → Subst Γ Θ :=
  fun σ ρ => fun A x => σ A (ρ A x)

def refl_ren : t₁ = t₂ → σ₁ = σ₂ → t₁{{σ₁}}ᵣ = t₂{{σ₂}}ᵣ :=
  fun ht₁t₂ hσ₁σ₂ => congrArg₂ _ ht₁t₂ hσ₁σ₂
def refl_subs : t₁ = t₂ → σ₁ = σ₂ → t₁{{σ₁}}ₛ = t₂{{σ₂}}ₛ :=
  fun ht₁t₂ hσ₁σ₂ => congrArg₂ _ ht₁t₂ hσ₁σ₂


def wk_lift_commute : (σ : Renaming Γ Δ) → (A : Ty) → (SubstOfRenaming σ) ⁺ A = SubstOfRenaming (σ ⁺ A) :=
  fun _ _ => rfl
def extend_lift_commute : (σ : Renaming Γ Δ) → (A : Ty) → (SubstOfRenaming σ) ⁺⁺ A = SubstOfRenaming (σ ⁺⁺ A) :=
  fun _ _ => funext₂
  fun _ x =>
  match x with
  | .zero => rfl
  | .succ x => rfl


def eq_lift : (t : Δ ⊢ A) → (σ : Renaming Γ Δ) → t{{σ}}ₛ = t{{σ}}ᵣ
  | .unit, _ => rfl
  | .var _, _ => rfl
  | .pair a b, σ => congrArg₂ Term.pair (eq_lift a σ) (eq_lift b σ)
  | .p₁ ab, σ => congrArg Term.p₁ (eq_lift ab σ)
  | .p₂ ab, σ => congrArg Term.p₂ (eq_lift ab σ)
  | .lam B e, σ => congrArg (Term.lam B ·) (Eq.trans (congrArg (e{{·}}ₛ) (extend_lift_commute σ B)) (eq_lift e (σ ⁺⁺ B)))
  | .app f x, σ => congrArg₂ Term.app (eq_lift f σ) (eq_lift x σ)

def lift_id : {Γ : Context Ty} → SubstOfRenaming (𝟙ᵣΓ : Renaming Γ Γ) = 𝟙ₛΓ := rfl


def Subst.eq_id : (t : Γ ⊢ A) → t{{𝟙ₛΓ}}ₛ = t :=
  fun t => Eq.trans (eq_lift t (𝟙ᵣΓ)) (Renaming.eq_id t)

@[simp]
def Subst.id_comp : (σ : Subst Γ Δ) → Subst.comp (𝟙ₛΓ) σ = σ :=
  fun σ => funext₂
  fun B x => eq_id (σ B x)

def Subst.eq_cons_wk : (σ : Subst Γ Δ) → (ρ : Renaming Δ Θ) → (t : Γ ⊢ A) → comp (σ ::ₛ t) (ρ ⁺ A) = comp σ (SubstOfRenaming ρ) :=
  fun _ _ _ => rfl

@[simp]
def Subst.comp_id : (σ : Subst Γ Δ) → comp σ (𝟙ₛΔ) = σ :=
  fun _ => rfl

def Subst.id_wk_comp : (σ : Subst Γ Δ) → (A : Ty) → comp (SubstOfRenaming (𝟙ᵣΓ ⁺ A)) σ = σ ⁺ A :=
  fun σ A => funext₂
  fun B x => eq_lift (σ B x) (𝟙ᵣΓ ⁺ A)
def Subst.comp_wk_id : (σ : Subst Γ Δ) → (A : Ty) → σ ⁺ A = comp (σ ⁺⁺ A) (𝟙ₛΔ ⁺ A) :=
  fun _ _ => rfl

def subst_ext_lemma {s : Γ ⊢ B} : {σ ρ : Subst Γ Δ} → (∀ A : Ty, ∀ x : Δ; B ∋ A, (σ ::ₛ s) A x = (ρ ::ₛ s) A x) → (∀ A : Ty, ∀ x : Δ ∋ A, σ A x = ρ A x) := by
  intro σ ρ
  intro h
  intro A x
  have := h A (.succ x)
  exact this
def subst_ext : {σ ρ : Subst Γ Δ} → (∀ A : Ty, ∀ x : Δ ∋ A, σ A x = ρ A x) → σ = ρ :=
  fun {_ _} => fun h => funext₂
  h

def comp_sub_ren : Subst Γ Δ → Renaming Δ Θ → Subst Γ Θ :=
  fun σ ρ => fun B x => σ B (ρ B x)
def comp_ren_sub : Renaming Γ Δ → Subst Δ Θ → Subst Γ Θ :=
  fun ρ σ => fun B x => (σ B x){{ρ}}ᵣ

def ext_resp_comp_sub_ren : (σ : Subst Γ Δ) → (ρ : Renaming Δ Θ) → (A : Ty) → (comp_sub_ren σ ρ) ⁺⁺ A = comp_sub_ren (σ ⁺⁺ A) (ρ ⁺⁺ A) :=
  fun _ _ _ => funext₂
  fun _ x =>
  match x with
  | .zero => rfl
  | .succ x => rfl

def ext_resp_comp_ren_sub : (ρ : Renaming Γ Δ) → (σ : Subst Δ Θ) → (A : Ty) → (comp_ren_sub ρ σ) ⁺⁺ A = comp_ren_sub (ρ ⁺⁺ A) (σ ⁺⁺ A) :=
  fun ρ  σ A => funext₂
  fun B x =>
  match x with
  | .zero => rfl
  | .succ x => by
    simp [comp_ren_sub]
    simp [PAddAdd.paddadd, Subst.extend, Subst.cons]
    let y := σ B x
    show y{{ρ}}ᵣ ⁺ A = (y ⁺ A){{ρ ⁺⁺ A}}ᵣ
    show y{{ρ}}ᵣ{{𝟙ᵣΓ ⁺ A}}ᵣ = y{{𝟙ᵣΔ ⁺ A}}ᵣ{{ρ ⁺⁺ A}}ᵣ
    rw [←Renaming.ren_comp _ _ _]
    rw [←Renaming.ren_comp _ _ _]
    congr

def «{{comp_sub_ren}}ₛ» : (σ : Subst Γ Δ) → (ρ : Renaming Δ Θ) → (t : Θ ⊢ A) → t{{comp_sub_ren σ ρ}}ₛ = t{{ρ}}ᵣ{{σ}}ₛ
  | _, _, .unit => rfl
  | _, _, .var _ => rfl
  | σ, ρ, .pair a b => congrArg₂ Term.pair («{{comp_sub_ren}}ₛ» σ ρ a) («{{comp_sub_ren}}ₛ» σ ρ b)
  | σ, ρ, .p₁ ab => congrArg Term.p₁ («{{comp_sub_ren}}ₛ» σ ρ ab)
  | σ, ρ, .p₂ ab => congrArg Term.p₂ («{{comp_sub_ren}}ₛ» σ ρ ab)
  | σ, ρ, .lam B e => congrArg (Term.lam B ·) (Eq.trans (congrArg (e{{·}}ₛ) (ext_resp_comp_sub_ren σ ρ B)) («{{comp_sub_ren}}ₛ» (σ ⁺⁺ B) (ρ ⁺⁺ B) e))
  | σ, ρ, .app f x => congrArg₂ Term.app («{{comp_sub_ren}}ₛ» σ ρ f) («{{comp_sub_ren}}ₛ» σ ρ x)

def «{{comp_ren_sub}}ₛ» : (ρ : Renaming Γ Δ) → (σ : Subst Δ Θ) → (t : Θ ⊢ A) → t{{comp_ren_sub ρ σ}}ₛ = t{{σ}}ₛ{{ρ}}ᵣ
  | _, _, .unit => rfl
  | _, _, .var _ => rfl
  | σ, ρ, .pair a b => congrArg₂ Term.pair («{{comp_ren_sub}}ₛ» σ ρ a) («{{comp_ren_sub}}ₛ» σ ρ b)
  | σ, ρ, .p₁ ab => congrArg Term.p₁ («{{comp_ren_sub}}ₛ» σ ρ ab)
  | σ, ρ, .p₂ ab => congrArg Term.p₂ («{{comp_ren_sub}}ₛ» σ ρ ab)
  | σ, ρ, .lam B e => congrArg (Term.lam B ·) (Eq.trans (congrArg (e{{·}}ₛ) (ext_resp_comp_ren_sub σ ρ B)) («{{comp_ren_sub}}ₛ» (σ ⁺⁺ B) (ρ ⁺⁺ B) e))
  | σ, ρ, .app f x => congrArg₂ Term.app («{{comp_ren_sub}}ₛ» σ ρ f) («{{comp_ren_sub}}ₛ» σ ρ x)

def Subst.subst_lift : (∀ A : Ty, ∀ x : Δ ∋ A, σ A x = σ' A x) → t{{σ}}ₛ = t{{σ'}}ₛ :=
  fun h => congrArg (t{{·}}ₛ) (funext₂ h)

def Subst.comp_preserve_extend' : (σ : Subst Γ Δ) → (ρ : Subst Δ Θ) → (A : Ty) → (comp σ ρ) ⁺ A = comp (σ ⁺⁺ A) (ρ ⁺ A) :=
  fun σ ρ A => funext₂
  fun B x =>
  let y := ρ B x
  show y{{σ}}ₛ{{𝟙ᵣΓ ⁺ A}}ᵣ = y{{𝟙ᵣΔ ⁺ A}}ᵣ{{σ ⁺⁺ A}}ₛ from calc
    y{{σ}}ₛ{{𝟙ᵣΓ ⁺ A}}ᵣ = y{{comp_ren_sub (𝟙ᵣΓ ⁺ A) σ}}ₛ := by rw [«{{comp_ren_sub}}ₛ»]
    _ = y{{σ ⁺ A}}ₛ := rfl
    _ = y{{comp_sub_ren (σ ⁺⁺ A) (𝟙ᵣΔ ⁺ A)}}ₛ := rfl
    _ = y{{(𝟙ᵣΔ ⁺ A)}}ᵣ{{σ ⁺⁺ A}}ₛ := by rw [«{{comp_sub_ren}}ₛ»]
def Subst.comp_preserve_extend : (σ : Subst Γ Δ) → (ρ : Subst Δ Θ) → (A : Ty) → (comp σ ρ) ⁺⁺ A = comp (σ ⁺⁺ A) (ρ ⁺⁺ A) :=
  fun σ ρ A => funext₂
  fun B x =>
  match x with
  | .zero => rfl
  | .succ x =>
  have h : (comp σ ρ ⁺ A) = comp (σ ⁺⁺ A) (ρ ⁺ A) := comp_preserve_extend' σ ρ A
  congr_fun₂ h B x

def Subst.comp_refl : (t : Γ ⊢ A) → t{{comp σ σ'}}ₛ = t{{σ'}}ₛ{{σ}}ₛ
  | .unit => rfl
  | .var x => rfl
  | .pair a b => congrArg₂ Term.pair (comp_refl a) (comp_refl b)
  | .p₁ ab => congrArg Term.p₁ (comp_refl ab)
  | .p₂ ab => congrArg Term.p₂ (comp_refl ab)
  | .lam B e => congrArg (Term.lam B ·) (Eq.trans (congrArg _ (comp_preserve_extend σ σ' B)) (comp_refl e))
  | .app f x => congrArg₂ Term.app (comp_refl f) (comp_refl x)

@[simp]
def Subst.assoc : (γ : Subst Γ Δ) → (δ : Subst Δ Θ) → (σ : Subst Θ Ξ) → comp (comp γ δ) σ = comp γ (comp δ σ) :=
  fun γ δ σ => funext₂
  fun B x => by
    simp [Subst.comp]
    rw [←comp_refl (σ B x)]

def Subst.extend_id_cons_eq_cons : (σ : Subst Γ Δ) → (A : Ty) → (x : Γ ⊢ A) → comp (𝟙ₛ_ ::ₛ x) (σ ⁺⁺ A) = σ ::ₛ x :=
  fun σ A t => funext₂
  fun B x =>
  match x with
  | .zero => rfl
  | .succ x =>
    show comp (𝟙ₛΓ ::ₛ t) (σ ⁺⁺ A) B (Member.succ x) = (σ ::ₛ t) B (Member.succ x) from
    show (((σ ⁺ A) ::ₛ (.var .zero)) B (Member.succ x)){{𝟙ₛΓ ::ₛ t}}ₛ = σ B x from
    show (σ B x){{𝟙ᵣ_ ⁺ A}}ᵣ{{𝟙ₛΓ ::ₛ t}}ₛ = σ B x from
    let y := σ B x
    show y{{𝟙ᵣ_ ⁺ A}}ᵣ{{𝟙ₛΓ ::ₛ t}}ₛ = y from
    Eq.trans («{{comp_sub_ren}}ₛ» (𝟙ₛΓ ::ₛ t) (𝟙ᵣ_ ⁺ A) y).symm (Eq.trans (congrArg (y{{·}}ₛ) rfl) (Subst.eq_id y))


instance STLC : Category (Context Ty) where
  Hom := Subst
  id _ := 𝟙ₛ_
  comp := Subst.comp

def Term.subs : Γ; B ⊢ A → Γ ⊢ B → Γ ⊢ A :=
  fun t s => t{{𝟙ₛΓ ::ₛ s}}ₛ
notation : max t "[[" s "]]₀" => Term.subs t s

def Subst.extend' : {Γ' : Context Ty} → (Subst Γ Δ) → Subst (Γ ;; Γ') (Δ ;; Γ')
  | .nil, σ => σ
  | _; A, σ => (extend' σ) ⁺⁺ A

def exchange : Renaming (Γ; A; B) (Γ; B; A) :=
  fun C x =>
  match x with
  | .zero => .succ .zero
  | .succ .zero => .zero
  | .succ (.succ x) => .succ (.succ x)
def rename_n : {Γ' : Context Ty} → Renaming (Γ ;; Γ'; B) (Γ; B ;; Γ')
  | .nil => fun C x => x
  | Γ'; A =>
  fun C x =>
  have ρ := (rename_n (Γ:=Γ) (Γ':=Γ') (B:=B)) ⁺⁺ A
  have y := ρ _ x
  exchange _ y
def Term.subs_n : Γ; B ;; Γ' ⊢ A → Γ ;; Γ' ⊢ B → Γ ;; Γ' ⊢ A :=
  fun t s => t{{rename_n}}ᵣ[[s]]₀
notation : max t "[[" s "]]" => Term.subs_n t s

def exchange_involution : Renaming.comp exchange exchange = 𝟙ᵣ(Γ; A; B) := by
  funext C x
  cases x with
  | zero => rfl
  | succ x =>
  cases x with
  | zero => rfl
  | succ x => rfl

def rename_n_inv : {Γ' : Context Ty} → Renaming (Γ; B ;; Γ') (Γ ;; Γ'; B)
  | .nil => 𝟙ᵣ_
  | Γ'; A => Renaming.comp ((rename_n_inv (Γ:=Γ) (Γ':=Γ') (B:=B)) ⁺⁺ A) exchange

def rename_n_rename_n_inv_id : Renaming.comp rename_n rename_n_inv = 𝟙ᵣ(Γ;; Γ'; B) := by
  funext C x
  induction Γ' generalizing Γ B with
  | nil => rfl
  | cons Γ' C ih =>
  cases x with
  | zero =>
    simp [Renaming.comp, rename_n_inv, rename_n, Renaming.id]
    simp [PAddAdd.paddadd, Renaming.extend, exchange, PAdd.padd, Renaming.wk, Renaming.cons]
    simp [Renaming.comp] at ih
    rw [ih]
    simp [Renaming.id]
  | succ x =>
  cases x with
  | zero => rfl
  | succ x =>
    simp [Renaming.comp, rename_n_inv, rename_n, Renaming.id]
    simp [PAddAdd.paddadd, Renaming.extend, exchange, PAdd.padd, Renaming.wk, Renaming.cons]
    simp [Renaming.comp] at ih
    rw [ih]
    simp [Renaming.id]

def rename_n_inv_rename_n_id : Renaming.comp rename_n_inv rename_n = 𝟙ᵣ(Γ; B ;; Γ') := by
  funext C x
  induction Γ' generalizing Γ B C with
  | nil => rfl
  | cons Γ' D ih =>
  cases x with
  | zero => rfl
  | succ x =>
    simp [rename_n, rename_n_inv, Renaming.comp]
    have h : ∀ y : (Γ ;; Γ' ; B) ; D ∋ _, exchange C (exchange C y) = y := by
      intro y
      show (Renaming.comp exchange exchange) _ y = y
      rw [exchange_involution]
      rfl
    rw [h]
    show Member.succ (rename_n_inv C (rename_n C x)) = Member.succ x
    congr
    simp [Renaming.comp] at ih
    rw [ih]
    rfl

def rename_n_cut : {Γ' : Context Ty} → (x : Γ ; B ;; Γ' ∋ A) → (h : x.size ≠ Γ'.size) → (.var x){{rename_n}}ᵣ = .var (.succ (x.cut h))
  | .nil, .succ x, hneq => rfl
  | Γ'; C, .zero, hneq => rfl
  | Γ'; C, .succ x, hneq => by
    have h : Member.size x ≠ Context.size Γ' := by {
      intro h
      simp [Member.size, Context.size] at hneq
      exact hneq h
    }
    have ih := rename_n_cut x h
    simp [Term.rename] at ih
    simp [Member.cut, Term.rename, rename_n, PAddAdd.paddadd, Renaming.extend, Renaming.cons, PAdd.padd, Renaming.wk]
    rw [ih]
    simp [exchange]
def Term.subs_n_var : {Γ' : Context Ty} → (x : Γ ; B ;; Γ' ∋ A) → (s : Γ ;; Γ' ⊢ B) → (h : x.size ≠ Γ'.size) → (.var x)[[s]] = .var (x.cut h)
  | .nil, .succ x, s, hneq => rfl
  | Γ'; C, .zero, s, hneq => rfl
  | Γ'; C, .succ x, s, hneq => by
    have h : Member.size x ≠ Context.size Γ' := by {
        intro h
        simp [Member.size, Context.size] at hneq
        exact hneq h
      }
    have ih := subs_n_var x
    let x' : (Γ; _ ;; Γ' ; C) ∋ _ := Member.succ (B:=C) x
    have h' := rename_n_cut x' hneq
    simp [Term.rename] at h'
    simp [Term.subs_n, Member.cut, Term.subs, Term.subst]
    rw [h']
    rfl

end STLC
