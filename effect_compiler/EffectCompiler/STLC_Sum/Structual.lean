
import EffectCompiler.STLC_Sum.Basic
import EffectCompiler.STLC_Sum.Subst

namespace STLC_Sum

namespace Member

def weakeningᵣ : (Δ : Context Ty) → Γ ∋ A → (Γ ;; Δ) ∋ A
  | .nil, m => m
  | Δ; _, m => .succ (weakeningᵣ Δ m)

def weakeningₗ : (Γ : Context Ty) → Δ ∋ A → (Γ ;; Δ) ∋ A
  | _, .zero => .zero
  | Γ, .succ x => .succ (weakeningₗ Γ x)

inductive Pos {Γ Δ} {A} : (Γ ;; Δ ∋ A) → Type where
  | left : (x: Γ ∋ A) → Pos (weakeningᵣ Δ x)
  | right : (x: Δ ∋ A) → Pos (weakeningₗ Γ x)

def pos : {Δ : Context Ty} → (x : Γ ;; Δ ∋ A) → Pos x
  | .nil, x => .left x
  | Δ; B, .zero => .right (@Member.zero _ Δ B)
  | Δ; B, .succ x =>
    match pos x with
    | .left x => .left x
    | .right x =>
      show @Pos Γ (Δ; B) A (.succ (weakeningₗ Γ x)) from
      show @Pos Γ (Δ; B) A (weakeningₗ Γ (.succ x)) from
      .right (.succ x)

def weakening : {Γ Δ : Context Ty} →  Γ ;; Δ ∋ A → Γ; B ;; Δ ∋ A :=
  fun x =>
  match pos x with
  | .left x => weakeningᵣ _ (.succ x)
  | .right x => weakeningₗ _ x

def cut : Γ; B ;; Γ' ∋ A → Γ ;; Γ' ⊢ B → Γ ;; Γ' ⊢ A :=
  fun x s =>
  match pos x with
  | .right x => .var (weakeningₗ _ x)
  | .left x =>
    match x with
    | .zero => s
    | .succ x => .var (weakeningᵣ _ x)

end Member

namespace Term

def weakening {Γ Γ' : Context Ty} {A B} : Γ ;; Γ' ⊢ A → (Γ; B) ;; Γ' ⊢ A
  | .unit => .unit
  | .var x => .var (Member.weakening x)
  | .pair a b => .pair a.weakening b.weakening
  | .p₁ ab => .p₁ ab.weakening
  | .p₂ ab => .p₂ ab.weakening
  | .lam _ e => .lam _ (@weakening _ (_; _) _ _ e)
  | .app f x => .app f.weakening x.weakening

def weakening0 : Γ ⊢ A → Γ; B ⊢ A := weakening (Γ':=.nil)

def cut : Γ; B ;; Γ' ⊢ A → Γ ;; Γ' ⊢ B → Γ ;; Γ' ⊢ A
  | .unit, s => .unit
  | .var x, s => Member.cut x s
  | .pair a b, s => .pair (a.cut s) (b.cut s)
  | .p₁ ab, s => .p₁ (ab.cut s)
  | .p₂ ab, s => .p₂ (ab.cut s)
  | .lam A e, s =>
    .lam A (e.cut (Γ':=_;_) s.weakening0)
  | .app f x, s => .app (f.cut s) (x.cut s)

def weakeningₗ : Γ' ⊢ A → Γ ;; Γ' ⊢ A
  | .unit => .unit
  | .var x => .var (Member.weakeningₗ _ x)
  | .pair a b => .pair a.weakeningₗ b.weakeningₗ
  | .p₁ ab => .p₁ ab.weakeningₗ
  | .p₂ ab => .p₂ ab.weakeningₗ
  | .lam _ e => .lam _ e.weakeningₗ
  | .app f x => .app f.weakeningₗ x.weakeningₗ

def weakeningᵣ : (Γ' : Context Ty) → Γ ⊢ A → Γ ;; Γ' ⊢ A
  | .nil, t => t
  | Γ'; _, t => (t.weakeningᵣ Γ').weakening0

end Term

def renaming_weakening : {Γ' : Context Ty} → (A  : Ty) → Renaming (Γ; A ;; Γ') (Γ ;; Γ')
  | .nil, A => 𝟙ᵣ_ ⁺ A
  | Γ'; B, A => (renaming_weakening A) ⁺⁺ B
def Member.pos_weakeningᵣ : Member.pos (Member.weakeningᵣ Γ' x) = Pos.left x := by
  induction Γ' with
  | nil => rfl
  | cons Γ' A ih =>
    simp [weakeningᵣ, pos]
    rw [ih]
def Member.pos_weakeningₗ : Member.pos (Member.weakeningₗ Γ' x) = Pos.right x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    simp [weakeningₗ, pos]
    rw [ih]
def Member.succ_weakening_resp : (Γ Γ' : Context Ty) → (x : Γ ;; Γ' ∋ A) → Member.succ (B:=B) (Member.weakening (B:=C) x) = Member.weakening (Δ:=_;_) (Member.succ x) := by
  intro Γ Γ' x
  induction Γ' generalizing Γ A B C with
  | nil => rfl
  | cons Γ' D ih =>
  cases x with
  | zero => rfl
  | succ x =>
    generalize h : Member.succ (Member.succ x) = y
    cases y with
    | zero => contradiction
    | succ y =>
    cases y with
    | zero =>
      exfalso
      simp at h
    | succ y =>
    cases pos y with
    | left x =>
      simp at h
      simp [weakening, pos, weakeningᵣ]
      rw [h, pos_weakeningᵣ]
    | right x =>
      simp at h
      simp [weakening, pos, weakeningᵣ]
      rw [h, pos_weakeningₗ]
      simp
      rfl
def eq_renaming_weakening : (t : Γ ;; Γ' ⊢ A) → (B : Ty) → t{{renaming_weakening B}}ᵣ = t.weakening
  | .unit, B => by
    simp [Term.rename, Term.weakening]
  | .var x, B => by
    simp [Term.rename, Term.weakening]
    induction Γ' with
    | nil =>
      simp [renaming_weakening]
      cases x
      repeat rfl
    | cons Γ' C ih =>
      cases x with
      | zero => rfl
      | succ x =>
        simp [renaming_weakening]
        simp [PAddAdd.paddadd, Renaming.extend, Renaming.cons]
        simp [PAdd.padd, Renaming.wk]
        rw [ih]
        exact Member.succ_weakening_resp _ _ _
  | .pair a b, B => by
    have ih₁ := eq_renaming_weakening a B
    have ih₂ := eq_renaming_weakening b B
    simp [Term.rename, Term.weakening]
    constructor
    repeat assumption
  | .p₁ ab, B => by
    have ih := eq_renaming_weakening ab B
    simp [Term.rename, Term.weakening]
    assumption
  | .p₂ ab, B => by
    have ih := eq_renaming_weakening ab B
    simp [Term.rename, Term.weakening]
    assumption
  | .lam C e, B => by
    have ih := eq_renaming_weakening (Γ':=_;_) e B
    simp [Term.rename, Term.weakening]
    rw [←ih]
    rfl
  | .app f x, B => by
    have ih₁ := eq_renaming_weakening f B
    have ih₂ := eq_renaming_weakening x B
    simp [Term.rename, Term.weakening]
    constructor
    repeat assumption
def eq_renaming_weakening0 : (t : Γ ;; Γ' ⊢ A) → (B : Ty) → t{{𝟙ᵣ_ ⁺ B}}ᵣ = t.weakening0 := by
  intro t B
  simp [Term.weakening0]
  rw [←eq_renaming_weakening]
  rfl

def renaming_weakeningᵣ : (Γ' : Context Ty) → Renaming (Γ ;; Γ') Γ
  | .nil => 𝟙ᵣ_
  | Γ'; A => (renaming_weakeningᵣ Γ') ⁺ A

def eq_renaming_weakeningᵣ : {Γ' : Context Ty} → (t : Γ ⊢ A) → t{{renaming_weakeningᵣ Γ'}}ᵣ = t.weakeningᵣ Γ'
  | .nil, t => by
    simp [renaming_weakeningᵣ, Term.weakeningᵣ]
    exact Renaming.eq_id _
  | Γ'; B, t => by
    have ih := eq_renaming_weakeningᵣ (Γ':=Γ') t
    simp [renaming_weakeningᵣ, Term.weakeningᵣ]
    simp [Term.weakening0]
    rw [←eq_renaming_weakening, ←ih]
    rw [←Renaming.ren_comp]
    congr

def eq_renaming_weakeningᵣ_member : {Γ' : Context Ty} → (x : Γ ∋ A) → (renaming_weakeningᵣ Γ') A x = Member.weakeningᵣ Γ' x := by
  intro Γ' x
  induction Γ' with
  | nil => rfl
  | cons Γ' B ih =>
    simp [renaming_weakeningᵣ, Member.weakeningᵣ, PAdd.padd, Renaming.wk]
    congr

def renaming_weakeningₗ : {Γ' : Context Ty} → Renaming (Γ ;; Γ') Γ'
  | .nil => fun _ _ => by contradiction
  | .nil; A =>
    fun B x =>
    match x with
    | .zero => .zero
  | Γ'; A =>
    fun B x =>
    match x with
    | .zero => .zero
    | .succ x => .succ (renaming_weakeningₗ _ x)

def eq_renaming_weakeningₗ : {Γ Γ' : Context Ty} → (t : Γ' ⊢ A) → t{{renaming_weakeningₗ}}ᵣ = t.weakeningₗ (Γ:=Γ):= by
  intro Γ Γ' t
  induction t generalizing Γ with
  | unit => rfl
  | var x =>
    rename_i Δ B
    simp [Term.rename, Term.weakeningₗ]
    induction Δ with
    | nil => contradiction
    | cons Δ C ih₁ =>
    induction Δ with
    | nil =>
      cases x with
      | zero => rfl
      | succ x => contradiction
    | cons Δ D ih₂ =>
      cases x with
      | zero => rfl
      | succ x =>
        simp [renaming_weakeningₗ, Member.weakeningₗ]
        rw [ih₁]
  | pair a b ih₁ ih₂ =>
    simp [Term.rename, Term.weakeningₗ]
    constructor
    exact ih₁
    exact ih₂
  | p₁ ab ih =>
    simp [Term.rename, Term.weakeningₗ]
    exact ih
  | p₂ ab ih =>
    simp [Term.rename, Term.weakeningₗ]
    exact ih
  | lam B e ih =>
    rename_i Δ C
    simp [Term.rename, Term.weakeningₗ]
    rw [←ih]
    congr
    funext D y
    cases Δ with
    | nil =>
      cases y with
      | zero => rfl
      | succ y => contradiction
    | cons Δ E =>
      cases y with
      | zero => rfl
      | succ y => rfl
  | app f x ih₁ ih₂ =>
    simp [Term.rename, Term.weakeningₗ]
    constructor
    exact ih₁
    exact ih₂

def Subst.extend_context : Subst Γ Γ' → (Δ : Context Ty) → Subst (Γ ;; Δ) (Γ' ;; Δ)
  | σ, .nil => σ
  | σ, Δ; A => (σ.extend_context Δ) ⁺⁺ A
instance : PAddAdd (Subst Γ Γ') (Context Ty) (fun Δ => Subst (Γ ;; Δ) (Γ' ;; Δ)) where
  paddadd := Subst.extend_context

def eq_subs_cut_lemma₁ : rename_n A (Member.weakeningₗ (Γ; B) x) = Member.succ (Member.weakeningₗ Γ x) := by
  rename_i Γ'
  induction x generalizing Γ B with
  | zero => rfl
  | succ x ih =>
    rename_i A C
    simp [Member.weakeningₗ]
    rw [←ih]
    rw [←ih]
    rw [ih]
    simp [rename_n, PAddAdd.paddadd, Renaming.extend, Renaming.cons, PAdd.padd, Renaming.wk]
    simp [exchange]
    rw [ih]
    simp
    congr
    rw [ih]
def eq_subs_cut_lemma₂ : rename_n B (Member.weakeningᵣ Γ' (Member.zero (Γ:=Γ) (A:=B))) = Member.zero := by
  induction Γ' with
  | nil => rfl
  | cons Γ' A ih =>
  simp [Member.weakeningᵣ, rename_n, PAddAdd.paddadd, Renaming.extend, Renaming.cons, PAdd.padd, Renaming.wk]
  rw [ih]
  rfl

def eq_subs_cut_lemma₃ : (rename_n A (Member.weakeningᵣ Γ' (Member.succ x)) : Γ ;; Γ'; B ∋ A) = Member.weakeningᵣ (Γ'; B) x := by
  induction Γ' generalizing Γ A B x with
  | nil => rfl
  | cons Γ' C ih =>
  simp [Member.weakeningᵣ, rename_n, PAddAdd.paddadd, Renaming.extend, Renaming.cons, PAdd.padd, Renaming.wk]
  rw [ih]
  simp [Member.weakeningᵣ, exchange]

def eq_subs_cut_lemma₄ : {B : Ty} → comp_sub_ren ((𝟙ₛ(Γ ;; Γ') ::ₛ s) ⁺⁺ B) (Renaming.extend rename_n B) = comp_sub_ren (𝟙ₛ(Γ ;; Γ'; B) ::ₛ s{{𝟙ᵣ(Γ ;; Γ') ⁺ B}}ᵣ) rename_n := by
  intro B
  rename_i A
  funext C y
  cases Γ' with
  | nil =>
    cases y with
    | zero => rfl
    | succ y =>
    cases y with
    | zero => rfl
    | succ y => rfl
  | cons Γ' D =>
    cases y with
    | zero => rfl
    | succ y =>
    cases y with
    | zero => rfl
    | succ y =>
    simp [comp_sub_ren] at *
    show ((𝟙ₛ(Γ ;; Γ'; D) ::ₛ s) ⁺ B) C (exchange C (Member.succ (rename_n C y))) = _
    show _ = (𝟙ₛ(Γ ;; Γ'; D; B) ::ₛ s{{𝟙ᵣ(Γ ;; Γ'; D) ⁺ B}}ᵣ) C (exchange C (Member.succ (exchange C (Member.succ (rename_n C y)))))
    generalize hy : rename_n C y = z
    cases z with
    | zero => rfl
    | succ z => rfl

def eq_subs_cut : {t : Γ; B ;; Γ' ⊢ A} → t[[s]] = t.cut s
  | .unit => by
    simp [Term.cut]
    rfl
  | .var x => by
    simp [Term.cut, Member.cut]
    cases Member.pos x with
    | right x =>
      simp [Term.subs_n, Term.rename, Term.subs, Term.subst]
      rw [eq_subs_cut_lemma₁]
      simp [Subst.cons]
      rfl
    | left x =>
    cases x with
    | zero =>
      simp [Term.subs_n, Term.rename, Term.subs, Term.subst]
      rw [eq_subs_cut_lemma₂]
      rfl
    | succ x =>
      simp [Term.subs_n, Term.rename, Term.subs, Term.subst]
      rw [eq_subs_cut_lemma₃]
      rfl
  | .pair a b => by
    simp [Term.subs_n, Term.subs, Term.rename, Term.subst]
    simp [Term.cut]
    constructor
    exact eq_subs_cut
    exact eq_subs_cut
  | .p₁ ab => by
    simp [Term.subs_n, Term.subs, Term.rename, Term.subst]
    simp [Term.cut]
    exact eq_subs_cut
  | .p₂ ab => by
    simp [Term.subs_n, Term.subs, Term.rename, Term.subst]
    simp [Term.cut]
    exact eq_subs_cut
  | .lam B e => by
    simp [Term.subs_n, Term.subs, Term.rename, Term.subst]
    simp [Term.cut]
    rw [←eq_subs_cut, Term.subs_n]
    rw [←eq_renaming_weakening0]
    simp [Term.subs]
    rw [←«{{comp_sub_ren}}ₛ»]
    rw [←«{{comp_sub_ren}}ₛ»]
    congr
    funext C y
    cases y with
    | zero => rfl
    | succ y =>
    rw [eq_subs_cut_lemma₄]
  | .app f x => by
    simp [Term.subs_n, Term.subs, Term.rename, Term.subst]
    simp [Term.cut]
    constructor
    exact eq_subs_cut
    exact eq_subs_cut

end STLC_Sum
