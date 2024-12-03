
import EffectCompiler.SystemF.Basic

import Batteries.Logic

namespace SystemF


def Ren'.comp : Ren' A B → Ren' B C → Ren' A C
  | f, g => fun _ => (f _) ∘ (g _)
def Ren'.lift_comp : lift (K:=K) (comp f g) = comp f.lift g.lift :=
  funext₂ fun _ i =>
  match i with
  | .zero => rfl
  | .succ _ => rfl
def Ren'.ren_comp : {t : Ty Φ K} → t{{comp f g}}ᵣ' = t{{g}}ᵣ'{{f}}ᵣ'
  | .var i => rfl
  | .unit => rfl
  | .bool => rfl
  | .fn A B => congrArg₂ Ty.fn ren_comp ren_comp
  | .pi K A => congrArg (Ty.pi K) (Eq.trans (congrArg (A{{·}}ᵣ') lift_comp) ren_comp)
  | .pair A B  => congrArg₂ Ty.pair ren_comp ren_comp

def Ren'.Sub'.comp : Sub' Φ'' Φ' → Ren' Φ' Φ  → Sub' Φ'' Φ
  | σ', ρ' => fun K i => σ' K <| ρ' K i
def Sub'.of_Ren' : Ren' Ψ Φ → Sub' Ψ Φ
  | ρ' => fun K i => .var <| ρ' K i
def Sub'.of_Ren'_lift : lift (K:=K) (of_Ren' ρ') = of_Ren' ρ'.lift := by
  funext K i
  cases i with
  | zero => rfl
  | succ i => rfl
def Sub'.of_Ren'_lemma : {t : Ty Φ K} → t.sub' (of_Ren' ρ') = t.ren' ρ'
  | .var i => rfl
  | .unit => rfl
  | .bool => rfl
  | .fn A B => congrArg₂ Ty.fn of_Ren'_lemma of_Ren'_lemma
  | .pi K A => congrArg (Ty.pi K) (Eq.trans (congrArg (A.sub' ·) of_Ren'_lift) of_Ren'_lemma)
  | .pair A B  => congrArg₂ Ty.pair of_Ren'_lemma of_Ren'_lemma

def Sub'.comp : Sub' Φ'' Φ' → Sub' Φ' Φ  → Sub' Φ'' Φ
  | σ, σ' => fun K i => (σ' K i).sub' σ
def Sub'.Ren'.comp : Ren' Φ'' Φ' → Sub' Φ' Φ  → Sub' Φ'' Φ
  | ρ', σ' => fun K i => (σ' K i).ren' ρ'

def Sub'.nil : Sub' Φ .nil :=
  fun K i => by contradiction
def Sub'.nil_lemma : (σ' : Sub' Φ .nil) → σ' = Sub'.nil := by
  intro σ'
  funext K i
  contradiction
def Sub'.nil_of_ren_nil : of_Ren' Ren'.nil = Sub'.nil (Φ:=Φ) := by
  apply Sub'.nil_lemma
def Ren'.Sub'.lift_comp : Sub'.lift (K:=K) (comp f g) = comp f.lift g.lift :=
  funext₂ fun _ i =>
  match i with
  | .zero => rfl
  | .succ _ => rfl
def Sub'.Ren'.lift_comp : Sub'.lift (K:=K) (comp f g) = comp f.lift g.lift :=
  funext₂ fun _ i =>
  match i with
  | .zero => rfl
  | .succ i => by {
    rename_i K
    simp [lift, comp, Ty.wk']
    rw [←Ren'.ren_comp, ←Ren'.ren_comp]
    congr
  }
def Ren'.Sub'.ren_sub_comp : {t : Ty Φ K} → t{{comp f g}}ₛ' = t{{g}}ᵣ'{{f}}ₛ'
  | .var i => rfl
  | .unit => rfl
  | .bool => rfl
  | .fn A B => congrArg₂ Ty.fn ren_sub_comp ren_sub_comp
  | .pi K A => congrArg (Ty.pi K) (Eq.trans (congrArg (A.sub' ·) lift_comp) ren_sub_comp)
  | .pair A B  => congrArg₂ Ty.pair ren_sub_comp ren_sub_comp
def Sub'.Ren'.sub_ren_comp : {t : Ty Φ K} → t{{comp f g}}ₛ' = t{{g}}ₛ'{{f}}ᵣ'
  | .var i => rfl
  | .unit => rfl
  | .bool => rfl
  | .fn A B => congrArg₂ Ty.fn sub_ren_comp sub_ren_comp
  | .pi K A => congrArg (Ty.pi K) (Eq.trans (congrArg (A.sub' ·) lift_comp) sub_ren_comp)
  | .pair A B  => congrArg₂ Ty.pair sub_ren_comp sub_ren_comp
def nil_ren_sub' : (A : SystemF.Ty .nil *) → A{{Ren'.nil}}ᵣ'{{σ}}ₛ' = A{{Sub'.nil}}ₛ' := by
  intro A
  rw [←Ren'.Sub'.ren_sub_comp]
  rw [←Sub'.nil_lemma]
def nil_ren_sub : (A : SystemF.Ty .nil *) → A{{Ren'.nil}}ᵣ'{{σ}}ₛ' = A{{Ren'.nil}}ᵣ' := by
  intro A
  rw [nil_ren_sub', ←Sub'.of_Ren'_lemma]
  congr
  rw [←Sub'.nil_lemma]
def Ren'.nil_lemma' : (ρ' : Ren' Ψ Φ) → Ren'.nil = comp ρ' Ren'.nil := by
  intro ρ'
  rw [←nil_lemma]

def Ren (Δ : Con Ψ) (Γ : Con Φ) (ρ' : Ren' Ψ Φ) := ∀ A : Ty Φ *, Γ ∋ A → Δ ∋ A{{ρ'}}ᵣ'

def Ren.lift : Ren Δ Γ ρ' → Ren (Δ; A{{ρ'}}ᵣ') (Γ; A) ρ'
  | ρ, _, .zero => .zero
  | ρ, _, .succ i => .succ <| ρ _ i
def Ren.lift' : Ren Δ Γ ρ' → Ren (Δ;* K) (Γ;* K) (ρ'.lift)
  | ρ, _, .succ' i (A:=A) =>
    have h : A.wk'{{ρ'.lift}}ᵣ' = A{{ρ'}}ᵣ'.wk' := by
      simp [Ty.wk']
      rw [←Ren'.ren_comp, ←Ren'.ren_comp]
      rfl
    h ▸ .succ' (ρ _ i)

def sub'₀_ren' : {B : Ty (Φ; K) K'} → B[[A]]'₀{{ρ'}}ᵣ' = B{{ρ'.lift}}ᵣ'[[A{{ρ'}}ᵣ']]'₀ := by {
  intro B
  simp [Ty.sub'₀]
  rw [←Ren'.Sub'.ren_sub_comp]
  rw [←Sub'.Ren'.sub_ren_comp]
  congr
  simp [Ren'.Sub'.comp, Sub'.Ren'.comp]
  funext K i
  cases i with
  | zero => rfl
  | succ i => rfl
}
def Term.ren : Γ ⊢ A → Ren Δ Γ ρ' → Δ ⊢ A{{ρ'}}ᵣ'
  | .var i, ρ => .var (ρ _ i)
  | .unit, ρ => .unit
  | .false, ρ => .false
  | .true, ρ => .true
  | .ifte b t f, ρ => .ifte (b.ren ρ) (t.ren ρ) (f.ren ρ)
  | .lam A e, ρ => .lam A{{ρ'}}ᵣ' (e.ren ρ.lift)
  | .app f x, ρ => .app (f.ren ρ) (x.ren ρ)
  | .Lam K e, ρ => .Lam K (e.ren ρ.lift')
  | .App e A (B:=B), ρ =>
    sub'₀_ren' ▸ .App (e.ren ρ) (A.ren' ρ')
  | .pair a b, ρ => .pair (a.ren ρ) (b.ren ρ)
  | .p₁ ab, ρ => .p₁ (ab.ren ρ)
  | .p₂ ab, ρ => .p₂ (ab.ren ρ)

def Ren'.id : (Γ : Context Kind) → Ren' Γ Γ :=
  fun _ _ => _root_.id
def Ren'.id_lift : (Ren'.id Φ).lift (K:=K) = Ren'.id (Φ; K) := by
  funext K' i
  cases i
  all_goals simp [lift, id]
def Ren'.id_rfl : {A : Ty Φ K} → A{{Ren'.id Φ}}ᵣ' = A
  | .var i => rfl
  | .unit => rfl
  | .bool => rfl
  | .fn A B => by
    simp [Ty.ren']
    constructor
    apply id_rfl
    apply id_rfl
  | .pi _ A => by
    simp [Ty.ren']
    rw [id_lift]
    apply id_rfl
  | .pair A B => by
    simp [Ty.ren']
    constructor
    apply id_rfl
    apply id_rfl
def Ren.id : (Γ : Con Φ) → Ren Γ Γ (Ren'.id Φ)
  | _, _ => Ren'.id_rfl ▸ _root_.id
prefix : max "𝟙ᵣ" => Ren.id

def Ren.wk : Ren Δ Γ ρ' → (A : Ty _ *) → Ren (Δ; A) Γ ρ'
  | ρ, _, _, i => .succ (ρ _ i)
def Term.wk : Γ ⊢ A → Γ; B ⊢ A
  | t => (Ren'.id_rfl (A:=A)) ▸ Term.ren t (Ren.wk (Ren.id Γ) B)
def Ren.wk' : Ren Δ Γ ρ' → (K : Kind) → Ren (Δ;* K) Γ (Ren'.comp Ren'.wk ρ')
  | ρ, K, A, i =>
    have h : A{{ρ'}}ᵣ'.wk' = A{{Ren'.comp _ _}}ᵣ' := by {
      simp [Ty.wk']
      rw [←Ren'.ren_comp]
    }
    h ▸ .succ' (ρ _ i)
def Term.wk' : Γ ⊢ A → Γ;* K ⊢ A.wk'
  | t => Term.ren t (Ren.wk' (Ren.id Γ) K)


def Sub (Δ : Con Ψ) (Γ : Con Φ) (σ' : Ren' Ψ Φ) := ∀ A : Ty Φ *, Γ ∋ A → Δ ⊢ A{{σ'}}ᵣ'
def Sub.lift : Sub Δ Γ ρ' → Sub (Δ; A{{ρ'}}ᵣ') (Γ; A) ρ'
  | σ, _, .zero => .var .zero
  | σ, _, .succ i => (σ _ i).wk
def Sub.lift' : Sub Δ Γ ρ' → Sub (Δ;* K) (Γ;* K) (ρ'.lift)
  | σ, _, .succ' i (A:=A) =>
    have h : A.wk'{{ρ'.lift}}ᵣ' = A{{ρ'}}ᵣ'.wk' := by
      simp [Ty.wk']
      rw [←Ren'.ren_comp, ←Ren'.ren_comp]
      rfl
    h ▸ (σ _ i).wk'

def Term.sub : Γ ⊢ A → Sub Δ Γ ρ' → Δ ⊢ A{{ρ'}}ᵣ'
  | .var i, σ => σ A i
  | .unit, σ => .unit
  | .true, σ => .true
  | .false, σ => .false
  | .ifte b t e, σ => .ifte (b.sub σ) (t.sub σ) (e.sub σ)
  | .pair a b, σ => .pair (a.sub σ) (b.sub σ)
  | .p₁ ab, σ => .p₁ (ab.sub σ)
  | .p₂ ab, σ => .p₂ (ab.sub σ)
  | .lam B e, σ => .lam _ (e.sub σ.lift)
  | .app f x, σ => .app (f.sub σ) (x.sub σ)
  | .Lam K e, σ => .Lam _ (e.sub σ.lift')
  | .App f B, σ =>
    have : (Δ ⊢ _{{ρ'.lift}}ᵣ'[[B{{ρ'}}ᵣ']]'₀) = (Δ ⊢ _[[B]]'₀{{ρ'}}ᵣ') := by {
      congr
      rw [sub'₀_ren']
    }
    this ▸ Term.App (f.sub σ) (B.ren' ρ')

def Sub.id : Sub Γ Γ (Ren'.id _)
  | _, i => Ren'.id_rfl ▸ .var i
def Sub.cons : Sub Δ Γ ρ' → Δ ⊢ A{{ρ'}}ᵣ' → Sub Δ (Γ; A) ρ'
  | _, s, _, .zero => s
  | σ, _, _, .succ i => σ _ i

def Term.sub0 : Γ; B ⊢ A → Γ ⊢ B → Γ ⊢ A
  | t, s =>
    let tmp := t.sub (Sub.cons Sub.id (Ren'.id_rfl ▸ s))
    have h : (Γ ⊢ A{{Ren'.id _}}ᵣ') = (Γ ⊢ A) := by
      congr
      apply Ren'.id_rfl
    h ▸ tmp

def Con.renameₜ : Con Φ → Ren' Ψ Φ → Con Ψ
  | .nil, ρ => .nil
  | .cons Γ A, ρ => sorry
  | .cons' Γ K, ρ => sorry
def Con.subₜ : Con Φ → Sub' Ψ Φ → Con Ψ := sorry
def Term.sub0' : {Γ : Con Φ} → Γ;* K ⊢ A → (B : Ty Φ K) → Γ ⊢ A[[B]]'₀ := by
  intro Γ t B
  simp [Ty.sub'₀]


end SystemF
