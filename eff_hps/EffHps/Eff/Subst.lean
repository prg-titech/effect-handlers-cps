
import EffHps.Eff.Syntax

namespace Eff

def Rename (Δ Γ : Con) := ∀ A : ValTy,  Γ ∋ A → Δ ∋ A
def Subst (Δ Γ : Con) := ∀ A : ValTy,  Γ ∋ A → Δ ⊢v A

def Rename.extend : Rename Δ Γ → Rename (Δ; A) (Γ; A)
  | _, _, .zero => .zero
  | ρ, _, .succ i => .succ (ρ _ i)
def Rename.id : (Γ : Con) → Rename Γ Γ
  | _, _ => _root_.id
prefix : max "𝟙ᵣ" => Rename.id

def Rename.wk : Rename Δ Γ → {A : ValTy} → Rename (Δ; A) Γ
  | ρ, _, _, i => .succ (ρ _ i)

-- class HAdd' (α : Type u) (β : Type v) (γ : outParam (α → β → Type w)) where
--   hAdd : (a : α) → (b : β) → γ a b
-- macro_rules | `($x ++ $y)   => `(binop% HAdd'.hAdd $x $y)

-- instance : HAdd' (Rename Δ Γ) ValTy (fun _ A => Rename (Δ; A) Γ) where
--   hAdd := Ren.wk


mutual
def Val.rename : Γ ⊢v A → Rename Δ Γ → Δ ⊢v A
  | .var i, ρ => .var (ρ _ i)
  -- | .bool b, ρ => .bool b
  | .false , ρ => .false
  | .true , ρ => .true
  | .lam _ e, ρ => .lam _ (e.rename ρ.extend)
  | .handler ret op, ρ => .handler (ret.rename ρ.extend) (op.rename ρ)
termination_by v => sizeOf v

def Cmp.rename : Γ ⊢c C → Rename Δ Γ → Δ ⊢c C
  | .return (E:=E) v, ρ => .return (v.rename ρ)
  | .op i v k, ρ => .op i (v.rename ρ) (k.rename ρ.extend)
  | .app f x, ρ => .app (f.rename ρ) (x.rename ρ)
  | .ifte b t e, ρ => .ifte (b.rename ρ) (t.rename ρ) (e.rename ρ)
  | .handle_with c h, ρ => .handle_with (c.rename ρ) (h.rename ρ)
termination_by c => sizeOf c

def OpClauses.rename : OpClauses Γ E C → Rename Δ Γ → OpClauses Δ E C
  | .nil, ρ => .nil
  | .cons cls cl, ρ => .cons (cls.rename ρ) (cl.rename ρ.extend.extend)
termination_by op => sizeOf op
end
notation : max t "{{" σ "}}ᵣ" => Val.rename t σ
notation : max t "{{" σ "}}ᵣ" => Cmp.rename t σ
notation : max t "{{" σ "}}ᵣ" => OpClauses.rename t σ

def Val.wk : Γ ⊢v A → (Γ; B) ⊢v A := fun t => t{{(𝟙ᵣΓ).wk}}ᵣ
def Cmp.wk : Γ ⊢c A → (Γ; B) ⊢c A := fun t => t{{(𝟙ᵣΓ).wk}}ᵣ

def Subst.lift : Subst Δ Γ → Subst (Δ; A) (Γ; A)
  | _, _, .zero => .var .zero
  | σ, _, .succ i => (σ _ i).wk

mutual
def Val.subst : Γ ⊢v A → Subst Δ Γ → Δ ⊢v A
  | .var i, σ => (σ _ i)
  | .false, σ => .false
  | .true, σ => .true
  | .lam _ e, σ => .lam _ (e.subst σ.lift)
  | .handler ret op, σ => .handler (ret.subst σ.lift) (op.subst σ)
  termination_by v => sizeOf v
def Cmp.subst : Γ ⊢c C → Subst Δ Γ → Δ ⊢c C
  | .return (E:=E) v, σ => .return (v.subst σ)
  | .op i v k, σ => .op i (v.subst σ) (k.subst σ.lift)
  -- | do c₁ in c₂, σ => do c₁.subst σ in c₂.subst σ.lift
  | .app f x, σ => .app (f.subst σ) (x.subst σ)
  | .ifte b t e, σ => .ifte (b.subst σ) (t.subst σ) (e.subst σ)
  | .handle_with c h, σ => .handle_with (c.subst σ) (h.subst σ)
  termination_by c => sizeOf c
def OpClauses.subst : OpClauses Γ E C → Subst Δ Γ → OpClauses Δ E C
  | .nil, σ => .nil
  | .cons cls cl, σ => .cons (cls.subst σ) (cl.subst σ.lift.lift)
  termination_by op => sizeOf op
end

notation : max t "{{" σ "}}ₛ" => Val.subst t σ
notation : max t "{{" σ "}}ₛ" => Cmp.subst t σ
-- notation : max t "{{" σ "}}ₛ" => Handler.subst t σ
notation : max t "{{" σ "}}ₛ" => OpClauses.subst t σ

def Subst.id : (Γ : Con) → Subst Γ Γ
  | _, _, i => .var i
prefix : max "𝟙ₛ" => Subst.id
def Subst.cons : Subst Δ Γ → Δ ⊢v A → Subst Δ (Γ; A)
  | _, t, _, .zero => t
  | σ, _, _, .succ i => σ _ i
infixl : 67 "; " => Subst.cons


def Val.subst₀ : Γ; B ⊢v A → Γ ⊢v B → Γ ⊢v A := fun t s => t{{𝟙ₛΓ; s}}ₛ
def Cmp.subst₀ : Γ; B ⊢c A → Γ ⊢v B → Γ ⊢c A := fun t s => t{{𝟙ₛΓ; s}}ₛ

notation : max t "[[" s "]]ₛ" => Val.subst₀ t s
notation : max t "[[" s "]]ₛ" => Cmp.subst₀ t s

end Eff
