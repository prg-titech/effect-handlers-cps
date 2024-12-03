
import EffectCompiler.Eff.FG_CBV.Syntax

namespace Eff
namespace FG_CBV

def Ren (Δ Γ : Context ValTy) := ∀ A : ValTy,  Γ ∋ A → Δ ∋ A
def Sub (Δ Γ : Context ValTy) := ∀ A : ValTy,  Γ ∋ A → Δ ⊢v A

def Ren.lift : Ren Δ Γ → Ren (Δ; A) (Γ; A)
  | _, _, .zero => .zero
  | ρ, _, .succ i => .succ (ρ _ i)
postfix : max "↑" => Ren.lift
def Ren.id : (Γ : Context ValTy) → Ren Γ Γ
  | _, _ => _root_.id
prefix : max "𝟙ᵣ" => Ren.id

def Ren.wk : Ren Δ Γ → (A : ValTy) → Ren (Δ; A) Γ
  | ρ, _, _, i => .succ (ρ _ i)

class HAdd' (α : Type u) (β : Type v) (γ : outParam (α → β → Type w)) where
  hAdd : (a : α) → (b : β) → γ a b
macro_rules | `($x ++ $y)   => `(binop% HAdd'.hAdd $x $y)

instance : HAdd' (Ren Δ Γ) ValTy (fun _ A => Ren (Δ; A) Γ) where
  hAdd := Ren.wk


mutual
def Val.rename : Γ ⊢v A → Ren Δ Γ → Δ ⊢v A
  | .var i, ρ => .var (ρ _ i)
  -- | .bool b, ρ => .bool b
  | .false , ρ => .false
  | .true , ρ => .true
  | .lam _ e, ρ => .lam _ (e.rename ρ.lift)
  | .handler hn, ρ => .handler (hn.rename ρ)
  termination_by v => sizeOf v
def Cmp.rename : Γ ⊢c C → Ren Δ Γ → Δ ⊢c C
  | .return v, ρ => .return (v.rename ρ)
  | .op i v k, ρ => .op i (v.rename ρ) (k.rename ρ.lift)
  -- | do c₁ in c₂, ρ => do c₁.rename ρ in c₂.rename ρ.lift
  | .app f x, ρ => .app (f.rename ρ) (x.rename ρ)
  | .ifte b t e, ρ => .ifte (b.rename ρ) (t.rename ρ) (e.rename ρ)
  | handle c with h, ρ => .handle_with (c.rename ρ) (h.rename ρ)
  termination_by c => sizeOf c
def Handler.rename : Γ ⊢h C ⇛ C' → Ren Δ Γ → Δ ⊢h C ⇛ C'
  | .mk val op, ρ => ⟨val.rename ρ.lift, op.rename ρ⟩
  termination_by hn => sizeOf hn
def OpClauses.rename : OpClauses Γ E C → Ren Δ Γ → OpClauses Δ E C
  | .nil, ρ => .nil
  | .cons cls cl, ρ => .cons (cls.rename ρ) (cl.rename ρ.lift.lift)
  termination_by op => sizeOf op
end
notation : max t "{{" σ "}}ᵣ" => Val.rename t σ
notation : max t "{{" σ "}}ᵣ" => Cmp.rename t σ
notation : max t "{{" σ "}}ᵣ" => Handler.rename t σ
notation : max t "{{" σ "}}ᵣ" => OpClauses.rename t σ

def Val.wk : Γ ⊢v A → (Γ; B) ⊢v A := fun t => t{{𝟙ᵣΓ ++ B}}ᵣ
def Cmp.wk : Γ ⊢c A → (Γ; B) ⊢c A := fun t => t{{𝟙ᵣΓ ++ B}}ᵣ

def Sub.lift : Sub Δ Γ → Sub (Δ; A) (Γ; A)
  | _, _, .zero => .var .zero
  | σ, _, .succ i => (σ _ i).wk

mutual
def Val.subst : Γ ⊢v A → Sub Δ Γ → Δ ⊢v A
  | .var i, σ => (σ _ i)
  -- | .bool b, σ => .bool b
  | .false, σ => .false
  | .true, σ => .true
  | .lam _ e, σ => .lam _ (e.subst σ.lift)
  | .handler hn, σ => .handler (hn.subst σ)
  termination_by v => sizeOf v
def Cmp.subst : Γ ⊢c C → Sub Δ Γ → Δ ⊢c C
  | .return v, σ => .return (v.subst σ)
  | .op i v k, σ => .op i (v.subst σ) (k.subst σ.lift)
  -- | do c₁ in c₂, σ => do c₁.subst σ in c₂.subst σ.lift
  | .app f x, σ => .app (f.subst σ) (x.subst σ)
  | .ifte b t e, σ => .ifte (b.subst σ) (t.subst σ) (e.subst σ)
  | handle c with h, σ => .handle_with (c.subst σ) (h.subst σ)
  termination_by c => sizeOf c
def Handler.subst : Γ ⊢h C ⇛ C' → Sub Δ Γ → Δ ⊢h C ⇛ C'
  | .mk val op, σ => ⟨val.subst σ.lift, op.subst σ⟩
  termination_by hn => sizeOf hn
def OpClauses.subst : OpClauses Γ E C → Sub Δ Γ → OpClauses Δ E C
  | .nil, σ => .nil
  | .cons cls cl, σ => .cons (cls.subst σ) (cl.subst σ.lift.lift)
  termination_by op => sizeOf op
end

notation : max t "{{" σ "}}ₛ" => Val.subst t σ
notation : max t "{{" σ "}}ₛ" => Cmp.subst t σ
notation : max t "{{" σ "}}ₛ" => Handler.subst t σ
notation : max t "{{" σ "}}ₛ" => OpClauses.subst t σ

def Sub.id : (Γ : Context ValTy) → Sub Γ Γ
  | _, _, i => .var i
prefix : max "𝟙ₛ" => Sub.id
def Sub.extend : Sub Δ Γ → Δ ⊢v A → Sub Δ (Γ; A)
  | _, t, _, .zero => t
  | σ, _, _, .succ i => σ _ i
infixl : 67 "; " => Sub.extend


def Val.subs₀ : Γ; B ⊢v A → Γ ⊢v B → Γ ⊢v A := fun t s => t{{𝟙ₛΓ; s}}ₛ
def Cmp.subs₀ : Γ; B ⊢c A → Γ ⊢v B → Γ ⊢c A := fun t s => t{{𝟙ₛΓ; s}}ₛ

notation : max t "[[" s "]]ₛ" => Val.subs₀ t s
notation : max t "[[" s "]]ₛ" => Cmp.subs₀ t s

end FG_CBV
end Eff
