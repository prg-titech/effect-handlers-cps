
import EffectCompiler.Eff.FG_CBV.Syntax
import EffectCompiler.Eff.FG_CBV.Subst

namespace Eff
namespace FG_CBV


inductive SmallStep : Γ ⊢c A → Γ ⊢c A → Prop where
  | β_do_return : SmallStep (do return x in c) c[[x]]ₛ
  | β_do_op : {v : Γ ⊢v A'} → {c₁ : Γ; B' ⊢c ⟨A, ⟨E⟩⟩} → {c₂ : Γ; A ⊢c ⟨B, ⟨E⟩⟩}
    → SmallStep (do .op i v c₁ in c₂) (.op i v (do c₁ in c₂{{(𝟙ᵣΓ ++ B')↑}}ᵣ))
  | ξ_do : SmallStep c₁ c₁' → SmallStep (do c₁ in c₂) (do c₁' in c₂)
  | β_ifte_false : SmallStep (.ifte .false c₁ c₂) c₁
  | β_ifte_true : SmallStep (.ifte .true c₁ c₂) c₂
  | β_app : SmallStep ((.lam _ e) <> x) (e[[x]]ₛ)
  | ξ_handle : SmallStep c c' → SmallStep (handle c with .handler h) (handle c' with .handler h)
  | β_handle_return : SmallStep (handle return v with .handler ⟨val, op⟩) val[[v]]ₛ
  | β_handle_op : {i : E ∋ ⟨A', B'⟩} → {v : Γ ⊢v A'} → {c : Γ; B' ⊢c ⟨A, ⟨E⟩⟩}
    → {val : Γ; A ⊢c C} → {op : OpClauses Γ E C}
    → SmallStep (handle .op i v c with .handler ⟨val, op⟩) (op.get i)[[.lam _ (handle c{{(𝟙ᵣΓ ++ A')↑}}ᵣ with .handler ⟨val, op⟩{{𝟙ᵣΓ ++ A' ++ B'}}ᵣ)]]ₛ[[v]]ₛ

end FG_CBV
end Eff
