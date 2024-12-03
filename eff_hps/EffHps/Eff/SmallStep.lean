
import EffHps.Eff.Syntax
import EffHps.Eff.Subst

namespace Eff

inductive SmallStep : Γ ⊢c A → Γ ⊢c A → Prop where
  -- | β_do_return : SmallStep (do return x in c) c[[x]]ₛ
  -- | β_do_op : {v : Γ ⊢v A'} → {c₁ : Γ; B' ⊢c ⟨A, ⟨E⟩⟩} → {c₂ : Γ; A ⊢c ⟨B, ⟨E⟩⟩}
  --   → SmallStep (do .op i v c₁ in c₂) (.op i v (do c₁ in c₂{{(𝟙ᵣΓ ++ B')↑}}ᵣ))
  -- | ξ_do : SmallStep c₁ c₁' → SmallStep (do c₁ in c₂) (do c₁' in c₂)
  | β_ifte_true : SmallStep (.ifte .true c₁ c₂) c₁
  | β_ifte_false : SmallStep (.ifte .false c₁ c₂) c₂
  | β_app : SmallStep (.app (.lam _ e) x) (e[[x]]ₛ)
  | ξ_handle : SmallStep c c' → SmallStep (.handle_with c (.handler ret op)) (.handle_with c' (.handler ret op))
  | β_handle_return : SmallStep (.handle_with (.return v) (.handler ret op)) ret[[v]]ₛ
  | β_handle_op : {i : E ∋ₛ ⟨A', B'⟩} → {v : Γ ⊢v A'} → {c : Γ; B' ⊢c ⟨A, E⟩}
    → {val : Γ; A ⊢c C} → {op : OpClauses Γ E C}
    → SmallStep (.handle_with (.op i v c) (.handler val op)) (op.get' i)[[.lam _ (.handle_with c{{(𝟙ᵣΓ).wk.extend}}ᵣ (.handler val op){{(𝟙ᵣΓ).wk.wk}}ᵣ)]]ₛ[[v]]ₛ

end Eff
