
import EffectCompiler.Eff.FG_CBV.Syntax
import EffectCompiler.Eff.FG_CBV.Subst

-- import EffectCompiler.SystemF.Basic

namespace Eff
namespace FG_CBV


-- inductive SmallStep : Γ ⊢c A → Γ ⊢c A → Prop where
--   | β_do_return : SmallStep (do return x in c) c[[x]]ₛ
--   | β_do_op : {v : Γ ⊢v A'} → {c₁ : Γ; B' ⊢c ⟨A, ⟨E⟩⟩} → {c₂ : Γ; A ⊢c ⟨B, ⟨E⟩⟩}
--     → SmallStep (do .op i v c₁ in c₂) (.op i v (do c₁ in c₂{{(𝟙ᵣΓ ++ B')↑}}ᵣ))
--   | ξ_do : SmallStep c₁ c₁' → SmallStep (do c₁ in c₂) (do c₁' in c₂)
--   | β_ifte_false : SmallStep (.ifte .false c₁ c₂) c₁
--   | β_ifte_true : SmallStep (.ifte .true c₁ c₂) c₂
--   | β_app : SmallStep ((.lam _ e) <> x) (e[[x]]ₛ)
--   | ξ_handle : SmallStep c c' → SmallStep (handle c with .handler h) (handle c' with .handler h)
--   | β_handle_return : SmallStep (handle return v with .handler ⟨val, op⟩) val[[v]]ₛ
--   | β_handle_op : {i : E ∋ ⟨A', B'⟩} → {v : Γ ⊢v A'} → {c : Γ; B' ⊢c ⟨A, ⟨E⟩⟩}
--     → {val : Γ; A ⊢c C} → {op : OpClauses Γ E C}
--     → SmallStep (handle .op i v c with .handler ⟨val, op⟩) (op.get i)[[.lam _ (handle c{{(𝟙ᵣΓ ++ A')↑}}ᵣ with .handler ⟨val, op⟩{{𝟙ᵣΓ ++ A' ++ B'}}ᵣ)]]ₛ[[v]]ₛ

inductive BigStep : Γ ⊢c A → Γ ⊢c A → Prop where
  | return : BigStep (return v) (return v)

-- def comp : Γ ⊢c ⟨A, ⟨E⟩⟩ → SystemF.Term Γ' A' := sorry

def eval : Γ ⊢c ⟨A, ⟨E⟩⟩ → Γ ⊢c ⟨A, ⟨E⟩⟩
  | .return v => .return v
  | .op i v c => .op i v c
  | do c₁ in c₂ =>
    have c₁ := eval c₁
    match c₁ with
    | .return v => eval c₂[[v]]ₛ
    | .op i v c₁ => .op i v (do c₁ in c₂{{((𝟙ᵣΓ).wk _)↑}}ᵣ)
    | c₁ => do c₁ in c₂
  | .lam _ e <> x => eval e[[x]]ₛ
  | .var i <> x => .var i <> x
  | .ifte .false _ c₂ => eval c₂
  | .ifte .true c₁ _ => eval c₁
  | .ifte (.var i) c₁ c₂ => .ifte (.var i) c₁ c₂
  | handle c with .handler ⟨val, op⟩ =>
    have c := eval c
    match c with
    | .return v => eval val[[v]]ₛ
    | .op i v c => eval <| (op.get i)[[Val.wk <| .lam _ handle c with .handler ⟨val, op⟩{{(𝟙ᵣΓ).wk _}}ᵣ]]ₛ[[v]]ₛ
    | c => handle c with .handler ⟨val, op⟩
  | handle c with .var i => handle c with .var i
decreasing_by all_goals sorry

#eval eval <| (.return .false : .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)
#reduce eval <| (.return .false : .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)

#eval eval <| (do .return .false in .return (.var .zero): .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)
#reduce eval <| (do .return .false in .return (.var .zero): .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)
#reduce eval <| ((.return (.var .zero))[[.false]]ₛ: .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)

#eval eval <| (
    do .return (
      .lam 𝔹 (
        do .op .zero .false (.return (.var .zero)) in
        .ifte (.var .zero) (.return (.var (.succ .zero))) (.return .false)))
    in
    .handle_with ((.var .zero) <> .false ) (.handler ⟨.return (.var .zero), .cons .nil (.var .zero <> .false)⟩)
    : .nil ⊢c ⟨𝔹, ⟨.nil⟩⟩)
#eval eval <| (
    do .return (
      .lam 𝔹 (
        do .op .zero .false (.return (.var .zero)) in
        .ifte (.var .zero) (.return (.var (.succ .zero))) (.return .false)))
    in
    .handle_with ((.var .zero) <> .false ) (.handler ⟨.return (.var .zero), .cons .nil (.var .zero <> .true)⟩)
    : .nil ⊢c ⟨𝔹, ⟨.nil⟩⟩)
#eval eval <| (
    do .return (
      .lam 𝔹 (
        do .op .zero .false (.return (.var .zero)) in
        .ifte (.var .zero) (.return (.var (.succ .zero))) (.return .false)))
    in
    .handle_with ((.var .zero) <> .true ) (.handler ⟨.return (.var .zero), .cons .nil (.var .zero <> .false)⟩)
    : .nil ⊢c ⟨𝔹, ⟨.nil⟩⟩)
#eval eval <| (
    do .return (
      .lam 𝔹 (
        do .op .zero .false (.return (.var .zero)) in
        .ifte (.var .zero)
          (.return (.var (.succ .zero)))
          (.return .false)))
    in
    .handle_with ((.var .zero) <> .true ) (.handler ⟨.return (.var .zero), .cons .nil (.var .zero <> .true)⟩)
    : .nil ⊢c ⟨𝔹, ⟨.nil⟩⟩)

mutual
inductive Normal : Γ ⊢c ⟨A, E⟩ → Type where
  | return : Normal (.return v)
  | op : Normal (.op i v c)
  | neutral : Neutral e → Normal e
inductive Neutral : Γ ⊢c ⟨A, E⟩ → Type where
  | app : Neutral ((.var i) <> x)
  | ifte : Neutral (.ifte (.var i) c₁ c₂)
  | do_in : Neutral c₁ → Neutral (do c₁ in c₂)
  | handle_h : Neutral (handle c with .var i)
  | handle_c : Neutral c → Neutral (handle c with h)
  -- | ifte : Normal c₁ → Normal c₂ → Neutral (.ifte (.var i) c₁ c₂)
  -- | handle : Normal c → Neutral (handle c with .var i)
end

def eval' : Γ ⊢c ⟨A, ⟨E⟩⟩ → Σ t : Γ ⊢c ⟨A, ⟨E⟩⟩, Normal t
  | .return v => ⟨.return v, .return⟩
  | .op i v c => ⟨.op i v c, .op⟩
  | do c₁ in c₂ =>
    have c₁ := eval' c₁
    match c₁ with
    | ⟨.return v, _⟩ => eval' c₂[[v]]ₛ
    | ⟨.op i v c₁, _⟩ => ⟨.op i v (do c₁ in c₂{{((𝟙ᵣΓ).wk _)↑}}ᵣ), .op⟩
    | ⟨c₁, .neutral hn_c₁⟩ => ⟨do c₁ in c₂, .neutral (.do_in hn_c₁)⟩
  | .lam _ e <> x => eval' e[[x]]ₛ
  | .var i <> x => ⟨.var i <> x, .neutral .app⟩
  | .ifte .false _ c₂ => eval' c₂
  | .ifte .true c₁ _ => eval' c₁
  | .ifte (.var i) c₁ c₂ => ⟨.ifte (.var i) c₁ c₂, .neutral .ifte⟩
  -- | handle (.return v) with .handler ⟨val, _⟩ => eval val[[v]]ₛ
  -- | handle (.op i v c) with .handler ⟨val, op⟩ => eval <| (op.get i)[[Val.wk <| .lam _ handle c with .handler ⟨val, op⟩{{(𝟙ᵣΓ).wk _}}ᵣ]]ₛ[[v]]ₛ
  -- | handle c with .handler ⟨val, op⟩ => handle eval c with .handler ⟨val, op⟩
  | handle c with .handler ⟨val, op⟩ =>
    have c := eval' c
    match c with
    | ⟨.return v, _⟩ => eval' val[[v]]ₛ
    | ⟨.op i v c, _⟩ => eval' <| (op.get i)[[Val.wk <| .lam _ handle c with .handler ⟨val, op⟩{{(𝟙ᵣΓ).wk _}}ᵣ]]ₛ[[v]]ₛ
    | ⟨c, .neutral hn_c⟩ => ⟨handle c with .handler ⟨val, op⟩, .neutral (.handle_c hn_c)⟩
  | handle c with .var i => ⟨handle c with .var i, .neutral .handle_h⟩
decreasing_by all_goals sorry

#eval eval' <| (.return .false : .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)
#reduce eval' <| (.return .false : .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)

#eval eval' <| (do .return .false in .return (.var .zero): .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)
#reduce eval' <| (do .return .false in .return (.var .zero): .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)
#reduce eval' <| ((.return (.var .zero))[[.false]]ₛ: .nil ⊢c ⟨.bool, ⟨.nil⟩⟩)

end FG_CBV
end Eff
