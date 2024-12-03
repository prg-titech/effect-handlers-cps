
import EffectCompiler.Eff.FG_CBV.Syntax
import EffectCompiler.Eff.FG_CBV.Subst

import EffectCompiler.SystemF.Basic
import EffectCompiler.SystemF.Subst


namespace Eff
namespace FG_CBV

mutual
@[reducible]
def ValTy.trans: ValTy → SystemF.Ty .nil *
  | .bool => .bool
  | .fn A C => A.trans ⇒ C.trans
  | .hn C D =>
    have : sizeOf C.val + sizeOf C.eff < 1 + sizeOf C + sizeOf D := by {
      cases C
      rename_i A E
      cases E
      rename_i E
      simp [CmpTy.val, CmpTy.eff]
      simp_arith
    }
    HandlerTy.trans C D.trans
  termination_by v => sizeOf v
@[reducible]
def CmpTy.trans: CmpTy → SystemF.Ty .nil * :=
  fun C => .pi .type ((HandlerTy.trans C (.var .zero)) ⇒ (.var .zero))
termination_by c => sizeOf c
decreasing_by {
  simp_wf
  rename_i C
  cases C
  rename_i A E
  cases E
  simp [CmpTy.val, CmpTy.eff]
  simp_arith
}
@[reducible]
def HandlerTy.trans: CmpTy → SystemF.Ty Φ * → SystemF.Ty Φ * :=
  fun C B =>
  have : sizeOf C.val < sizeOf C.val + sizeOf C.eff := by {
    simp_arith
    exact Signature.sizeOf_lemma _
  }
  have : sizeOf C.eff < sizeOf C.val + sizeOf C.eff := by {
    simp_arith
    exact ValTy.sizeOf_lemma _
  }
  let ρ' : SystemF.Ren' _ .nil := SystemF.Ren'.nil
  .pair (.fn C.val.trans{{ρ'}}ᵣ B) (Signature.trans C.eff B)
termination_by c => sizeOf c.val + sizeOf c.eff
@[reducible]
def Signature.trans : (S : Context OpTy) → SystemF.Ty Φ * → SystemF.Ty Φ *
  | .nil, _ => .pair .unit .unit
  | .cons S op, C =>
    .pair (op.trans C) (Signature.trans S C)
    termination_by S => sizeOf S
@[reducible]
def OpTy.trans : OpTy → SystemF.Ty Φ * → SystemF.Ty Φ *
  | ⟨A, B⟩, C =>
    let ρ' : SystemF.Ren' _ .nil := SystemF.Ren'.nil
    .fn A.trans{{ρ'}}ᵣ <| .fn (.fn B.trans{{ρ'}}ᵣ C) C
  termination_by op => sizeOf op
end

def OpTy.trans_ren_lemma : (OpTy.trans op B){{ρ'}}ᵣ = OpTy.trans op B{{ρ'}}ᵣ := by
  rename_i Φ Ψ
  cases op
  case mk A' B' =>
  simp [OpTy.trans, SystemF.Ty.ren']
  constructor
  rw [←SystemF.Ren'.ren_comp]
  generalize ρ'.comp SystemF.Ren'.nil = ρ''
  rw [SystemF.Ren'.nil_lemma ρ'']
  rw [←SystemF.Ren'.ren_comp]
  generalize ρ'.comp SystemF.Ren'.nil = ρ''
  rw [SystemF.Ren'.nil_lemma ρ'']
def Signature.trans_ren_lemma : (Signature.trans S B){{ρ'}}ᵣ = Signature.trans S B{{ρ'}}ᵣ := by
  rename_i Φ Ψ
  cases S with
  | nil => simp [Signature.trans, SystemF.Ty.ren']
  | cons S B =>
    simp [Signature.trans, SystemF.Ty.ren']
    constructor
    apply OpTy.trans_ren_lemma
    apply Signature.trans_ren_lemma
def HandlerTy.trans_ren_lemma : (HandlerTy.trans ⟨A, ⟨E⟩⟩ B){{ρ'}}ᵣ = HandlerTy.trans ⟨A, ⟨E⟩⟩ B{{ρ'}}ᵣ := by
  simp [trans, SystemF.Ty.ren']
  constructor
  rw [←SystemF.Ren'.ren_comp]
  generalize ρ'.comp SystemF.Ren'.nil = ρ''
  rw [SystemF.Ren'.nil_lemma ρ'']
  apply Signature.trans_ren_lemma
def OpTy.trans_sub_lemma : (OpTy.trans op B).sub' σ' = OpTy.trans op (B.sub' σ') := by
  rename_i Φ Ψ
  cases op
  case mk A' B' =>
  simp [OpTy.trans, SystemF.Ty.sub']
  constructor
  rw [SystemF.nil_ren_sub]
  rw [SystemF.nil_ren_sub]
def Signature.trans_sub_lemma : (Signature.trans S B).sub' σ' = Signature.trans S (B.sub' σ') := by
  rename_i Φ Ψ
  cases S with
  | nil => simp [Signature.trans, SystemF.Ty.sub']
  | cons S B =>
    simp [Signature.trans, SystemF.Ty.sub']
    constructor
    apply OpTy.trans_sub_lemma
    apply Signature.trans_sub_lemma
@[simp]
def Context.trans: Context ValTy → SystemF.Con .nil
  | .nil => .nil
  | .cons Γ A => .cons (trans Γ) A.trans
notation: max "⟦" t "⟧v" => ValTy.trans t
notation: max "⟦" t "⟧v" => Context.trans t
notation: max "⟦" t "⟧⇛" t': max => HandlerTy.trans t t'
notation: max "⟦" t "⟧c" => CmpTy.trans t

def ret_cl : Δ ⊢ ⟦C⟧⇛B → Δ ⊢ SystemF.Ty.fn ⟦C.val⟧v{{ρ'}}ᵣ B
  | t => by
    simp [HandlerTy.trans] at t
    rw [SystemF.Ren'.nil_lemma ρ']
    exact .p₁ t
def Signature.op_cl : Δ ⊢ Signature.trans E B → E ∋ ⟨A', B'⟩ → Δ ⊢ .fn ⟦A'⟧v{{ρ'}}ᵣ (.fn (.fn ⟦B'⟧v{{ρ'}}ᵣ B) B)
  | t, .zero => by
    simp [Signature.trans, OpTy.trans] at t
    rw [SystemF.Ren'.nil_lemma ρ']
    exact .p₁ t
  | t, .succ i => by
    simp [Signature.trans] at t
    apply op_cl _ i
    exact .p₂ t

def op_cl : Δ ⊢ ⟦C⟧⇛B → C.eff ∋ ⟨A', B'⟩ → Δ ⊢ .fn ⟦A'⟧v{{ρ'}}ᵣ (.fn (.fn ⟦B'⟧v{{ρ'}}ᵣ B) B)
  | t, i => by
    simp [HandlerTy.trans] at t
    rw [SystemF.Ren'.nil_lemma ρ']
    apply Signature.op_cl (.p₂ t) i

def Member.trans : Member Γ A →  ⟦Γ⟧v ∋ ⟦A⟧v
  | .zero => .zero
  | .succ i => .succ <| Member.trans i
mutual
def Val.trans : Γ ⊢v A →  ⟦Γ⟧v ⊢ ⟦A⟧v
  | .var i => .var <| Member.trans i
  | .false => .false
  | .true => .true
  | .lam A e (C:=⟨B, ⟨E⟩⟩) =>
    let ρ' : SystemF.Ren' (.nil; .type) .nil := SystemF.Ren'.wk
    let ρ : SystemF.Ren (⟦Γ; A⟧v;* *; (⟦⟨B, ⟨E⟩⟩⟧⇛(.var .zero))) ⟦Γ; A⟧v ρ' := by  {
      intro T i
      apply SystemF.Con.Member.succ
      apply SystemF.Con.Member.succ'
      assumption
    }
    let this : (⟦A⟧v ⇒ SystemF.Ty.pi .type (⟦⟨B, ⟨E⟩⟩⟧⇛(SystemF.Ty.var .zero) ⇒ SystemF.Ty.var .zero)) = ⟦A ⇒ ⟨B, ⟨E⟩⟩⟧v := by {
      simp [ValTy.trans, CmpTy.trans]
    }
    this ▸
    .lam ⟦A⟧v (.Lam .type (.lam (⟦⟨B, ⟨E⟩⟩⟧⇛(.var .zero)) (Cmp.trans e ρ (.var .zero))))
  | .handler h (C:=C) (C':=C') =>
    let this : ⟦C ⇛ C'⟧v = ⟦C⟧⇛⟦C'⟧c := by simp [ValTy.trans]
    this ▸ h.trans
termination_by v => sizeOf v
def Cmp.trans: Γ ⊢c C → (ρ : SystemF.Ren Δ ⟦Γ⟧v ρ') → Δ ⊢ (⟦C⟧⇛B) → Δ ⊢ B
  | .return v, ρ, h =>
    let v := v.trans
    let v := SystemF.Term.ren v ρ
    .app (ret_cl h) v
  | .op i (A':=A') (B':=B') v c, ρ, h =>
    let op := op_cl h i (ρ':=ρ')
    let ρ'' : SystemF.Ren (Δ; ⟦B'⟧v{{ρ'}}ᵣ) ⟦Γ; B'⟧v ρ' := by {
      intro K i
      cases i with
      | zero => constructor
      | succ i =>
        constructor
        exact ρ K i
    }
    -- TODO : replace it by ρ.lift?
    .app (.app op (SystemF.Term.ren v.trans ρ)) (.lam _ (Cmp.trans c (ρ'' : SystemF.Ren _ _ ρ') h.wk))
  -- | .do_in c₁ c₂, ρ, h => sorry
  | .app (A:=A') v₁ v₂, ρ, h => by
    let this : ⟦A' ⇒ ⟨A, ⟨E⟩⟩⟧v = (⟦A'⟧v ⇒ ⟦⟨A, ⟨E⟩⟩⟧c) := by {
      simp [ValTy.trans]
    }
    let v₁ := this ▸ v₁.trans
    let v₁ := v₁.ren ρ
    let v₂ := v₂.trans
    let v₂ := v₂.ren ρ
    let x := SystemF.Term.app v₁ v₂
    simp [CmpTy.trans] at x
    let y := SystemF.Term.App x B
    simp [SystemF.Ty.ren', SystemF.Ty.sub'₀, SystemF.Ty.sub', SystemF.Ren'.lift] at y
    simp [HandlerTy.trans, SystemF.Ty.ren', SystemF.Ren'.lift, SystemF.Ty.sub'] at y
    rw [Signature.trans_ren_lemma, Signature.trans_sub_lemma] at y
    simp [SystemF.Ty.ren', SystemF.Ren'.lift, SystemF.Ty.sub'] at y
    simp [SystemF.Sub'.id, SystemF.Sub'.extend] at y
    rw [←SystemF.Ren'.ren_comp, SystemF.Ren'.nil_lemma (ρ'.lift.comp _), SystemF.nil_ren_sub] at y
    simp [HandlerTy.trans] at h
    exact SystemF.Term.app y h
    -- let x := SystemF.Term.app (this ▸ v₁.trans.ren ρ) (v₂.trans.ren ρ)
    -- let y : Δ ⊢ (⟦CmpTy.mk A (Signature.mk E)⟧⇛B ⇒ B) := by {
    --   have this : (⟦CmpTy.mk A (Signature.mk E)⟧⇛B ⇒ B) = (⟦CmpTy.mk A (Signature.mk E)⟧⇛(.var .zero) ⇒ (.var .zero))[[B]]'₀ := by {
    --       simp [SystemF.Ty.sub'₀, SystemF.Ty.sub', HandlerTy.trans]
    --       constructor
    --       constructor
    --       constructor
    --       rw [SystemF.nil_ren_sub]
    --       rfl
    --       rw [Signature.trans_sub_lemma]
    --       rfl
    --       rfl
    --   }
    --   rw [this]
    --   apply SystemF.Term.App
    --   exact x
    -- }
    -- .app y h
  | .ifte v c₁ c₂, ρ, h =>
    let v := SystemF.Term.ren v.trans ρ
    let c₁ := Cmp.trans c₁ ρ h
    let c₂ := Cmp.trans c₂ ρ h
    .ifte v c₁ c₂
  | .handle_with (C:=C) c v, ρ, h => by
    rename Context SystemF.Kind => Φ
    cases C
    case mk A' E' =>
    cases E'
    case mk E' =>
    let v := v.trans
    let v := SystemF.Term.ren v ρ
    simp only [ValTy.trans] at v
    apply SystemF.Term.app _ h
    simp only [HandlerTy.trans]
    rw [HandlerTy.trans_ren_lemma] at v
    let cv := Cmp.trans c ρ v
    rw [CmpTy.trans] at cv
    let cvB := SystemF.Term.App cv B
    simp [SystemF.Ty.sub'₀, SystemF.Ty.ren', SystemF.Ty.sub', HandlerTy.trans, SystemF.Ren'.lift, SystemF.Sub'.extend] at cvB
    simp [Signature.trans_ren_lemma, Signature.trans_sub_lemma] at cvB
    simp [SystemF.Ty.ren', SystemF.Ty.sub', SystemF.Ren'.lift, SystemF.Sub'.extend] at cvB
    rw [←SystemF.Ren'.ren_comp, SystemF.Ren'.nil_lemma (ρ'.lift.comp _), SystemF.nil_ren_sub] at cvB
    exact cvB
  termination_by c => sizeOf c
def Handler.trans : Handler Γ C C' → ⟦Γ⟧v ⊢ ⟦C⟧⇛⟦C'⟧c
  | ⟨ret, op⟩ =>
  -- by
  --   simp [HandlerTy.trans]
  --   apply SystemF.Term.pair
    let ρ' : SystemF.Ren' (.nil; .type) .nil := by {
      intro K i
      apply Member.succ
      assumption
    }
    let ρ := SystemF.Ren.id .nil
    _
    -- {
    --   cases C'
    --   rename_i B E'
    --   cases E'
    --   rename_i E'
    --   simp [CmpTy.trans]
    --   apply SystemF.Term.lam
    --   apply SystemF.Term.Lam
    --   apply SystemF.Term.lam
    --   apply Cmp.trans ret
    --   {
    --     show SystemF.Ren _ _ ρ'
    --     intro K i
    --     apply SystemF.Con.Member.succ
    --     apply SystemF.Con.Member.succ'
    --     rw [←SystemF.Ren'.nil_lemma (SystemF.Ren'.id .nil), SystemF.Ren'.id_rfl]
    --     assumption
    --   }
    --   {
    --     simp [HandlerTy.trans]
    --     apply SystemF.Term.var .zero
    --   }
    -- }
    -- {
    --   let this := OpClauses.trans op
    --   simp [HandlerTy.trans] at this
    --   assumption
    -- }
termination_by h => sizeOf h
    -- match h with
    -- | ⟨ret, op⟩ => sizeOf ret + sizeOf op
def OpClauses.trans : OpClauses Γ E C → ⟦Γ⟧v ⊢ Signature.trans E ⟦C⟧c
  | .nil => .pair .unit .unit
  | .cons S c => by
    simp [Signature.trans]
    apply SystemF.Term.pair _ S.trans
    rename_i A' B'
    simp [OpTy.trans]
    apply SystemF.Term.lam
    apply SystemF.Term.lam
    rw [←SystemF.Ren'.nil_lemma (SystemF.Ren'.id .nil)]
    rw [SystemF.Ren'.id_rfl]
    rw [SystemF.Ren'.id_rfl]
    cases C
    rename_i A E
    cases E
    rename_i E
    simp [CmpTy.trans]
    apply SystemF.Term.Lam
    apply SystemF.Term.lam
    apply Cmp.trans c _ _
    exact SystemF.Ren'.wk
    {
      intro K i
      apply SystemF.Con.Member.succ
      apply SystemF.Con.Member.succ'
      rw [←Context.trans, ←CmpTy.trans, ←ValTy.trans, ←Context.trans]
      assumption
    }
    apply SystemF.Term.var .zero
  termination_by S => sizeOf S
end

end FG_CBV
end Eff
