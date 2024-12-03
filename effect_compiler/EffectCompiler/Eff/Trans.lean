
import EffectCompiler.Eff.Syntax
import EffectCompiler.Eff.Subst

import EffectCompiler.SystemF.Basic

import EffectCompiler.Eff.SmallStep

import Lean.Elab.Tactic.LibrarySearch

namespace Eff

mutual
def ValTy.trans: ValTy → SystemF.Ty .nil
  | .bool => .bool
  | .fn A C => A.trans ⇒ CmpTy.trans C
  | .hn ((A, E), D) =>
    HandlerTy.trans (A, E) (CmpTy.trans D)
termination_by v => sizeOf v

def CmpTy.trans: CmpTy → SystemF.Ty .nil :=
  fun C => .pi ((HandlerTy.trans C (.var .zero)) ⇒ (.var .zero))
termination_by c => sizeOf c
decreasing_by {
  simp_wf
  rename_i C
  cases C
  rename_i A E
  simp_arith
}

def HandlerTy.trans: CmpTy → SystemF.Ty Φ → SystemF.Ty Φ :=
  fun C B =>
  have : sizeOf C.1 < sizeOf C.1 + sizeOf C.2 := by {
    simp_arith
    exact Signature.sizeOf_lemma _
  }
  have : sizeOf C.2 < sizeOf C.1 + sizeOf C.2 := by {
    simp_arith
    exact ValTy.sizeOf_lemma _
  }
  let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
  .pair (.fn C.1.trans{{ρ'}}ᵣₜ B) (Signature.trans C.2 B)
termination_by c => sizeOf c.1 + sizeOf c.2

def Signature.trans : (S : Context OpTy) → SystemF.Ty Φ → SystemF.Ty Φ
  | .nil, _ => .pair .unit .unit
  | .cons S op, C =>
    .pair (op.trans C) (Signature.trans S C)
    termination_by S => sizeOf S

def OpTy.trans : OpTy → SystemF.Ty Φ → SystemF.Ty Φ
  | ⟨A, B⟩, C =>
    let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
    .fn A.trans{{ρ'}}ᵣₜ <| .fn (.fn B.trans{{ρ'}}ᵣₜ C) C
  termination_by op => sizeOf op
end


def OpTy.trans_ren_lemma : (OpTy.trans op B){{ρ'}}ᵣₜ = OpTy.trans op B{{ρ'}}ᵣₜ := by
  rename_i Φ Ψ
  cases op
  case mk A' B' =>
  simp [OpTy.trans, SystemF.Ty.renameₜ]
  constructor
  rw [←SystemF.Renameₜ.ren_comp]
  generalize ρ'.comp SystemF.Renameₜ.nil = ρ''
  rw [SystemF.Renameₜ.nil_eta ρ'']
  rw [←SystemF.Renameₜ.ren_comp]
  generalize ρ'.comp SystemF.Renameₜ.nil = ρ''
  rw [SystemF.Renameₜ.nil_eta ρ'']
def Signature.trans_ren_lemma : (Signature.trans S B){{ρ'}}ᵣₜ = Signature.trans S B{{ρ'}}ᵣₜ := by
  rename_i Φ Ψ
  cases S with
  | nil => simp [Signature.trans, SystemF.Ty.renameₜ]
  | cons S B =>
    simp [Signature.trans, SystemF.Ty.renameₜ]
    constructor
    apply OpTy.trans_ren_lemma
    apply Signature.trans_ren_lemma
def HandlerTy.trans_ren_lemma : (HandlerTy.trans (A, E) B){{ρ'}}ᵣₜ = HandlerTy.trans (A, E) B{{ρ'}}ᵣₜ := by
  simp [trans, SystemF.Ty.renameₜ]
  constructor
  rw [←SystemF.Renameₜ.ren_comp]
  generalize ρ'.comp SystemF.Renameₜ.nil = ρ''
  rw [SystemF.Renameₜ.nil_eta ρ'']
  apply Signature.trans_ren_lemma
def OpTy.trans_sub_lemma : (OpTy.trans op B).substₜ σ' = OpTy.trans op (B.substₜ σ') := by
  rename_i Φ Ψ
  cases op
  case mk A' B' =>
  simp [OpTy.trans, SystemF.Ty.substₜ]
  constructor
  rw [SystemF.nil_ren_sub]
  rw [SystemF.nil_ren_sub]
def Signature.trans_sub_lemma : (Signature.trans S B).substₜ σ' = Signature.trans S (B.substₜ σ') := by
  rename_i Φ Ψ
  cases S with
  | nil => simp [Signature.trans, SystemF.Ty.substₜ]
  | cons S B =>
    simp [Signature.trans, SystemF.Ty.substₜ]
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

-- def ret_cl : Φ / Δ ⊢ ⟦C⟧⇛B → Φ / Δ ⊢ SystemF.Ty.fn ⟦C.val⟧v{{ρ'}}ᵣₜ B
--   | t => by
--     simp [HandlerTy.trans] at t
--     rw [SystemF.Renameₜ.nil_eta ρ']
--     exact .p₁ t
-- def Signature.op_cl : Φ / Δ ⊢ Signature.trans E B → E ∋ ⟨A', B'⟩ → Φ / Δ ⊢ .fn ⟦A'⟧v{{ρ'}}ᵣₜ (.fn (.fn ⟦B'⟧v{{ρ'}}ᵣₜ B) B)
--   | t, .zero => by
--     simp [Signature.trans, OpTy.trans] at t
--     rw [SystemF.Renameₜ.nil_eta ρ']
--     exact .p₁ t
--   | t, .succ i => by
--     simp [Signature.trans] at t
--     apply op_cl _ i
--     exact .p₂ t

-- def op_cl : Φ / Δ ⊢ ⟦C⟧⇛B → C.eff ∋ ⟨A', B'⟩ → Φ / Δ ⊢ .fn ⟦A'⟧v{{ρ'}}ᵣₜ (.fn (.fn ⟦B'⟧v{{ρ'}}ᵣₜ B) B)
--   | t, i => by
--     simp [HandlerTy.trans] at t
--     rw [SystemF.Renameₜ.nil_eta ρ']
--     apply Signature.op_cl (.p₂ t) i

def Member.trans : Member Γ A →  ∅ / ⟦Γ⟧v ∋ ⟦A⟧v
  | .zero => .zero
  | .succ i => .succ <| Member.trans i

-- mutual
-- def Val.trans : Γ ⊢v A → ∅ / ⟦Γ⟧v ⊢ ⟦A⟧v
--   | .var i => .var <| Member.trans i
--   | .false => (ValTy.trans.eq_def _) ▸ .false
--   | .true => (ValTy.trans.eq_def _) ▸ .true
--   | .lam A e (C:=C) =>
--     let h : (∅ / ⟦Γ⟧v ⊢ (⟦A⟧v ⇒ ⟦C⟧c)) = (∅ / ⟦Γ⟧v ⊢ ⟦.fn A C⟧v) := by
--       simp [ValTy.trans]
--     have : sizeOf e + 1 < 1 + sizeOf Γ + sizeOf C + sizeOf A + sizeOf e := by {
--       simp_arith
--       show 0 < _
--       apply Nat.lt_add_left
--       apply ValTy.sizeOf_lemma
--     }
--     h ▸ .lam ⟦A⟧v (Cmp.trans' e)
--   | .handler (A:=A) (E:=E) ret op (C:=C) =>
--     have : sizeOf ret + 1 < 1 + sizeOf Γ + sizeOf A + sizeOf C + sizeOf E + sizeOf ret + sizeOf op := by {
--       simp_arith
--       show 0 < _
--       apply Nat.lt_add_right
--       apply Nat.lt_add_right
--       apply Nat.lt_add_right
--       apply Nat.lt_add_left
--       apply ValTy.sizeOf_lemma
--     }
--     have this : ⟦(A, E) ⇛ C⟧v = .pair _ _ := by {
--       simp [ValTy.trans, HandlerTy.trans];
--       rw [←SystemF.Renameₜ.nil_eta SystemF.Renameₜ.id, SystemF.Renameₜ.id_rfl]
--       rfl
--     }
--     this ▸ .pair
--     (
--       .lam ⟦A⟧v (Cmp.trans' ret)
--     )
--     (OpClauses.trans op)
-- termination_by v => sizeOf v
-- def Cmp.trans': Γ ⊢c C → ∅ / ⟦Γ⟧v ⊢ ⟦C⟧c
--   | .app (A:=A') v₁ v₂ =>
--     let h : ⟦.fn A' C⟧v = (⟦A'⟧v ⇒ ⟦C⟧c) := by simp [ValTy.trans]
--     let v₁' := h ▸ v₁.trans
--     let v₂' := v₂.trans
--     let x := SystemF.Term.app v₁' v₂'
--     x
--   | .handle_with (C:=(A, E)) c v => by
--     let v' := v.trans
--     simp only [ValTy.trans] at v'
--     let ρ' : SystemF.Renameₜ .nil .nil := SystemF.Renameₜ.id
--     let ρ : SystemF.Rename _ _ ⟦Γ⟧v ⟦Γ⟧v ρ' := SystemF.Rename.id _
--     exact Cmp.trans c ρ v'
--   | c =>
--     let h : SystemF.Ty.pi (⟦C⟧⇛(SystemF.Ty.var .zero) ⇒ SystemF.Ty.var .zero) = ⟦C⟧c := by {
--       simp [CmpTy.trans]
--     }
--     let ρ' : SystemF.Renameₜ (.nil;*) .nil := .succ
--     let ρ : SystemF.Rename _ _ ((⟦Γ⟧v).wk; ⟦C⟧⇛(SystemF.Ty.var .zero)) ⟦Γ⟧v ρ' := by  {
--         intro T i
--         apply SystemF.Con.Member.succ
--         apply SystemF.Con.Member.renameₜ
--         assumption
--     }
--     h ▸ (.lamₜ (.lam (⟦C⟧⇛(.var .zero)) (Cmp.trans c ρ (.var .zero))))
-- termination_by c => sizeOf c + 1
-- def Cmp.trans: Γ ⊢c C → (ρ : SystemF.Rename _ _ Δ ⟦Γ⟧v ρ') → _ / Δ ⊢ (⟦C⟧⇛B) → _ / Δ ⊢ B
--   | .return (E:=E) v, ρ, h => .app (ret_cl h) (v.trans.rename ρ)
--   | .op i (A':=A') (B':=B') v c, ρ, h =>
--     let op := op_cl h i (ρ':=ρ')
--     let ρ'' : SystemF.Rename _ _ (Δ; ⟦B'⟧v{{ρ'}}ᵣₜ) ⟦Γ; B'⟧v ρ' := by {
--       intro K i
--       cases i with
--       | zero => constructor
--       | succ i =>
--         constructor
--         exact ρ i
--     }
--     -- TODO : replace it by ρ.lift?
--     .app (.app op (SystemF.Term.rename v.trans ρ)) (.lam _ (Cmp.trans c (ρ'' : SystemF.Rename _ _ _ _ ρ') h.wk))
--   | .app (A:=A') v₁ v₂, ρ, h => by
--     let this : ⟦.fn A' C⟧v = (⟦A'⟧v ⇒ ⟦C⟧c) := by simp [ValTy.trans]
--     let v₁ := this ▸ v₁.trans
--     let v₁ := v₁.rename ρ
--     let v₂ := v₂.trans
--     let v₂ := v₂.rename ρ
--     let x := SystemF.Term.app v₁ v₂
--     simp [CmpTy.trans] at x
--     let y := SystemF.Term.appₜ x B
--     simp [SystemF.Ty.renameₜ, SystemF.Ty.substₜ₀, SystemF.Ty.substₜ, SystemF.Renameₜ.extend] at y
--     simp [HandlerTy.trans, SystemF.Ty.renameₜ, SystemF.Renameₜ.extend, SystemF.Ty.substₜ] at y
--     rw [Signature.trans_ren_lemma, Signature.trans_sub_lemma] at y
--     simp [SystemF.Ty.renameₜ, SystemF.Renameₜ.extend, SystemF.Ty.substₜ] at y
--     simp [SystemF.Substₜ.id, SystemF.Substₜ.cons] at y
--     rw [←SystemF.Renameₜ.ren_comp, SystemF.Renameₜ.nil_eta (ρ'.extend.comp _), SystemF.nil_ren_sub] at y
--     simp [HandlerTy.trans] at h
--     exact SystemF.Term.app y h
--     -- let x := SystemF.Term.app (this ▸ v₁.trans.ren ρ) (v₂.trans.ren ρ)
--     -- let y : Δ ⊢ (⟦CmpTy.mk A (Signature.mk E)⟧⇛B ⇒ B) := by {
--     --   have this : (⟦CmpTy.mk A (Signature.mk E)⟧⇛B ⇒ B) = (⟦CmpTy.mk A (Signature.mk E)⟧⇛(.var .zero) ⇒ (.var .zero))[[B]]'₀ := by {
--     --       simp [SystemF.Ty.sub'₀, SystemF.Ty.sub', HandlerTy.trans]
--     --       constructor
--     --       constructor
--     --       constructor
--     --       rw [SystemF.nil_ren_sub]
--     --       rfl
--     --       rw [Signature.trans_sub_lemma]
--     --       rfl
--     --       rfl
--     --   }
--     --   rw [this]
--     --   apply SystemF.Term.App
--     --   exact x
--     -- }
--     -- .app y h
--   | .ifte v c₁ c₂, ρ, h =>
--     let v := v.trans.rename ρ
--     let c₁ := Cmp.trans c₁ ρ h
--     let c₂ := Cmp.trans c₂ ρ h
--     have : ⟦ValTy.bool⟧v{{ρ'}}ᵣₜ = SystemF.Ty.bool := by {
--       simp [ValTy.trans, SystemF.Ty.renameₜ]
--     }
--     .ifte (this ▸ v) c₁ c₂
--   | .handle_with (C:=C) c v, ρ, h => by
--     rename SystemF.Conₜ => Φ
--     let v := v.trans
--     let v := SystemF.Term.rename v ρ
--     simp only [ValTy.trans] at v
--     apply SystemF.Term.app _ h
--     simp only [HandlerTy.trans]
--     rw [ValTy.trans, HandlerTy.trans_ren_lemma] at v
--     let cv := Cmp.trans c ρ v
--     rw [CmpTy.trans] at cv
--     let cvB := SystemF.Term.appₜ cv B
--     simp [SystemF.Ty.substₜ₀, SystemF.Ty.renameₜ, SystemF.Ty.substₜ, HandlerTy.trans, SystemF.Renameₜ.extend, SystemF.Substₜ.cons] at cvB
--     simp [Signature.trans_ren_lemma, Signature.trans_sub_lemma] at cvB
--     simp [SystemF.Ty.renameₜ, SystemF.Ty.substₜ, SystemF.Renameₜ.extend, SystemF.Substₜ.cons] at cvB
--     rw [←SystemF.Renameₜ.ren_comp, SystemF.Renameₜ.nil_eta (ρ'.extend.comp _), SystemF.nil_ren_sub] at cvB
--     exact cvB
-- termination_by c => sizeOf c
-- def OpClauses.trans : OpClauses Γ E C → _ / ⟦Γ⟧v ⊢ Signature.trans E ⟦C⟧c
--   | .nil => (Signature.trans.eq_def _ _) ▸ .pair .unit .unit
--   | .cons (A:=A') (B:=B) (E:=E') S c =>
--     have : sizeOf c + 1 < 1 + sizeOf Γ + sizeOf E' + sizeOf C + sizeOf A' + sizeOf B + sizeOf S + sizeOf c := by {
--       simp_arith
--       show 0 < _
--       apply Nat.lt_add_right
--       apply Nat.lt_add_left
--       apply ValTy.sizeOf_lemma
--     }
--     have this : Signature.trans _ ⟦C⟧c = .pair _ _ := by {
--       simp [Signature.trans, OpTy.trans]
--       congr
--       rw [←SystemF.Renameₜ.nil_eta SystemF.Renameₜ.id, SystemF.Renameₜ.id_rfl]
--       rw [←SystemF.Renameₜ.nil_eta SystemF.Renameₜ.id, SystemF.Renameₜ.id_rfl]
--       simp [ValTy.trans]
--       rfl
--     }
--     this ▸ .pair (.lam _ (.lam _ (Cmp.trans' c))) S.trans
-- termination_by S => sizeOf S
-- end

def ret_cl : Φ / Δ ⊢ → Φ / Δ ⊢
  | t =>  .p₁ t
def Signature.op_cl : {E : Signature} → Φ / Δ ⊢ → E ∋ ⟨A', B'⟩ → Φ / Δ ⊢
  | _, t, .zero => .p₁ t
  | _, t, .succ i => op_cl (.p₂ t) i

def op_cl : {E : Signature} → Φ / Δ ⊢ → E ∋ ⟨A', B'⟩ → Φ / Δ ⊢
  | _, t, i => Signature.op_cl (.p₂ t) i

mutual

def Val.trans : Γ ⊢v A → ∅ / ⟦Γ⟧v ⊢
  | .var i => .var <| Member.trans i
  | .true => .true
  | .false => .false
  | .lam (C:=C) A e =>
    have : sizeOf e + 1 < 1 + sizeOf Γ + sizeOf C + sizeOf A + sizeOf e := by {
      simp_arith
      apply Nat.lt_add_left
      exact ValTy.sizeOf_lemma A
    }
    .lam ⟦A⟧v e.trans
  | .handler (A:=A) (E:=E) ret op (C:=C) =>
    have : sizeOf ret + 1 < 1 + sizeOf Γ + sizeOf A + sizeOf C + sizeOf E + sizeOf ret + sizeOf op := by {
        simp_arith
        show 0 < _
        apply Nat.lt_add_right
        apply Nat.lt_add_right
        apply Nat.lt_add_right
        apply Nat.lt_add_left
        apply ValTy.sizeOf_lemma
      }
    .pair (.lam _ ret.trans) (OpClauses.trans op)
termination_by v => sizeOf v

def Cmp.trans : Γ ⊢c C → ∅ / ⟦Γ⟧v ⊢
  | .app (A:=A') v₁ v₂ => .app v₁.trans v₂.trans
  | .handle_with (C:=(A, E)) c v => c.colon (𝟙ᵣ_) ⟦C⟧c v.trans
  | c =>
    let ρ' : SystemF.Renameₜ (.nil;*) .nil := .succ
    let ρ : SystemF.Rename _ _ ((⟦Γ⟧v).wk; ⟦C⟧⇛(SystemF.Ty.var .zero)) ⟦Γ⟧v ρ' := by  {
        intro T i
        apply SystemF.Con.Member.succ
        apply SystemF.Con.Member.renameₜ
        assumption
    }
    .lamₜ (.lam (⟦C⟧⇛(.var .zero)) (c.colon ρ (.var .zero) (.var .zero)))
termination_by c => sizeOf c + 1

def Cmp.colon : Γ ⊢c C → (ρ : SystemF.Rename Ψ _ Δ ⟦Γ⟧v ρₜ) → (B : SystemF.Ty Ψ) → Ψ / Δ ⊢ → Ψ / Δ ⊢
  | .return (E:=E) v, ρ, B, h => .app (ret_cl h) (v.trans{{ρ}}ᵣ)
  | .op i (A':=A') (B':=B') v c, ρ, B, h =>
    let ρ'' : SystemF.Rename _ _ (Δ; ⟦B'⟧v{{ρₜ}}ᵣₜ) ⟦Γ; B'⟧v ρₜ := by {
      intro K i
      cases i with
      | zero => constructor
      | succ i =>
        constructor
        exact ρ i
    }
    .app (.app (op_cl h i) v.trans{{ρ}}ᵣ) (.lam _ (c.colon ρ'' B h.wk))
  | .app (A:=A') v₁ v₂, ρ, B, h => .app (.appₜ (.app (v₁.trans{{ρ}}ᵣ) (v₂.trans{{ρ}}ᵣ)) B) h
  | .ifte v c₁ c₂, ρ, B, h => .ifte (v.trans.rename ρ) (c₁.colon ρ B h) (c₂.colon ρ B h)
  | .handle_with (C:=C) (C':=C') c v, ρ, B, h => .app (.appₜ (c.colon ρ (⟦C'⟧c{{ρₜ}}ᵣₜ) (v.trans{{ρ}}ᵣ)) B) h
termination_by c => sizeOf c

def OpClauses.trans : OpClauses Γ E C → _ / ⟦Γ⟧v ⊢
  | .nil => .pair .unit .unit
  | .cons (A:=A') (B:=B) (E:=E') S c =>
    have : sizeOf c + 1 < 1 + sizeOf Γ + sizeOf E' + sizeOf C + sizeOf A' + sizeOf B + sizeOf S + sizeOf c := by {
      simp_arith
      show 0 < _
      apply Nat.lt_add_right
      apply Nat.lt_add_left
      apply ValTy.sizeOf_lemma
    }
    .pair (.lam _ (.lam _ (Cmp.trans c))) S.trans
termination_by S => sizeOf S

end

mutual

def Val.preserve_type : (t : Γ ⊢v A) → SystemF.Extrinsic.Typing t.trans ⟦A⟧v
  | .var i => by
    simp [Val.trans]
    constructor
  | .true => by
    simp [Val.trans, ValTy.trans]
    constructor
  | .false => by
    simp [Val.trans, ValTy.trans]
    constructor
  | .lam B e (C:=C) => by
    simp [Val.trans, ValTy.trans]
    constructor
    apply Cmp.preserve_type
  | .handler ret op (A:=A) (E:=E) (C:=C) => by
    simp [Val.trans, ValTy.trans, HandlerTy.trans]
    constructor
    have : ⟦A⟧v{{SystemF.Renameₜ.nil}}ᵣₜ = ⟦A⟧v := by {
      rw [←SystemF.Renameₜ.nil_eta (SystemF.Renameₜ.id), SystemF.Renameₜ.id_rfl]
    }
    rw [this]
    constructor
    apply Cmp.preserve_type
    apply OpClauses.preserve_type
termination_by v => sizeOf v

def Cmp.preserve_type : (t : Γ ⊢c C) → SystemF.Extrinsic.Typing t.trans ⟦C⟧c
  | .return ret => by
    simp [Cmp.trans, CmpTy.trans]
    constructor
    constructor
    apply Cmp.colon_preserve_type
    constructor
  | .op i v c => sorry
  | .app v₁ v₂ => sorry
  | .ifte b t e => sorry
  | .handle_with c v => sorry
termination_by c => sizeOf c + 1
def Cmp.colon_preserve_type : (t : Γ ⊢c C) → SystemF.Extrinsic.Typing h ⟦C⟧⇛B →  SystemF.Extrinsic.Typing (t.colon ρ B h) B
  | .return ret, J => by
    rename_i Φ Δ ρₜ
    simp [Cmp.colon, ret_cl]
    simp [HandlerTy.trans] at J
    constructor
    constructor
    assumption
    rw [←SystemF.Renameₜ.nil_eta ρₜ]
    refine SystemF.Extrinsic.Typing.rename ?_ ρ
    apply Val.preserve_type
  | .op i v c (A':=A') (B':=B'), J => by
    rename_i Φ Δ ρₜ
    simp [Cmp.colon, op_cl]
    constructor
    constructor
  | .app v₁ v₂ (A:=A), J => by
    rename_i Φ Δ ρₜ
    let ⟨A', E⟩ := C
    simp [Cmp.colon]
    simp [HandlerTy.trans] at J
    constructor
    have J₁ := Val.preserve_type v₁
    have J₂ := Val.preserve_type v₂
    have J₁' : SystemF.Extrinsic.Typing v₁.trans{{ρ}}ᵣ _ := by {
      apply SystemF.Extrinsic.Typing.rename
      assumption
    }
    have J₂' : SystemF.Extrinsic.Typing v₂.trans{{ρ}}ᵣ _ := by {
      apply SystemF.Extrinsic.Typing.rename
      assumption
    }
    simp [ValTy.trans, SystemF.Ty.renameₜ] at J₁ J₁'
    have J' : SystemF.Extrinsic.Typing (.app v₁.trans{{ρ}}ᵣ v₂.trans{{ρ}}ᵣ) _ := by {
      constructor
      assumption
      assumption
    }
    simp [CmpTy.trans, SystemF.Ty.renameₜ] at J'
    have J'' : SystemF.Extrinsic.Typing (.appₜ (.app v₁.trans{{ρ}}ᵣ v₂.trans{{ρ}}ᵣ) B) _ := by {
      constructor
      assumption
    }
    simp [SystemF.Ty.substₜ₀, SystemF.Ty.substₜ, SystemF.Substₜ.cons, SystemF.Renameₜ.extend] at J''
    assumption
    simp [HandlerTy.trans]
    simp [SystemF.Ty.renameₜ, SystemF.Ty.substₜ]
    rw [Signature.trans_ren_lemma, Signature.trans_sub_lemma]
    simp [SystemF.Ty.renameₜ, SystemF.Renameₜ.extend, SystemF.Ty.substₜ, SystemF.Substₜ.cons]
    rw [←SystemF.Substₜ.subs_compₛᵣ, SystemF.nil_ren_sub ⟦A'⟧v]
    assumption
  | .ifte b t e, J => by
    rename_i Φ Δ ρₜ
    simp [Cmp.colon]
    constructor
    have : SystemF.Ty.bool = SystemF.Ty.bool{{ρₜ}}ᵣₜ := by simp [SystemF.Ty.renameₜ]
    rw [this]
    refine SystemF.Extrinsic.Typing.rename ?_ ρ
    have : SystemF.Ty.bool = ⟦.bool⟧v := by simp [ValTy.trans]
    rw [this]
    apply Val.preserve_type
    apply Cmp.colon_preserve_type
    assumption
    apply Cmp.colon_preserve_type
    assumption
  | .handle_with c v, J => sorry
termination_by c => sizeOf c

def OpClauses.preserve_type : (op : OpClauses Γ E C) → SystemF.Extrinsic.Typing op.trans (Signature.trans E ⟦C⟧c) := sorry

end
def Relation.ReflTransGen.ofEq : a = b → Relation.ReflTransGen f a b := by
  intro h
  rw [h]
def Sub.trans : Sub Δ Γ → SystemF.Extrinsic.Subst ∅ ∅ ⟦Δ⟧v ⟦Γ⟧v := sorry

def trans_sub_comm : {t : Γ ⊢v C} → {σ : Sub Δ Γ} → t{{σ}}ₛ.trans = t.trans.subst σ.trans 𝟙ᵣₜ := by
  intro t σ
  sorry

def trans_colon_lemma : {t : (Γ; A) ⊢c C} → {v : Γ ⊢v A} → {ρ : SystemF.Rename Ψ _ Δ ⟦Γ⟧v ρ'}
  → SystemF.Extrinsic.MultiStep0 (.app (.appₜ t.trans{{ρ.extend}}ᵣ[[v.trans{{ρ}}ᵣ]]ₛ B) h) (t[[v]]ₛ.colon ρ B h) := by
  intro t v ρ
  cases t with
  | app f x =>
    simp [Cmp.trans, SystemF.Extrinsic.Term.rename, SystemF.Extrinsic.Term.subst₀, SystemF.Extrinsic.Term.subst]
    simp [Cmp.subs₀, Cmp.subst, Cmp.colon]
    apply SystemF.Extrinsic.MultiStep0.ξ_app₁
    apply SystemF.Extrinsic.MultiStep0.ξ_appₜ
    rw [trans_sub_comm, trans_sub_comm]
    apply Relation.ReflTransGen.ofEq
    congr
    sorry
    sorry
  | _ => sorry


def trans.simulation_lemma₁ : {i : E ∋ (A', B')} → {v : Γ' ⊢v A'} → {c : (Γ'; B') ⊢c (A'', E)} → {val : (Γ'; A'') ⊢c C} → {op : OpClauses Γ' E C} → {ρ : SystemF.Rename Φ SystemF.Conₜ.nil Δ ⟦Γ'⟧v ρₜ}
  → (handle Cmp.op i v c with Val.handler val op).colon ρ B h ⟶ₛ+
  (op.get i)[[Val.lam B' handle c{{((𝟙ᵣΓ').wk A')↑}}ᵣwith(Val.handler val op){{((𝟙ᵣΓ').wk A').wk B'}}ᵣ]]ₛ[[v]]ₛ.colon ρ B h := by
{
  intro i v c val op ρ
  cases i with
  | zero =>
    simp [Cmp.colon, op_cl, Signature.op_cl, Val.trans]
    cases op with
    | cons S op =>
      simp [OpClauses.get, OpClauses.trans, SystemF.Extrinsic.Term.rename, SystemF.Extrinsic.Term.wk]
      apply Relation.TransGen.head'
      constructor
      constructor
      constructor
      constructor
      constructor
      constructor
      apply Relation.ReflTransGen.head
      constructor
      constructor
      constructor
      constructor
      constructor
      apply Relation.ReflTransGen.head
      constructor
      constructor
      constructor
      constructor
      apply Relation.ReflTransGen.head
      constructor
      constructor
      constructor
      constructor
      constructor
  | succ i => sorry
}
def trans.simulation {t t' : Γ ⊢c A} : SmallStep t t' → (t.colon ρ B h ⟶ₛ+ t'.colon ρ B h) := by
  intro htt'
  induction htt' generalizing B h with
  | β_ifte_true =>
    simp [Cmp.colon, Val.trans]
    constructor
    constructor
  | β_ifte_false =>
    simp [Cmp.colon, Val.trans]
    constructor
    constructor
  | β_app =>
    simp [Cmp.colon, Val.trans, SystemF.Extrinsic.Term.rename]
    apply Relation.TransGen.head'
    apply SystemF.Extrinsic.SmallStep.ξ_app₁
    apply SystemF.Extrinsic.SmallStep.ξ_appₜ
    apply SystemF.Extrinsic.SmallStep.β_app
    apply trans_colon_lemma
  | ξ_handle hcc' =>
    rename_i Φ Δ ρₜ Γ' C A' E c c' ret op ih
    simp [Cmp.colon]
    refine SystemF.Extrinsic.MultiStep.ξ_app₁ ?ξ_handle.a
    exact SystemF.Extrinsic.MultiStep.ξ_appₜ ih
  | β_handle_return =>
    simp [Cmp.colon, ret_cl, Val.trans, SystemF.Extrinsic.Term.rename]
    apply Relation.TransGen.head
    constructor
    constructor
    constructor
    constructor
    apply Relation.TransGen.head'
    constructor
    constructor
    constructor
    apply trans_colon_lemma
  | β_handle_op =>
    rename_i Φ Δ ρₜ E Γ' A' B' A'' C i v c val op
    simp [HAdd'.hAdd]
    simp [Cmp.colon, op_cl, Val.trans, SystemF.Extrinsic.Term.rename]
    cases i with
    | zero =>
      simp [Signature.op_cl]
      apply Relation.TransGen.head'
      constructor
      constructor
      constructor
      constructor
      constructor
      constructor
      constructor
      constructor
      cases op with
      | cons E op =>
        simp [OpClauses.trans, SystemF.Extrinsic.Term.rename]

    | succ i => sorry

end Eff
