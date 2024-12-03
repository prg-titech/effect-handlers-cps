
import EffectCompiler.Eff.Syntax2
-- import EffectCompiler.Eff.Subst

import EffectCompiler.SystemF.Basic


namespace Eff

mutual
def ValTy.trans: ValTy → SystemF.Ty .nil
  | .bool => .bool
  | .fn A B!E => A.trans ⇒ CmpTy.trans B!E
  | .hn (A!E, D) =>
    have h : sizeOf A!E.val + sizeOf A!E.eff < 1 + (1 + sizeOf A!E + sizeOf D) := sorry
    HandlerTy.trans A!E (CmpTy.trans D)
termination_by v => sizeOf v

def CmpTy.trans: CmpTy → SystemF.Ty .nil :=
  fun ⟨A, E⟩ =>
    have : sizeOf A + sizeOf E < 1 + sizeOf A + sizeOf E := sorry
    .pi ((HandlerTy.trans ⟨A, E⟩ (.var .zero)) ⇒ (.var .zero))
termination_by c => sizeOf c
-- decreasing_by {
--   simp_wf
--   rename_i C
--   cases C
--   rename_i A E
--   simp_arith
-- }

def HandlerTy.trans: CmpTy → SystemF.Ty Φ → SystemF.Ty Φ :=
  fun ⟨A, E⟩ B =>
  have : sizeOf A < sizeOf A + sizeOf E := by {
    simp_arith
    -- exact Signature.sizeOf_lemma _
    sorry
  }
  have : sizeOf E < sizeOf A + sizeOf E := by {
    simp_arith
    exact ValTy.sizeOf_lemma _
  }
  have : 0 < sizeOf E := sorry
  let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
  .pair (.fn A.trans{{ρ'}}ᵣₜ B) (Signature.trans E B)
termination_by c => sizeOf c.val + sizeOf c.eff

def Signature.trans : (S : Signature) → SystemF.Ty Φ → SystemF.Ty Φ
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

def ValTy.trans': ValTy → SystemF.Ty .nil
  | .bool => .bool
  | .fn A C => .fn A.trans' .unit
  | .hn (⟨A, E⟩, D) => .unit

example : 1 + 1 = 2 := rfl
example : ValTy.bool.trans' = SystemF.Ty.bool := rfl
example : ValTy.bool.trans = SystemF.Ty.bool := rfl

variable (Φ : SystemF.Conₜ)

mutual
inductive Even where
  | zero : Even
  | succ : Odd → Even
inductive Odd where
  | succ : Even → Odd
end

mutual
def Even.toNat : (n : Even) → Nat
  | .zero => 0
  | .succ i => i.toNat + 1
def Odd.toNat : (n : Odd) → Nat
  | .succ i => i.toNat + 1
end

example : (Odd.succ (.zero)).toNat = 1 := rfl
example : (Even.succ (Odd.succ (.zero))).toNat = 2 := rfl
#eval (Even.succ (Odd.succ (.zero))).toNat


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

def ret_cl : Φ / Δ ⊢ ⟦C⟧⇛B → Φ / Δ ⊢ SystemF.Ty.fn ⟦C.val⟧v{{ρ'}}ᵣₜ B
  | t => by
    simp [HandlerTy.trans] at t
    rw [SystemF.Renameₜ.nil_eta ρ']
    exact .p₁ t
def Signature.op_cl : Φ / Δ ⊢ Signature.trans E B → E ∋ ⟨A', B'⟩ → Φ / Δ ⊢ .fn ⟦A'⟧v{{ρ'}}ᵣₜ (.fn (.fn ⟦B'⟧v{{ρ'}}ᵣₜ B) B)
  | t, .zero => by
    simp [Signature.trans, OpTy.trans] at t
    rw [SystemF.Renameₜ.nil_eta ρ']
    exact .p₁ t
  | t, .succ i => by
    simp [Signature.trans] at t
    apply op_cl _ i
    exact .p₂ t

def op_cl : Φ / Δ ⊢ ⟦C⟧⇛B → C.eff ∋ ⟨A', B'⟩ → Φ / Δ ⊢ .fn ⟦A'⟧v{{ρ'}}ᵣₜ (.fn (.fn ⟦B'⟧v{{ρ'}}ᵣₜ B) B)
  | t, i => by
    simp [HandlerTy.trans] at t
    rw [SystemF.Renameₜ.nil_eta ρ']
    apply Signature.op_cl (.p₂ t) i

def Member.trans : Member Γ A →  ∅ / ⟦Γ⟧v ∋ ⟦A⟧v
  | .zero => .zero
  | .succ i => .succ <| Member.trans i

mutual
def Val.trans : Γ ⊢v A → ∅ / ⟦Γ⟧v ⊢ ⟦A⟧v
  | .var i => .var <| Member.trans i
  | .false => (ValTy.trans.eq_def _) ▸ .false
  | .true => (ValTy.trans.eq_def _) ▸ .true
  | .lam A e (C:=C) =>
    let h : (∅ / ⟦Γ⟧v ⊢ (⟦A⟧v ⇒ ⟦C⟧c)) = (∅ / ⟦Γ⟧v ⊢ ⟦.fn A C⟧v) := by
      simp [ValTy.trans]
    have : sizeOf e + 1 < 1 + sizeOf Γ + sizeOf C + sizeOf A + sizeOf e := by {
      simp_arith
      show 0 < _
      apply Nat.lt_add_left
      apply ValTy.sizeOf_lemma
    }
    h ▸ .lam ⟦A⟧v (Cmp.trans' e)
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
    have this : ⟦(A, E) ⇛ C⟧v = .pair _ _ := by {
      simp [ValTy.trans, HandlerTy.trans];
      rw [←SystemF.Renameₜ.nil_eta SystemF.Renameₜ.id, SystemF.Renameₜ.id_rfl]
      rfl
    }
    this ▸ .pair
    (
      .lam ⟦A⟧v (Cmp.trans' ret)
    )
    (OpClauses.trans op)
termination_by v => sizeOf v
def Cmp.trans': Γ ⊢c C → ∅ / ⟦Γ⟧v ⊢ ⟦C⟧c
  | .app (A:=A') v₁ v₂ =>
    let h : ⟦.fn A' C⟧v = (⟦A'⟧v ⇒ ⟦C⟧c) := by simp [ValTy.trans]
    let v₁' := h ▸ v₁.trans
    let v₂' := v₂.trans
    let x := SystemF.Term.app v₁' v₂'
    x
  | .handle_with (C:=(A, E)) c v => by
    let v' := v.trans
    simp only [ValTy.trans] at v'
    let ρ' : SystemF.Renameₜ .nil .nil := SystemF.Renameₜ.id
    let ρ : SystemF.Rename _ _ ⟦Γ⟧v ⟦Γ⟧v ρ' := SystemF.Rename.id _
    exact Cmp.trans c ρ v'
  | c =>
    let h : SystemF.Ty.pi (⟦C⟧⇛(SystemF.Ty.var .zero) ⇒ SystemF.Ty.var .zero) = ⟦C⟧c := by {
      simp [CmpTy.trans]
    }
    let ρ' : SystemF.Renameₜ (.nil;*) .nil := .succ
    let ρ : SystemF.Rename _ _ ((⟦Γ⟧v).wk; ⟦C⟧⇛(SystemF.Ty.var .zero)) ⟦Γ⟧v ρ' := by  {
        intro T i
        apply SystemF.Con.Member.succ
        apply SystemF.Con.Member.renameₜ
        assumption
    }
    h ▸ (.lamₜ (.lam (⟦C⟧⇛(.var .zero)) (Cmp.trans c ρ (.var .zero))))
termination_by c => sizeOf c + 1
def Cmp.trans: Γ ⊢c C → (ρ : SystemF.Rename _ _ Δ ⟦Γ⟧v ρ') → _ / Δ ⊢ (⟦C⟧⇛B) → _ / Δ ⊢ B
  | .return (E:=E) v, ρ, h => .app (ret_cl h) (v.trans.rename ρ)
  | .op i (A':=A') (B':=B') v c, ρ, h =>
    let op := op_cl h i (ρ':=ρ')
    let ρ'' : SystemF.Rename _ _ (Δ; ⟦B'⟧v{{ρ'}}ᵣₜ) ⟦Γ; B'⟧v ρ' := by {
      intro K i
      cases i with
      | zero => constructor
      | succ i =>
        constructor
        exact ρ i
    }
    -- TODO : replace it by ρ.lift?
    .app (.app op (SystemF.Term.rename v.trans ρ)) (.lam _ (Cmp.trans c (ρ'' : SystemF.Rename _ _ _ _ ρ') h.wk))
  | .app (A:=A') v₁ v₂, ρ, h => by
    let this : ⟦.fn A' C⟧v = (⟦A'⟧v ⇒ ⟦C⟧c) := by simp [ValTy.trans]
    let v₁ := this ▸ v₁.trans
    let v₁ := v₁.rename ρ
    let v₂ := v₂.trans
    let v₂ := v₂.rename ρ
    let x := SystemF.Term.app v₁ v₂
    simp [CmpTy.trans] at x
    let y := SystemF.Term.appₜ x B
    simp [SystemF.Ty.renameₜ, SystemF.Ty.substₜ₀, SystemF.Ty.substₜ, SystemF.Renameₜ.extend] at y
    simp [HandlerTy.trans, SystemF.Ty.renameₜ, SystemF.Renameₜ.extend, SystemF.Ty.substₜ] at y
    rw [Signature.trans_ren_lemma, Signature.trans_sub_lemma] at y
    simp [SystemF.Ty.renameₜ, SystemF.Renameₜ.extend, SystemF.Ty.substₜ] at y
    simp [SystemF.Substₜ.id, SystemF.Substₜ.cons] at y
    rw [←SystemF.Renameₜ.ren_comp, SystemF.Renameₜ.nil_eta (ρ'.extend.comp _), SystemF.nil_ren_sub] at y
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
    let v := v.trans.rename ρ
    let c₁ := Cmp.trans c₁ ρ h
    let c₂ := Cmp.trans c₂ ρ h
    have : ⟦ValTy.bool⟧v{{ρ'}}ᵣₜ = SystemF.Ty.bool := by {
      simp [ValTy.trans, SystemF.Ty.renameₜ]
    }
    .ifte (this ▸ v) c₁ c₂
  | .handle_with (C:=C) c v, ρ, h => by
    rename SystemF.Conₜ => Φ
    let v := v.trans
    let v := SystemF.Term.rename v ρ
    simp only [ValTy.trans] at v
    apply SystemF.Term.app _ h
    simp only [HandlerTy.trans]
    rw [ValTy.trans, HandlerTy.trans_ren_lemma] at v
    let cv := Cmp.trans c ρ v
    rw [CmpTy.trans] at cv
    let cvB := SystemF.Term.appₜ cv B
    simp [SystemF.Ty.substₜ₀, SystemF.Ty.renameₜ, SystemF.Ty.substₜ, HandlerTy.trans, SystemF.Renameₜ.extend, SystemF.Substₜ.cons] at cvB
    simp [Signature.trans_ren_lemma, Signature.trans_sub_lemma] at cvB
    simp [SystemF.Ty.renameₜ, SystemF.Ty.substₜ, SystemF.Renameₜ.extend, SystemF.Substₜ.cons] at cvB
    rw [←SystemF.Renameₜ.ren_comp, SystemF.Renameₜ.nil_eta (ρ'.extend.comp _), SystemF.nil_ren_sub] at cvB
    exact cvB
termination_by c => sizeOf c
def OpClauses.trans : OpClauses Γ E C → _ / ⟦Γ⟧v ⊢ Signature.trans E ⟦C⟧c
  | .nil => (Signature.trans.eq_def _ _) ▸ .pair .unit .unit
  | .cons (A:=A') (B:=B) (E:=E') S c =>
    have : sizeOf c + 1 < 1 + sizeOf Γ + sizeOf E' + sizeOf C + sizeOf A' + sizeOf B + sizeOf S + sizeOf c := by {
      simp_arith
      show 0 < _
      apply Nat.lt_add_right
      apply Nat.lt_add_left
      apply ValTy.sizeOf_lemma
    }
    have this : Signature.trans _ ⟦C⟧c = .pair _ _ := by {
      simp [Signature.trans, OpTy.trans]
      congr
      rw [←SystemF.Renameₜ.nil_eta SystemF.Renameₜ.id, SystemF.Renameₜ.id_rfl]
      rw [←SystemF.Renameₜ.nil_eta SystemF.Renameₜ.id, SystemF.Renameₜ.id_rfl]
      simp [ValTy.trans]
      rfl
    }
    this ▸ .pair (.lam _ (.lam _ (Cmp.trans' c))) S.trans
termination_by S => sizeOf S
end

end Eff
