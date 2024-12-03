
import EffectCompiler.Eff.Syntax
import EffectCompiler.Eff.Subst

import EffectCompiler.SystemFwithRecord.Basic

-- import EffectCompiler.Eff.SmallStep

import Lean.Elab.Tactic.LibrarySearch

namespace Eff

-- def ValTy.trans : ValTy → SystemF.Ty .nil
--   | .bool => .bool
--   | .fn A ⟨B, E⟩ => A.trans ⇒
--     let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
--     .pi ((.pair
--       (.fn A.trans{{ρ'}}ᵣₜ (.var .zero))
--       (
--         let f := fun i =>
--           have : sizeOf (E.get i) < sizeOf E := sorry
--           let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
--           .fn (E.get i).1.trans{{ρ'}}ᵣₜ <| .fn (.fn (E.get i).2.trans{{ρ'}}ᵣₜ (.var .zero)) (.var .zero)
--         .record f
--       )
--     ) ⇒ (.var .zero))
--   | .hn ((A, E), (B, E')) =>
--     let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
--     let ρ'' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
--     let f := fun i =>
--       have : sizeOf (E.get i) < sizeOf E := sorry
--       let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
--       SystemF.Ty.fn (E.get i).1.trans{{ρ'}}ᵣₜ <| .fn (.fn (E.get i).2.trans{{ρ'}}ᵣₜ B.trans) B.trans
--     let f' := fun i =>
--       have : sizeOf (E.get i) < sizeOf E := sorry
--       let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
--       SystemF.Ty.fn (E.get i).1.trans{{ρ'}}ᵣₜ <| .fn (.fn (E.get i).2.trans{{ρ'}}ᵣₜ (.var .zero)) (.var .zero)
--     .pair (.fn A.trans{{ρ'}}ᵣₜ (.pi ((.pair (.fn B.trans{{ρ''}}ᵣₜ (.var .zero)) (.record f')) ⇒ (.var .zero)))) (.record f)
--     -- HandlerTy.trans (A, E) (CmpTy.trans (B, E'))
-- decreasing_by
--   simp_arith
--   simp
--   apply Nat.lt_add_left
--   apply Nat.lt_add_left
--   trans
--   show _ < sizeOf (E.get i)
--   cases (E.get i)
--   simp_arith
--   assumption
--   simp
--   apply Nat.lt_add_left
--   apply Nat.lt_add_left
--   trans
--   show _ < sizeOf (E.get i)
--   cases (E.get i)
--   simp_arith
--   assumption
--   simp
--   apply Nat.lt_add_left
--   apply Nat.lt_add_right
--   apply Nat.lt_add_left
--   apply Nat.lt_add_left
--   trans
--   show _ < sizeOf (E.get i)
--   cases (E.get i)
--   simp_arith
--   assumption
--   simp
--   apply Nat.lt_add_left
--   apply Nat.lt_add_right
--   apply Nat.lt_add_left
--   apply Nat.lt_add_left
--   trans
--   show _ < sizeOf (E.get i)
--   cases (E.get i)
--   simp_arith
--   assumption
--   simp
--   apply Nat.lt_add_left
--   apply Nat.lt_add_right
--   apply Nat.lt_add_left
--   apply Nat.lt_add_left
--   trans
--   show _ < sizeOf (E.get i)
--   cases (E.get i)
--   simp_arith
--   assumption
--   simp
--   apply Nat.lt_add_left
--   apply Nat.lt_add_right
--   apply Nat.lt_add_left
--   apply Nat.lt_add_left
--   trans
--   show _ < sizeOf (E.get i)
--   cases (E.get i)
--   simp_arith
--   assumption
--   simp_arith
--   simp_arith

mutual
def ValTy.trans: ValTy → SystemF.Ty .nil
  | .bool => .bool
  | .fn A C => A.trans ⇒ CmpTy.trans C
  | .hn (C, D) =>
    HandlerTy.trans C (CmpTy.trans D)
termination_by v => sizeOf v
decreasing_by
  simp_arith
  simp_arith
  simp_arith
  cases C
  simp_arith

def CmpTy.trans: CmpTy → SystemF.Ty .nil :=
  fun (A, E) => .pi ((HandlerTy.trans (A, E) (.var .zero)) ⇒ (.var .zero))
termination_by c => sizeOf c
decreasing_by
  simp

def HandlerTy.trans: CmpTy → SystemF.Ty Φ → SystemF.Ty Φ :=
  fun (A, E) B =>
  let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
  .pair (.fn A.trans{{ρ'}}ᵣₜ B) (Signature.trans E B)
termination_by c => sizeOf c.1 + sizeOf c.2
decreasing_by
  simp_arith
  show 0 < _
  exact Signature.sizeOf_lemma _
  simp_arith
  show 0 < _
  exact ValTy.sizeOf_lemma _

def Signature.trans : (S : Context OpTy) → SystemF.Ty Φ → SystemF.Ty Φ :=
  fun S C =>
  let f := fun i =>
    have : sizeOf (S.get i) < sizeOf S := by sorry
    (S.get i).trans C
  .record f
termination_by S => sizeOf S

def OpTy.trans : OpTy → SystemF.Ty Φ → SystemF.Ty Φ
  | (A, B), C =>
    let ρ' : SystemF.Renameₜ _ .nil := SystemF.Renameₜ.nil
    .fn A.trans{{ρ'}}ᵣₜ <| .fn (.fn B.trans{{ρ'}}ᵣₜ C) C
termination_by op => sizeOf op
end

-- example : ValTy.bool.trans = SystemF.Ty.bool := rfl

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
def OpTy.trans_sub_lemma : (OpTy.trans op B){{σ'}}ₛₜ = OpTy.trans op B{{σ'}}ₛₜ := by
  rename_i Φ Ψ
  cases op
  case mk A' B' =>
  simp [OpTy.trans, SystemF.Ty.substₜ]
  constructor
  rw [SystemF.nil_ren_sub]
  rw [SystemF.nil_ren_sub]
def Signature.trans_ren_lemma : (Signature.trans S B){{ρ'}}ᵣₜ = Signature.trans S B{{ρ'}}ᵣₜ := by
  rename_i Φ Ψ
  cases S with
  | nil =>
    simp [Signature.trans, SystemF.Ty.renameₜ]
    funext i
    exact Fin.elim0 i
  | cons S B =>
    simp [Signature.trans, SystemF.Ty.renameₜ]
    funext i
    apply OpTy.trans_ren_lemma
def Signature.trans_sub_lemma : (Signature.trans S B){{σ'}}ₛₜ = Signature.trans S B{{σ'}}ₛₜ := by
  rename_i Φ Ψ
  cases S with
  | nil =>
    simp [Signature.trans, SystemF.Ty.substₜ]
    funext i
    exact Fin.elim0 i
  | cons S B =>
    simp [Signature.trans, SystemF.Ty.substₜ]
    funext i
    apply OpTy.trans_sub_lemma
def HandlerTy.trans_ren_lemma : (HandlerTy.trans (A, E) B){{ρ'}}ᵣₜ = HandlerTy.trans (A, E) B{{ρ'}}ᵣₜ := by
  simp [trans, SystemF.Ty.renameₜ]
  constructor
  rw [←SystemF.Renameₜ.ren_comp]
  generalize ρ'.comp SystemF.Renameₜ.nil = ρ''
  rw [SystemF.Renameₜ.nil_eta ρ'']
  apply Signature.trans_ren_lemma
def HandlerTy.trans_sub_lemma : (HandlerTy.trans (A, E) B){{σ'}}ₛₜ = HandlerTy.trans (A, E) B{{σ'}}ₛₜ := by
  simp [trans, SystemF.Ty.substₜ]
  constructor
  rw [SystemF.nil_ren_sub]
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
decreasing_by
  sorry
  sorry
  sorry

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
  | .return (E:=E) v, ρ, B, h => .app (.p₁ h) (v.trans{{ρ}}ᵣ)
  | .op i (A':=A') (B':=B') v c, ρ, B, h =>
    let ρ'' : SystemF.Rename _ _ (Δ; ⟦B'⟧v{{ρₜ}}ᵣₜ) ⟦Γ; B'⟧v ρₜ :=
      fun {K} i =>
      match i with
      | .zero => .zero
      | .succ i => .succ (ρ i)
    .app (.app (.proj (.p₂ h) i.asFin) v.trans{{ρ}}ᵣ) (.lam _ (c.colon ρ'' B h.wk))
  | .app (A:=A') v₁ v₂, ρ, B, h => .app (.appₜ (.app (v₁.trans{{ρ}}ᵣ) (v₂.trans{{ρ}}ᵣ)) B) h
  | .ifte v c₁ c₂, ρ, B, h => .ifte (v.trans.rename ρ) (c₁.colon ρ B h) (c₂.colon ρ B h)
  | .handle_with (C:=C) (C':=C') c v, ρ, B, h => .app (.appₜ (c.colon ρ (⟦C'⟧c{{ρₜ}}ᵣₜ) (v.trans{{ρ}}ᵣ)) B) h
termination_by c => sizeOf c

def OpClauses.trans_aux : (S : OpClauses Γ E C) → (Fin E.length) → _ / ⟦Γ⟧v ⊢
  | .nil => fun i => Fin.elim0 i
  | .cons (A:=A') (B:=B) (E:=E') S c =>
    fun i => i.cases (.lam _ (.lam _ c.trans)) (fun i => OpClauses.trans_aux S i)
termination_by S => sizeOf S
decreasing_by
  sorry
  sorry

def OpClauses.trans : OpClauses Γ E C → _ / ⟦Γ⟧v ⊢ :=
  fun S =>
  .record (OpClauses.trans_aux S)
termination_by S => sizeOf S + 1

end

def OpClauses.trans_aux_lemma : (S : OpClauses Γ E C) → (i : E ∋ (A, B)) → S.trans_aux i.asFin = (.lam _ (.lam _ (S.get i).trans)) := by
  intro S i
  cases S with
  | nil => contradiction
  | cons S c =>
  cases i with
  | zero =>
    simp [trans_aux, Member.asFin]
    rfl
  | succ i =>
    simp [trans_aux, Fin.cases, Fin.induction, Fin.induction.go]
    apply trans_aux_lemma

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
decreasing_by
  sorry
  sorry

def Cmp.preserve_type : (t : Γ ⊢c C) → SystemF.Extrinsic.Typing t.trans ⟦C⟧c
  | .return ret => by
    let (A, E) := C
    simp [Cmp.trans, CmpTy.trans]
    constructor
    constructor
    apply Cmp.colon_preserve_type
    constructor
  | .op i v c => by
    let (A, E) := C
    simp [Cmp.trans, CmpTy.trans]
    constructor
    constructor
    apply Cmp.colon_preserve_type
    constructor
  | .app v₁ v₂ => by
    simp [Cmp.trans]
    constructor
    have J := Val.preserve_type v₁
    simp [ValTy.trans] at J
    assumption
    apply Val.preserve_type v₂
  | .ifte b t e => by
    let (A, E) := C
    simp [Cmp.trans, CmpTy.trans]
    constructor
    constructor
    apply Cmp.colon_preserve_type
    constructor
  | .handle_with c v => by
    simp [Cmp.trans]
    apply Cmp.colon_preserve_type
    rw [←ValTy.trans]
    apply Val.preserve_type
termination_by c => sizeOf c + 1
decreasing_by
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry

def Cmp.colon_preserve_type : (t : Γ ⊢c C) → SystemF.Extrinsic.Typing h ⟦C⟧⇛B →  SystemF.Extrinsic.Typing (t.colon ρ B h) B
  | .return ret, J => by
    rename_i Φ Δ ρₜ
    let (A, E) := C
    simp [Cmp.colon]
    simp [HandlerTy.trans] at J
    constructor
    constructor
    assumption
    rw [←SystemF.Renameₜ.nil_eta ρₜ]
    refine SystemF.Extrinsic.Typing.rename ?_ ρ
    apply Val.preserve_type
  | .op i v c (A':=A') (B':=B'), J => by
    rename_i Φ Δ ρₜ
    let (A, E) := C
    simp [Cmp.colon]
    constructor
    constructor
    simp [HandlerTy.trans, Signature.trans] at J
    have J' := SystemF.Extrinsic.Typing.p₂ J
    have J'' := SystemF.Extrinsic.Typing.proj J' (i:=i.asFin)
    rw [Context.get_eq _ _] at J''
    simp [OpTy.trans] at J''
    assumption
    rw [←SystemF.Renameₜ.nil_eta ρₜ]
    refine SystemF.Extrinsic.Typing.rename ?_ ρ
    apply Val.preserve_type
    rw [←SystemF.Renameₜ.nil_eta ρₜ]
    constructor
    apply Cmp.colon_preserve_type
    sorry
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
  | .handle_with c v, J => by
    let (A, E) := C
    simp [Cmp.colon]
    constructor
    rename_i ρₜ C'
    have J := @Cmp.colon_preserve_type _ _ _ _ (v.trans{{ρ}}ᵣ) ⟦(A, E)⟧c{{ρₜ}}ᵣₜ ρₜ ρ c (by {
      rw [←HandlerTy.trans_ren_lemma]
      apply SystemF.Extrinsic.Typing.rename
      rw [←ValTy.trans]
      apply Val.preserve_type v
    })
    simp [CmpTy.trans, SystemF.Extrinsic.Term.renameₜ] at J ⊢
    have J' := SystemF.Extrinsic.Typing.appₜ J (B:=B)
    assumption
    rw [HandlerTy.trans_ren_lemma]
    simp [SystemF.Ty.renameₜ, SystemF.Renameₜ.extend]
    rw [HandlerTy.trans_sub_lemma]
    simp [SystemF.Ty.substₜ, SystemF.Substₜ.cons]
    assumption
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
  simp [Cmp.colon, Val.trans]
  simp [OpClauses.trans, SystemF.Extrinsic.Term.rename]
  apply Relation.TransGen.head'
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.ξ_appₜ
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.ξ_proj
  apply SystemF.Extrinsic.SmallStep.β_p₂
  apply Relation.ReflTransGen.head
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.ξ_appₜ
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.β_proj
  apply Relation.ReflTransGen.head
  rw [OpClauses.trans_aux_lemma]
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.ξ_appₜ
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.β_app
  apply Relation.ReflTransGen.head
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.ξ_appₜ
  apply SystemF.Extrinsic.SmallStep.β_app
  apply Relation.ReflTransGen.head
  apply SystemF.Extrinsic.SmallStep.ξ_app₁
  apply SystemF.Extrinsic.SmallStep.ξ_appₜ
  apply SystemF.Extrinsic.SmallStep.β_appₜ
  -- cases E with
  -- | nil => contradiction
  -- | cons E a =>
  -- cases op with
  -- | cons S op =>
  -- simp [Cmp.colon, Val.trans]
  simp [OpClauses.trans_aux]
  -- cases i with
  -- | zero =>
  --   simp [Cmp.colon, Val.trans]
  --   cases op with
  --   | cons S op =>
  --     simp [OpClauses.get, OpClauses.trans, OpClauses.trans_aux, SystemF.Extrinsic.Term.rename, SystemF.Extrinsic.Term.wk]
  --     apply Relation.TransGen.head'
  --     constructor
  --     constructor
  --     constructor
  --     constructor
  --     constructor
  --     constructor
  --     apply Relation.ReflTransGen.head
  --     constructor
  --     constructor
  --     constructor
  --     constructor
  --     constructor
  --     apply Relation.ReflTransGen.head
  --     constructor
  --     constructor
  --     constructor
  --     constructor
  --     apply Relation.ReflTransGen.head
  --     constructor
  --     constructor
  --     constructor
  --     constructor
  --     constructor
  -- | succ i => sorry
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
