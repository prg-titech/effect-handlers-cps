
import EffHps.Eff.Syntax
-- import EffHps.Eff.Subst

import EffHps.SystemF.Basic

-- import EffHps.Eff.SmallStep

import Lean.Elab.Tactic.LibrarySearch

namespace Eff

variable {Varₜ : Type} {Var : SystemF.ty Varₜ → Type}
mutual
def ValTy.trans: ValTy → SystemF.ty Varₜ
  | .bool => .bool
  | .fn A C => .fn A.trans (C.trans)
  | .hn C D =>
    HandlerTy.trans C (D.trans)
termination_by v => sizeOf v
decreasing_by
  simp_arith
  simp_arith
  simp_arith
  cases C
  simp_arith

def CmpTy.trans: CmpTy → SystemF.ty Varₜ :=
  fun ⟨A, E⟩ => .pi fun X => ((HandlerTy.trans ⟨A, E⟩ (SystemF.ty.fn (.var X) (.var X))))
termination_by C => sizeOf C
decreasing_by
  simp

def HandlerTy.trans: CmpTy → SystemF.ty Varₜ → SystemF.ty Varₜ :=
  fun ⟨A, E⟩ B =>
  .pair (.fn A.trans B) (E.trans B)
termination_by C => sizeOf C.1 + sizeOf C.2
decreasing_by
  simp_arith
  show 0 < _
  apply Signature.zero_lt_size
  simp_arith
  apply ValTy.sizeOf_lemma

def Signature.trans : (S : Signature) → SystemF.ty Varₜ → SystemF.ty Varₜ :=
  fun S C =>
  let f := fun i =>
    (S.get i).trans C
  .record f
termination_by S => sizeOf S
decreasing_by
  apply Signature.sizeof_lemma

def OpTy.trans : OpTy → SystemF.ty Varₜ → SystemF.ty Varₜ
  | opty, C =>
    .fn opty.1.trans <| .fn (.fn opty.2.trans C) C
termination_by op => sizeOf op
decreasing_by
  cases opty
  simp_arith
  cases opty
  simp_arith
end

example : ValTy.bool.trans (Varₜ:=Varₜ) = SystemF.ty.bool := rfl

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
def HandlerTy.trans_ren_lemma : (HandlerTy.trans C B){{ρ'}}ᵣₜ = HandlerTy.trans C B{{ρ'}}ᵣₜ := by
  cases C
  simp [trans, SystemF.Ty.renameₜ]
  constructor
  rw [←SystemF.Renameₜ.ren_comp]
  generalize ρ'.comp SystemF.Renameₜ.nil = ρ''
  rw [SystemF.Renameₜ.nil_eta ρ'']
  apply Signature.trans_ren_lemma
def HandlerTy.trans_sub_lemma : (HandlerTy.trans C B){{σ'}}ₛₜ = HandlerTy.trans C B{{σ'}}ₛₜ := by
  cases C
  simp [trans, SystemF.Ty.substₜ]
  constructor
  rw [SystemF.nil_ren_sub]
  apply Signature.trans_sub_lemma
@[simp]
def Con.trans: Con → SystemF.Con ∅
  | .nil => .nil
  | .cons Γ A => .cons (trans Γ) A.trans
notation: max "⟦" t "⟧v" => ValTy.trans t
notation: max "⟦" t "⟧v" => Con.trans t
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

-- def Member.trans : Γ ∋ A → SystemF.Con.Member ∅ ⟦Γ⟧v ⟦A⟧v
--   | .zero => .zero
--   | .succ i => .succ <| Member.trans i

-- def Member.trans : Γ ∋ A → SystemF.rep (ValTy.trans A)
--   | .zero => sorry
--   | .succ i => sorry

mutual
def Val.trans : Val (Var ∘ (⟦·⟧v)) A → SystemF.Term Var ⟦A⟧v
  | .var x => .var x
  | .true => .true
  | .false => .false
  | .lam (C:=C) A f => .lam _ _
  | .handler ret op => _

end
mutual

def Val.trans : ⊢[Var]v A → SystemF.Term Var
  | .var i => .var <| Member.trans i
  | .true => .true
  | .false => .false
  | .lam (C:=C) A e => .lam ⟦A⟧v e.trans
  | .handler (A:=A) (E:=E) ret op (C:=C) => .pair (.lam _ ret.trans) (OpClauses.trans op)
termination_by v => sizeOf v
decreasing_by
  simp_arith
  show 0 < _
  apply Nat.lt_add_left
  apply ValTy.sizeOf_lemma
  simp_arith
  show 0 < _
  apply Nat.lt_add_right
  apply Nat.lt_add_left
  apply Signature.zero_lt_size
  simp_arith
  show 0 < _
  apply Nat.lt_add_right
  apply Nat.lt_add_left
  apply Signature.zero_lt_size

def Cmp.trans : Γ ⊢c C → ∅ / ⟦Γ⟧v ⊢
  | .app (A:=A') v₁ v₂ => .app v₁.trans v₂.trans
  | .handle_with c v => c.colon (𝟙ᵣ_) ⟦C⟧c v.trans
  | c =>
    let ρₜ : SystemF.Renameₜ (.nil;*) .nil := .succ
    let ρ : SystemF.Rename _ _ ((⟦Γ⟧v).wk; ⟦C⟧⇛(SystemF.Ty.var .zero)) ⟦Γ⟧v ρₜ :=
      fun _ i => .succ i{{ρₜ}}ᵣₜ
    .lamₜ (.lam (⟦C⟧⇛(.var .zero)) (c.colon ρ (.var .zero) (.var .zero)))
termination_by c => sizeOf c + 1

def Cmp.colon : Γ ⊢c C → (ρ : SystemF.Rename Ψ _ Δ ⟦Γ⟧v ρₜ) → (B : SystemF.Ty Ψ) → Ψ / Δ ⊢ → Ψ / Δ ⊢
  | .return (E:=E) v, ρ, B, h => .app (.p₁ h) (v.trans{{ρ}}ᵣ)
  | .op i (A':=A') (B':=B') v c, ρ, B, h =>
    .app (.app (.proj (.p₂ h) i.asFin) v.trans{{ρ}}ᵣ) (.lam _ (c.colon ρ.extend B h.wk))
  | .app (A:=A') v₁ v₂, ρ, B, h => .app (.appₜ (.app (v₁.trans{{ρ}}ᵣ) (v₂.trans{{ρ}}ᵣ)) B) h
  | .ifte v c₁ c₂, ρ, B, h => .ifte (v.trans.rename ρ) (c₁.colon ρ B h) (c₂.colon ρ B h)
  | .handle_with (C:=C) (C':=C') c v, ρ, B, h => .app (.appₜ (c.colon ρ (⟦C'⟧c{{ρₜ}}ᵣₜ) (v.trans{{ρ}}ᵣ)) B) h
termination_by c => sizeOf c

-- def OpClauses.trans_aux : (S : OpClauses Γ E C) → (Fin E.length) → _ / ⟦Γ⟧v ⊢
--   | .nil => fun i => Fin.elim0 i
--   | .cons (A:=A') (B:=B) (E:=E') S c =>
--     fun i => i.cases (.lam _ (.lam _ c.trans)) (fun i => OpClauses.trans_aux S i)
-- termination_by S => sizeOf S
-- decreasing_by
--   simp_arith
--   show 0 < _
--   apply Nat.lt_add_right
--   apply Nat.lt_add_left
--   apply ValTy.sizeOf_lemma
--   simp_arith

def OpClauses.trans : OpClauses Γ E C → _ / ⟦Γ⟧v ⊢ :=
  fun S =>
  -- .record (OpClauses.trans_aux S)
  .record (
    fun i => (.lam _ (.lam _ (S.get i).trans))
  )
termination_by S => sizeOf S + 1
decreasing_by
  simp_arith
  apply OpClauses.sizeof_lemma

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
      rw [←SystemF.Renameₜ.nil_eta (𝟙ᵣₜ _)]
      apply SystemF.Renameₜ.id_rfl
    }
    rw [this]
    constructor
    apply Cmp.preserve_type
    apply OpClauses.preserve_type
termination_by v => sizeOf v
decreasing_by
  simp_arith
  show 0 < _
  apply Nat.lt_add_left
  apply ValTy.sizeOf_lemma
  simp_arith
  show 0 < _
  apply Nat.lt_add_right
  apply Nat.lt_add_left
  apply Signature.zero_lt_size
  simp_arith
  show 0 < _
  apply Nat.lt_add_right
  apply Nat.lt_add_left
  apply Signature.zero_lt_size

def Cmp.preserve_type : (t : Γ ⊢c C) → SystemF.Extrinsic.Typing t.trans ⟦C⟧c
  | .return ret => by
    let ⟨A, E⟩ := C
    simp [Cmp.trans, CmpTy.trans]
    constructor
    constructor
    apply Cmp.colon_preserve_type
    constructor
  | .op i v c => by
    let ⟨A, E⟩ := C
    simp [Cmp.trans, CmpTy.trans]
    constructor
    constructor
    apply Cmp.colon_preserve_type
    constructor
  | .app v₁ v₂ => by
    rename_i C' A
    simp [Cmp.trans]
    constructor
    show SystemF.Extrinsic.Typing v₁.trans (⟦A⟧v ⇒ ⟦C⟧c)
    have J := Val.preserve_type v₁
    simp [ValTy.trans] at J
    assumption
    apply Val.preserve_type v₂
  | .ifte b t e => by
    let ⟨A, E⟩ := C
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
  simp_arith
  simp_arith
  simp_arith
  simp_arith
  simp_arith
  simp_arith
  simp_arith

def Cmp.colon_preserve_type : (t : Γ ⊢c C) → SystemF.Extrinsic.Typing h ⟦C⟧⇛B →  SystemF.Extrinsic.Typing (t.colon ρ B h) B
  | .return ret, J => by
    rename_i Φ Δ ρₜ _ _
    let ⟨A, E⟩ := C
    simp [Cmp.colon]
    simp [HandlerTy.trans] at J
    constructor
    constructor
    assumption
    rw [←SystemF.Renameₜ.nil_eta ρₜ]
    refine SystemF.Extrinsic.Typing.rename ?_ ρ
    apply Val.preserve_type
  | .op i v c (A':=A') (B':=B'), J => by
    rename_i Φ Δ ρₜ _ _
    let ⟨A, E⟩ := C
    simp [Cmp.colon]
    constructor
    constructor
    simp [HandlerTy.trans, Signature.trans] at J
    have J' := SystemF.Extrinsic.Typing.p₂ J
    have J'' := SystemF.Extrinsic.Typing.proj J' (i:=i.asFin)
    rw [Signature.get_asfin] at J''
    simp [OpTy.trans] at J''
    assumption
    rw [←SystemF.Renameₜ.nil_eta ρₜ]
    refine SystemF.Extrinsic.Typing.rename ?_ ρ
    apply Val.preserve_type
    rw [←SystemF.Renameₜ.nil_eta ρₜ]
    constructor
    apply Cmp.colon_preserve_type
    apply SystemF.Extrinsic.Typing.wk
    assumption
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
    let ⟨A, E⟩ := C
    simp [Cmp.colon]
    constructor
    rename_i ρₜ C'
    have J := @Cmp.colon_preserve_type _ _ _ _ (v.trans{{ρ}}ᵣ) ⟦⟨A, E⟩⟧c{{ρₜ}}ᵣₜ ρₜ ρ c (by {
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

def OpClauses.preserve_type : (op : OpClauses Γ E C) → SystemF.Extrinsic.Typing op.trans (Signature.trans E ⟦C⟧c) := by {
  intro S
  simp [OpClauses.trans]
  simp [Signature.trans]
  constructor
  intro i
  simp [OpTy.trans]
  rw [←SystemF.Renameₜ.nil_eta (𝟙ᵣₜ _), SystemF.Renameₜ.id_rfl, SystemF.Renameₜ.id_rfl]
  constructor
  have : ⟦.fn (E.get i).2 C⟧v = .fn ⟦(E.get i).2⟧v ⟦C⟧c := by {
    simp [ValTy.trans]
  }
  rw [←this]
  constructor
  apply Cmp.preserve_type
}
termination_by op => sizeOf op + 1
decreasing_by
  simp_arith
  apply OpClauses.sizeof_lemma

end

def Rename.rest : Rename Δ (Γ; A) → Rename Δ Γ :=
  fun ρ =>
  fun _ i => ρ _ (.succ i)

def Rename.trans : Rename Δ Γ → SystemF.Rename ∅ ∅ ⟦Δ⟧v ⟦Γ⟧v (𝟙ᵣₜ_) :=
  fun ρ =>
  fun _ i =>
  match Γ with
  | .nil => by contradiction
  | .cons Γ A =>
  match i with
  | .zero =>
    SystemF.Renameₜ.id_rfl ▸ (Member.trans (ρ _ .zero))
    -- cast (congrArg _ SystemF.Renameₜ.id_rfl.symm) (Member.trans (ρ _ .zero))
  | .succ i => Rename.trans ρ.rest _ i

def Rename.trans_lemma : {ρ : Rename Δ Γ} → HEq (ρ.trans ⟦A⟧v (Member.trans i)) (Member.trans (ρ A i)) := by
  intro ρ
  cases i with
  | zero =>
    apply HEq.symm
    apply heq_of_cast_eq ?_ ?_
    exact congrArg _ SystemF.Renameₜ.id_rfl.symm
    simp [Rename.trans, Member.trans]
    rw [Eq.rec_eq_cast]
  | succ i =>
    simp [Rename.trans, Member.trans]
    apply HEq.trans
    apply Rename.trans_lemma
    simp [Rename.rest]

def Rename.comm_trans_extend : {ρ : Rename Δ Γ} → HEq (ρ.trans.extend (A:=⟦A⟧v)) (ρ.extend (A:=A)).trans := by
  intro ρ
  sorry

mutual

def Val.comm_trans_rename : {t : Γ ⊢v A} → t.trans{{ρ.trans}}ᵣ = t{{ρ}}ᵣ.trans := by
  intro t
  cases t with
  | var i =>
    simp [Val.trans, Val.rename, SystemF.Extrinsic.Term.rename]
    constructor
    apply SystemF.Renameₜ.id_rfl
    apply Rename.trans_lemma
  | false => simp [Val.trans, Val.rename, SystemF.Extrinsic.Term.rename]
  | true => simp [Val.trans, Val.rename, SystemF.Extrinsic.Term.rename]
  | lam B e =>
    simp [Val.trans, Val.rename, SystemF.Extrinsic.Term.rename]
    constructor
    apply SystemF.Renameₜ.id_rfl
    apply HEq.trans
    show HEq e.trans{{ρ.trans.extend}}ᵣ e.trans{{ρ.extend.trans}}ᵣ
    congr
    rw [SystemF.Renameₜ.id_rfl]
    apply Rename.comm_trans_extend
    apply heq_of_eq
    apply Cmp.comm_trans_rename
  | handler val op =>
    simp [Val.trans, Val.rename, SystemF.Extrinsic.Term.rename]
    constructor
    constructor
    rw [SystemF.Renameₜ.id_rfl]
    apply HEq.trans
    show HEq val.trans{{ρ.trans.extend}}ᵣ val.trans{{ρ.extend.trans}}ᵣ
    congr
    rw [SystemF.Renameₜ.id_rfl]
    apply Rename.comm_trans_extend
    apply heq_of_eq
    apply Cmp.comm_trans_rename
    apply OpClauses.comm_trans_rename

def Cmp.comm_trans_rename : {t : Γ ⊢c C} → t.trans{{ρ.trans}}ᵣ = t{{ρ}}ᵣ.trans := by
  intro t
  cases t with
  | «return» v =>
    simp [Cmp.trans, Cmp.rename, SystemF.Extrinsic.Term.rename]
    constructor
    rw [SystemF.Renameₜ.id_extend, SystemF.Renameₜ.id_rfl]
    simp [Cmp.colon]
    simp [SystemF.Extrinsic.Term.rename, SystemF.Rename.extend]
    have := Val.comm_trans_rename (t:=v) (ρ:=ρ)
    rw [←this]
  | op i v c => sorry
  | app f x => sorry
  | ifte b t e => sorry
  | handle_with c v => sorry
def OpClauses.comm_trans_rename : {S : OpClauses Γ E C} → S.trans{{ρ.trans}}ᵣ = S{{ρ}}ᵣ.trans := by sorry

end

end Eff
