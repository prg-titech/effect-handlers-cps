
import EffectCompiler.Context
-- import EffectCompiler.Notation

import Mathlib.Logic.Equiv.Basic

import Lean

import Batteries.Data.Vector

open Lean PrettyPrinter Delaborator SubExpr Elab Meta


namespace Eff

mutual
inductive ValTy : Type where
  | bool : ValTy
  | fn : ValTy → CmpTy → ValTy
  | hn : CmpTy × CmpTy → ValTy
deriving Repr
inductive CmpTy : Type where
  | mk : ValTy → Signature → CmpTy
deriving Repr
inductive Signature : Type where
  | nil : Signature
  | cons : Signature → OpTy → Signature
deriving Repr
inductive OpTy : Type where
  | mk : ValTy → ValTy → OpTy
deriving Repr
inductive HandlerTy : Type where
  | mk : CmpTy → CmpTy → HandlerTy
deriving Repr
end

infixr : 26 " ⇒ " => ValTy.fn
notation : 26 C " ⇛ " D => ValTy.hn (C, D)

infixl:67 ";ₛ " => Signature.cons

inductive Signature.Member : Signature → OpTy → Type where
  | zero : Member (S;ₛ op)  op
  | succ : Member S op → Member (S;ₛ op') op
deriving Repr
infix: 60 " ∋ₛ " => Signature.Member

def Signature.length : Signature → Nat
  | nil => 0
  | cons S _ => S.length + 1
def Signature.get : (S : Signature) → Fin (S.length) → OpTy
  | nil, i => Fin.elim0 i
  | cons S op, i =>
    i.cases op (fun i => S.get i)

mutual
inductive Val : Context ValTy → ValTy → Type where
  | var : Γ ∋ A → Val Γ A
  | false : Val Γ .bool
  | true : Val Γ .bool
  | lam : (A : ValTy) → Cmp (Γ; A) B!E →  Val Γ (.fn A B!E)
  | handler : Cmp (Γ; A) C → OpClauses Γ E C → Val Γ (A!E ⇛ C)
deriving Repr

inductive Cmp : Context ValTy → CmpTy → Type where
  | return : Val Γ A → Cmp Γ ⟨A, E⟩
  | op : E ∋ₛ ⟨A', B'⟩ → Val Γ A' → Cmp (Γ; B') A!E → Cmp Γ A!E
  | app : Val Γ (A ⇒ C) → Val Γ A → Cmp Γ C
  | ifte : Val Γ .bool → Cmp Γ C → Cmp Γ C → Cmp Γ C
  | handle_with : Cmp Γ C → Val Γ (C ⇛ C') → Cmp Γ C'
deriving Repr
inductive OpClauses : Context ValTy → Signature → CmpTy → Type where
  | nil : OpClauses Γ .nil C
  | cons : OpClauses Γ E C → Cmp (Γ; A; (B ⇒ C)) C → OpClauses Γ (E;ₛ ⟨A, B⟩) C
deriving Repr
end

infix : 26 " ⊢v " => Val
infix : 26 " ⊢c " => Cmp
abbrev Handler Γ A E A' E' := Cmp (Γ; A) ⟨A', E'⟩ × OpClauses Γ E ⟨A, E⟩
notation : 26 Γ " ⊢h " A "!" E: max " ⇛ " A' "!" E' : max => Handler Γ A E A' E'

-- notation : max "ff" => Val.false
-- notation : max "tt" => Val.true

notation : max "return " v => Cmp.return v
notation : max "do " c₁ " in " c₂ => Cmp.do_in c₁ c₂
infixl : 80 " @ " => Cmp.app
notation : max "handle" c "with" h => Cmp.handle_with c h
notation : max "if" b "then" c₁ "else" c₂ => Cmp.ifte b c₁ c₂

abbrev CmpTy.val : CmpTy → ValTy
  | ⟨A, _⟩ => A
def CmpTy.eff : CmpTy → Signature
  | ⟨_, E⟩ => E

-- def OpClauses' (Γ : Context ValTy) (E : Context OpTy) (C : CmpTy) := (∀ A' B', E ∋ ⟨A', B'⟩ → Cmp (Γ; A'; (B' ⇒ C)) C)

-- def OpClauses_of_OpClauses' : {E : Context OpTy} → OpClauses' Γ E C → OpClauses Γ E C
--   | .nil, _ => .nil
--   | .cons _ ⟨A, B⟩, op => .cons (OpClauses_of_OpClauses' (fun A B i => op A B (.succ i))) (op A B .zero)
-- def OpClauses'_of_OpClauses : OpClauses Γ E C → OpClauses' Γ E C
--   | .nil => fun _ _ _ => by contradiction
--   | .cons cls cl => fun _ _ i => match i with
--     | .zero => cl
--     | .succ i => OpClauses'_of_OpClauses cls _ _ i
-- def OpClauses_iff_OpClauses'.left_inv : Function.LeftInverse (@OpClauses_of_OpClauses' Γ C E)  (@OpClauses'_of_OpClauses Γ E C)
--   | .nil => rfl
--   | .cons _ _ => congrArg (OpClauses.cons · _) (OpClauses_iff_OpClauses'.left_inv _)
-- def OpClauses_iff_OpClauses'.right_inv_lemma : OpClauses_of_OpClauses' op = .cons cls cl → OpClauses_of_OpClauses' (fun A B i => op A B (.succ i)) = cls := by
--   intro h
--   rename Context OpTy => E
--   cases E with
--   | nil =>
--     simp [OpClauses_of_OpClauses']
--     cases cls
--     trivial
--   | cons E Op => sorry
-- def OpClauses_iff_OpClauses'.right_inv : Function.RightInverse (@OpClauses_of_OpClauses' Γ C E)  (@OpClauses'_of_OpClauses Γ E C) := by
--   intro op
--   cases E with
--   | nil =>
--     simp [OpClauses_of_OpClauses', OpClauses'_of_OpClauses]
--     funext A B i
--     contradiction
--   | cons E Op =>
--     funext A' B' i
--     cases i with
--     | zero => rfl
--     | succ i =>
--       cases h : OpClauses_of_OpClauses' op with
--       | cons cls cl =>
--         simp [OpClauses'_of_OpClauses]
--         apply congrFun
--         apply congrFun
--         apply congrFun
--         let op' := fun A' B' i ↦ op A' B' (.succ i)
--         show _ = op'
--         rw [←OpClauses_iff_OpClauses'.right_inv op']
--         apply congrArg
--         exact (OpClauses_iff_OpClauses'.right_inv_lemma h).symm
-- def OpClauses_iff_OpClauses' : OpClauses Γ E C ≃ OpClauses' Γ E C where
--   toFun := OpClauses'_of_OpClauses
--   invFun := OpClauses_of_OpClauses'
--   left_inv := OpClauses_iff_OpClauses'.left_inv
--   right_inv := OpClauses_iff_OpClauses'.right_inv

def OpClauses.get : {E : Signature} → OpClauses Γ E C → E ∋ₛ ⟨A, B⟩ → Cmp (Γ; A; (B ⇒ C)) C
  | .nil, .nil, i => by contradiction
  | _;ₛ ⟨A, B⟩, .cons cls cl, .zero => cl
  | E;ₛ ⟨_, _⟩, .cons cls cl, .succ i => cls.get i

def ValTy.sizeOf_lemma : (A : ValTy) → 0 < sizeOf A
  | .bool => by simp_arith
  | .fn A D => by simp_arith
  | .hn H => by simp_arith
def Signature.sizeOf_lemma : (E : Context OpTy) → 0 < sizeOf E
  | .nil => by simp_arith
  | .cons E op => by simp_arith

end Eff
