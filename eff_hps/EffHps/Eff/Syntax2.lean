
import EffHps.Notation
import Batteries.Data.List

namespace Eff

inductive ValTy : Type where
  | bool : ValTy
  | fn : ValTy → ValTy × List (ValTy × ValTy) → ValTy
  | hn : ValTy × List (ValTy × ValTy) → ValTy × List (ValTy × ValTy) → ValTy
deriving Repr

abbrev OpTy := ValTy × ValTy
abbrev Signature := List OpTy
abbrev CmpTy := ValTy × List OpTy

-- instance : FnNotation ValTy CmpTy ValTy where
--   fn := ValTy.fn

infix : 26 " ⇛ " => ValTy.hn

inductive Con : Type where
  | nil : Con
  | cons : Con → ValTy → Con
infixl : 90 "; " => Con.cons

inductive Con.Member : Con → ValTy → Type where
  | zero : Member (Γ; A) A
  | succ : Member Γ A → Member (Γ; B) A
notation : 90 Γ: 90 " ∋ " A: 90 => Con.Member Γ A

mutual
inductive Val : Con → ValTy → Type where
  | var : Γ ∋ A → Val Γ A
  | false : Val Γ .bool
  | true : Val Γ .bool
  | lam : (A : ValTy) → Cmp (Γ; A) C →  Val Γ (.fn A C)
  | handler : Cmp (Γ; A) C → OpClauses Γ E C → Val Γ ((A, E) ⇛ C)
inductive Cmp : Con → CmpTy → Type where
  | return : Val Γ A → Cmp Γ (A, E)
  | op : (A', B') ∈ E → Val Γ A' → Cmp (Γ; B') ⟨A, E⟩ → Cmp Γ ⟨A, E⟩
  | app : Val Γ (.fn A C) → Val Γ A → Cmp Γ C
  | ifte : Val Γ .bool → Cmp Γ C → Cmp Γ C → Cmp Γ C
  | handle_with : Cmp Γ C → Val Γ (C ⇛ C') → Cmp Γ C'
inductive OpClauses : Con → Signature → CmpTy → Type where
| nil : OpClauses Γ .nil C
| cons : OpClauses Γ E C → Cmp (Γ; A; (.fn B C)) C → OpClauses Γ ((A, B) :: E) C
end

infix : 26 " ⊢v " => Val
infix : 26 " ⊢c " => Cmp
-- abbrev Handler Γ A E A' E' := Cmp (Γ; A) ⟨A', E'⟩ × OpClauses Γ E ⟨A, E⟩
-- notation : 26 Γ " ⊢h " A "!" E: max " ⇛ " A' "!" E' : max => Handler Γ A E A' E'


-- notation : max "return " v => Cmp.return v
-- notation : max "do " c₁ " in " c₂ => Cmp.do_in c₁ c₂
-- infixl : 80 " @ " => Cmp.app
-- notation : max "handle" c "with" h => Cmp.handle_with c h
-- notation : max "if" b "then" c₁ "else" c₂ => Cmp.ifte b c₁ c₂


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

-- def OpClauses.get : {E : Signature} → OpClauses Γ E C → (i : Fin E.length) → Cmp (Γ; (E.get i).1; (.fn (E.get i).2 C)) C
--   | .nil, .nil, i => Fin.elim0 i
--   | _;ₛ ⟨_, _⟩, .cons S cl, i => i.cases cl (fun i => S.get i)
-- -- def OpClauses.get' : {E : Signature} → OpClauses Γ E C → ⟨A, B⟩ ∈ E → Cmp (Γ; A; (.fn B C)) C
-- --   | .nil, .nil, i => by contradiction
-- --   | ⟨A, B⟩ :: _, .cons cls cl, .haed => cl
-- --   | ⟨_, _⟩ :: E, .cons cls cl, .succ i => cls.get' i

def ValTy.sizeOf_lemma : (A : ValTy) → 0 < sizeOf A
  | .bool => by simp_arith
  | .fn A D => by simp_arith
  | .hn C C' => by simp_arith
def Signature.sizeOf_lemma : (E : Signature) → 0 < sizeOf E
  | .nil => by simp_arith
  | .cons E op => by simp_arith

-- def OpClauses.sizeof_lemma : {S : OpClauses Γ E C} → ∀ i, sizeOf (S.get i) < sizeOf S := by
--   intro S i
--   cases S with
--   | nil => exact Fin.elim0 i
--   | cons E opty =>
--     cases i using Fin.cases with
--     | zero =>
--       simp [get]
--       simp_arith
--     | succ i =>
--       simp [get]
--       apply Nat.lt_add_right
--       apply Nat.lt_add_left
--       apply sizeof_lemma

end Eff
