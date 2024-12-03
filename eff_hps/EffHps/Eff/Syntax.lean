
import EffHps.Notation


namespace Eff


mutual
inductive ValTy : Type where
  | bool : ValTy
  | fn : ValTy → CmpTy → ValTy
  | hn : CmpTy → CmpTy → ValTy
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

def Signature.Member.asFin : S ∋ₛ opty → Fin S.length
  | .zero => ⟨0, by simp[length]⟩
  | .succ i => .succ i.asFin

def Signature.get_asfin : {S : Signature} → {i : S ∋ₛ opty} → S.get i.asFin = opty := by
  intro S i
  induction i with
  | zero => simp [get, Member.asFin]
  | succ i ih =>
    simp [get, Member.asFin]
    assumption

def Signature.zero_lt_size : {E : Signature} → 0 < sizeOf E := by
  intro E
  cases E with
  | nil => simp
  | cons E opty => simp_arith

def Signature.sizeof_lemma : {E : Signature} → ∀ i, sizeOf (E.get i) < sizeOf E := by
  intro E i
  cases E with
  | nil => exact Fin.elim0 i
  | cons E opty =>
    cases i using Fin.cases with
    | zero =>
      simp [get]
      simp_arith
    | succ i =>
      simp [get]
      apply Nat.lt_add_right
      apply Nat.lt_add_left
      apply sizeof_lemma


mutual
inductive Val (Var : ValTy → Type) : ValTy → Type where
  | var : Var A → Val Var A
  | false : Val Var .bool
  | true : Val Var .bool
  | lam : (A : ValTy) → (Var A → Cmp Var C) →  Val Var (.fn A C)
  | handler : (Var A → Cmp Var C) → OpClauses Var E C → Val Var (⟨A, E⟩ ⇛ C)
inductive Cmp (Var : ValTy → Type) : CmpTy → Type where
  | return : Val Var A → Cmp Var ⟨A, E⟩
  | op : E ∋ₛ ⟨A', B'⟩ → Val Var A' → (Var B' → Cmp Var ⟨A, E⟩) → Cmp Var ⟨A, E⟩
  | app : Val Var (.fn A C) → Val Var A → Cmp Var C
  | ifte : Val Var .bool → Cmp Var C → Cmp Var C → Cmp Var C
  | handle_with : Cmp Var C → Val Var (C ⇛ C') → Cmp Var C'
inductive OpClauses (Var : ValTy → Type) : Signature → CmpTy → Type where
  | nil : OpClauses Var .nil C
  | cons : OpClauses Var E C → (Var (.fn B C) → Var A → Cmp Var C) → OpClauses Var (E;ₛ ⟨A, B⟩) C
end

notation : 26 "⊢[" Var "]v " A => Val Var A
notation : 26 "⊢[" Var "]c " A => Cmp Var A
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
-- def OpClauses.get' : {E : Signature} → OpClauses Γ E C → E ∋ₛ ⟨A, B⟩ → Cmp (Γ; A; (.fn B C)) C
--   | .nil, .nil, i => by contradiction
--   | _;ₛ ⟨A, B⟩, .cons cls cl, .zero => cl
--   | E;ₛ ⟨_, _⟩, .cons cls cl, .succ i => cls.get' i

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
