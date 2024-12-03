
import EffectCompiler.Context
-- import EffectCompiler.Notation

import Mathlib.Logic.Equiv.Basic

import Lean

open Lean PrettyPrinter Delaborator SubExpr Elab Meta



namespace Eff

inductive ValTy : Type where
  | bool : ValTy
  | fn : ValTy → (ValTy × Context (ValTy × ValTy)) → ValTy
  | hn : (ValTy × Context (ValTy × ValTy)) × (ValTy × Context (ValTy × ValTy)) → ValTy
deriving Repr

abbrev OpTy := ValTy × ValTy
abbrev Signature := Context OpTy
abbrev CmpTy := ValTy × Signature
abbrev HandlerTy := CmpTy × CmpTy

infixr : 26 " ⇒ " => ValTy.fn
notation : 26 C " ⇛ " D => ValTy.hn (C, D)

mutual
inductive Val : Context ValTy → ValTy → Type where
  | var : Γ ∋ A → Val Γ A
  | false : Val Γ .bool
  | true : Val Γ .bool
  | lam : (A : ValTy) → Cmp (Γ; A) C →  Val Γ (.fn A C)
  | handler : Cmp (Γ; A) C → OpClauses Γ E C → Val Γ ((A, E) ⇛ C)
deriving Repr

inductive Cmp : Context ValTy → CmpTy → Type where
  | return : Val Γ A → Cmp Γ ⟨A, E⟩
  | op : E ∋ (A', B') → Val Γ A' → Cmp (Γ; B') (A, E) → Cmp Γ (A, E)
  | app : Val Γ (A ⇒ C) → Val Γ A → Cmp Γ C
  | ifte : Val Γ .bool → Cmp Γ C → Cmp Γ C → Cmp Γ C
  | handle_with : Cmp Γ C → Val Γ (C ⇛ C') → Cmp Γ C'
deriving Repr
inductive OpClauses : Context ValTy → Signature → CmpTy → Type where
  | nil : OpClauses Γ .nil C
  | cons : OpClauses Γ E C → Cmp (Γ; A; (B ⇒ C)) C → OpClauses Γ (E; (A, B)) C
deriving Repr
end

infix : 26 " ⊢v " => Val
infix : 26 " ⊢c " => Cmp
abbrev Handler Γ C C' := Cmp (Γ; C.1) C' × OpClauses Γ C.2 C
notation : 26 Γ " ⊢h " C: max " ⇛ " C': max => Handler Γ C C'

-- notation : max "ff" => Val.false
-- notation : max "tt" => Val.true

notation : max "return " v => Cmp.return v
notation : max "do " c₁ " in " c₂ => Cmp.do_in c₁ c₂
infixl : 80 " <> " => Cmp.app
notation : max "handle" c "with" h => Cmp.handle_with c h
notation : max "if" b "then" c₁ "else" c₂ => Cmp.ifte b c₁ c₂

abbrev CmpTy.val : CmpTy → ValTy := (·.1)
def CmpTy.eff : CmpTy → Signature := (·.2)

def OpClauses' (Γ : Context ValTy) (E : Context OpTy) (C : CmpTy) := (∀ A' B', E ∋ ⟨A', B'⟩ → Cmp (Γ; A'; (B' ⇒ C)) C)

def OpClauses_of_OpClauses' : {E : Context OpTy} → OpClauses' Γ E C → OpClauses Γ E C
  | .nil, _ => .nil
  | .cons _ ⟨A, B⟩, op => .cons (OpClauses_of_OpClauses' (fun A B i => op A B (.succ i))) (op A B .zero)
def OpClauses'_of_OpClauses : OpClauses Γ E C → OpClauses' Γ E C
  | .nil => fun _ _ _ => by contradiction
  | .cons cls cl => fun _ _ i => match i with
    | .zero => cl
    | .succ i => OpClauses'_of_OpClauses cls _ _ i
def OpClauses_iff_OpClauses'.left_inv : Function.LeftInverse (@OpClauses_of_OpClauses' Γ C E)  (@OpClauses'_of_OpClauses Γ E C)
  | .nil => rfl
  | .cons _ _ => congrArg (OpClauses.cons · _) (OpClauses_iff_OpClauses'.left_inv _)
def OpClauses_iff_OpClauses'.right_inv_lemma : OpClauses_of_OpClauses' op = .cons cls cl → OpClauses_of_OpClauses' (fun A B i => op A B (.succ i)) = cls := by
  intro h
  rename Context OpTy => E
  cases E with
  | nil =>
    simp [OpClauses_of_OpClauses']
    cases cls
    trivial
  | cons E Op => sorry
def OpClauses_iff_OpClauses'.right_inv : Function.RightInverse (@OpClauses_of_OpClauses' Γ C E)  (@OpClauses'_of_OpClauses Γ E C) := by
  intro op
  cases E with
  | nil =>
    simp [OpClauses_of_OpClauses', OpClauses'_of_OpClauses]
    funext A B i
    contradiction
  | cons E Op =>
    funext A' B' i
    cases i with
    | zero => rfl
    | succ i =>
      cases h : OpClauses_of_OpClauses' op with
      | cons cls cl =>
        simp [OpClauses'_of_OpClauses]
        apply congrFun
        apply congrFun
        apply congrFun
        let op' := fun A' B' i ↦ op A' B' (.succ i)
        show _ = op'
        rw [←OpClauses_iff_OpClauses'.right_inv op']
        apply congrArg
        exact (OpClauses_iff_OpClauses'.right_inv_lemma h).symm
def OpClauses_iff_OpClauses' : OpClauses Γ E C ≃ OpClauses' Γ E C where
  toFun := OpClauses'_of_OpClauses
  invFun := OpClauses_of_OpClauses'
  left_inv := OpClauses_iff_OpClauses'.left_inv
  right_inv := OpClauses_iff_OpClauses'.right_inv

def OpClauses.get : {E : Context OpTy} → OpClauses Γ E C → E ∋ ⟨A, B⟩ → Cmp (Γ; A; (B ⇒ C)) C
  | .nil, .nil, i => by contradiction
  | _; ⟨A, B⟩, .cons cls cl, .zero => cl
  | E; ⟨_, _⟩, .cons cls cl, .succ i => cls.get i

def ValTy.sizeOf_lemma : (A : ValTy) → 0 < sizeOf A
  | .bool => by simp_arith
  | .fn A D => by simp_arith
  | .hn H => by simp_arith
def Signature.sizeOf_lemma : (E : Context OpTy) → 0 < sizeOf E
  | .nil => by simp_arith
  | .cons E op => by simp_arith

-- declare_syntax_cat val
-- declare_syntax_cat cmp

-- syntax ident : val
-- syntax "true"    : val
-- syntax "false"   : val
-- syntax "$" num : val
-- syntax "λ" term "," term "=>" cmp : val
-- syntax "(" val ")" : val

-- syntax ident : cmp
-- syntax "return" val : cmp
-- syntax "op" num val cmp : cmp
-- syntax "do" cmp "in" cmp : cmp
-- syntax "(" cmp ")" : cmp

-- syntax "[" term "|v" val "]" : term
-- syntax "[" term "," term "|c" cmp "]" : term

-- macro_rules
--   | `([ $Γ |v false ]) => `(@Val.false $Γ)
--   | `([ $Γ |v true ]) => `(@Val.true $Γ)
--   | `([$Γ |v $ $n:num ]) => `(Val.var (Γ:=$Γ) (Context.get' $Γ ⟨$n, by decide⟩))
--   | `([$Γ |v λ $A:term , $E => $c:cmp]) => `(Val.lam (Γ:=$Γ) $A [$Γ; $A, $E |c $c])
--   | `([$Γ |v ($v)]) => `([$Γ |v $v])
-- macro_rules
--   | `([$Γ , $E |c return $c]) => `(Cmp.return (Γ:=$Γ) (E:=⟨$E⟩) [$Γ |v $c])
--   | `([$Γ , $E |c op $n $v $c]) => `(Cmp.op (Γ:=$Γ) (E:=⟨$E⟩) (Context.get' $E ⟨$n, by decide⟩) [$Γ |v $v] [$Γ; _, $E |c $c])
--   | `([$Γ , $E |c do $c₁ : $A in $c₂]) => `(Cmp.do_in [$Γ, $E |c $c₁] [($Γ; $A), $E |c $c₂])
--   | `([$Γ , $E |c ($c)]) => `([$Γ , $E |c $c])

-- notation "𝔹" => ValTy.bool

-- #eval [.nil, .nil |c
--   do return
--     (λ 𝔹, .nil; ⟨𝔹, 𝔹⟩ =>
--       do (op 0 false (return $0)) : 𝔹 in
--       return $0) : (𝔹 ⇒ ⟨𝔹, ⟨.nil; ⟨𝔹, 𝔹⟩⟩⟩)
--   in
--   return $0
-- ]
-- syntax term "!" term : term
-- syntax "do" term "in" term : term

-- @[app_unexpander CmpTy.mk]
-- def unexpandCmpTy : Unexpander
--   | `($_ $T $E) => `($T ! $E)
--   | _ => throw ()

-- @[app_unexpander Val.bool]
-- def unexpandValBool : Unexpander
--   | `($_ $b) => `($b)
--   | _ => throw ()
-- @[app_unexpander Val.lam]
-- def unexpandValLam : Unexpander
--   | `($_ $T $t) => `(λ $T => $t)
--   | _ => throw ()

-- @[app_unexpander Cmp.return]
-- def unexpandCmpReturn : Unexpander
--   | `($_ [$Γ |v $x:val]) => `([$Γ, _ |c return $x])
--   | `($_ $x) => `(return $x)
--   | _ => throw ()

-- @[app_unexpander Cmp.do_in]
-- def unexpandCmpDoIn : Unexpander
--   | `($_ $c₁ $c₂) => `(do $c₁ in $c₂)
--   | _ => throw ()

-- #check Val.bool (Γ:=.nil) .false
-- #check [.nil |v false ]
-- -- #eval [.nil |v false ]
-- #reduce [.nil |v false ]
-- #reduce [.nil |v true ]

-- #check [.nil , _ |c return false]
-- #reduce [.nil , _ |c return false]

-- #reduce 𝔹 ⇒ ⟨𝔹, ⟨.nil⟩⟩
-- #reduce [.nil |v λ 𝔹 ⇒ ⟨𝔹, ⟨.nil⟩⟩, _ => return false]

-- #reduce [.nil, _ |c do return false in return true]

end Eff

declare_syntax_cat lang
syntax num   : lang
syntax ident : lang
syntax "let " ident " := " lang " in " lang: lang
syntax "[Lang| " lang "]" : term

inductive LangExpr
  | numConst : Nat → LangExpr
  | ident    : String → LangExpr
  | letE     : String → LangExpr → LangExpr → LangExpr

macro_rules
  | `([Lang| $x:num ]) => `(LangExpr.numConst $x)
  | `([Lang| $x:ident]) => `(LangExpr.ident $(Lean.quote (toString x.getId)))
  | `([Lang| let $x:ident := $v:lang in $b:lang]) => `(LangExpr.letE $(Lean.quote (toString x.getId)) [Lang| $v] [Lang| $b])

instance : Coe NumLit (TSyntax `lang) where
  coe s := ⟨s.raw⟩

instance : Coe Ident (TSyntax `lang) where
  coe s := ⟨s.raw⟩

-- LangExpr.letE "foo" (LangExpr.numConst 12)
--   (LangExpr.letE "bar" (LangExpr.ident "foo") (LangExpr.ident "foo")) : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]

@[app_unexpander LangExpr.numConst]
def unexpandNumConst : Unexpander
  | `(LangExpr.numConst $x:num) => `([Lang| $x])
  | _ => throw ()

@[app_unexpander LangExpr.ident]
def unexpandIdent : Unexpander
  | `(LangExpr.ident $x:str) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| $name])
  | _ => throw ()

@[app_unexpander LangExpr.letE]
def unexpandLet : Unexpander
  | `(LangExpr.letE $x:str [Lang| $v:lang] [Lang| $b:lang]) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| let $name := $v in $b])
  | _ => throw ()

-- [Lang| let foo := 12 in foo] : LangExpr
#check [Lang|
  let foo := 12 in foo
]

-- [Lang| let foo := 12 in let bar := foo in foo] : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]
