
import Mathlib.Data.Set.Basic

import EffectCompiler.STLC.Basic


namespace Eff

mutual
inductive VTy : Type where
  | unit : VTy
  | fn : VTy → CTy → VTy
  | hand : CTy → CTy → VTy
inductive Eff : Type where
  | mk : List OpSig → Eff
inductive OpSig : Type where
  | mk : VTy → VTy → OpSig
inductive CTy : Type where
  | mk : VTy → Eff → CTy
end
instance : FnNotation VTy CTy VTy where
  fn := VTy.fn

namespace Example
variable (A : VTy) (E : Eff)
#check (⟨A, A⟩ : OpSig)
#check (⟨[]⟩ : Eff)
#check (⟨A, E⟩ : CTy)
end Example


-- inductive Con : Type
--   | nil : Con
--   | cons : Con → VTy → Con
-- infixl : 80 "; " => Con.cons

-- inductive Member : Con → VTy → Type where
--   | zero : Member (Γ; A) A
--   | succ : Member Γ A → Member (Γ; B) A
-- infix: 70 " ∋ " => Member
def Con := Context VTy

inductive HList { α : Type} ( β : α → Type) : List α → Type
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i :: is)

mutual
inductive Val : Con → VTy → Type where
  | var : Γ ∋ A → Val Γ A
  | unit : Val Γ .unit
  | lam : Cmp (Γ; A) C → Val Γ (A ⇒ C)
  | handler : Handler Γ C C' → Val Γ (.hand C C')
inductive Cmp : Con → CTy → Type where
  | app : Val Γ (A ⇒ C) → Val Γ A → Cmp Γ C
  | return : Val Γ A → Cmp Γ ⟨A, E⟩
  | do : ⟨A, B⟩ ∈ E → Val Γ A → Cmp Γ ⟨B, ⟨E⟩⟩
  | handle_with : Cmp Γ C → Val Γ (.hand C D) → Cmp Γ D
  | let : Cmp Γ ⟨A, E⟩ → Cmp (Γ; A) ⟨B, E⟩ → Cmp Γ ⟨B, E⟩
inductive OpClauses : Con → Eff → CTy → Type where
  | nil : OpClauses Γ E C
  | cons : Cmp (Γ; A; (B ⇒ C)) C → OpClauses Γ ⟨E⟩ C → OpClauses Γ ⟨(⟨A, B⟩ :: E)⟩ C
inductive Handler : Con → CTy → CTy →  Type where
  | mk :
    Cmp (Γ; A) C →
    OpClauses Γ E C →
    Handler Γ ⟨A, E⟩ C
end

mutual
inductive Result : VTy → Type where
  | unit : Result .unit
  | closure : Cmp (Γ; A) C → Env Γ → Result (A ⇒ C)
inductive Env : Con → Type where
  | nil : Env .nil
  | cons : Env Γ → Result A → Env (Γ; A)
end
notation : 80 Γ "; " A => Env.cons Γ A

def Env.get : Env Γ → Γ ∋ A → Result A
  | .cons _ r, .zero => r
  | .cons env _, .succ i => env.get i
instance {Γ : Con} : GetElem (Env Γ) (Γ ∋ A) (Result A) (fun _ _ => True) where
  getElem env i _ := env.get i



def VTy.trans : VTy → STLC.Ty
  | .unit => .unit
  | _ => sorry
def CTy.trans : CTy → STLC.Ty := sorry
def Con.trans : Con → Context STLC.Ty := sorry

mutual
def Val.trans : Val Γ A → STLC.Term Γ.trans A.trans
  | .var i => sorry
  | .unit => .unit
  | .lam e => sorry
  | .handler h => sorry
def Cmp.trans : Cmp Γ C → STLC.Term Γ.trans (C.trans ⇒ D) → STLC.Term Γ.trans D
  | .app f e, k => sorry
  | .return v, k => sorry
  | .do h v, k => sorry
  | .handle_with c v, k =>
    let k' : STLC.Term Γ.trans _ := STLC.Term.lam C.trans (.var .zero)
    let handler := v.trans
    .app k (c.trans sorry)
  | .let a b, k => sorry
end

end Eff
