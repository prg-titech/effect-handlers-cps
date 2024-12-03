
import Mathlib.Data.Set.Basic


mutual
inductive VTy : Type where
  | unit : VTy
  | nat : VTy
  | fn : VTy → CTy → VTy
inductive CTy : Type where
  | mk : VTy → Bool → CTy
end
infix: 30 " ⇒ " => VTy.fn

namespace Example
variable (A : VTy) (E : Eff)
end Example


inductive Con : Type
  | nil : Con
  | cons : Con → VTy → Con
infixl : 20 "; " => Con.cons

inductive Member : Con → VTy → Type where
  | zero : Member (Γ; A) A
  | succ : Member Γ A → Member (Γ; B) A
infix: 70 " ∋ " => Member

inductive HList { α : Type} ( β : α → Type) : List α → Type
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i :: is)

mutual
inductive Val : Con → VTy → Type where
  | var : Γ ∋ A → Val Γ A
  | unit : Val Γ .unit
  | lam : Cmp (Γ; A) C → Val Γ (A ⇒ C)
inductive Cmp : Con → CTy → Type where
  | app : Val Γ (A ⇒ C) → Val Γ A → Cmp Γ C
  | return : Val Γ A → Cmp Γ ⟨A, false⟩
  | send : Val Γ .nat → Cmp Γ ⟨B, true⟩
  | handle_with : Cmp Γ ⟨A, a⟩ → Val (Γ; .nat; .nat ⇒ ⟨B, b⟩) B → Cmp Γ ⟨D, a ∧ b⟩
  | let : Cmp Γ ⟨A, a⟩ → Cmp (Γ; A) ⟨B, b⟩ → Cmp Γ ⟨B, a ∨ b⟩
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

-- def Val.evalv : Val Γ A → Env Γ → Result A
--   | val n , _ => .num n
--   | var i, env => env[i]
--   | lam f, env => .closure f env

-- def Cmp.evalc? : Cmp Γ (a, A) → Env Γ → Option (Result A)
--   | add a b, env =>
--     match a.evalv env, b.evalv env with
--     | .num a, .num b => some $ .num (a + b)
--   | app f e, env =>
--     match f.evalv env with
--     | .closure f' env' => evalc? f' (env'; e.evalv env)
--   | .return _ , env => sorry
--   | throw , env => sorry
--   | .catch _ _ , env => sorry
--   | .let _ _ , env => sorry
