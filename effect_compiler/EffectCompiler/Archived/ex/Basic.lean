
inductive VTy : Type where
  | N : VTy
  | fn : VTy → (Bool × VTy) → VTy
infix: 30 " ⇒ " => VTy.fn

inductive Con : Type
  | nil : Con
  | cons : Con → VTy → Con
notation : 80 Γ "; " A => Con.cons Γ A

inductive Member : Con → VTy → Type where
  | zero : Member (Γ; A) A
  | succ : Member Γ A → Member (Γ; B) A
infix: 70 " ∋ " => Member

mutual
inductive Val : Con → VTy → Type where
  | val : Nat → Val Γ .N
  | var : Γ ∋ A → Val Γ A
  | lam : Cmp (Γ; A) C → Val Γ (A ⇒ C)
inductive Cmp : Con → (Bool × VTy) → Type where
  | add : Val Γ .N → Val Γ .N → Cmp Γ (false, .N)
  | app : Val Γ (A ⇒ C) → Val Γ A → Cmp Γ C
  | return : Val Γ A → Cmp Γ (false, A)
  | throw : Cmp Γ (true, A)
  | catch : Cmp Γ (a, A) → Cmp Γ (b, A) → Cmp Γ (a ∧ b, A)
  | let : Cmp Γ (a, A) → Cmp (Γ; A) (b, B)  → Cmp Γ (a ∨ b, B)
end

mutual
inductive Result : VTy → Type where
  | num : Nat → Result .N
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

def Val.evalv : Val Γ A → Env Γ → Result A
  | val n , _ => .num n
  | var i, env => env[i]
  | lam f, env => .closure f env

def Cmp.evalc? : Cmp Γ (a, A) → Env Γ → Option (Result A)
  | add a b, env =>
    match a.evalv env, b.evalv env with
    | .num a, .num b => some $ .num (a + b)
  | app f e, env =>
    match f.evalv env with
    | .closure f' env' => evalc? f' (env'; e.evalv env)
  | .return _ , env => sorry
  | throw , env => sorry
  | .catch _ _ , env => sorry
  | .let _ _ , env => sorry
