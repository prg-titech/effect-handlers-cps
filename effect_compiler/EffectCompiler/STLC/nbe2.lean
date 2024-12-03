
import EffectCompiler.STLC.Basic
import EffectCompiler.STLC.SmallStep

open STLC

namespace STLC

mutual
inductive Nf : Context Ty → Ty → Type where
  | unit : Nf Γ .unit
  | lam : (A: Ty) → Nf (Γ; A) B → Nf Γ (A ⇒ B)
  | pair : Nf Γ A → Nf Γ B → Nf Γ (A ⊗ B)
  | ne : Ne Γ A → Nf Γ A
  deriving Repr
inductive Ne : Context Ty → Ty → Type where
  | var : Γ ∋ A → Ne Γ A
  | app : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
  | p₁ : Ne Γ (A ⊗ B) → Ne Γ A
  | p₂ : Ne Γ (A ⊗ B) → Ne Γ B
  deriving Repr
end

-- def Env (D : Context Ty → Ty → Type) : Context Ty → Context Ty → Type :=
--   fun Γ Δ  => ∀ A, Δ ∋ A → D Γ A

-- def Env.cons : Env D Γ Δ → D Γ A → Env D Γ (Δ; A)
--   | _, x, _, .zero => x
--   | ρ, _, _, .succ i => ρ _ i
def Env (D : Ty → Type) : Context Ty → Type :=
  fun Γ => ∀ A, Γ ∋ A → D A

def Env.cons : Env D Γ → D A → Env D (Γ; A)
  | _, x, _, .zero => x
  | ρ, _, _, .succ i => ρ _ i

def NE (A : Ty) := ∀ Γ, Option (Ne Γ A)
def NF (A : Ty) := ∀ Γ, Nf Γ A
def NE.var {A : Ty} (i: Nat) : NE A :=
  fun Γ => if h : i < Γ.length then
    if h' : Γ.get ⟨i, h⟩ = A then some <| .var <| h' ▸ Γ.get' ⟨i, h⟩
    else none
  else none
def Ty.interp : Ty → Type
  | .unit => Unit ⊕ NE .unit
  | A ⇒ B => (A.interp → B.interp) ⊕ NE (A ⇒ B)
  | A ⊗ B => (A.interp × B.interp) ⊕ NE (A ⊗ B)

def Ty.interp.inr': {A : Ty} →  NE A → Ty.interp A
  | .unit, x => .inr x
  | _ ⇒ _, x => .inr x
  | _ ⊗ _, x => .inr x

mutual
def Term.interp : Γ ⊢ A → Env Ty.interp Γ → Ty.interp A
  | .var i, ρ => ρ _ i
  | .unit, ρ => .inl ()
  | .lam _ t, ρ => .inl fun x => t.interp (ρ.cons x)
    -- fun x => t.interp (ρ.cons x)
  | .app f x, ρ => Ty.interp.app (f.interp ρ) (x.interp ρ)
    -- f.interp ρ <| x.interp ρ
  | .pair a b, ρ => .inl ⟨a.interp ρ, b.interp ρ⟩
  | .p₁ ab, ρ => Ty.interp.p₁ (ab.interp ρ)
  | .p₂ ab, ρ => Ty.interp.p₂ (ab.interp ρ)
def Ty.interp.app {A B : Ty} : Ty.interp (A ⇒ B) → Ty.interp A → Ty.interp B :=
  fun f a => match f with
  | .inl f => f a
  | .inr e => .inr' <| fun Γ => (e Γ).map <| fun f => .app f (reify a Γ)
def Ty.interp.p₁ {A B : Ty} : Ty.interp (A ⊗ B) → Ty.interp A :=
  fun ab => match ab with
  | .inl ab => ab.1
  | .inr e => .inr' <| fun Γ => (e Γ).map <| fun e => .p₁ e
def Ty.interp.p₂ {A B : Ty} : Ty.interp (A ⊗ B) → Ty.interp B :=
  fun ab => match ab with
  | .inl ab => ab.2
  | .inr e => .inr' <| fun Γ => (e Γ).map <| fun e => .p₂ e
def reify : {A : Ty} → Ty.interp A → NF A
  | .unit => fun x => fun Γ => x.elim (fun _ => .unit) (fun x => (x Γ).elim .unit (fun x => .ne x))
  | A ⇒ B => fun f => fun Γ =>
    .lam _ <| reify (Ty.interp.app f <| reflect (NE.var 0)) (Γ; A)
  | A ⊗ B => fun ab => fun Γ => .pair (reify (Ty.interp.p₁ ab) Γ) (reify (Ty.interp.p₂ ab) Γ)
def reflect : {A : Ty} → NE A → Ty.interp A
  | .unit => fun x => .inr' x
  | A ⇒ B => fun f => .inr' f
  | A ⊗ B => fun x => .inr' x
end

def Env.id : {Γ : Context Ty} → Env Ty.interp Γ
  | .nil => fun _ _ => by contradiction
  | .cons Γ A => id.cons <| .inr' <| NE.var 0
def nf : Γ ⊢ A → Nf Γ A :=
  fun t => reify (t.interp Env.id) Γ

#eval ((ƛ _ => .var .zero) @ Term.unit : .nil ⊢ _)
#eval reify ((Term.unit : .nil ⊢ _).interp (fun _ _ => by contradiction)) .nil
#eval reify (((ƛ _ => .var .zero) @ Term.unit : .nil ⊢ _).interp (fun _ _ => by contradiction)) .nil
#check (.p₂ (.pair .unit (.pair .unit .unit)) : .nil ⊢ _).interp (fun _ _ => by contradiction)
#eval reify ((.p₂ (.pair .unit (.pair .unit .unit)) : .nil ⊢ _).interp (fun _ _ => by contradiction)) .nil

#eval nf (Term.unit : .nil ⊢ _)
#eval nf ((ƛ _ => .var .zero) @ Term.unit : .nil ⊢ _)
#eval nf (.p₂ (.pair .unit (.pair .unit .unit)) : .nil ⊢ _)
#eval nf (ƛ _ => (.var (.succ .zero)) @ (.var .zero) : .nil; (.unit ⇒ .unit) ⊢ _)

end STLC
