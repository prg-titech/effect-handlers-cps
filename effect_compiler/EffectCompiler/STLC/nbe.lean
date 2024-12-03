
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

mutual
def Nf.rename : Nf Γ A → Renaming Δ Γ → Nf Δ A
  | .unit, ρ => .unit
  | .lam _ e, ρ => .lam _ (Nf.rename e (ρ.extend _))
  | .pair a b, ρ => .pair (Nf.rename a ρ) (Nf.rename b ρ)
  | .ne e, ρ => .ne <| Ne.rename e ρ
def Ne.rename : Ne Γ A → Renaming Δ Γ → Ne Δ A
  | .var i, ρ => .var <| ρ _ i
  | .app f x, ρ => .app (Ne.rename f ρ) (Nf.rename x ρ)
  | .p₁ ab, ρ => .p₁ (Ne.rename ab ρ)
  | .p₂ ab, ρ => .p₂ (Ne.rename ab ρ)
end

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

def Sem : Context Ty → Ty → Type
  | Γ, .unit => Nf Γ .unit
  | Γ, A ⇒ B => ({Δ : Context Ty} → Renaming Δ Γ → Sem Δ A → Sem Δ B) ⊕ Ne Γ (A ⇒ B)
  | Γ, A ⊗ B => Sem Γ A × Sem Γ B ⊕ Ne Γ (A ⊗ B)
    -- ({Δ : Context Ty} → Renaming Δ Γ → Sem Δ A × Sem Δ B) ⊕ Ne Γ (A ⊗ B)
infix : 60 " ⊨ " => Sem

def Sem.ofNe : {A : Ty} → Ne Γ A → Γ ⊨ A
  | .unit, x => .ne x
  | _ ⇒ _, f => .inr f
  | _ ⊗ _, ab => .inr ab

def Sem.rename : {A : Ty} → Γ ⊨ A → Renaming Δ Γ → Δ ⊨ A
  | .unit, x, ρ => Nf.rename x ρ
  | A ⇒ B, .inl f, ρ => .inl fun {Δ'} ρ' x => f (ρ'.comp ρ) x
  | A ⇒ B, .inr f, ρ => .inr <| Ne.rename f ρ
  | A ⊗ B, .inl ab, ρ => .inl ⟨Sem.rename ab.1 ρ, Sem.rename ab.2 ρ⟩
  | A ⊗ B, .inr ab, ρ => .inr <| Ne.rename ab ρ

def Env : Context Ty → Context Ty → Type :=
  fun Γ Δ  => ∀ A, Δ ∋ A → Γ ⊨ A

def Env.cons {A : Ty} : Env Γ Δ → Γ ⊨ A → Env Γ (Δ; A)
  | _, x, _, .zero => x
  | ρ, _, _, .succ i => ρ _ i

mutual
def reflect : {A : Ty} → Ne Γ A → Γ ⊨ A
  | .unit, x => .ne x
  | A ⇒ B, f => .inr f
  | A ⊗ B, ab => .inr ab
def reify : {A : Ty} → Γ ⊨ A → Nf Γ A
  | .unit, x => x
  | A ⇒ B, .inl f => .lam _ (reify (f (.succ (A:=·)) (reflect (.var .zero))))
  | A ⇒ B, .inr f => .ne f
  | A ⊗ B, .inl ab => .pair (reify ab.1) (reify ab.2)
  | A ⊗ B, .inr ab => .ne ab
def Term.interp : Γ ⊢ A → Env Δ Γ → Δ ⊨ A
  | .var i, ρ => ρ _ i
  | .unit, ρ => .unit
  | .lam _ t, ρ => .inl fun {Δ'} r x => t.interp (Env.cons ((Sem.rename · r) ∘ ρ ·) x)
    -- fun x => t.interp (ρ.cons x)
  | .app f x, ρ => Sem.app (f.interp ρ) (x.interp ρ)
    -- f.interp ρ <| x.interp ρ
  | .pair a b, ρ => .inl ⟨a.interp ρ, b.interp ρ⟩
  | .p₁ ab, ρ => Sem.p₁ (ab.interp ρ)
  | .p₂ ab, ρ => Sem.p₂ (ab.interp ρ)
def Sem.app : Γ ⊨ (A ⇒ B) → Γ ⊨ A → Γ ⊨ B
  | .inl f, x => f (𝟙ᵣ Γ) x
  | .inr f, x => .ofNe <| .app f (reify x)
def Sem.p₁ : Γ ⊨ (A ⊗ B) → Γ ⊨ A
  | .inl ab => ab.1
  | .inr ab => .ofNe <| .p₁ ab
def Sem.p₂ : Γ ⊨ (A ⊗ B) → Γ ⊨ B
  | .inl ab => ab.2
  | .inr ab => .ofNe <| .p₂ ab
end

def Env.id : {Γ : Context Ty} → Env Γ Γ
  | _; _, _, i => .ofNe <| .var i

def nf : Γ ⊢ A → Nf Γ A :=
  fun t => reify (t.interp Env.id)

mutual
def Nf.emb : Nf Γ A → Σ t : Γ ⊢ A, Normal t
  | .unit => ⟨.unit, .unit⟩
  | .lam _ e => ⟨.lam _ e.emb.1, .lam e.emb.2⟩
  | .pair a b => ⟨.pair a.emb.1 b.emb.1, .pair a.emb.2 b.emb.2⟩
  | .ne e => ⟨e.emb.1, .neutral e.emb.2⟩
def Ne.emb : Ne Γ A → Σ t : Γ ⊢ A, Neutral t
  | .var i => ⟨.var i, .var⟩
  | .app f x => ⟨.app f.emb.1 x.emb.1, .app f.emb.2 x.emb.2⟩
  | .p₁ ab => ⟨.p₁ ab.emb.1, .p₁ ab.emb.2⟩
  | .p₂ ab => ⟨.p₂ ab.emb.1, .p₂ ab.emb.2⟩
end

#eval nf (Term.unit : .nil ⊢ _)
#eval nf ((ƛ _ => .var .zero) @ Term.unit : .nil ⊢ _)
#eval nf (.p₂ (.pair .unit (.pair .unit .unit)) : .nil ⊢ _)
#eval (·.1) <| Nf.emb <| nf (ƛ _ => (.var (.succ .zero)) @ (.var .zero) : .nil; (.unit ⇒ .unit) ⊢ _)

#reduce nf (Term.unit : .nil ⊢ _)
#reduce nf ((ƛ _ => .var .zero) @ Term.unit : .nil ⊢ _)
#reduce nf (.p₂ (.pair .unit (.pair .unit .unit)) : .nil ⊢ _)
#reduce (·.1) <| Nf.emb <| nf (ƛ _ => (.var (.succ .zero)) @ (.var .zero) : .nil; (.unit ⇒ .unit) ⊢ _)

end STLC
