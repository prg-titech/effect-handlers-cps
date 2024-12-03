
import EffectCompiler.Context

import Batteries.Logic


namespace SystemF

inductive Kind : Type where
  | type : Kind
  | fn : Kind → Kind → Kind
notation: max (priority:=high) "*" => Kind.type
infixr : 26 " ⇒ " => Kind.fn

-- mutual
inductive Ty : Context Kind → Kind → Type where
  | var : Φ ∋ K → Ty Φ K
  | unit : Ty Φ *
  | bool : Ty Φ *
  | fn : Ty Φ * → Ty Φ * → Ty Φ *
  | pi : (K : Kind) → Ty (Φ; K) * → Ty Φ *
  | pair : Ty Φ * → Ty Φ * → Ty Φ *
--   | tuple : Tuple n Φ → Ty Φ *
-- inductive Tuple : Nat → Context Kind →  Type where
--   | pair : Ty Φ * → Ty Φ * → Tuple 2 Φ
--   | cons : Tuple n Φ → Ty Φ * → Tuple (n+1) Φ
-- end

infixr : 26 " ⇒ " => Ty.fn

def Ren' (Φ Ψ : Context Kind) := ∀ K, Ψ ∋ K → Φ ∋ K
def Ren'.lift : Ren' Φ Ψ → Ren' (Φ; K) (Ψ; K)
  | _, _, .zero => .zero
  | ρ', _, .succ i => .succ (ρ' _ i)

-- mutual
-- @[simp, reducible]
def Ty.ren' : Ty Ψ K → Ren' Φ Ψ → Ty Φ K
  | .var i, ρ' => .var (ρ' _ i)
  | .unit, ρ' => .unit
  | .bool, ρ' => .bool
  | .fn A B, ρ' => .fn (A.ren' ρ') (B.ren' ρ')
  | .pi _ A, ρ' => .pi _ (A.ren' ρ'.lift)
  | .pair A B, ρ' => .pair (A.ren' ρ') (B.ren' ρ')
  -- | .tuple t, ρ' => .tuple (t.ren' ρ')
-- @[simp, reducible]
-- def Tuple.ren' : Tuple n Ψ → Ren' Φ Ψ → Tuple n Φ
--   | .pair A B, ρ' => .pair (A.ren' ρ') (B.ren' ρ')
--   | .cons p C, ρ' => .cons (p.ren' ρ') (C.ren' ρ')
-- end
notation : max t "{{" σ "}}ᵣ'" => Ty.ren' t σ
def Ren'.wk : Ren' (Φ; K) Φ := (.succ (A:=·))
def Ty.wk' : Ty Φ K → Ty (Φ; K') K :=
  fun A => A.ren' Ren'.wk

def Sub' (Φ Ψ : Context Kind) := ∀ K, Ψ ∋ K → Ty Φ K
def Sub'.lift : Sub' Φ Ψ → Sub' (Φ; K) (Ψ; K)
  | _, _, .zero => .var .zero
  | σ', _, .succ i => (σ' _ i).wk'
-- mutual
def Ty.sub' : Ty Ψ K → Sub' Φ Ψ → Ty Φ K
  | .var i, σ' => (σ' _ i)
  | .unit, σ' => .unit
  | .bool, σ' => .bool
  | .fn A B, σ' => .fn (A.sub' σ') (B.sub' σ')
  | .pi _ A, σ' => .pi _ (A.sub' σ'.lift)
  | .pair A B, σ' => .pair (A.sub' σ') (B.sub' σ')
--   | .tuple t, σ' => .tuple (t.sub' σ')
-- def Tuple.sub' : Tuple n Ψ → Sub' Φ Ψ → Tuple n Φ
--   | .pair A B, σ' => .pair (A.sub' σ') (B.sub' σ')
--   | .cons p C, σ' => .cons (p.sub' σ') (C.sub' σ')
-- end
def Sub'.extend : Sub' Φ Ψ → Ty Φ K → Sub' Φ (Ψ; K)
  | _, A, _, .zero => A
  | σ', _, _, .succ i => σ' _ i
def Sub'.id : Sub' Φ Φ := (.var (K:=·))
def Ty.sub'₀ : Ty (Φ; K) J → Ty Φ K → Ty Φ J :=
  fun A B => A.sub' (Sub'.extend Sub'.id B)
notation : max A "{{" σ "}}ₛ'" => Ty.sub' A σ
notation : max A "[[" B "]]'₀" => Ty.sub'₀ A B

inductive Con : Context Kind → Type where
  | nil : Con .nil
  | cons : Con Φ → Ty Φ * → Con Φ
  | cons' : Con Φ → (K : Kind) → Con (Φ; K)
infixl:67 "; " => Con.cons
infixl:67 ";* " => Con.cons'
inductive Con.Member : Con Φ → Ty Φ * → Type where
  | zero : Member (Γ; A) A
  | succ : Member Γ A → Member (Γ; B) A
  | succ' : Member Γ A → Member (Γ;* K) A.wk'
infix: 60 " ∋ " => Con.Member

inductive Term : Con Φ → Ty Φ * → Type where
  | var {Γ : Con Φ} : Γ ∋ A → Term Γ A
  | unit : Term Γ .unit
  | false : Term Γ .bool
  | true : Term Γ .bool
  | ifte : Term Γ .bool → Term Γ A → Term Γ A → Term Γ A
  | lam : (A : Ty Φ *) → Term (Γ; A) B → Term Γ (A ⇒ B)
  | app : Term Γ (A ⇒ B) → Term Γ A → Term Γ B
  | Lam {Γ : Con Φ} : (K : Kind) → {B : Ty _ _} → Term (Γ;* K) B → Term Γ (.pi K B)
  | App {Γ : Con Φ} : Term Γ (.pi K B) → (A : Ty Φ K) → Term Γ B[[A]]'₀
  | pair : Term Γ A → Term Γ B → Term Γ (.pair A B)
  | p₁ : Term Γ (.pair A B) → Term Γ A
  | p₂ : Term Γ (.pair A B) → Term Γ B
infix : 26 " ⊢ " => Term

syntax "ƛ " term " => " term : term
macro_rules
  | `(ƛ $t => $e) => `(Term.lam $t $e)
infixl : 80 " @ " => Term.app

def Ren'.nil : Ren' Φ .nil :=
  fun K i => by contradiction

def Ren'.nil_lemma : (ρ' : Ren' Φ .nil) → ρ' = Ren'.nil := by
  intro ρ'
  funext K i
  contradiction

-- def wk'_sub'₀ : (A B : SystemF.Ty Φ *) → (A.wk')[[B]]'₀ = A := by
--   intro A B
--   cases A with
--   | var i => simp [Ty.sub'₀, Ty.wk', Ren'.wk, Ty.sub', Sub'.extend, Sub'.id]
--   | unit => simp [Ty.sub'₀, Ty.wk', Ren'.wk, Ty.sub', Sub'.extend, Sub'.id]
--   | bool => simp [Ty.sub'₀, Ty.wk', Ren'.wk, Ty.sub', Sub'.extend, Sub'.id]
--   | fn A B =>
--     simp [Ty.sub'₀, Ty.wk', Ty.sub']
--     constructor
--     apply wk'_sub'₀
--     apply wk'_sub'₀
--   | pi K A =>
--     simp [Ty.sub'₀, Ty.wk', Ty.sub']
--     sorry
--   | pair A B =>
--     simp [Ty.sub'₀, Ty.wk', Ty.sub']
--     constructor
--     apply wk'_sub'₀
--     apply wk'_sub'₀


end SystemF
