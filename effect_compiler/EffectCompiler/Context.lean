

inductive Context : (Ty : Type) → Type where
  | nil : Context Ty
  | cons : Context Ty → Ty → Context Ty
  deriving BEq, DecidableEq, Repr
infixl:67 "; " => Context.cons

namespace Context

def concat {Ty} : Context Ty → Context Ty → Context Ty
  | Γ, .nil => Γ
  | Γ, Δ; A => (concat Γ Δ); A
infixl : 61 " ;; " => concat

@[simp]
def length (Γ : Context Ty) : Nat :=
  match Γ with
  | nil       => 0
  | cons Γ _A => Nat.succ Γ.length

def nil_concat : {Γ : Context Ty} → .nil ;; Γ = Γ
  | .nil => rfl
  | _; _ => by
    simp [concat]
    exact nil_concat
  -- congrArg₂ Context.cons nil_concat rfl


-- def ext? : (Γ' : Context Ty) → (Γ : Context Ty) → Option (Σ' Δ, Γ' = Γ ;; Δ)
--   | .nil, Γ => .none
--   | Δ; A, Γ =>
--     if h : (Δ; A) = Γ then
--       .some ⟨.nil, h⟩
--     else
--       match ext? Δ Γ with
--       | .some ⟨Γ', hΔ⟩ => .some ⟨Γ'; A, by simp [hΔ]; rfl⟩
--       | .none => .none

def size : Context Ty → Nat
  | .nil => 0
  | Δ; _ => Δ.size + 1

end Context

inductive Member : (Γ : Context Ty) → (A : Ty) → Type where
  | zero  : Member (Γ; A) A
  | succ  : Member Γ A → Member (Γ; B) A
  deriving BEq, DecidableEq, Repr
infix: 60 " ∋ " => Member

namespace Member

@[app_unexpander zero]
def zero.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_) => `(0)
@[app_unexpander succ]
def succ.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $n:num) =>
    let m := Nat.succ n.getNat
    let t := Lean.Syntax.mkNumLit $ toString m
    `($t)
  | _ => throw ()

@[simp]
def size : Γ ∋ A → Nat
  | .zero => 0
  | .succ x => x.size + 1

def asFin : Γ ∋ A → Fin Γ.length
  | .zero => ⟨0, by simp [Context.length]⟩
  | .succ x => .succ x.asFin

-- x : Γ ∋ A ↔ (Γ, x.size)

def cut : {Γ' : Context Ty} → (x : Γ; B ;; Γ' ∋ A) → x.size ≠ Γ'.size → Γ ;; Γ' ∋ A
  | .nil, .succ x, h => x
  | Γ'; C, .zero, h => .zero
  | Γ'; C, .succ x, h =>
    have h' : size x ≠ Context.size Γ' := by {
      intro hneq
      simp [size, Context.size] at h
      exact h hneq
    }
    .succ (x.cut h')

end Member

def Context.get {Ty} : (Γ : Context Ty) → Fin Γ.length → Ty
  | cons _ A,  ⟨0, _⟩ => A
  | cons Γ _, ⟨Nat.succ i, h⟩ => get Γ ⟨i, Nat.le_of_succ_le_succ h⟩

def Context.get' {Ty} : (Γ : Context Ty) → (n: Fin Γ.length) → Γ ∋ (Γ.get n)
  | cons _ _,  ⟨0, _⟩ => .zero
  | cons Γ _, ⟨Nat.succ i, h⟩ => .succ (get' Γ ⟨i, Nat.le_of_succ_le_succ h⟩)

def Context.get_sizeOf {Ty} : (Γ : Context Ty) → (i : Fin Γ.length) → sizeOf (Γ.get i) < sizeOf Γ := by
  intro Γ i
  induction Γ with
  | nil => exact Fin.elim0 i
  | cons Γ A _ =>
    simp_arith

def Context.get_eq {Ty} {A} : (Γ : Context Ty) → (i : Γ ∋ A) →  Γ.get i.asFin = A
  | .nil, i => by contradiction
  | .cons Γ B, .zero => rfl
  | .cons Γ B, .succ i => by
    simp [get]
    apply get_eq
