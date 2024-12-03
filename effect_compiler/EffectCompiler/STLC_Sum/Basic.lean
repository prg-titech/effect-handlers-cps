
import EffectCompiler.Context
import EffectCompiler.Notation


namespace STLC_Sum

inductive Ty where
  | unit  : Ty
  | prod  : Ty → Ty → Ty
  | fn    : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  deriving BEq, DecidableEq, Repr
notation : max "𝟙" => Ty.unit
instance : ProdNotation Ty where
  prod := Ty.prod
instance : SumNotation Ty where
  sum := Ty.sum
instance : FnNotation Ty Ty Ty where
  fn := Ty.fn


namespace Ty
def size : Ty → Nat
  | 𝟙 => 1
  | A ⊗ B => A.size + B.size + 1
  | A ⇒ B => A.size + B.size + 1
  | A ⨁ B => A.size + B.size + 1

@[simp]
theorem one_le_size {A : Ty}: 1 ≤ A.size := by
  cases A with
  | unit => trivial
  | prod A B =>
    simp [size]
  | fn A B =>
    simp [size]
  | sum A B =>
    simp [size]

end Ty

inductive Term : (Γ: Context Ty) → (A : Ty) → Type
  | var       : Γ ∋ A → Term Γ A
  | unit      : Term Γ 𝟙
  | pair  : Term Γ A → Term Γ B → Term Γ (.prod A B)
  | p₁    : Term Γ (.prod A B) → Term Γ A
  | p₂    : Term Γ (.prod A B) → Term Γ B
  | lam       : (A : Ty) → Term (Γ; A) B → Term Γ (A ⇒ B)
  | app       : Term Γ (A ⇒ B) → Term Γ A → Term Γ B
  | inl : Term Γ A → Term Γ (A ⨁ B)
  | inr : Term Γ B → Term Γ (A ⨁ B)
  | case : Term Γ (A ⨁ B) → Term (Γ; A) C → Term (Γ; B) C → Term Γ C
  deriving Repr
infix : 26 " ⊢ " => Term

syntax "ƛ " term " => " term : term
macro_rules
  | `(ƛ $t => $e) => `(Term.lam $t $e)
infixl : 80 " @ " => Term.app

namespace Term

def inhabitant : (A : Ty) → Γ ⊢ A
  | 𝟙 => .unit
  | A ⊗ B => .pair (inhabitant A) (inhabitant B)
  | A ⇒ B => .lam A (inhabitant B)
  | A ⨁ _ => .inl (inhabitant A)

instance : Inhabited (Γ ⊢ A) where
  default := inhabitant A

@[simp]
def size : Γ ⊢ A → Nat
  | .unit => 1
  | .var x => x.size
  | .pair a b => a.size + b.size + 1
  | .p₁ ab => ab.size + 1
  | .p₂ ab => ab.size + 1
  | .lam _ e => e.size + 1
  | .app f x => f.size + x.size + 1
  | .inl a => a.size + 1
  | .inr b => b.size + 1
  | .case m a b => m.size + a.size + b.size + 1

@[simp]
def size_var_lt_succ : (Term.var x).size < (Term.var (.succ (B:=B) x)).size := by
  simp [size, Member.size]
end Term

end STLC_Sum
