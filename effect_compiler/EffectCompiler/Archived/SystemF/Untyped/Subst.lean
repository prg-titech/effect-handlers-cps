
import EffectCompiler.SystemF.Basic
import EffectCompiler.SystemF.Untyped.Basic


namespace SystemF
namespace Untyped

def Ren (n : Nat) (m : Nat) := Fin m → Fin n
def Subs (n : Nat) (m : Nat) := Fin m → Term n

def Ren.lift : Ren n m → Ren (n + 1) (m + 1)
  | ρ, i => i.cases
    0
    fun i => .succ (ρ i)
def Ren.id : Ren n n := _root_.id
def Ren.wk : Ren n m → Ren (n + 1) m
  | ρ, i => .succ (ρ i)

def Term.rename : Term m → Ren n m → Term n
  | .var i, ρ => .var <| ρ i
  | .unit, _ => .unit
  | .p₁ ab, ρ => .p₁ (ab.rename ρ)
  | .p₂ ab, ρ => .p₂ (ab.rename ρ)
  | .pair a b, ρ => .pair (a.rename ρ) (b.rename ρ)
  | .true, _ => .true
  | .false, _ => .false
  | .ifte b t e, ρ => .ifte (b.rename ρ) (t.rename ρ) (e.rename ρ)
  | .lam e, ρ => .lam (e.rename ρ.lift)
  | .app f x, ρ => .app (f.rename ρ) (x.rename ρ)
def Term.wk : Term n → Term (n + 1)
  | t => t.rename Ren.id.wk

def Subs.lift : Subs n m → Subs (n + 1) (m + 1)
  | σ, i => i.cases
    (.var 0)
    fun i => (σ i).wk
def Subs.id : Subs n n := (.var ·)
def Subs.wk : Subs n m → Subs (n + 1) m
  | σ, i => (σ i).wk
def Subs.cons : Subs n m → Term n → Subs n (m + 1)
  | σ, s, i => i.cases
    s
    fun i => (σ i)

def Term.subs : Term m → Subs n m → Term n
  | .var i, σ => σ i
  | .unit, _ => .unit
  | .p₁ ab, σ => .p₁ (ab.subs σ)
  | .p₂ ab, σ => .p₂ (ab.subs σ)
  | .pair a b, σ => .pair (a.subs σ) (b.subs σ)
  | .true, _ => .true
  | .false, _ => .false
  | .ifte b t e, σ => .ifte (b.subs σ) (t.subs σ) (e.subs σ)
  | .lam e, σ => .lam (e.subs σ.lift)
  | .app f x, σ => .app (f.subs σ) (x.subs σ)

def Term.subs0 : Term (n + 1) → Term n → Term n
  | t, s => t.subs (Subs.id.cons s)


end Untyped
end SystemF
