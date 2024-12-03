
import EffectCompiler.SystemF.Basic

import Mathlib.Logic.Function.Basic


namespace SystemF

@[simp]
def Con.num_var : Con Φ → Nat
  | .nil => 0
  | .cons Γ _ => Γ.num_var + 1
  | .cons' Γ _ => Γ.num_var + 1

def Con.Member.ith? : {Γ : Con Φ} →  Γ ∋ A → Fin Γ.num_var
  | _, .zero => ⟨0, by simp⟩
  | _, .succ i =>
    let ⟨i, isLt⟩ := i.ith?
    ⟨i+1, by simp_arith; assumption⟩
  | _, .succ' i =>
    let ⟨i, isLt⟩ := i.ith?
    ⟨i+1, by simp_arith; assumption⟩

#check Fin.val_eq_of_eq
#check Fin.eq_of_val_eq
def Con.Member.ith?_inj : {Γ : Con Φ} → Function.Injective (ith? (Γ:=Γ) (A:=A)) := by {
  intro Γ i j h
  cases i
  cases j
  rfl
  simp [ith?] at h
  cases h
  cases j
  simp [ith?] at h
  cases h
  simp [ith?] at h
  congr
  exact ith?_inj (Fin.eq_of_val_eq h)
  simp [ith?] at h
  have := Fin.val_eq_of_eq h
  simp at this
}
-- def Con.Member.ith?_inj : {Γ : Con Φ} → (i j : Γ ∋ A) → i.ith? = j.ith? → i = j := by {
--   intro Γ i j h
--   cases i with
--   | zero =>
--     cases j with
--     | zero => rfl
--     | succ j =>
--       simp [ith?] at h
--       cases h
--   | succ i =>
--     cases j with
--     | zero =>
--       simp [ith?] at h
--       cases h
--     | succ j =>
--       simp [ith?] at h
--       sorry
--   | succ' i => sorry
-- }

namespace Untyped

inductive Term : (n : Nat) → Type where
  | var : (i : Fin n) → Term n
  | unit  : Term n
  | p₁ : (ab : Term n) → Term n
  | p₂ : (ab : Term n) → Term n
  | pair : (a : Term n) → (b : Term n) → Term n
  | true : Term n
  | false : Term n
  | ifte : Term n → Term n → Term n → Term n
  | lam : Term (n + 1) → Term n
  | app : Term n → Term n → Term n

end Untyped

def Term.erase : Γ ⊢ A → Untyped.Term Γ.num_var
  | .var i => .var i.ith?
  | .unit => .unit
  | .p₁ ab => .p₁ ab.erase
  | .p₂ ab => .p₂ ab.erase
  | .pair a b => .pair a.erase b.erase
  | .true => .true
  | .false => .false
  | .ifte b t e => .ifte b.erase t.erase e.erase
  | .lam _ e => .lam e.erase
  | .app f x => .app f.erase x.erase
  | .Lam _ e => .lam e.erase
  | .App f A => .app f.erase .unit

def Term.erase_inj {t t' : Γ ⊢ A} : t.erase = t'.erase → t = t' := by {
  intro htt'
  induction t with
  | var i =>
    cases t'
    all_goals simp [erase] at htt'
    congr
  | _ => sorry
}

end SystemF
