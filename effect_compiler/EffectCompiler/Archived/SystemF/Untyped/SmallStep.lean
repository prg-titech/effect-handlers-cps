
import EffectCompiler.SystemF.Basic
import EffectCompiler.SystemF.SmallStep
import EffectCompiler.SystemF.Untyped.Basic
import EffectCompiler.SystemF.Untyped.Subst

import Mathlib.Logic.Relation


namespace SystemF
namespace Untyped

inductive SmallStep : Term n → Term n → Prop where
  | β_app : SmallStep (.app (.lam e) x) (e.subs0 x)
  | β_p₁ : SmallStep (.p₁ (.pair a b)) a
  | β_p₂ : SmallStep (.p₂ (.pair a b)) b
  | β_ifte₁ : SmallStep (.ifte .true t e) t
  | β_ifte₂ : SmallStep (.ifte .false t e) e
  | ξ_p₁ : SmallStep ab ab' → SmallStep (.p₁ ab) (.p₁ ab')
  | ξ_p₂ : SmallStep ab ab' → SmallStep (.p₂ ab) (.p₂ ab')
  | ξ_pair₁ : SmallStep a a' → SmallStep (.pair a b) (.pair a' b)
  | ξ_pair₂ : SmallStep b b' → SmallStep (.pair a b) (.pair a b')
  | ξ_ifte₁ : SmallStep b b' → SmallStep (.ifte b t e) (.ifte b' t e)
  | ξ_ifte₂ : SmallStep t t' → SmallStep (.ifte b t e) (.ifte b t' e)
  | ξ_ifte₃ : SmallStep e e' → SmallStep (.ifte b t e) (.ifte b t e')
  | ξ_lam : SmallStep e e' → SmallStep (.lam e) (.lam e')
  | ξ_app₁ : SmallStep f f' → SmallStep (.app f x) (.app f' x)
  | ξ_app₂ : SmallStep x x' → SmallStep (.app f x) (.app f x')

inductive Normal : Term n → Prop
def Normal.not_prog : Normal t → ∀ t', ¬(SmallStep t t') := sorry
def normal_of_not_smallstep : ∀ t', ¬(SmallStep t t') → Normal t := sorry
def not_normal_of_smallstep : SmallStep t t' → ¬ Normal t := sorry

end Untyped

def erase_lemma : (t : Γ ⊢ A) → (u : Untyped.Term Γ.num_var) → t.erase = u → (Normal t ∧ Untyped.Normal u) ∨ (∃ t' : Γ ⊢ A, ∃ u', t'.erase = u' ∧ SmallStep t t' ∧ Untyped.SmallStep u u'):= sorry

def erase_lemma' (t : Γ ⊢ A) : Untyped.SmallStep t.erase u' → ∃ t' : Γ ⊢ A, t'.erase = u' ∧ SmallStep t t' := by {
  intro h
  let u := t.erase
  have htu : t.erase = u := by trivial
  have := erase_lemma t u htu
  cases this with
  | inl h' =>
    have := htu ▸ Untyped.not_normal_of_smallstep h
    have ⟨_, _⟩ := h'
    contradiction
  | inr h' =>
    have ⟨t', u', ht'u', htt', huu'⟩ := h'
    exists t'
}

def erase_lemma'' (t : Γ ⊢ A) : Relation.ReflTransGen Untyped.SmallStep t.erase u' → ∃ t' : Γ ⊢ A, t'.erase = u' ∧ Relation.ReflTransGen SmallStep t t' := by {
  intro h
  induction h with
  | refl =>
    exists t
  | tail h hu₁u₂ ih =>
    rename_i _ u₁ u₂
    let ⟨t', ht'u₁, htt'⟩ := ih
    have ⟨t'', ht''u₂, ht't''⟩:= erase_lemma' t' (ht'u₁ ▸ hu₁u₂)
    exists t''
}

def erase_lemma₃ (t t': Γ ⊢ A) : Untyped.SmallStep t.erase t'.erase → SmallStep t t' := by {
  intro h
  have ⟨t₁, _⟩ := erase_lemma' t h
}

end SystemF
