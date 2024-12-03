
import EffectCompiler.SystemF.Basic
import EffectCompiler.SystemF.Subst

namespace SystemF

inductive Term.SmallStep : Γ ⊢ A → Γ ⊢ A → Prop
  | β_app : SmallStep ((ƛ B => e) @ x) (e.sub0 x)
  | β_App : SmallStep (Term.App (.Lam K e) B) (Term.App (.Lam K e) B)
  | ξ_lam : @SmallStep Φ (Γ; B) A e e' → SmallStep (ƛ B => e) (ƛ B => e')
  | ξ_app₁ : SmallStep f f' → SmallStep (f @ x) (f' @ x)
  | ξ_app₂ : SmallStep x x' → SmallStep (f @ x) (f @ x')

-- inductive SmallStep : Γ ⊢ A → Γ ⊢ A → Prop
inductive Normal : Γ ⊢ A → Prop

-- def Normal.not_prog : Normal t → ∀ t', ¬(SmallStep t t') := sorry
-- def normal_of_not_smallstep : ∀ t', ¬(SmallStep t t') → Normal t := sorry
-- def not_normal_of_smallstep : SmallStep t t' → ¬ Normal t := sorry

end SystemF
