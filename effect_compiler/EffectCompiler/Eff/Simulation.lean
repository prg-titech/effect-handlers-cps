
import EffectCompiler.Eff.Comp2
import EffectCompiler.Eff.SmallStep

import Lean.Elab.Tactic.LibrarySearch

namespace Eff

def Cmp.comp {Γ} {A} : Γ ⊢c A → ∅ / ⟦Γ⟧v ⊢ .pi (.fn (⟦A⟧⇛(.var .zero)) (.var .zero)) :=
  fun t => by
  apply SystemF.Term.lamₜ
  apply SystemF.Term.lam
  apply trans t _ (.var .zero)
  exact SystemF.Renameₜ.nil
  intro C i
  apply SystemF.Con.Member.succ
  rw [←SystemF.Renameₜ.nil_eta (ρ':=.succ)]
  apply SystemF.Con.Member.renameₜ
  assumption
  -- .lamₜ (.lam _ )



set_option pp.proofs true
def trans.simulation {t t' : Γ ⊢c A} : SmallStep t t' → (t.trans ρ h ⟶ₛ+ t'.trans ρ h) := by
  rename_i Φ Γ' ρₜ B
  intro htt'
  induction htt' with
  | β_ifte_true =>
    simp [Cmp.trans, Val.trans, SystemF.Term.rename]
    constructor
    have := @Cmp.trans.proof_14 Φ ρₜ
    sorry
    -- apply SystemF.SmallStep.β_ifte₁
  | β_ifte_false =>
    simp [Cmp.trans, Val.trans, SystemF.Term.rename]
    constructor
    apply SystemF.SmallStep.β_ifte₂
  | β_app =>
    simp [Cmp.trans]
    simp [Val.trans]
    rename_i Δ A' V e v
    apply Relation.TransGen.tail
    constructor
    apply SystemF.SmallStep.ξ_app₁
    rw [Eq.rec_eq_cast]
  | ξ_handle hss' => sorry
  | β_handle_return => sorry
  | β_handle_op => sorry
  -- cases t with
  -- | «return» v => sorry
  -- | op i v e => sorry
  -- | app v₁ v₂ => sorry
  -- | ifte v e e' => sorry
  -- | handle_with e v => sorry
def comp.simulation {t t' : Γ ⊢c A} : SmallStep t t' → (t.comp ⟶ₛ+ t'.comp) := sorry

end Eff
