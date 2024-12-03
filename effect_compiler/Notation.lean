
class ProdNotation (α : Type): Type where
  prod : α → α → α
infixl : 28 " ⊗ " => ProdNotation.prod
attribute [match_pattern] ProdNotation.prod
class FnNotation (α : Type): Type where
  fn : α → α → α
infixr : 26 (priority:=high) " ⇒ " => FnNotation.fn
attribute [match_pattern] FnNotation.fn
class BoxNotation (α : Type): Type where
  box : α → α
prefix : max "□" => BoxNotation.box
attribute [match_pattern] BoxNotation.box
class SumNotation (α : Type): Type where
  sum : α → α → α 
infix : 27 " ⨁ " => SumNotation.sum
attribute [match_pattern] SumNotation.sum


class PAdd (α : Type) (β : Type) (γ : outParam (β → Type)) where
  padd : α → (b : β) → γ b
infixl : 80 " ⁺ " => PAdd.padd
class PAddAdd (α : Type) (β : Type) (γ : outParam (β → Type)) where
  paddadd : α → (b : β) → γ b
infixl : 80 " ⁺⁺ " => PAddAdd.paddadd