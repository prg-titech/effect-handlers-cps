
class ProdNotation (α : Type): Type where
  prod : α → α → α
infixl : 28 " ⊗ " => ProdNotation.prod
attribute [match_pattern] ProdNotation.prod
class FnNotation (α : outParam Type) (β : outParam Type) (γ : Type): Type where
  fn : α → β → γ
infixr : 26 (priority:=high) " ⇒ " => FnNotation.fn
attribute [simp, match_pattern] FnNotation.fn

class SumNotation (α : Type): Type where
  sum : α → α → α
infix : 27 " ⨁ " => SumNotation.sum
attribute [match_pattern] SumNotation.sum
