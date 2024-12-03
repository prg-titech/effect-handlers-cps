
import EffHps.Notation

import Batteries.Logic
import Batteries.Data.Vector
import Mathlib.Logic.Relation

open Relation
open Batteries

namespace SystemF


inductive Kind where
  | star : Kind

inductive ty (Varₜ : Type) : Type where
  | var : Varₜ → ty Varₜ
  | unit : ty Varₜ
  | pair : ty Varₜ → ty Varₜ → ty Varₜ
  | record : (Fin n → ty Varₜ) → ty Varₜ
  | bool : ty Varₜ
  | fn : ty Varₜ → ty Varₜ → ty Varₜ
  | pi : (Varₜ  → ty Varₜ) → ty Varₜ

def ty.squash : ty (ty Varₜ) → ty Varₜ
  | .var e => e
  | .unit => .unit
  | .pair a b => .pair a.squash b.squash
  | .record f => .record (fun i => (f i).squash)
  | .bool => .bool
  | .fn A B => .fn A.squash B.squash
  | .pi f => .pi fun B => (f (.var B)).squash


def Ty := {Varₜ : Type} → ty Varₜ

-- 1 free variable
def Ty₁ := {Varₜ : Type} → Varₜ → ty Varₜ

def Ty.subst : Ty₁ → Ty → Ty :=
  fun s t => (s t).squash

example : Ty.subst (fun X => ty.var X) .unit = .unit (Varₜ:=Varₜ) := rfl


inductive Term (Var : ty Varₜ → Type) : ty Varₜ → Type  where
  | var : Var T → Term Var T
  | unit : Term Var .unit
  | pair : Term Var A → Term Var B → Term Var (.pair A B)
  | p₁ : Term Var (.pair A B) → Term Var A
  | p₂ : Term Var (.pair A B) → Term Var B
  | record : ((i : Fin n) → Term Var (f i)) → Term Var (.record f)
  | proj : Term Var (.record f) → (i : Fin _) → Term Var (f i)
  | ifte : Term Var .bool → Term Var A → Term Var A → Term Var A
  | true : Term Var .bool
  | false : Term Var .bool
  | lam : (A : ty Varₜ) → (Var A → Term Var B) → Term Var (.fn A B)
  | app : Term Var (.fn A B) → Term Var A → Term Var B
  | lamₜ : {f : Varₜ → ty Varₜ} → ((A : Varₜ) → Term Var (f A)) → Term Var (.pi fun A => f A)
  -- | appₜ : Term Var (.pi f) → (B : ty Varₜ) → Term Var _

example {Varₜ : Type} {Var : ty Varₜ → Type} {A B : ty Varₜ} : Term Var (.fn A (.fn B A)) := .lam A fun x => .lam B fun y => .var x
example {Varₜ : Type} {Var : ty Varₜ → Type} : Term Var (.pi fun X => (.fn (.var X) (.var X))) :=
  .lamₜ fun A => .lam (.var A) fun x => .var x


def Term.squash : Term (Term Var) A → Term Var A
  | .var i => i
  | .unit => .unit
  | .pair a b => .pair a.squash b.squash
  | .p₁ ab => .p₁ ab.squash
  | .p₂ ab => .p₂ ab.squash
  | .record f => .record (fun i => (f i).squash)
  | .proj (f:=f) r i => .proj r.squash i
  | .true => .true
  | .false => .false
  | .ifte b t e => .ifte b.squash t.squash e.squash
  | .lam A f => .lam A fun x => (f (.var x)).squash
  | .app f e => .app f.squash e.squash
  | .lamₜ f => .lamₜ fun A => (f A).squash

-- 1 free variable
def Term₁ {Varₜ : Type} (A B : ty Varₜ) := {Var : ty Varₜ → Type} → (Var A → Term Var B)

def Term.subst : Term₁ A B → Term Var A → Term Var B :=
  fun s t => (s t).squash

example {Varₜ} {A : ty Varₜ} {Var} : (Term.lam (Var:=Var) A fun x => .var x) = (Term.lam A fun x => .var x) := rfl
example {Varₜ} {A : ty Varₜ} {Var : ty Varₜ → Type} : Term.subst (fun x => .var x) .unit = .unit (Var:=Var) := rfl

def Varₜ : Type := sorry
def Var : ty Varₜ → Type := sorry

-- def Renameₜ (Ψ Φ : Conₜ) := Φ∋* → Ψ∋*
-- def Substₜ (Ψ Φ : Conₜ) := Φ∋* → Ty Ψ

-- def Renameₜ.extend {Ψ Φ} : Renameₜ Ψ Φ → Renameₜ (Ψ;*) (Φ;*)
--   | _, .zero => .zero
--   | ρₜ, .succ i => .succ (ρₜ i)

-- def Renameₜ.id : (Φ : Conₜ) → Renameₜ Φ Φ := fun _ => _root_.id
-- prefix : max "𝟙ᵣₜ" => Renameₜ.id

-- def Renameₜ.id_extend {Φ} : (𝟙ᵣₜ Φ).extend = 𝟙ᵣₜ (Φ;*) := by
--   funext i
--   cases i
--   all_goals simp [extend, id]

-- def Renameₜ.nil : ∀ {Φ}, Renameₜ Φ ∅ :=
--   fun _ => by contradiction

-- def Renameₜ.nil_eta {Φ} : (ρ' : Renameₜ Φ ∅) → ρ' = Renameₜ.nil := by
--   intro ρ'
--   funext i
--   contradiction


-- def Ty.renameₜ {Ψ Φ} : Ty Φ → Renameₜ Ψ Φ → Ty Ψ
--   | .var i, ρₜ => .var (ρₜ i)
--   | .unit, _ => .unit
--   | .record f, ρ => .record (fun i => (f i).renameₜ ρ)
--   | .pair A B, ρₜ => .pair (A.renameₜ ρₜ) (B.renameₜ ρₜ)
--   | .bool, _ => .bool
--   | .fn A B, ρₜ => .fn (A.renameₜ ρₜ) (B.renameₜ ρₜ)
--   | .pi A, ρₜ => .pi (A.renameₜ ρₜ.extend)
-- notation : max A "{{" ρₜ "}}ᵣₜ" => Ty.renameₜ A ρₜ

-- def Renameₜ.id_rfl {Φ} : {A : Ty Φ} → A{{𝟙ᵣₜ _}}ᵣₜ = A
--   | .var i => rfl
--   | .unit => rfl
--   | .bool => rfl
--   | .record f => by
--     simp [Ty.renameₜ]
--     funext i
--     apply id_rfl
--   | .fn A B => by
--     simp [Ty.renameₜ]
--     constructor
--     apply id_rfl
--     apply id_rfl
--   | .pi A => by
--     simp [Ty.renameₜ]
--     rw [id_extend]
--     apply id_rfl
--   | .pair A B => by
--     simp [Ty.renameₜ]
--     constructor
--     apply id_rfl
--     apply id_rfl

-- def Ty.wk {Φ} : Ty Φ → Ty (Φ;*) := fun t => (t.renameₜ .succ)

-- def Substₜ.extend {Ψ Φ} : Substₜ Ψ Φ → Substₜ (Ψ;*) (Φ;*)
--   | _, .zero => .var .zero
--   | σₜ, .succ i => (σₜ i).wk

-- def Ty.substₜ {Ψ Φ} : Ty Φ → Substₜ Ψ Φ → Ty Ψ
--   | .var i, σₜ => σₜ i
--   | .unit, _ => .unit
--   | .record f, σₜ => .record (fun i => (f i).substₜ σₜ)
--   | .pair A B, σₜ => .pair (A.substₜ σₜ) (B.substₜ σₜ)
--   | .bool, _ => .bool
--   | .fn A B, σₜ => .fn (A.substₜ σₜ) (B.substₜ σₜ)
--   | .pi A, σₜ => .pi (A.substₜ σₜ.extend)
-- notation : max A "{{" σₜ "}}ₛₜ" => Ty.substₜ A σₜ

-- def Substₜ.cons {Ψ Φ} : Substₜ Ψ Φ → Ty Ψ → Substₜ Ψ (Φ;*)
--   | _, A, .zero => A
--   | σₜ, _, .succ i => σₜ i
-- notation : 100 σₜ "; " A => Substₜ.cons σₜ A

-- def Substₜ.id : (Φ : Conₜ) → Substₜ Φ Φ := fun _ => (.var ·)
-- prefix : max "𝟙ₛₜ" => Substₜ.id

-- def Ty.substₜ₀ {Φ}: Ty (Φ;*) → Ty Φ → Ty Φ :=
--   fun A B => A{{𝟙ₛₜ _; B}}ₛₜ
-- notation : max A "[[" B "]]ₛₜ" => Ty.substₜ₀ A B

-- def Renameₜ.comp {Φ'' Φ' Φ} : Renameₜ Φ'' Φ' → Renameₜ Φ' Φ → Renameₜ Φ'' Φ :=
--   fun ρₜ' ρₜ => ρₜ' ∘ ρₜ

-- def Substₜ.comp {Φ'' Φ' Φ} : Substₜ Φ'' Φ' → Substₜ Φ' Φ → Substₜ Φ'' Φ :=
--   fun σₜ' σₜ i => (σₜ i).substₜ σₜ'

-- def Substₜ.compᵣₛ {Φ'' Φ' Φ} : Renameₜ Φ'' Φ' → Substₜ Φ' Φ → Substₜ Φ'' Φ :=
--   fun ρₜ σₜ i => (σₜ i).renameₜ ρₜ
-- def Substₜ.compₛᵣ {Φ'' Φ' Φ} : Substₜ Φ'' Φ' → Renameₜ Φ' Φ → Substₜ Φ'' Φ :=
--   fun σₜ ρₜ => σₜ ∘ ρₜ

-- def Renameₜ.extend_comp {Φ'' Φ' Φ} {f : Renameₜ Φ'' Φ'} {g : Renameₜ Φ' Φ} : extend (comp f g) = comp f.extend g.extend :=
--   funext fun i =>
--   match i with
--   | .zero => rfl
--   | .succ _ => rfl

-- def Renameₜ.ren_comp {Φ'' Φ' Φ} {ρₜ' : Renameₜ Φ'' Φ'} {ρₜ : Renameₜ Φ' Φ} : {t : Ty Φ} → t{{comp ρₜ' ρₜ}}ᵣₜ = t{{ρₜ}}ᵣₜ{{ρₜ'}}ᵣₜ
--   | .var _ => rfl
--   | .unit => rfl
--   | .bool => rfl
--   | .record f => by
--     simp [Ty.renameₜ]
--     funext i
--     apply ren_comp
--   | .fn _ _ => congrArg₂ Ty.fn ren_comp ren_comp
--   | .pi _ => congrArg Ty.pi (Eq.trans (congrArg _ extend_comp) ren_comp)
--   | .pair _ _  => congrArg₂ Ty.pair ren_comp ren_comp

-- def Substₜ.extend_compᵣₛ {Φ'' Φ' Φ} {f : Renameₜ Φ'' Φ'} {g : Substₜ Φ' Φ} : extend (Substₜ.compᵣₛ f g) = compᵣₛ f.extend g.extend :=
--   funext fun i =>
--   match i with
--   | .zero => rfl
--   | .succ _ => by
--     simp [extend, compᵣₛ, Ty.wk]
--     rw [←Renameₜ.ren_comp, ←Renameₜ.ren_comp]
--     rfl
-- def Substₜ.extend_compₛᵣ {Φ'' Φ' Φ} {f : Substₜ Φ'' Φ'} {g : Renameₜ Φ' Φ} : extend (Substₜ.compₛᵣ f g) = compₛᵣ f.extend g.extend :=
--   funext fun i =>
--   match i with
--   | .zero => rfl
--   | .succ _ => rfl

-- def Substₜ.subs_compᵣₛ : {t : Ty Φ} → t{{compᵣₛ ρₜ σₜ}}ₛₜ = t{{σₜ}}ₛₜ{{ρₜ}}ᵣₜ
--   | .var _ => rfl
--   | .unit => rfl
--   | .bool => rfl
--   | .record f => by
--     simp [Ty.substₜ, Ty.renameₜ]
--     funext i
--     apply subs_compᵣₛ
--   | .fn _ _ => congrArg₂ Ty.fn subs_compᵣₛ subs_compᵣₛ
--   | .pi _ => congrArg Ty.pi (Eq.trans (congrArg _ extend_compᵣₛ) subs_compᵣₛ)
--   | .pair _ _  => congrArg₂ Ty.pair subs_compᵣₛ subs_compᵣₛ
-- def Substₜ.subs_compₛᵣ : {t : Ty Φ} → t{{compₛᵣ σₜ ρₜ}}ₛₜ = t{{ρₜ}}ᵣₜ{{σₜ}}ₛₜ
--   | .var _ => rfl
--   | .unit => rfl
--   | .bool => rfl
--   | .record f => by
--     simp [Ty.substₜ, Ty.renameₜ]
--     funext i
--     apply subs_compₛᵣ
--   | .fn _ _ => congrArg₂ Ty.fn subs_compₛᵣ subs_compₛᵣ
--   | .pi _ => congrArg Ty.pi (Eq.trans (congrArg _ extend_compₛᵣ) subs_compₛᵣ)
--   | .pair _ _  => congrArg₂ Ty.pair subs_compₛᵣ subs_compₛᵣ

-- def Substₜ.extend_comp : extend (Substₜ.comp f g) = comp f.extend g.extend :=
--   funext fun i =>
--   match i with
--   | .zero => rfl
--   | .succ _ => by
--     simp [extend, comp, Ty.wk]
--     rw [←subs_compᵣₛ, ←subs_compₛᵣ]
--     rfl

-- def Substₜ.subs_comp : {t : Ty Φ} → t{{comp σₜ σₜ'}}ₛₜ = t{{σₜ'}}ₛₜ{{σₜ}}ₛₜ
--   | .var _ => rfl
--   | .unit => rfl
--   | .bool => rfl
--   | .record f => by
--     simp [Ty.substₜ]
--     funext i
--     apply subs_comp
--   | .fn _ _ => congrArg₂ Ty.fn subs_comp subs_comp
--   | .pi _ => congrArg Ty.pi (Eq.trans (congrArg _ extend_comp) subs_comp)
--   | .pair _ _  => congrArg₂ Ty.pair subs_comp subs_comp

-- def Substₜ.substₜ₀_renameₜ : {A : Ty _} → A[[B]]ₛₜ{{ρₜ}}ᵣₜ = A{{ρₜ.extend}}ᵣₜ[[B{{ρₜ}}ᵣₜ]]ₛₜ := by
--   intro A
--   simp [Ty.substₜ₀]
--   rw [←Substₜ.subs_compᵣₛ]
--   rw [←Substₜ.subs_compₛᵣ]
--   congr
--   funext i
--   cases i with
--   | zero => rfl
--   | succ i => rfl

-- def Substₜ.id_extend : (𝟙ₛₜ Φ).extend = 𝟙ₛₜ _ :=
--   funext fun i =>
--   match i with
--   | .zero => rfl
--   | .succ _ => rfl

-- def Substₜ.subs_id : {t : Ty Φ} → t{{𝟙ₛₜ _}}ₛₜ = t
--   | .var _ => rfl
--   | .unit => rfl
--   | .bool => rfl
--   | .record f => by
--     simp [Ty.substₜ]
--     funext i
--     apply subs_id
--   | .fn _ _ => congrArg₂ Ty.fn subs_id subs_id
--   | .pi _ => congrArg Ty.pi (Eq.trans (congrArg _ id_extend) subs_id)
--   | .pair _ _  => congrArg₂ Ty.pair subs_id subs_id

-- def Substₜ.of_Renameₜ : Renameₜ Ψ Φ → Substₜ Ψ Φ
--   | ρₜ => fun i => .var <| ρₜ i
-- def Substₜ.of_Renameₜ_extend : extend (of_Renameₜ ρₜ) = of_Renameₜ ρₜ.extend := by
--   funext i
--   cases i with
--   | zero => rfl
--   | succ i => rfl
-- def Substₜ.of_Renameₜ_lemma : {A : Ty Φ} → A{{of_Renameₜ ρₜ}}ₛₜ = A{{ρₜ}}ᵣₜ
--   | .var _ => rfl
--   | .unit => rfl
--   | .bool => rfl
--   | .record f => by
--     simp [Ty.substₜ, Ty.renameₜ]
--     funext i
--     apply of_Renameₜ_lemma
--   | .fn _ _ => congrArg₂ Ty.fn of_Renameₜ_lemma of_Renameₜ_lemma
--   | .pi A => congrArg Ty.pi (Eq.trans (congrArg (A.substₜ ·) of_Renameₜ_extend) of_Renameₜ_lemma)
--   | .pair _ _ => congrArg₂ Ty.pair of_Renameₜ_lemma of_Renameₜ_lemma

-- def Substₜ.nil : ∀ {Φ}, Substₜ Φ ∅ :=
--   fun i => by contradiction

-- def Substₜ.nil_eta : (σₜ : Substₜ Φ ∅) → σ' = Substₜ.nil := by
--   intro _
--   funext i
--   contradiction

-- def nil_ren_sub' : (A : Ty ∅) → A{{Renameₜ.nil}}ᵣₜ{{σ}}ₛₜ = A{{Substₜ.nil}}ₛₜ := by
--   intro A
--   rw [←Substₜ.subs_compₛᵣ]
--   congr
--   rw [←Substₜ.nil_eta (σₜ:=σ.compₛᵣ Renameₜ.nil)]
-- def nil_ren_sub : (A : Ty ∅) → A{{Renameₜ.nil}}ᵣₜ{{σ}}ₛₜ = A{{Renameₜ.nil}}ᵣₜ := by
--   intro A
--   rw [nil_ren_sub', ←Substₜ.of_Renameₜ_lemma]
--   congr
--   rw [←Substₜ.nil_eta (σₜ:=Substₜ.of_Renameₜ Renameₜ.nil)]
--   assumption

-- inductive Con : Conₜ → Type where
--   | nil : Con Φ
--   | cons : Con Φ → Ty Φ → Con Φ
-- infixl : 90 "; " => Con.cons
-- namespace Con

-- def renameₜ : Con Φ → Renameₜ Ψ Φ → Con Ψ
--   | .nil, _ => .nil
--   | .cons Γ A, ρₜ => Γ.renameₜ ρₜ ; A.renameₜ ρₜ
-- notation : max Γ "{{" ρₜ "}}ᵣₜ" => Con.renameₜ Γ ρₜ

-- def wk : Con Φ → Con (Φ;*) := (·.renameₜ .succ)
-- def substₜ : Con Φ → Substₜ Ψ Φ → Con Ψ
--   | .nil, _ => .nil
--   | .cons Γ A, σₜ => Γ.substₜ σₜ ; A.substₜ σₜ
-- notation : max Γ "{{" σₜ "}}ₛₜ" => Con.substₜ Γ σₜ

-- def substₜ₀ : Con (Φ;*) → Ty Φ → Con Φ :=
--   fun Γ B => Γ{{𝟙ₛₜ _; B}}ₛₜ
-- notation : max Γ "[[" B "]]ₛₜ" => Con.substₜ₀ Γ B

-- inductive Member : (Φ : Conₜ) → Con Φ → Ty Φ → Type where
--   | zero : Member Φ (Γ; A) A
--   | succ : Member Φ Γ A → Member Φ (Γ; B) A
-- notation : 90 Φ: 90 " / " Γ: 90 " ∋ " A: 90 => Member Φ Γ A

-- def Member.renameₜ : Φ / Γ ∋ A → (ρₜ : Renameₜ Ψ Φ) → Ψ / Γ.renameₜ ρₜ ∋ A.renameₜ ρₜ
--   | .zero, ρₜ => .zero
--   | .succ i, ρₜ => .succ (i.renameₜ ρₜ)
-- notation : max i "{{" ρₜ "}}ᵣₜ" => Member.renameₜ i ρₜ
-- def Member.wk : Φ / Γ ∋ A → Φ;* / Γ.wk ∋ A.wk :=
--   fun i => i.renameₜ .succ

-- def Member.substₜ : Φ / Γ ∋ A → (σₜ : Substₜ Ψ Φ) → Ψ / Γ.substₜ σₜ ∋ A.substₜ σₜ
--   | .zero, σₜ => .zero
--   | .succ i, σₜ => .succ (i.substₜ σₜ)
-- notation : max i "{{" σₜ "}}ₛₜ" => Member.substₜ i σₜ

-- end Con

-- inductive Term : (Φ : Conₜ) → Con Φ → Ty Φ → Type where
--   | var : Φ / Γ ∋ A → Term Φ Γ A
--   | unit : Term Φ Γ .unit
--   | record : ((i : Fin n) → Term Φ Γ (f i)) → Term Φ Γ (.record f)
--   | proj : {f : Fin n → Ty Φ} → Term Φ Γ (.record f) → (i : Fin n) → Term Φ Γ (f i)
--   | pair : Term Φ Γ A → Term Φ Γ B →  Term Φ Γ (.pair A B)
--   | p₁ : Term Φ Γ (.pair A B) → Term Φ Γ A
--   | p₂ : Term Φ Γ (.pair A B) → Term Φ Γ B
--   | true : Term Φ Γ .bool
--   | false : Term Φ Γ .bool
--   | ifte : Term Φ Γ .bool → Term Φ Γ A → Term Φ Γ A → Term Φ Γ A
--   | lam : (A : Ty Φ) → Term Φ (Γ; A) B → Term Φ Γ (A ⇒ B)
--   | app : Term Φ Γ (A ⇒ B) → Term Φ Γ A → Term Φ Γ B
--   | lamₜ : Term (Φ;*) Γ.wk A → Term Φ Γ (.pi A)
--   | appₜ : Term Φ Γ (.pi A) → (B : Ty Φ) → Term Φ Γ A[[B]]ₛₜ
-- notation : 90 Φ: 90 " / " Γ: 90 " ⊢ " A: 90 => Term Φ Γ A

-- def Rename (Ψ Φ) (Δ : Con Ψ) (Γ : Con Φ) (ρₜ : Renameₜ Ψ Φ) :=
--   ∀ (A : Ty Φ), Φ / Γ ∋ A → Ψ / Δ ∋ A{{ρₜ}}ᵣₜ
-- def Subst (Ψ Φ) (Δ : Con Ψ) (Γ : Con Φ) (ρₜ : Renameₜ Ψ Φ) :=
--   ∀ (A : Ty Φ), Φ / Γ ∋ A → Ψ / Δ ⊢ A{{ρₜ}}ᵣₜ

-- def Rename.extend : Rename Ψ Φ Δ Γ ρₜ → Rename Ψ Φ (Δ; A{{ρₜ}}ᵣₜ) (Γ; A) ρₜ
--   | _, _, .zero => .zero
--   | ρ, _, .succ i => .succ (ρ _ i)

-- def Rename.extend' : Rename Ψ Φ Δ Γ ρₜ → Rename (Ψ;*) (Φ;*) Δ.wk Γ.wk ρₜ.extend :=
--   fun ρ =>
--   fun {A} i =>
--   match Γ with
--   | .nil => by contradiction
--   | .cons Γ A =>
--   match i with
--   | .zero =>
--     have : A{{ρₜ}}ᵣₜ.wk = A.wk{{ρₜ.extend}}ᵣₜ := by {
--       simp [Ty.wk]
--       rw [←Renameₜ.ren_comp, ←Renameₜ.ren_comp]
--       congr
--     }
--     this ▸ (ρ _ .zero).wk
--   | .succ i =>
--     let ρ' : Rename _ _ _ _ _ := fun _ => ρ _ ∘ .succ
--     ρ'.extend' _ i

-- def substₜ₀_renameₜ : {B : Ty (Φ;*)} → B[[A]]ₛₜ{{ρₜ}}ᵣₜ = B{{ρₜ.extend}}ᵣₜ[[A{{ρₜ}}ᵣₜ]]ₛₜ := by {
--   intro B
--   simp [Ty.substₜ₀]
--   rw [←Substₜ.subs_compᵣₛ, ←Substₜ.subs_compₛᵣ]
--   congr
--   funext i
--   cases i with
--   | zero => rfl
--   | succ i => rfl
-- }

-- def Term.rename : Φ / Γ ⊢ A → Rename Ψ Φ Δ Γ ρₜ → Ψ / Δ ⊢ A{{ρₜ}}ᵣₜ
--   | var i, ρ => var (ρ _ i)
--   | unit, ρ => .unit
--   | .record g, ρ => .record (fun i => (g i).rename ρ)
--   | .proj (f:=f) r i , ρ => .proj (r.rename ρ) i
--   | pair a b, ρ => .pair (a.rename ρ) (b.rename ρ)
--   | p₁ ab, ρ => .p₁ (ab.rename ρ)
--   | p₂ ab, ρ => .p₂ (ab.rename ρ)
--   | true, ρ => .true
--   | false, ρ => .false
--   | ifte b t e, ρ => .ifte (b.rename ρ) (t.rename ρ) (e.rename ρ)
--   | lam B e, ρ => .lam B{{ρₜ}}ᵣₜ (e.rename ρ.extend)
--   | app f x, ρ => .app (f.rename ρ) (x.rename ρ)
--   | lamₜ e, ρ => .lamₜ (e.rename ρ.extend')
--   | appₜ f B, ρ => substₜ₀_renameₜ ▸ .appₜ (f.rename ρ) B{{ρₜ}}ᵣₜ
-- notation : max A "{{" ρ "}}ᵣ" => Term.rename A ρ

-- def Rename.id : (Γ : Con Φ) → Rename Φ Φ Γ Γ (𝟙ᵣₜ _)
--   | _, _ => Renameₜ.id_rfl ▸ _root_.id
-- prefix : max "𝟙ᵣ" => Rename.id

-- def Rename.nil : (Γ : Con Φ) → Rename Φ .nil Γ .nil Renameₜ.nil :=
--   fun Γ =>
--   fun _ i => by contradiction

-- def Rename.wk : Rename Ψ Φ Δ Γ ρₜ → (A : Ty _) → Rename Ψ Φ (Δ; A) Γ ρₜ
--   | ρ, _, _, i => .succ (ρ _ i)

-- def Rename.rest : Rename Ψ Φ Δ (Γ; A) ρₜ → Rename Ψ Φ Δ Γ ρₜ :=
--   fun ρ =>
--   fun _ i => ρ _ (.succ i)

-- def Term.wk : Φ / Γ ⊢ A → Φ / Γ; B ⊢ A
--   | t => (Renameₜ.id_rfl (A:=A)) ▸ Term.rename t (Rename.wk (𝟙ᵣ Γ) B)

-- def Subst.extend : Subst Ψ Φ Δ Γ ρₜ → Subst Ψ Φ (Δ; A{{ρₜ}}ᵣₜ) (Γ; A) ρₜ
--   | _, _, .zero => .var .zero
--   | σ, _, .succ i => (σ _ i).wk

-- def Term.renameₜ : Φ / Γ ⊢ A → (ρ : Renameₜ Ψ Φ) → Ψ / Γ{{ρ}}ᵣₜ ⊢ A{{ρ}}ᵣₜ
--   | var i, ρₜ => var (i.renameₜ ρₜ)
--   | unit, ρₜ => .unit
--   | record f, ρₜ => .record (fun i => (f i).renameₜ ρₜ)
--   | proj (f:=f) r i, ρₜ => .proj (r.renameₜ ρₜ) i
--   | pair a b, ρₜ => .pair (a.renameₜ ρₜ) (b.renameₜ ρₜ)
--   | p₁ ab, ρₜ => .p₁ (ab.renameₜ ρₜ)
--   | p₂ ab, ρₜ => .p₂ (ab.renameₜ ρₜ)
--   | true, ρₜ => .true
--   | false, ρₜ => .false
--   | ifte b t e, ρₜ => .ifte (b.renameₜ ρₜ) (t.renameₜ ρₜ) (e.renameₜ ρₜ)
--   | lam B e, ρₜ => .lam (B.renameₜ ρₜ) (e.renameₜ ρₜ)
--   | app f x, ρₜ => .app (f.renameₜ ρₜ) (x.renameₜ ρₜ)
--   | lamₜ e, ρₜ =>
--     have this : ∀ {Φ Ψ} {Γ : Con Φ} {ρₜ : Renameₜ Ψ Φ}, Γ.wk{{ρₜ.extend}}ᵣₜ = Γ{{ρₜ}}ᵣₜ.wk := by {
--       intro Φ Ψ Γ σₜ
--       simp [Con.wk]
--       induction Γ with
--       | nil => trivial
--       | cons Γ B ih =>
--         simp [Con.renameₜ, Con.substₜ]
--         constructor
--         apply ih
--         rw [←Renameₜ.ren_comp, ←Renameₜ.ren_comp]
--         congr
--     }
--     .lamₜ (this ▸ e.renameₜ ρₜ.extend)
--   | appₜ (A:=C) f B, ρₜ =>
--     have : C{{ρₜ.extend}}ᵣₜ[[B{{ρₜ}}ᵣₜ]]ₛₜ = C[[B]]ₛₜ{{ρₜ}}ᵣₜ := by {
--       simp [Ty.substₜ₀]
--       rw [←Substₜ.subs_compᵣₛ, ←Substₜ.subs_compₛᵣ]
--       congr
--       funext i
--       cases i with
--       | zero => rfl
--       | succ i => rfl
--     }
--     this ▸ .appₜ (f.renameₜ ρₜ) (B.renameₜ ρₜ)
-- notation : max t "{{" ρₜ "}}ᵣₜ" => Term.renameₜ t ρₜ

-- def Term.substₜ : Φ / Γ ⊢ A → (σ : Substₜ Ψ Φ) → Ψ / Γ.substₜ σ ⊢ A.substₜ σ
--   | var i, σₜ => var (i.substₜ σₜ)
--   | unit, σₜ => .unit
--   | record f, σₜ => .record (fun i => (f i).substₜ σₜ)
--   | proj (f:=f) r i, σₜ => .proj (r.substₜ σₜ) i
--   | pair a b, σₜ => .pair (a.substₜ σₜ) (b.substₜ σₜ)
--   | p₁ ab, σₜ => .p₁ (ab.substₜ σₜ)
--   | p₂ ab, σₜ => .p₂ (ab.substₜ σₜ)
--   | true, σₜ => .true
--   | false, σₜ => .false
--   | ifte b t e, σₜ => .ifte (b.substₜ σₜ) (t.substₜ σₜ) (e.substₜ σₜ)
--   | lam B e, σₜ => .lam (B.substₜ σₜ) (e.substₜ σₜ)
--   | app f x, σₜ => .app (f.substₜ σₜ) (x.substₜ σₜ)
--   | lamₜ e, σₜ =>
--     have this : ∀ {Φ Ψ} {Γ : Con Φ} {σₜ : Substₜ Ψ Φ}, Γ.wk{{σₜ.extend}}ₛₜ = Γ{{σₜ}}ₛₜ.wk := by {
--       intro Φ Ψ Γ σₜ
--       simp [Con.wk]
--       induction Γ with
--       | nil => trivial
--       | cons Γ B ih =>
--         simp [Con.renameₜ, Con.substₜ]
--         constructor
--         apply ih
--         rw [←Substₜ.subs_compᵣₛ, ←Substₜ.subs_compₛᵣ]
--         congr
--     }
--     .lamₜ (this ▸ e.substₜ σₜ.extend)
--   | appₜ (A:=C) f B, σₜ =>
--     have : C{{σₜ.extend}}ₛₜ[[B{{σₜ}}ₛₜ]]ₛₜ = C[[B]]ₛₜ{{σₜ}}ₛₜ := by {
--       simp [Ty.substₜ₀]
--       rw [←Substₜ.subs_comp, ←Substₜ.subs_comp]
--       congr
--       funext i
--       cases i with
--       | zero => rfl
--       | succ i =>
--         simp [Substₜ.comp, Substₜ.extend, Substₜ.cons, Substₜ.id, Ty.substₜ, Ty.wk]
--         rw [←Substₜ.subs_compₛᵣ, ←Substₜ.subs_id (t:=σₜ i), ←Substₜ.subs_comp]
--         congr
--     }
--     this ▸ .appₜ (f.substₜ σₜ) (B.substₜ σₜ)
-- notation : max t "{{" ρₜ "}}ₛₜ" => Term.substₜ t ρₜ


-- def Term.substₜ₀ : Φ;* / Γ.wk ⊢ A → (B : Ty Φ) → Φ / Γ ⊢ A[[B]]ₛₜ :=
--   fun t B =>
--   have : ∀ {Φ} {Γ: Con Φ} {B}, Γ.wk{{𝟙ₛₜ _; B}}ₛₜ = Γ := by {
--     intro Φ Γ B
--     induction Γ with
--     | nil => trivial
--     | cons Γ C ih =>
--       simp [Con.wk, Con.renameₜ, Con.substₜ]
--       constructor
--       assumption
--       rw [←Substₜ.subs_compₛᵣ, ←Substₜ.subs_id (t:=C), ←Substₜ.subs_comp]
--       congr
--   }
--   @this _ Γ B ▸ t{{𝟙ₛₜ _; B}}ₛₜ
-- notation : max t "[[" B "]]ₛₜ" => Term.substₜ₀ t B

-- def Subst.extend' : Subst Ψ Φ Δ Γ ρₜ → Subst (Ψ;*) (Φ;*) Δ.wk Γ.wk ρₜ.extend :=
--   fun σ =>
--   fun {A} i =>
--   match Γ with
--   | .nil => by contradiction
--   | .cons Γ A =>
--   match i with
--   | .zero =>
--     have : Ψ;* / Δ{{Conₜ.Member.succ}}ᵣₜ ⊢ A{{ρₜ}}ᵣₜ{{Conₜ.Member.succ}}ᵣₜ = Ψ;* / Δ.wk ⊢ A{{Conₜ.Member.succ}}ᵣₜ{{ρₜ.extend}}ᵣₜ := by {
--       simp [Con.wk]
--       apply congrArg₂
--       rfl
--       rw [←Renameₜ.ren_comp, ←Renameₜ.ren_comp]
--       congr
--     }
--     this ▸ (σ _ .zero).renameₜ .succ
--   | .succ i =>
--     let σ' : Subst _ _ _ _ _ := fun _ => σ _ ∘ .succ
--     σ'.extend' _ i


-- def Term.subst : Φ / Γ ⊢ A → Subst Ψ Φ Δ Γ ρₜ → Ψ / Δ ⊢ A{{ρₜ}}ᵣₜ
--   | var i, σ => σ _ i
--   | unit, σ => .unit
--   | record f, σ => .record (fun i => (f i).subst σ)
--   | proj (f:=f) r i, σ => .proj (r.subst σ) i
--   | pair a b, σ => .pair (a.subst σ) (b.subst σ)
--   | p₁ ab, σ => .p₁ (ab.subst σ)
--   | p₂ ab, σ => .p₂ (ab.subst σ)
--   | true, σ => .true
--   | false, σ => .false
--   | ifte b t e, σ => .ifte (b.subst σ) (t.subst σ) (e.subst σ)
--   | lam B e, σ => .lam B{{ρₜ}}ᵣₜ (e.subst σ.extend)
--   | app f x, σ => .app (f.subst σ) (x.subst σ)
--   | lamₜ e, σ => .lamₜ (e.subst σ.extend')
--   | appₜ (A:=C) f B, σ =>
--     have : C{{ρₜ.extend}}ᵣₜ[[B{{ρₜ}}ᵣₜ]]ₛₜ = C[[B]]ₛₜ{{ρₜ}}ᵣₜ := by {
--       simp [Ty.substₜ₀]
--       rw [←Substₜ.subs_compᵣₛ, ←Substₜ.subs_compₛᵣ]
--       congr
--       funext i
--       cases i with
--       | zero => rfl
--       | succ i => rfl
--     }
--     this ▸ .appₜ (f.subst σ) B{{ρₜ}}ᵣₜ
-- notation : max A "{{" σ "}}ₛ" => Term.subst A σ

-- def Subst.cons : Subst Ψ Φ Δ Γ ρₜ → Ψ / Δ ⊢ A{{ρₜ}}ᵣₜ → Subst Ψ Φ Δ (Γ; A) ρₜ
--   | _, t, _, .zero => t
--   | σₜ, _, _, .succ i => σₜ _ i
-- notation : 100 σₜ "; " A => Subst.cons σₜ A

-- def Subst.id : (Γ : Con Φ) → Subst Φ Φ Γ Γ (𝟙ᵣₜ _) :=
--   fun _ _ => Renameₜ.id_rfl ▸ (.var ·)
-- prefix : max "𝟙ₛ" => Subst.id

-- def Term.subst₀ : Φ / Γ; A ⊢ B → Φ / Γ ⊢ A → Φ / Γ ⊢ B :=
--   fun t s =>
--   have : ∀ {A}, Φ / Γ ⊢ A = Φ / Γ ⊢ A{{𝟙ᵣₜ _}}ᵣₜ := by {
--     intro A
--     congr
--     exact Renameₜ.id_rfl.symm
--   }
--   let σ : Subst _ _ _ _ _ := 𝟙ₛ _; (this ▸ s)
--   this ▸ t{{σ}}ₛ
-- notation : max t "[[" s "]]ₛ" => Term.subst₀ t s

-- def update {T : Type} : (Fin n → T) → Fin n → T → Fin n → T :=
--   fun f i t =>
--   fun j =>
--   if i = j then
--     t
--   else
--     f j

-- inductive SmallStep : Φ / Γ ⊢ A → Φ / Γ ⊢ A → Prop where
--   | β_app : SmallStep (.app (.lam B e) x) e[[x]]ₛ
--   | β_appₜ : SmallStep (.appₜ (.lamₜ e) B) e[[B]]ₛₜ
--   | β_proj : SmallStep (.proj (.record f) i) (f i)
--   | β_p₁ : SmallStep (.p₁ (.pair a b)) a
--   | β_p₂ : SmallStep (.p₂ (.pair a b)) b
--   | β_ifte₁ : SmallStep (.ifte .true t e) t
--   | β_ifte₂ : SmallStep (.ifte .false t e) e
--   | ξ_record : SmallStep (f i) t → SmallStep (.record f) (.record (update f i t))
--   | ξ_proj : SmallStep r r' → SmallStep (.proj r i) (.proj r' i)
--   | ξ_pair₁ : SmallStep a a' → SmallStep (.pair a b) (.pair a' b)
--   | ξ_pair₂ : SmallStep b b' → SmallStep (.pair a b) (.pair a b')
--   | ξ_p₁ : SmallStep ab ab' → SmallStep (.p₁ ab) (.p₁ ab')
--   | ξ_p₂ : SmallStep ab ab' → SmallStep (.p₂ ab) (.p₂ ab')
--   | ξ_ifte₀ : SmallStep b b' → SmallStep (.ifte b t e) (.ifte b' t e)
--   | ξ_ifte₁ : SmallStep t t' → SmallStep (.ifte b t e) (.ifte b t' e)
--   | ξ_ifte₂ : SmallStep e e' → SmallStep (.ifte b t e) (.ifte b t e')
--   | ξ_lam : SmallStep e e' → SmallStep (.lam _ e) (.lam _ e')
--   | ξ_app₁ : SmallStep f f' → SmallStep (.app f x) (.app f' x)
--   | ξ_app₂ : SmallStep x x' → SmallStep (.app f x) (.app f x')
--   | ξ_lamₜ : SmallStep e e' → SmallStep (.lamₜ e) (.lamₜ e')
--   | ξ_appₜ : SmallStep f f' → SmallStep (.appₜ f B) (.appₜ f' B)
-- infix: 30 " ⟶ₛ " => SmallStep

-- def MultiStep (t t' : Φ / Γ ⊢ A) := TransGen SmallStep t t'
-- infix: 30 " ⟶ₛ+ " => MultiStep

-- namespace Extrinsic

-- inductive Term : (Φ : Conₜ) → Con Φ → Type where
--   | var : Φ / Γ ∋ A → Term Φ Γ
--   | unit : Term Φ Γ
--   | record : ((i : Fin n) → Term Φ Γ) → Term Φ Γ
--   | proj : Term Φ Γ → (i : Fin n) → Term Φ Γ
--   | pair : Term Φ Γ → Term Φ Γ →  Term Φ Γ
--   | p₁ : Term Φ Γ → Term Φ Γ
--   | p₂ : Term Φ Γ → Term Φ Γ
--   | true : Term Φ Γ
--   | false : Term Φ Γ
--   | ifte : Term Φ Γ → Term Φ Γ → Term Φ Γ → Term Φ Γ
--   | lam : (A : Ty Φ) → Term Φ (Γ; A) → Term Φ Γ
--   | app : Term Φ Γ → Term Φ Γ → Term Φ Γ
--   | lamₜ : Term (Φ;*) Γ.wk → Term Φ Γ
--   | appₜ : Term Φ Γ → (B : Ty Φ) → Term Φ Γ
-- notation : 90 Φ: 90 " / " Γ: 90 " ⊢ " => Term Φ Γ

-- inductive Typing : (t : Φ / Γ ⊢) → Ty Φ → Prop where
--   | var : (i : Φ / Γ ∋ A) → Typing (.var i) A
--   | unit : Typing .unit .unit
--   | record : ((i : Fin n) → Typing (g i) (f i))→ Typing (.record g) (.record f)
--   | proj : Typing r (.record f) → Typing (.proj r i) (f i)
--   | pair : Typing a A → Typing b B → Typing (.pair a b) (.pair A B)
--   | p₁ : Typing ab (.pair A B) → Typing (.p₁ ab) A
--   | p₂ : Typing ab (.pair A B) → Typing (.p₂ ab) B
--   | true : Typing .true .bool
--   | false : Typing .false .bool
--   | ifte : Typing b .bool → Typing t A → Typing e A → Typing (.ifte b t e) A
--   | lam : Typing (Γ:=Γ;A) e B → Typing (.lam A e) (A ⇒ B)
--   | app : Typing f (A ⇒ B) → Typing x A → Typing (.app f x) B
--   | lamₜ : Typing (Φ:=Φ;*) e B → Typing (.lamₜ e) (.pi B)
--   | appₜ : Typing (Φ:=Φ) f (.pi A) → Typing (.appₜ f B) A[[B]]ₛₜ

-- def Term.renameₜ : Φ / Γ ⊢ → (ρ : Renameₜ Ψ Φ) → Ψ / Γ{{ρ}}ᵣₜ ⊢
--   | var i, ρₜ => var (i.renameₜ ρₜ)
--   | unit, ρₜ => .unit
--   | record f, ρₜ => .record (fun i => (f i).renameₜ ρₜ)
--   | proj r i, ρₜ => .proj (r.renameₜ ρₜ) i
--   | pair a b, ρₜ => .pair (a.renameₜ ρₜ) (b.renameₜ ρₜ)
--   | p₁ ab, ρₜ => .p₁ (ab.renameₜ ρₜ)
--   | p₂ ab, ρₜ => .p₂ (ab.renameₜ ρₜ)
--   | true, ρₜ => .true
--   | false, ρₜ => .false
--   | ifte b t e, ρₜ => .ifte (b.renameₜ ρₜ) (t.renameₜ ρₜ) (e.renameₜ ρₜ)
--   | lam B e, ρₜ => .lam (B.renameₜ ρₜ) (e.renameₜ ρₜ)
--   | app f x, ρₜ => .app (f.renameₜ ρₜ) (x.renameₜ ρₜ)
--   | lamₜ e, ρₜ =>
--     have this : ∀ {Φ Ψ} {Γ : Con Φ} {ρₜ : Renameₜ Ψ Φ}, Γ.wk{{ρₜ.extend}}ᵣₜ = Γ{{ρₜ}}ᵣₜ.wk := by {
--       intro Φ Ψ Γ σₜ
--       simp [Con.wk]
--       induction Γ with
--       | nil => trivial
--       | cons Γ B ih =>
--         simp [Con.renameₜ, Con.substₜ]
--         constructor
--         apply ih
--         rw [←Renameₜ.ren_comp, ←Renameₜ.ren_comp]
--         congr
--     }
--     .lamₜ (this ▸ e.renameₜ ρₜ.extend)
--   | .appₜ f B, ρₜ =>
--     .appₜ (f.renameₜ ρₜ) (B.renameₜ ρₜ)
-- notation : max t "{{" ρₜ "}}ᵣₜ" => Term.renameₜ t ρₜ

-- def Term.rename : Φ / Γ ⊢ → Rename Ψ Φ Δ Γ ρₜ → Ψ / Δ ⊢
--   | var i, ρ => var (ρ _ i)
--   | unit, ρ => .unit
--   | record f, ρ => .record (fun i => (f i).rename ρ)
--   | proj r i, ρ => .proj (r.rename ρ) i
--   | pair a b, ρ => .pair (a.rename ρ) (b.rename ρ)
--   | p₁ ab, ρ => .p₁ (ab.rename ρ)
--   | p₂ ab, ρ => .p₂ (ab.rename ρ)
--   | true, ρ => .true
--   | false, ρ => .false
--   | ifte b t e, ρ => .ifte (b.rename ρ) (t.rename ρ) (e.rename ρ)
--   | lam B e, ρ => .lam B{{ρₜ}}ᵣₜ (e.rename ρ.extend)
--   | app f x, ρ => .app (f.rename ρ) (x.rename ρ)
--   | lamₜ e, ρ => .lamₜ (e.rename ρ.extend')
--   | appₜ f B, ρ => .appₜ (f.rename ρ) B{{ρₜ}}ᵣₜ
-- notation : max A "{{" ρ "}}ᵣ" => Term.rename A ρ

-- def Term.wk : Φ / Γ ⊢ → Φ / Γ; B ⊢
--   | t => t{{(Rename.wk (𝟙ᵣ Γ) B)}}ᵣ

-- def Term.substₜ : Φ / Γ ⊢ → (σ : Substₜ Ψ Φ) → Ψ / Γ.substₜ σ ⊢
--   | var i, σₜ => var (i.substₜ σₜ)
--   | unit, σₜ => .unit
--   | record f, σₜ => .record (fun i => (f i).substₜ σₜ)
--   | proj r i, σₜ => .proj (r.substₜ σₜ) i
--   | pair a b, σₜ => .pair (a.substₜ σₜ) (b.substₜ σₜ)
--   | p₁ ab, σₜ => .p₁ (ab.substₜ σₜ)
--   | p₂ ab, σₜ => .p₂ (ab.substₜ σₜ)
--   | true, σₜ => .true
--   | false, σₜ => .false
--   | ifte b t e, σₜ => .ifte (b.substₜ σₜ) (t.substₜ σₜ) (e.substₜ σₜ)
--   | lam B e, σₜ => .lam (B.substₜ σₜ) (e.substₜ σₜ)
--   | app f x, σₜ => .app (f.substₜ σₜ) (x.substₜ σₜ)
--   | lamₜ e, σₜ =>
--     have this : ∀ {Φ Ψ} {Γ : Con Φ} {σₜ : Substₜ Ψ Φ}, Γ.wk{{σₜ.extend}}ₛₜ = Γ{{σₜ}}ₛₜ.wk := by {
--       intro Φ Ψ Γ σₜ
--       simp [Con.wk]
--       induction Γ with
--       | nil => trivial
--       | cons Γ B ih =>
--         simp [Con.renameₜ, Con.substₜ]
--         constructor
--         apply ih
--         rw [←Substₜ.subs_compᵣₛ, ←Substₜ.subs_compₛᵣ]
--         congr
--     }
--     .lamₜ (this ▸ e.substₜ σₜ.extend)
--   | appₜ f B, σₜ => .appₜ (f.substₜ σₜ) (B.substₜ σₜ)
-- notation : max t "{{" ρₜ "}}ₛₜ" => Term.substₜ t ρₜ


-- def Term.substₜ₀ : Φ;* / Γ.wk ⊢ → (B : Ty Φ) → Φ / Γ ⊢ :=
--   fun t B =>
--   have : ∀ {Φ} {Γ: Con Φ} {B}, Γ.wk{{𝟙ₛₜ _; B}}ₛₜ = Γ := by {
--     intro Φ Γ B
--     induction Γ with
--     | nil => trivial
--     | cons Γ C ih =>
--       simp [Con.wk, Con.renameₜ, Con.substₜ]
--       constructor
--       assumption
--       rw [←Substₜ.subs_compₛᵣ, ←Substₜ.subs_id (t:=C), ←Substₜ.subs_comp]
--       congr
--   }
--   @this _ Γ B ▸ t{{𝟙ₛₜ _; B}}ₛₜ
-- notation : max t "[[" B "]]ₛₜ" => Term.substₜ₀ t B

-- def Subst (Φ) (Δ : Con Φ) (Γ : Con Φ) :=
--   ∀ (A : Ty Φ), Φ / Γ ∋ A → Φ / Δ ⊢

-- def Subst.extend : Subst Φ Δ Γ → Subst Φ (Δ; A) (Γ; A)
--   | _, _, .zero => .var .zero
--   | σ, _, .succ i => (σ _ i).wk
-- def Subst.extend' : Subst Φ Δ Γ → Subst (Φ;*) Δ.wk Γ.wk :=
--   fun σ =>
--   fun A i =>
--   match Γ with
--   | .nil => by contradiction
--   | .cons Γ A =>
--   match i with
--   | .zero => (σ _ .zero).renameₜ .succ
--   | .succ i =>
--     let σ' : Subst _ _ _ := fun _ => σ _ ∘ .succ
--     σ'.extend' _ i
-- def Term.subst : Φ / Γ ⊢ → Subst Φ Δ Γ → Φ / Δ ⊢
--   | var i, σ => σ _ i
--   | unit, σ => .unit
--   | record f, σ => .record (fun i => (f i).subst σ)
--   | proj r i, σ => .proj (r.subst σ) i
--   | pair a b, σ => .pair (a.subst σ) (b.subst σ)
--   | p₁ ab, σ => .p₁ (ab.subst σ)
--   | p₂ ab, σ => .p₂ (ab.subst σ)
--   | true, σ => .true
--   | false, σ => .false
--   | ifte b t e, σ => .ifte (b.subst σ) (t.subst σ) (e.subst σ)
--   | lam B e, σ => .lam B (e.subst σ.extend)
--   | app f x, σ => .app (f.subst σ) (x.subst σ)
--   | lamₜ e, σ => .lamₜ (e.subst σ.extend')
--   | appₜ f B, σ => .appₜ (f.subst σ) B
-- notation : max A "{{" σ "}}ₛ" => Term.subst A σ

-- def Subst.cons : Subst Φ Δ Γ → Φ / Δ ⊢ → Subst Φ Δ (Γ; A)
--   | _, t, _, .zero => t
--   | σₜ, _, _, .succ i => σₜ _ i
-- notation : 100 σₜ "; " A => Subst.cons σₜ A

-- def Subst.id : (Γ : Con Φ) →  Subst Φ Γ Γ := fun _ _ => (.var ·)
-- prefix : max "𝟙ₛ" => Subst.id

-- def Term.subst₀ : Φ / Γ; A ⊢ → Φ / Γ ⊢ → Φ / Γ ⊢:=
--   fun t s => t{{𝟙ₛ _; s}}ₛ
-- notation : max t "[[" s "]]ₛ" => Term.subst₀ t s

-- def Typing.rename : {t : Φ / Γ ⊢} → Typing t A → (ρ : Rename Ψ Φ Δ Γ ρₜ) → Typing t{{ρ}}ᵣ A{{ρₜ}}ᵣₜ := by {
--   intro t h ρ
--   induction h generalizing Δ Ψ with
--   | var i => apply Typing.var
--   | unit => constructor
--   | record f ih =>
--     constructor
--     intro i
--     apply ih
--   | proj r ih =>
--     constructor
--     apply ih
--   | pair a b iha ihb =>
--     constructor
--     apply iha
--     apply ihb
--   | p₁ ab ih =>
--     constructor
--     apply ih
--   | p₂ ab ih =>
--     constructor
--     apply ih
--   | true => constructor
--   | false => constructor
--   | ifte b t e ihb iht ihe =>
--     constructor
--     apply ihb
--     apply iht
--     apply ihe
--   | lam t ih =>
--     constructor
--     apply ih
--   | app f x ihf ihx =>
--     constructor
--     apply ihf
--     apply ihx
--   | lamₜ t ih =>
--     constructor
--     apply ih
--   | appₜ f ih =>
--     rw [Substₜ.substₜ₀_renameₜ]
--     constructor
--     apply ih
-- }

-- def Typing.wk : {t : Φ / Γ ⊢} → {B : Ty Φ} → Typing t A → Typing (t.wk (B:=B)) A := by {
--   intro t B h
--   simp [Term.wk]
--   rw [←Renameₜ.id_rfl (A:=A)]
--   apply rename
--   assumption
-- }

-- inductive SmallStep : Φ / Γ ⊢ → Φ / Γ ⊢ → Prop where
--   | β_app : SmallStep (.app (.lam B e) x) e[[x]]ₛ
--   | β_appₜ : SmallStep (.appₜ (.lamₜ e) B) e[[B]]ₛₜ
--   | β_proj : SmallStep (.proj (.record f) i) (f i)
--   | β_p₁ : SmallStep (.p₁ (.pair a b)) a
--   | β_p₂ : SmallStep (.p₂ (.pair a b)) b
--   | β_ifte₁ : SmallStep (.ifte .true t e) t
--   | β_ifte₂ : SmallStep (.ifte .false t e) e
--   | ξ_record : SmallStep (f i) t → SmallStep (.record f) (.record (update f i t))
--   | ξ_proj : SmallStep r r' → SmallStep (.proj r i) (.proj r' i)
--   | ξ_pair₁ : SmallStep a a' → SmallStep (.pair a b) (.pair a' b)
--   | ξ_pair₂ : SmallStep b b' → SmallStep (.pair a b) (.pair a b')
--   | ξ_p₁ : SmallStep ab ab' → SmallStep (.p₁ ab) (.p₁ ab')
--   | ξ_p₂ : SmallStep ab ab' → SmallStep (.p₂ ab) (.p₂ ab')
--   | ξ_ifte₀ : SmallStep b b' → SmallStep (.ifte b t e) (.ifte b' t e)
--   | ξ_ifte₁ : SmallStep t t' → SmallStep (.ifte b t e) (.ifte b t' e)
--   | ξ_ifte₂ : SmallStep e e' → SmallStep (.ifte b t e) (.ifte b t e')
--   | ξ_lam : SmallStep e e' → SmallStep (.lam _ e) (.lam _ e')
--   | ξ_app₁ : SmallStep f f' → SmallStep (.app f x) (.app f' x)
--   | ξ_app₂ : SmallStep x x' → SmallStep (.app f x) (.app f x')
--   | ξ_lamₜ : SmallStep e e' → SmallStep (.lamₜ e) (.lamₜ e')
--   | ξ_appₜ : SmallStep f f' → SmallStep (.appₜ f B) (.appₜ f' B)
-- infix: 30 " ⟶ₛ " => SmallStep

-- def MultiStep (t t' : Φ / Γ ⊢) := TransGen SmallStep t t'
-- infix: 30 " ⟶ₛ+ " => MultiStep

-- def MultiStep0 (t t' : Φ / Γ ⊢) := ReflTransGen SmallStep t t'
-- infix: 30 " ⟶ₛ* " => MultiStep0

-- def MultiStep.ξ_app₁ : MultiStep f f' → MultiStep (.app f x) (.app f' x) :=
--   fun htt' =>
--   TransGen.lift (SystemF.Extrinsic.Term.app · x) (fun _ _ htt' => .ξ_app₁ htt') htt'
-- def MultiStep.ξ_appₜ : MultiStep f f' → MultiStep (.appₜ f B) (.appₜ f' B) :=
--   fun htt' =>
--   TransGen.lift (SystemF.Extrinsic.Term.appₜ · B) (fun _ _ htt' => .ξ_appₜ htt') htt'
-- def MultiStep0.ξ_app₁ : MultiStep0 f f' → MultiStep0 (.app f x) (.app f' x) :=
--   fun htt' =>
--   ReflTransGen.lift (SystemF.Extrinsic.Term.app · x) (fun _ _ htt' => .ξ_app₁ htt') htt'
-- def MultiStep0.ξ_appₜ : MultiStep0 f f' → MultiStep0 (.appₜ f B) (.appₜ f' B) :=
--   fun htt' =>
--   ReflTransGen.lift (SystemF.Extrinsic.Term.appₜ · B) (fun _ _ htt' => .ξ_appₜ htt') htt'

-- -- def Subst.comp : Subst Φ'' Φ' Γ'' Γ' → Renameₜ Φ'' Φ' → Subst Φ' Φ Γ' Γ → Renameₜ Φ' Φ → Subst Φ'' Φ Γ'' Γ × Renameₜ Φ'' Φ :=
-- --   fun σ' ρ' σ ρ => .mk (fun i => (σ i).subst σ' ρ') (Renameₜ.comp ρ' ρ)

-- -- def Subst.compᵣₛ : Renameₜ Φ'' Φ' → Substₜ Φ' Φ → Substₜ Φ'' Φ :=
-- --   fun ρₜ σₜ i => (σₜ i).renameₜ ρₜ
-- -- def Subst.compₛᵣ : Substₜ Φ'' Φ' → Renameₜ Φ' Φ → Substₜ Φ'' Φ :=
-- --   fun σₜ ρₜ => σₜ ∘ ρₜ

-- def Rename.comp {Φ'' Φ' Φ} {Γ'' : Con Φ''} {Γ' : Con Φ'} {Γ : Con Φ} {ρₜ' : Renameₜ Φ'' Φ'} {ρₜ : Renameₜ Φ' Φ} : Rename Φ'' Φ' Γ'' Γ' ρₜ' → Rename Φ' Φ Γ' Γ ρₜ → Rename Φ'' Φ Γ'' Γ (Renameₜ.comp ρₜ' ρₜ) :=
--   fun ρ' ρ =>
--   fun _ i => SystemF.Renameₜ.ren_comp ▸ ρ' _ (ρ _ i)

-- #check cast_eq_iff_heq.mp
-- def Rename.extend_comp {Φ'' Φ' Φ} {Γ'' : Con Φ''} {Γ' : Con Φ'} {Γ : Con Φ} {ρₜ' : Renameₜ Φ'' Φ'} {ρₜ : Renameₜ Φ' Φ} {f : Rename Φ'' Φ' Γ'' Γ' ρₜ'} {g : Rename Φ' Φ Γ' Γ ρₜ} {A : Ty Φ} : HEq (Rename.extend (A:=A) (comp f g)) (comp f.extend (g.extend (A:=A))) := by

--   -- refine HEq.symm (heq_of_eqRec_eq ?h₁ ?h₂)
--   refine heq_of_eqRec_eq ?h₁ ?h₂
--   rw [Renameₜ.ren_comp]
--   funext B i
--   cases i with
--   | zero =>
--     simp [Rename.extend, Rename.comp]
--     rw [@eqRec_eq_cast]
--   | succ i =>
--     simp [Rename.extend, Rename.comp]

--   -- funext fun i =>
--   -- match i with
--   -- | .zero => rfl
--   -- | .succ _ => rfl
-- def Rename.ren_comp {Φ'' Φ' Φ} {ρₜ' : Renameₜ Φ'' Φ'} {ρₜ : Renameₜ Φ' Φ} {Γ'' : Con Φ''} {Γ' : Con Φ'} {Γ : Con Φ} {f : Rename Φ'' Φ' Γ'' Γ' ρₜ'} {g : Rename Φ' Φ Γ' Γ ρₜ} : {t : Φ / Γ ⊢} → t{{comp f g}}ᵣ = t{{g}}ᵣ{{f}}ᵣ
--   | .var _ => by
--     simp [Term.rename]
--     constructor
--     exact Renameₜ.ren_comp
--     simp [comp]
--   | .unit => rfl
--   | .pair a b => congrArg₂ Term.pair ren_comp ren_comp
--   | .p₁ ab => congrArg _ ren_comp
--   | .p₂ ab => congrArg _ ren_comp
--   | .record f => by
--     simp [Term.rename]
--     funext i
--     exact ren_comp
--   | .proj p i => by
--     simp [Term.rename]
--     exact ren_comp
--   | .false => rfl
--   | .true => rfl
--   | .ifte b t e => by
--     simp [Term.rename]
--     constructor
--     exact ren_comp
--     constructor
--     exact ren_comp
--     exact ren_comp
--   | .lam _ t => by
--     simp [Term.rename]
--     constructor
--     exact Renameₜ.ren_comp

--   | .app f x => sorry
--   | .lamₜ t => sorry
--   | .appₜ f B => sorry
--   -- | .record f => by
--   --   simp [Ty.renameₜ]
--   --   funext i
--   --   apply ren_comp
--   -- | .fn _ _ => congrArg₂ Ty.fn ren_comp ren_comp
--   -- | .pi _ => congrArg Ty.pi (Eq.trans (congrArg _ extend_comp) ren_comp)
--   -- | .pair _ _  => congrArg₂ Ty.pair ren_comp ren_comp

-- end Extrinsic

end SystemF
