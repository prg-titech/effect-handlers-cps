
import EffectCompiler.STLC_Sum.Basic
import EffectCompiler.STLC_Sum.SmallStep

import Mathlib.Tactic.Find


namespace STLC_Sum

inductive Progress : Γ ⊢ A → Type
  | step : t ⟶ₛ t' → Progress t
  | done : Normal t → Progress t

def Term.progress : (t : Γ ⊢ A) → Progress t
  | .unit => .done .unit
  | .var x => .done (.neutral .var)
  | .pair a b =>
    match a.progress with
    | .step haa' => .step (.ξ_PAIR₁ haa')
    | .done hn_a =>
    match b.progress with
    | .step hbb' => .step (.ξ_PAIR₂ hbb')
    | .done hn_b => .done (.pair hn_a hn_b)
  | .p₁ ab =>
    match ab.progress with
    | .step habab' => .step (.ξ_P₁ habab')
    | .done hn_ab =>
    match hn_ab with
    | .pair hn_a hn_b => .step .β_P₁
    | .neutral hne_t => .done (.neutral (.p₁ hne_t))
  | .p₂ ab =>
    match ab.progress with
    | .step habab' => .step (.ξ_P₂ habab')
    | .done hn_ab =>
    match hn_ab with
    | .pair hn_a hn_b => .step .β_P₂
    | .neutral hne_t => .done (.neutral (.p₂ hne_t))
  | .lam B e =>
    match e.progress with
    | .step hee' => .step (.ξ_LAM hee')
    | .done hn_e => .done (.lam hn_e)
  | .app f x =>
    match f.progress with
    | .step hff' => .step (.ξ_APP₁ hff')
    | .done hn_f =>
    match hn_f with
    | .lam hn_e => .step .β_APP
    | .neutral hne_f =>
    match x.progress with
    | .step hxx' => .step (.ξ_APP₂ hxx')
    | .done hn_x => .done (.neutral (.app hne_f hn_x))
  | .inl a =>
    match a.progress with
    | .step haa' => .step (.ξ_INL haa')
    | .done hn_a => .done (.inl hn_a)
  | .inr b =>
    match b.progress with
    | .step hbb' => .step (.ξ_INR hbb')
    | .done hn_b => .done (.inr hn_b)
  | .case m a b =>
    match m.progress with
    | .step hmm' => .step (.ξ_CASE₁ hmm')
    | .done hn_m =>
    match hn_m with
    | .inl hn_a => .step .β_CASE₁
    | .inr hn_b => .step .β_CASE₂
    | .neutral hne_m =>
    match a.progress with
    | .step haa' => .step (.ξ_CASE₂ haa')
    | .done hn_a =>
    match b.progress with
    | .step hbb' => .step (.ξ_CASE₃ hbb')
    | .done hn_b => .done (.neutral (.case hne_m hn_a hn_b))

end STLC_Sum
