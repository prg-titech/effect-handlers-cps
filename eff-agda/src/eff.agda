
{-# OPTIONS --rewriting #-}


open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module Eff where

-- open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning; trans)
open import Data.List using ( List; _∷_; []; map; _++_; lookup; length; zip )
open import Data.List.Membership.Propositional using (_∈_)
-- open import Data.List.Properties using ( map-∘ )
open import Data.List.Relation.Unary.All using (All; _∷_; []; uncons; _[_]=_; tabulate) renaming ( lookup to lookupₐ ; zip to zipₐ)
open import Data.List.Relation.Unary.All.Properties using (lookup-map; []=⇒lookup)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Product using ( ∃; _×_ ; _,_ )
open import Data.Fin using (Fin)
open import Function using (_∘_)
open import Function.Base using (case_of_; case_returning_of_)


-- data _∈_ {A : Set} : A → List A → Set where
--     Z : {x : A} {xs : List A} → x ∈ (x ∷ xs)
--     S_ : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

∈-map : {A B : Set} {x : A} {xs : List A} {f : A → B} → x ∈ xs → f x ∈ (map f xs)
∈-map (here refl) = here refl
∈-map (there i) = there (∈-map i)

∈-map-inv : {A B : Set} {xs : List A} {f : A → B} {y : B} → y ∈ (map f xs) → ∃ λ (x : A) → f x ≡ y × x ∈ xs
∈-map-inv {xs = x ∷ xs} (here refl) = x , (refl , (here refl))
∈-map-inv {xs = x ∷ xs} (there i) with ∈-map-inv i
... | x' , h , j = x' , (h , (there j))

-- toFin : {A : Set} {x : A} {xs : List A} → x ∈ xs → Fin (length xs)
-- toFin Z = Fin.zero
-- toFin (S i) = Fin.suc (toFin i)

toFin : {A : Set} {x : A} {xs : List A} → x ∈ xs → Fin (length xs)
toFin (here refl) = Fin.zero
toFin (there i) = Fin.suc (toFin i)

lookup_toFin : {A : Set} {l : List A} {x : A} {i : x ∈ l}  → lookup l (toFin i) ≡ x
lookup_toFin {i = here refl} = refl
lookup_toFin {l = y ∷ l} {i = there i} = lookup_toFin {l = l}

map-All : {A : Set} {B : A → Set} (f : (x : A) → B x) → (l : List A) → All B l
map-All f [] = []
map-All f (x ∷ l) = f x ∷ map-All f l

map-∘ : ∀ {A B C : Set} {l : List A} {f : B → C} {g : A → B} → map f (map g l) ≡ map (f ∘ g) l
map-∘ {l = []} = refl
map-∘ {l = x ∷ l} = cong₂ _∷_ refl (map-∘ {l = l})

-- mapₐ : ∀ {A : Set} {B : Set} {P : A → Set} {Q : B → Set} {l : List A} {f : A → B} → All P l → (h : (x : A) → P x → Q (f x)) → All Q (map f l)
-- mapₐ {A} {B} {P} {Q} [] h = []
-- mapₐ {A} {B} {P} {Q} (_∷_ {x} px pl) h = h x px ∷ (mapₐ pl h)

mapₐ : ∀ {A : Set} {P : A → Set} {Q : A → Set} {l : List A} → All P l → (h : (x : A) → P x → Q x) → All Q l
mapₐ {A} {P} {Q} [] h = []
mapₐ {A} {P} {Q} (_∷_ {x} px pl) h = h x px ∷ (mapₐ pl h)

{-# REWRITE lookup_toFin map-∘ #-}

CmpTy : Set
Eff : Set
data Sig : Set


data ValTy : Set where
    unit : ValTy
    bool : ValTy
    _⇒_ : ValTy → CmpTy → ValTy
    _⇛_ : CmpTy → CmpTy → ValTy

CmpTy = ValTy × Eff

data Sig where
    op : ValTy → ValTy → Sig
Eff = List Sig

data cmp (ν : ValTy → Set) : CmpTy → Set
OpCluases : (ν : ValTy → Set) → Eff → CmpTy → Set

data val (ν : ValTy → Set) : ValTy → Set where
    `_ : ∀ {A} → ν A → val ν A
    unit : val ν unit
    false : val ν bool
    true : val ν bool
    ƛ<_>_ : ∀ {C} → (A : ValTy) → (ν A → cmp ν C) → val ν (A ⇒ C)
    handler : ∀ {A E C} → (ν A → cmp ν C) → OpCluases ν E C → val ν ((A , E) ⇛ C)

data cmp ν where
    return : ∀ {A E} → val ν A → cmp ν (A , E)
    doop : ∀ {E : Eff} {A' B' : ValTy} {A} → (op A' B') ∈ E → val ν A' → (ν B' → cmp ν (A , E)) → cmp ν (A , E)
    _∙_ : ∀ {A C} → val ν (A ⇒ C) → val ν A → cmp ν C
    if_then_else_ : ∀ {C} → val ν bool → cmp ν C → cmp ν C → cmp ν C
    handle_wiz_ : ∀ {C C'} → cmp ν C → val ν (C ⇛ C') → cmp ν C'

OpCluases ν E D =
    All (λ {(op A' B') →
    -- ( ν A' → val ν ((B' ⇒ D) ⇒ D))}
    ( ν A' → ν (B' ⇒ D) → cmp ν D)}
  ) E

data _[_]vtm↦_ {ν : ValTy → Set} : {A B : ValTy} → (ν A → val ν B) → val ν A → val ν B → Set
data _[_]ctm↦_ {ν : ValTy → Set} : {A : ValTy} {C : CmpTy} → (ν A → cmp ν C) → val ν A → cmp ν C → Set
-- data _[_]opcl↦_ {ν : ValTy → Set} : {A : ValTy} {E : Eff} {C : CmpTy} → (ν A → OpCluases ν E C) → val ν A → OpCluases ν E C → Set
_[_]opcl↦_ : {ν : ValTy → Set} {A : ValTy} {E : Eff} {C : CmpTy} → (ν A → OpCluases ν E C) → val ν A → OpCluases ν E C → Set

_[_,_]ctm₂↦_ : {ν : ValTy → Set} {A B : ValTy} {C : CmpTy} → (ν A → ν B → cmp ν C) → val ν A → val ν B → cmp ν C → Set
_[_,_]ctm₂↦_ {ν } {A} {B} {C} f a b c =
    ∃ λ (f' : ν B → cmp ν C) →
    ((λ x → ƛ< B > f x) [ a ]vtm↦ (ƛ< B > f')) × (f' [ b ]ctm↦ c)

-- data _[_]opcl↦_ {ν} where
--     [] : ∀ {A} {v : val ν A} {C} → _[_]opcl↦_ {C = C} (λ x → [])  v []
--     _∷_ :
--         ∀ {A} {v : val ν A} {A' B'} {C} {E} {px : ν A → ν A' → ν (B' ⇒ C) → cmp ν C} {opcl : ν A → OpCluases ν E C} {px' : ν A' → ν (B' ⇒ C) → cmp ν C} {opcl'} → 
--         (∀ (x : ν A') (k : ν _) → ((λ (a : ν A) → px a x k) [ v ]ctm↦ px' x k)) → 
--         opcl [ v ]opcl↦ opcl' →
--         (λ x → (px x) ∷ (opcl x)) [ v ]opcl↦ (px' ∷ opcl')

_[_]opcl↦_ {ν} {A} {E} {C} opcl v opcl' =
    ∀ {A' B'} (i : op A' B' ∈ E) →
    (x : ν A') → (k : ν (B' ⇒ C)) →
    (λ a → (lookupₐ (opcl a) i) x k) [ v ]ctm↦ (lookupₐ opcl' i) x k


data _[_]vtm↦_ {ν} where
    `= : ∀ {A} {v : val ν A} → (λ x → ` x) [ v ]vtm↦ v
    `≠ : ∀ {A B} {v : val ν A} (x : ν B) → (λ _ → ` x) [ v ]vtm↦ (` x)
    unit : ∀ {A} {v : val ν A} → (λ x → unit) [ v ]vtm↦ unit
    false : ∀ {A} {v : val ν A} → (λ x → false) [ v ]vtm↦ false
    true : ∀ {A} {v : val ν A} → (λ x → true) [ v ]vtm↦ true
    ƛ<>_ :
        ∀ {A B} {C} {v : val ν A} {f : ν A → ν B → cmp ν C} {f' : ν B → cmp ν C} →
        (∀ (b : ν B) → (λ a → f a b) [ v ]ctm↦ f' b) → 
        (λ b → ƛ< B > f b) [ v ]vtm↦ (ƛ< B > f')
    handler :
        ∀ {A A'} {E'} {C'} {v : val ν A}
        {f-ret : ν A → ν A' → cmp ν C'} {f-opcl : ν A → OpCluases ν E' C'}
        {ret : ν A' → cmp ν C'} {opcl : OpCluases ν E' C'} →
        (∀ (y : ν A') → (λ x → f-ret x y) [ v ]ctm↦ ret y) →
        (f-opcl) [ v ]opcl↦ opcl →
        (λ x → handler (f-ret x) (f-opcl x)) [ v ]vtm↦ handler ret opcl

data _[_]ctm↦_ {ν} where
    return :
        ∀ {A B} {E} {s : val ν A}
        {v : val ν B}
        {f : ν A → val ν B} →
        f [ s ]vtm↦ v → 
        (λ x → return {ν = ν} {E = E} (f x)) [ s ]ctm↦ (return v)
    doop :
        ∀ {A B A' B'} {E} {i : op A' B' ∈ E} {s : val ν A}
        {f-v : ν A → val ν A'} {f-c : ν A → ν B' → cmp ν (B , E) }
        {v : val ν A'} {c : ν B' → cmp ν (B , E)} →
        (f-v [ s ]vtm↦ v) →
        (∀ b → (λ x → f-c x b) [ s ]ctm↦ c b) →
        (λ x → doop i (f-v x) (f-c x)) [ s ]ctm↦ doop i v c
    _∙_ :
        ∀ {A A' B'} {s : val ν A}
        {f₁ : ν A → val ν (A' ⇒ B')} {f₂ : ν A → val ν A'}
        {f : val ν (A' ⇒ B')} {x : val ν A'} →
        (f₁ [ s ]vtm↦ f) →
        (f₂ [ s ]vtm↦ x) →
        (λ x → f₁ x ∙ f₂ x) [ s ]ctm↦ (f ∙ x)
    if_then_else_ :
        ∀ {A B} {s : val ν A}
        {fb : ν A → val ν bool} {ft fe : ν A → cmp ν B}
        {b : val ν bool} {t e : cmp ν B} →
        (fb [ s ]vtm↦ b) →
        (ft [ s ]ctm↦ t) →
        (fe [ s ]ctm↦ e) →
        (λ x → if fb x then ft x else fe x) [ s ]ctm↦ (if b then t else e)
    handle_wiz_ :
        ∀ {A} {C C'} {s : val ν A}
        {f₁ : ν A → cmp ν C} {f₂ : ν A → val ν (C ⇛ C')}
        {c : cmp ν C} {v : val ν (C ⇛ C')} →
        (f₁ [ s ]ctm↦ c) →
        (f₂ [ s ]vtm↦ v) →
        (λ x → handle f₁ x wiz f₂ x) [ s ]ctm↦ (handle c wiz v)

E : Eff
E = op unit bool ∷ []

E-decide : op unit bool ∈ E
E-decide = here refl

example_choose : ∀ {ν} {A : ValTy} →  val ν (A ⇒ ((A ⇒ (A , E)) , []))
example_choose {ν} {A} = ƛ< A > (λ x → return (ƛ< A > (λ y →
                        handle doop E-decide unit (λ b → return (` b))
                        wiz handler
                            (
                                λ b → if (` b) then
                                    return (` x)
                                else
                                    return (` y)
                            )
                            (
                                -- (λ z → ƛ< (bool ⇒ (A , E)) > λ k → doop E-decide unit λ b → (` k) ∙ (`  b))
                                (λ z k → doop E-decide unit (λ b → (` k) ∙ (` b)))
                                ∷ []
                            )
                    )))

example_pickTrue : ∀ {ν} {A : ValTy} →  val ν ((A , op unit bool ∷ []) ⇛ (A , []))
example_pickTrue {ν} {A} =
                        handler {E = E}
                            (λ x → return (` x))
                            (
                                -- (λ z → ƛ< (bool ⇒ (A , [])) > λ k → (` k) ∙ true)
                                ((λ z k → (` k) ∙ true))
                                ∷ []
                            )

example_choose_handle_picktrue : ∀ {ν} {A : ValTy} →  cmp ν (bool , [])

data ty (τ : Set) : Set where
    `_ : τ → ty τ
    unit : ty τ
    bool : ty τ
    _⊗_ : ty τ → ty τ → ty τ
    -- rec : ∀ {n} → (Fin n → ty τ) → ty τ
    rec : List (ty τ) → ty τ
    _⇒_ : ty τ → ty τ → ty τ
    Π_ : (τ → ty τ) → ty τ

data _[_]ty↦_ {τ : Set} : (τ → ty τ) → ty τ → ty τ → Set where
    `= : ∀ (A : ty τ) → (λ x → ` x) [ A ]ty↦ A
    `≠ : ∀ (A : ty τ) (x : τ) → (λ _ → ` x) [ A ]ty↦ (` x)
    unit : ∀ {A : ty τ} → (λ _ → unit) [ A ]ty↦ unit
    bool : ∀ {A : ty τ} → (λ _ → bool) [ A ]ty↦ bool
    _⊗_ : ∀ {f₁ f₂} {A A₁ A₂} →
        f₁ [ A ]ty↦ A₁ →
        f₂ [ A ]ty↦ A₂ →
        ---------------
        (λ a → f₁ a ⊗ f₂ a) [ A ]ty↦ (A₁ ⊗ A₂)
    rec : ∀ {A} {l : List (τ → ty τ)} {l' : List (ty τ)} →
        All (λ {(f , e) → f [ A ]ty↦ e}) (zip l l') →
        (λ a → rec (map (λ f → f a) l))[ A ]ty↦ (rec l')
    _⇒_ : ∀ {f₁ f₂} {A A₁ A₂} →
        f₁ [ A ]ty↦ A₁ →
        f₂ [ A ]ty↦ A₂ →
        ---------------
        (λ a → f₁ a ⇒ f₂ a) [ A ]ty↦ (A₁ ⇒ A₂)
    Π_ : ∀ {f : τ → τ → ty τ} {f'} {A } →
        (∀ a → (λ b → f b a) [ A ]ty↦ f' a) → 
        ---------------------------------
        (λ a → Π (f a)) [ A ]ty↦ (Π f')

data term (τ : Set) (ν : ty τ → Set) : ty τ → Set where
    `_ : ∀ {A} → ν A → term τ ν A
    unit : term τ ν unit
    true : term τ ν bool
    false : term τ ν bool
    if_then_else_ : ∀ {A : ty τ} → term τ ν bool → term τ ν A → term τ ν A → term τ ν A
    _⊗_ : ∀ {A B} → term τ ν A → term τ ν B → term τ ν (A ⊗ B)
    _[1] : ∀ {A B} → term τ ν (A ⊗ B) → term τ ν A
    _[2] : ∀ {A B} → term τ ν (A ⊗ B) → term τ ν B
    -- rec : ∀ {n} → {f : Fin n → ty τ} → ((i : Fin n) → term τ ν (f i)) → term τ ν (rec f)
    rec : ∀ {l : List (ty τ)} → (All (λ A → term τ ν A) l) → term τ ν (rec l)
    _[_] : ∀ {l : List (ty τ)} → term τ ν (rec l) → (i : Fin (length l)) → term τ ν (lookup l i)
    ƛ<_>_ : ∀ {B} → (A : ty τ) → (ν A → term τ ν B) → term τ ν (A ⇒ B)
    _∙_ : ∀ {A B} → term τ ν (A ⇒ B) → term τ ν A → term τ ν B
    Λ_ : ∀ {f : τ → ty τ} → ((A : τ) → term τ ν (f A)) → term τ ν (Π f)
    _<>_ : ∀ {f : τ → ty τ} {A} → term τ ν (Π f) → (B : ty τ) → {h : f [ B ]ty↦ A} → term τ ν A

data _[_,_]tmty↦_ {τ : Set} {ν : ty τ → Set} : {f : τ → ty τ} → ((A : τ) → term τ ν (f A)) → (B : ty τ) → {B' : ty τ} → (h : f [ B ]ty↦ B') → term τ ν B' → Set where
    unit : ∀ {A : ty τ} {B : ty τ} → (λ _ → unit) [ B , unit ]tmty↦ unit
    true : ∀ {A : ty τ} {B : ty τ} → (λ _ → true) [ B , bool ]tmty↦ true
    false : ∀ {A : ty τ} {B : ty τ} → (λ _ → false) [ B , bool ]tmty↦ false
    if_then_else_ :
        ∀ {A : τ → ty τ} {A' B : ty τ} {b : term τ ν bool} {t e : term τ ν A'}
        {fb : τ → term τ ν bool} {ft fe : (t : τ) → term τ ν (A t)}
        {h} →
        fb [ B , bool ]tmty↦ b →
        ft [ B , h ]tmty↦ t →
        fe [ B , h ]tmty↦ e →
        (λ x → if fb x then ft x else fe x) [ B , h ]tmty↦ (if b then t else e)
    _⊗_ : 
        ∀ {A B : τ → ty τ} {A' B' C : ty τ} {a : term τ ν A'} {b : term τ ν B'}
        {f₁ : (t : τ) → term τ ν (A t)} {f₂ : (t : τ) → term τ ν (B t)}
        {ha} {hb} →
        f₁ [ C , ha ]tmty↦ a → 
        f₂ [ C , hb ]tmty↦ b → 
        (λ x → f₁ x ⊗ f₂ x) [ C , ha ⊗ hb ]tmty↦ (a ⊗ b)
    -- ƛ<_>_ :
    --     ∀ {A B' C' : ty τ} {B C : τ → ty τ}
    --     {f : (t : τ) → ν (B t) → term τ ν (C t)} {f' : ν B' → term τ ν C'}
    --     {h} →
    --     (h' : B [ A ]ty↦ B') →
    --     (∀ t → ∀ (b : term τ ν (B t)) → {! _[_]tm↦_  !}) →
    --     (λ t → f t {!   !}) [ A , h ]tmty↦ f' {!   !} →
    --     (λ b → ƛ< B b > f b) [ A , h' ⇒ h ]tmty↦ (ƛ< B' > f')
    -- TODO: More Patterns


data _[_]tm↦_ {τ : Set} {ν : ty τ → Set} : {A B : ty τ} → (ν A → term τ ν B) → term τ ν A → term τ ν B → Set where
    `= : ∀ {A : ty τ} {t : term τ ν A} → (λ x → ` x) [ t ]tm↦ t
    `≠ : ∀ {A B : ty τ} {t : term τ ν A} (x : ν B) → (λ _ → ` x) [ t ]tm↦ (` x)
    unit : ∀ {A : ty τ} {t : term τ ν A} → (λ _ → unit) [ t ]tm↦ unit
    true : ∀ {A : ty τ} {t : term τ ν A} → (λ _ → true) [ t ]tm↦ true
    false : ∀ {A : ty τ} {t : term τ ν A} → (λ _ → false) [ t ]tm↦ false
    if_then_else_ :
        ∀ {A B : ty τ} {b : term τ ν bool} {t e : term τ ν A} {s : term τ ν B} {fb : ν B → term τ ν bool} {ft fe : ν B → term τ ν A} →
        fb [ s ]tm↦ b → 
        ft [ s ]tm↦ t → 
        fe [ s ]tm↦ e → 
        (λ x → if fb x then ft x else fe x) [ s ]tm↦ (if b then t else e)
    _⊗_ : 
        ∀ {A B C : ty τ} {a : term τ ν A} {b : term τ ν B} {s : term τ ν C} {f₁ : ν C → term τ ν A} {f₂ : ν C → term τ ν B} →
        f₁ [ s ]tm↦ a → 
        f₂ [ s ]tm↦ b → 
        (λ x → f₁ x ⊗ f₂ x) [ s ]tm↦ (a ⊗ b)
    _[1] : 
        ∀ {A B C : ty τ} {ab : term τ ν (A ⊗ B)} {s : term τ ν C} {f : ν C → term τ ν (A ⊗ B)} →
        f [ s ]tm↦ ab → 
        (λ x → (f x) [1]) [ s ]tm↦ (ab [1])
    _[2] : 
        ∀ {A B C : ty τ} {ab : term τ ν (A ⊗ B)} {s : term τ ν C} {f : ν C → term τ ν (A ⊗ B)} →
        f [ s ]tm↦ ab → 
        (λ x → (f x) [2]) [ s ]tm↦ (ab [2])
    -- rec : 
    --     ∀ {A : ty τ} {s : term τ ν A}
    --     {l : List (ty τ)} {f-r : All (λ B → ν A → term τ ν B) l}
    --     {r : All (λ B → term τ ν B) l} →
    --     (∀ {B} (i : B ∈ l) → (lookupₐ f-r i) [ s ]tm↦ lookupₐ r i) →
    --     (λ x → rec (mapₐ f-r λ _ f → f x)) [ s ]tm↦ (rec r)
    rec : 
        ∀ {A : ty τ} {s : term τ ν A}
        {l : List (ty τ)} {r : ν A → All (λ B → term τ ν B) l}
        {r' : All (λ B → term τ ν B) l} →
        (∀ {B} (i : B ∈ l) → (λ x → lookupₐ (r x) i) [ s ]tm↦ lookupₐ r' i) →
        (λ x → rec (r x)) [ s ]tm↦ (rec r')
    _[_] :
        ∀ {A B : ty τ} {s : term τ ν A}
        {l : List (ty τ)} {f : ν A → term τ ν (rec l)}
        {r : term τ ν (rec l)} →
        f [ s ]tm↦ r →
        (i : B ∈ l) →
        (λ x → (f x) [ toFin i ]) [ s ]tm↦ (r [ toFin i ])
    ƛ<>_ :
        ∀ {A B C : ty τ} {s : term τ ν A}
        {f : ν A → ν B → term τ ν C} {f' : ν B → term τ ν C} →
        (∀ b → (λ a → f a b) [ s ]tm↦ f' b) →
        (λ b → ƛ< B > f b) [ s ]tm↦ (ƛ< B > f')
    _∙_ :
        ∀ {A B C : ty τ} {s : term τ ν A}
        {f₁ : ν A → term τ ν (B ⇒ C)} {f₂ : ν A → term τ ν B}
        {f : term τ ν (B ⇒ C)} {t : term τ ν B} →
        f₁ [ s ]tm↦ f →
        f₂ [ s ]tm↦ t →
        (λ x → f₁ x ∙ f₂ x) [ s ]tm↦ (f ∙ t)
    Λ_ :
        ∀ {A : ty τ} {s : term τ ν A}
        {g : τ → ty τ}
        {f : ν A → (B : τ) → term τ ν (g B)}
        {f' : (B : τ) → term τ ν (g B)} →
        (∀ B → (λ x → f x B) [ s ]tm↦ f' B) →
        (λ x → Λ f x) [ s ]tm↦ (Λ f')
    _<> :
        ∀ {A B C : ty τ} {s : term τ ν A}
        {g : τ → ty τ}
        {h : g [ B ]ty↦ C}
        {f : ν A → term τ ν (Π g)}
        {t : term τ ν (Π g)} →
        f [ s ]tm↦ t →
        (λ x → _<>_ (f x) B {h = h}) [ s ]tm↦ (_<>_ t B {h = h})


{-# TERMINATING #-}
[_]vty : ∀ {τ} → ValTy → ty τ
[_]cty : ∀ {τ} → CmpTy → ty τ
[_]⇛_ : ∀ {τ} → CmpTy → ty τ → ty τ
[_]eff_ : ∀ {τ} → Eff → ty τ → ty τ
[_]sig_ :  ∀ {τ} → Sig → ty τ → ty τ

[ unit ]vty = unit 
[ bool ]vty = bool
[ A ⇒ C ]vty = [ A ]vty ⇒ [ C ]cty
[ C ⇛ D ]vty = [ C ]⇛ [ D ]cty

[ C ]cty = Π λ X → ([ C ]⇛ (` X)) ⇒ (` X)

[ A , E ]⇛ B = ([ A ]vty ⇒ B) ⊗ ([ E ]eff B)

[ E ]eff B = rec (map (λ x → [ x ]sig B) E)

[ op A B ]sig C = [ A ]vty ⇒ (([ B ]vty ⇒ C) ⇒ C)

example_bool_trans : ∀ {τ} → [ bool ]vty ≡ bool {τ}
example_bool_trans = refl

example_fn_trans : ∀ {τ A C} → [_]vty {τ} (A ⇒ C) ≡ [ A ]vty ⇒ [ C ]cty
example_fn_trans = refl

[]vty-subst : ∀ {τ} {A B} → (λ (_ : τ) → [ A ]vty) [ B ]ty↦ [ A ]vty
[]cty-subst : ∀ {τ} {C B} → (λ (_ : τ) → [ C ]cty) [ B ]ty↦ [ C ]cty

[]vty-subst {τ} {unit} {B} = unit
[]vty-subst {τ} {bool} {B} = bool
[]vty-subst {τ} {A ⇒ A'} {B} = []vty-subst ⇒ []cty-subst
[]vty-subst {τ} {(A , E) ⇛ D} {B} = ([]vty-subst ⇒ []cty-subst) ⊗ rec {l = map (λ x → λ _ → [ x ]sig [ D ]cty) E} aux
    where
        aux : ∀ {E} → All (λ { (f , e) → f [ B ]ty↦ e }) (zip (map (λ x _ → [ x ]sig [ D ]cty) E) (map (λ x → [ x ]sig [ D ]cty) E))
        aux {[]} = []
        aux {(op A' B') ∷ E} = ([]vty-subst ⇒ (([]vty-subst ⇒ []cty-subst) ⇒ []cty-subst)) ∷ aux

[]cty-subst {τ} {C = A , E} {B} = Π λ a → (([]vty-subst ⇒ `≠ B a) ⊗ rec {l = map (λ x → λ _ → [ x ]sig (` a)) E} aux) ⇒ `≠ B a
    where
        aux : ∀ {a : τ} {E : Eff} → All (λ { (f , e) → f [ B ]ty↦ e }) (zip (map (λ x z → [ x ]sig (` a)) E) (map (λ x → [ x ]sig (` a)) E))
        aux {a} {[]} = []
        aux {a} {(op A' B') ∷ E} = ([]vty-subst ⇒ (([]vty-subst ⇒ (`≠ B a)) ⇒ (`≠ B a))) ∷ aux


[]sig-[]↦-comm : ∀ {τ} {s} {A B} {f : τ → ty τ} →
    f [ B ]ty↦ A →
    (λ (z : τ) → [ s ]sig (f z)) [ B ]ty↦ ([ s ]sig A)
[]sig-[]↦-comm {τ} {s = op A' B'} {A} {B} h = []vty-subst ⇒ (([]vty-subst ⇒ h) ⇒ h)

[]eff-[]↦-comm : ∀ {τ} {E} {A B} {f : τ → ty τ} →
    f [ B ]ty↦ A →
    (λ (z : τ) → [ E ]eff (f z)) [ B ]ty↦ ([ E ]eff A)
[]eff-[]↦-comm {τ} {E} {A} {B} {f} h = rec {l = map (λ x → λ z → [ x ]sig f z) E} aux
    where
        aux : ∀ {E} → All (λ { (f , e) → f [ B ]ty↦ e }) (zip (map (λ x z → [ x ]sig f z) E) (map (λ x → [ x ]sig A) E))
        aux {[]} = []
        aux {x ∷ E} = []sig-[]↦-comm h ∷ aux
    
[]⇛-[]↦-comm : ∀ {τ} {C} {A B} {f : τ → ty τ} →
    f [ B ]ty↦ A →
    (λ (z : τ) → [ C ]⇛ (f z)) [ B ]ty↦ ([ C ]⇛ A)
[]⇛-[]↦-comm {τ} {A' , B'} {A} {B} {f} h = ([]vty-subst ⇒ h) ⊗ []eff-[]↦-comm h

subst-lemma : ∀ {τ} → (C : CmpTy) → (B : ty τ) → (λ X → ([ C ]⇛ (` X)) ⇒ (` X)) [ B ]ty↦ (([ C ]⇛ B) ⇒ B)
subst-lemma {τ} C B = []⇛-[]↦-comm (`= B) ⇒ (`= B)


[_]vtm : ∀ {τ : Set} {ν : ty τ → Set} {A} → val (ν ∘ [_]vty) A → term τ ν [ A ]vty
[_]ctm : ∀ {τ : Set} {ν : ty τ → Set} {C} → cmp (ν ∘ [_]vty) C → term τ ν [ C ]cty
_/_ : ∀ {τ : Set} {ν : ty τ → Set} {C B} → cmp (ν ∘ [_]vty) C → term τ ν ([ C ]⇛ B) → term τ ν B
[_]opcl : ∀ {τ : Set} {ν : ty τ → Set} {E C} → OpCluases (ν ∘ [_]vty) E C → term τ ν ([ E ]eff [ C ]cty)

[ ` x ]vtm = ` x
[ unit ]vtm = unit
[ false ]vtm = false
[ true ]vtm = true
[ ƛ< A > f ]vtm = ƛ< [ A ]vty > λ x → [ f x ]ctm
[ handler {A = A} ret opcl ]vtm = (ƛ< [ A ]vty > (λ x → [ ret x ]ctm)) ⊗ [ opcl ]opcl

[_]ctm {_} {_} {C} (return v) =
    Λ (λ A → ƛ< [ C ]⇛ (` A) > λ h →
    (return v) / (` h))
[_]ctm {τ} {ν} {C} (doop {E} {A'} {B'} i v c) =
    Λ (λ A → ƛ< [ C ]⇛ (` A) > λ h →
    (doop i v c) / (` h))
[_]ctm {C = C} (f ∙ x) = [ f ]vtm ∙ [ x ]vtm
-- [_]ctm {C = C} (if b then t else e) = if [ b ]vtm then [ t ]ctm else [ e ]ctm
[_]ctm {C = C} (if b then t else e) =
    Λ (λ A → ƛ< [ C ]⇛ (` A) > λ h →
    (if b then t else e) / (` h))
[_]ctm {C = C'} (handle c wiz v) = c / [ v ]vtm

return v / h = (h [1]) ∙ [ v ]vtm
doop {E} {A'} {B'} i v c / h =
    (((h [2]) [ toFin (∈-map i) ]) ∙ [ v ]vtm) ∙ (ƛ< [ B' ]vty > λ x → c x / h)
_/_ {C = C} {B = B} (f ∙ x) h = (_<>_ ([ f ]vtm ∙ [ x ]vtm) B {h = subst-lemma C B}) ∙ h
_/_ {C = C} (if b then t else e) h = if [ b ]vtm then (t / h) else (e / h)
_/_ {C = C'} {B = B} (handle c wiz v) h = (_<>_ (c / [ v ]vtm) B {h = subst-lemma C' B} ) ∙ h

[_]opcl-aux : ∀ {τ : Set} {ν : ty τ → Set} {E D} → OpCluases (ν ∘ [_]vty) E D → All (term τ ν) (map (λ x → [ x ]sig [ D ]cty) E)
[_]opcl-aux [] = []
-- [_]opcl-aux {D = D} (_∷_ {op A' B'} px opcl) = (ƛ< [ A' ]vty > λ x → [ px x ]vtm) ∷ [ opcl ]opcl-aux
[_]opcl-aux {D = D} (_∷_ {op A' B'} px opcl) = (ƛ< [ A' ]vty > λ x → ƛ< [ B' ]vty ⇒ [ D ]cty > λ k → [ (px x k) ]ctm) ∷ [ opcl ]opcl-aux

[_]opcl {τ} {ν} {E} {C} opcl = rec ([ opcl ]opcl-aux)


lookupₐ[]opcl-there : ∀ {τ : Set} {ν : ty τ → Set} {E D} → (opcl : OpCluases (ν ∘ [_]vty) E D) →
    ∀ {A' B'} {A'' B''} {px : (ν [ A'' ]vty) → (ν [ (B'' ⇒ D) ]vty) → cmp (ν ∘ [_]vty) D} → (i : op A' B' ∈ E)  →
    lookupₐ ([_]opcl-aux {τ} {ν} (px ∷ opcl)) (∈-map (there i)) ≡ lookupₐ ([_]opcl-aux {τ} {ν} opcl) (∈-map i)
lookupₐ[]opcl-there opcl i = refl
lookupₐ[]opcl-aux :
    ∀ {τ : Set} {ν : ty τ → Set} {E D} → (opcl : OpCluases (ν ∘ [_]vty) E D) →
    ∀ {A' B'} → (i : op A' B' ∈ E) →
    lookupₐ ([_]opcl-aux {τ} {ν} opcl) (∈-map i) ≡ ƛ< [ A' ]vty > λ (x : ν _) → ƛ< [ B' ]vty ⇒ [ D ]cty > λ (k : ν _) → [ ((lookupₐ opcl i) x k) ]ctm
lookupₐ[]opcl-aux (px ∷ opcl) (here refl) = refl
lookupₐ[]opcl-aux {τ} {ν} {E = op A'' B'' ∷ xs} {D = (A , E')} (px ∷ opcl) (there i) rewrite lookupₐ[]opcl-there {τ} {ν} opcl {px = px} i = lookupₐ[]opcl-aux opcl i

 
example_false_trans : ∀ {τ ν} → [ false ]vtm ≡ false {τ} {ν}
example_false_trans = refl

-- [ ƛ< bool > (λ x → return {E = []} (` x)) ]vtm

example_vtm : ∀ {ν} → val ν (bool ⇒ (bool , []))
example_vtm = ƛ< bool > (λ x → return {E = []} (` x))

example_vtm_trans : ∀ {τ ν} → term τ ν ([ (bool ⇒ (bool , [])) ]vty)
example_vtm_trans = [ ƛ< bool > (λ x → return {E = []} (` x)) ]vtm

-- example_vtm' : ∀ {ν} → val ν (bool ⇒ (unit , []))
-- example_vtm' = ƛ< bool > (λ x → return {E = []} (` x))

-- example_vtm'_trans : ∀ {τ ν} → term τ ν ([ (bool ⇒ (unit , [])) ]vty)
-- example_vtm'_trans = [ ƛ< bool > (λ x → return {E = []} (` x)) ]vtm

Val : ValTy → Set₁
Val = λ (A : ValTy) → ∀ {ν : ValTy → Set} → val ν A

Cmp : CmpTy → Set₁
Cmp = λ (C : CmpTy) → ∀ {ν : ValTy → Set} → cmp ν C

Ty : Set₁
Ty = ∀ {τ} → ty τ

Term : Ty → Set₁
Term A = ∀ {τ : Set} {ν : ty τ → Set} → term τ ν (A {τ})

[_]v : ∀ {A} → Val A → Term [ A ]vty
[_]v {A} v {τ} {ν} =  [ v {ν ∘ [_]vty} ]vtm

[_]c : ∀ {C} → Cmp C → Term [ C ]cty
[_]c {C} v {τ} {ν} =  [ v {ν ∘ [_]vty} ]ctm


data _↝ctm_ {ν : ValTy → Set} : {C : CmpTy} → cmp ν C → cmp ν C → Set where
    β-ifte-true :
        ∀ {C} {t e : cmp ν C} →
        (if true then t else e) ↝ctm t
    β-ifte-false :
        ∀ {C} {t e : cmp ν C} →
        (if false then t else e) ↝ctm e
    β-app :
        ∀ {A} {C} {f : ν A → cmp ν C} {s : val ν A} {t : cmp ν C} →
        f [ s ]ctm↦ t →
        ((ƛ< A > (λ x → f x)) ∙ s) ↝ctm t
    ξ-handle :
        ∀ {C C'} {c c' : cmp ν C} {h : val ν (C ⇛ C')} →
        c ↝ctm c' →
        (handle c wiz h) ↝ctm (handle c' wiz h)
    β-handle-return :
        ∀ {A} {C} {E} {v : val ν A} {ret : ν A → cmp ν C} {opcl : OpCluases ν E C} {cᵣ : cmp ν C} →
        ret [ v ]ctm↦ cᵣ →
        (handle return v wiz handler ret opcl) ↝ctm cᵣ
    β-handle-doop :
        ∀ {A A' B'} {C} {E}
        {i : op A' B' ∈ E} {v : val ν A'} {c : ν B' → cmp ν (A , E)} {ret : ν A → cmp ν C}
        {opcl : OpCluases ν E C} {c' : cmp ν C} →
        -- {f'} →
        -- ∀ {cᵢ : ν (B' ⇒ C) → ν A' → cmp ν C} →
        -- opcl [ i ]= f → 
        (lookupₐ opcl i) [ v , ƛ< B' > (λ x → handle (c x) wiz (handler ret opcl)) ]ctm₂↦ c' →
        -- (lookupₐ opcl i) [ v ]vtm↦ f' →
        -- (lookupₐ opcl i) [ v ]vtm↦ (ƛ< B' ⇒ C > f') →
        -- (f') [ ƛ< B' > (λ x → handle (c x) wiz (handler ret opcl)) ]ctm↦ c' →
        -- (λ x → f' ∙ (` x)) [ ƛ< B' > (λ x → handle (c x) wiz (handler ret opcl)) ]ctm↦ c' → 
        (handle doop i v c wiz handler ret opcl) ↝ctm c'

data frame[_]tm↦_ {τ : Set} {ν : ty τ → Set} : ty τ → ty τ → Set where
    if[∙]then_else_ : ∀ {A} → term τ ν A → term τ ν A → frame[ bool ]tm↦ A
    if_then[∙]else_ : ∀ {A} → term τ ν bool → term τ ν A → frame[ A ]tm↦ A
    if_then_else[∙] : ∀ {A} → term τ ν bool → term τ ν A → frame[ A ]tm↦ A
    [∙]⊗_ : ∀ {A B} → term τ ν B → frame[ A ]tm↦ (A ⊗ B)
    _⊗[∙] : ∀ {A B} → term τ ν A → frame[ B ]tm↦ (A ⊗ B)
    [∙][1] : ∀ {A B} → frame[ A ⊗ B ]tm↦ A
    [∙][2] : ∀ {A B} → frame[ A ⊗ B ]tm↦ B
    [∙][_] : ∀ {l : List (ty τ)} → (i : Fin (length l)) → frame[ (rec l) ]tm↦ (lookup l i)
    [∙]∙_ : ∀ {A B} → term τ ν A → frame[ A ⇒ B ]tm↦ B
    _∙[∙] : ∀ {A B} → term τ ν (A ⇒ B) → frame[ A ]tm↦ B
    [∙]<>_ : ∀ {A} {f : τ → ty τ} → (B : ty τ) → {h : f [ B ]ty↦ A} → frame[ Π f ]tm↦ A
    -- More patterns
frame-apply : ∀ {τ} {ν} {A B} → frame[ A ]tm↦ B → term τ ν A → term τ ν B
frame-apply {τ} {ν} {.bool} {B} (if[∙]then t else e) s = if s then t else e
frame-apply {τ} {ν} {A} {B} (if b then[∙]else e) s = if b then s else e
frame-apply {τ} {ν} {A} {B} if b then t else[∙] s = if b then t else s
frame-apply {τ} {ν} {A} {B} ([∙]⊗ b) s = s ⊗ b
frame-apply {τ} {ν} {A} {B} (a ⊗[∙]) s = a ⊗ s
frame-apply {τ} {ν} {.(_ ⇒ B)} {B} ([∙]∙ x) s = s ∙ x
frame-apply {τ} {ν} {A} {B} (f ∙[∙]) s = f ∙ s
frame-apply {τ} {ν} {.(Π _)} {B} ([∙]<>_ B' {h}) s = _<>_ s B' {h}
frame-apply {τ} {ν} {.(B ⊗ _)} {B} [∙][1] s = s [1]
frame-apply {τ} {ν} {.(_ ⊗ B)} {B} [∙][2] s = s [2]
frame-apply {τ} {ν} {rec l} {.(lookup l i)} [∙][ i ] s = s [ i ]

data _↝tm_ {τ : Set} {ν : ty τ → Set} : {A : ty τ} → term τ ν A → term τ ν A → Set where
    β-[1] :
        ∀ {A B} {a : term τ ν A} {b : term τ ν B} →
        ((a ⊗ b) [1]) ↝tm a
    β-[2] :
        ∀ {A B} {a : term τ ν A} {b : term τ ν B} →
        ((a ⊗ b) [2]) ↝tm b
    β-[_] :
        ∀ {A} {l : List (ty τ)}
        {r : All (λ A → term τ ν A) l} →
        {i : A ∈ l} →
        ((rec r)[ toFin i ]) ↝tm (lookupₐ r i)
    β-ifte-true :
        ∀ {A} {t e : term τ ν A} →
        (if true then t else e) ↝tm t
    β-ifte-false :
        ∀ {A} {t e : term τ ν A} →
        (if false then t else e) ↝tm e
    β-app :
        ∀ {A B} {s : term τ ν A} {f : ν A → term τ ν B} {t : term τ ν B} →
        f [ s ]tm↦ t →
        ((ƛ< A > f) ∙ s) ↝tm t
    β-<> :
        ∀ {A B B'} {s : term τ ν A}
        {g : τ → ty τ} {f : (A : τ) → term τ ν (g A)} →
        (h : g [ B ]ty↦ B') → 
        (t : term τ ν B') →
        f [ B , h ]tmty↦ t →
        (_<>_ (Λ f) B {h = h}) ↝tm t
    ξ[_]_ :
        ∀ {A B} {t t' : term τ ν A} →
        (f : frame[ A ]tm↦ B) → 
        (t ↝tm t')→ 
        frame-apply f t ↝tm frame-apply f t'
    -- TODO : More patterns

exapmle-↝tm : ∀ {τ} {ν} → (false {τ} {ν} ⊗ (((false ⊗ true)[1]) ⊗ true)) ↝tm ((false ⊗ (false ⊗ true)))
exapmle-↝tm = ξ[ false ⊗[∙] ] (ξ[ [∙]⊗ true ] β-[1])

data _↝*tm_ {τ : Set} {ν : ty τ → Set} : {A : ty τ} → term τ ν A → term τ ν A → Set where
    refl : ∀ {A} {t : term τ ν A} → t ↝*tm t
    _⊙_ :
        ∀ {A} {t₁ t₂ t₃ : term τ ν A} →
        (t₁ ↝tm t₂) → t₂ ↝*tm t₃ →
        t₁ ↝*tm t₃

data _↝+tm_ {τ : Set} {ν : ty τ → Set} : {A : ty τ} → term τ ν A → term τ ν A → Set where
    _⊙_ :
        ∀ {A} {t₁ t₂ t₃ : term τ ν A} →
        (t₁ ↝tm t₂) → t₂ ↝*tm t₃ →
        t₁ ↝+tm t₃

ξ[_]*_ :
    ∀ {τ} {ν} {A B} {t t' : term τ ν A} →
    (f : frame[ A ]tm↦ B) → 
    (t ↝*tm t')→ 
    frame-apply f t ↝*tm frame-apply f t'
ξ[_]+_ :
    ∀ {τ} {ν} {A B} {t t' : term τ ν A} →
    (f : frame[ A ]tm↦ B) → 
    (t ↝+tm t')→ 
    frame-apply f t ↝+tm frame-apply f t'

[]ctm↝*/ :
    ∀ {τ} {ν : ty τ → Set}
    {C : CmpTy}
    {t : cmp (ν ∘ [_]vty) C}
    {B : ty τ} {h : term τ ν ([ C ]⇛ B)} →
    ((_<>_ [ t ]ctm B {h = subst-lemma C B} ) ∙ h) ↝*tm (t / h)
-- []ctm↝*/ {t = return v} {B} = (ξ[ ([∙]∙ _) ] β-<> (([]⇛-[]↦-comm (`= B)) ⇒ `= B) _ {!   !}) ⊙ {!   !}
-- []ctm↝*/ {t = doop i v c} = {!   !}
-- []ctm↝*/ {t = f ∙ x} = refl
-- []ctm↝*/ {t = if b then t else e} = {!   !}
-- []ctm↝*/ {t = handle h wiz v} = refl

[]vtm-subst-comm :
    ∀ {τ} {ν : ty τ → Set} {A B : ValTy} {s : val (ν ∘ [_]vty) A}
    {t : val (ν ∘ [_]vty) B}
    {f : ν [ A ]vty → val (ν ∘ [_]vty) B} →
    f [ s ]vtm↦ t →
    (λ x → [ f x ]vtm) [ [ s ]vtm ]tm↦ ([_]vtm {τ = τ} {ν = ν} t)
[]ctm-subst-comm :
    ∀ {τ} {ν : ty τ → Set} {A : ValTy} {C : CmpTy}
    {f : ν [ A ]vty → cmp (ν ∘ [_]vty) C} {s : val (ν ∘ [_]vty) A}
    {t : cmp (ν ∘ [_]vty) C} →
    f [ s ]ctm↦ t →
    (λ x → [ f x ]ctm) [ [ s ]vtm ]tm↦ ([_]ctm {τ = τ} {ν = ν} t)
[]opcl-subst-comm :
    ∀ {τ} {ν : ty τ → Set} {A : ValTy} {E : Eff} {C : CmpTy}
    {s : val (ν ∘ [_]vty) A}
    {f-opcl : (ν ∘ [_]vty) A → OpCluases (ν ∘ [_]vty) E C} {opcl : OpCluases (ν ∘ [_]vty) E C} →
    f-opcl [ s ]opcl↦ opcl →
    (λ (x : (ν ∘ [_]vty) A) → [ f-opcl x ]opcl) [ [ s ]vtm ]tm↦ ([_]opcl {τ = τ} {ν = ν} opcl)
/-subst-comm :
    ∀ {τ} {ν : ty τ → Set} {A : ValTy} {C : CmpTy} {D : ty τ}
    {f : (ν ∘ [_]vty) A → cmp (ν ∘ [_]vty) C} {s : val (ν ∘ [_]vty) A} {t : cmp (ν ∘ [_]vty) C}
    {fh : ν [ A ]vty →  term τ ν ([ C ]⇛ D)}
    {h : term τ ν ([ C ]⇛ D)} →
    f [ s ]ctm↦ t →
    fh [ [ s ]vtm ]tm↦ h →
    (λ x → f x / fh x) [ [ s ]vtm ]tm↦ (t / h)

[]vtm-subst-comm `= = `=
[]vtm-subst-comm (`≠  x) = `≠ x
[]vtm-subst-comm unit = unit
[]vtm-subst-comm false = false
[]vtm-subst-comm true = true
[]vtm-subst-comm (ƛ<> h) = ƛ<> λ b → []ctm-subst-comm (h b)
[]vtm-subst-comm (handler h-f-ret h-opcl) = (ƛ<> (λ b → []ctm-subst-comm (h-f-ret b))) ⊗ []opcl-subst-comm h-opcl

[]ctm-subst-comm (return h-v) = Λ λ B → ƛ<> (λ b → /-subst-comm (return h-v) (`≠ b))
[]ctm-subst-comm (doop h-v h-c) = Λ λ C → ƛ<> (λ c' → /-subst-comm (doop h-v h-c) (`≠ c'))
[]ctm-subst-comm (h-f ∙ h-x) = ([]vtm-subst-comm h-f) ∙ ([]vtm-subst-comm h-x)
[]ctm-subst-comm (if h-b then h-t else h-e) = Λ λ C → ƛ<> (λ c' → /-subst-comm (if h-b then h-t else h-e) (`≠ c'))
[]ctm-subst-comm (handle h-c wiz h-v) = /-subst-comm h-c ([]vtm-subst-comm h-v)

/-subst-comm (return h-v) h-subst-fh = (h-subst-fh [1]) ∙ []vtm-subst-comm h-v
/-subst-comm (doop {i = i} h-v h-c) h-subst-fh = (((h-subst-fh [2]) [ ∈-map i ]) ∙ []vtm-subst-comm h-v) ∙ (ƛ<> λ b → /-subst-comm (h-c b) h-subst-fh)
/-subst-comm (h-f ∙ h-x) h-subst-fh = ((([]vtm-subst-comm h-f) ∙ ([]vtm-subst-comm h-x)) <>) ∙ h-subst-fh
/-subst-comm (if h-x then h-subst-t else h-subst-e) h-subst-fh = if []vtm-subst-comm h-x then /-subst-comm h-subst-t h-subst-fh else /-subst-comm h-subst-e h-subst-fh
/-subst-comm (handle h-subst-c wiz h-subst-v) h-subst-fh = ((/-subst-comm h-subst-c ([]vtm-subst-comm h-subst-v)) <>) ∙ h-subst-fh

[]opcl-subst-comm-aux :
    ∀ {τ} {ν} {A} {A' B'} {C} {E} {s : val (ν ∘ [_]vty) A} {i : op A' B' ∈ E} {opcl : ν [ A ]vty → OpCluases _ E C} {opcl' : OpCluases _ E C} →
    opcl [ s ]opcl↦ opcl' →
    (λ x → lookupₐ ([_]opcl-aux {τ} {ν} (opcl x)) (∈-map i)) [ [ s ]vtm ]tm↦ lookupₐ [ opcl' ]opcl-aux (∈-map i)
[]opcl-subst-comm-aux {τ} {ν} {i = i} {opcl} h-subst =
    let aux = h-subst i in
    let aux' = λ x k → []ctm-subst-comm (aux x k) in
    {! !}

[]opcl-subst-comm h-subst =
    rec λ i →
        let (sig , h , j) = ∈-map-inv i in
        case sig of λ where
            (op A' B') → let aux = {! h-subst j  !} in {!   !}

-- [↝]ctm :
--     ∀ {τ : Set} {ν : ty τ → Set} {C} {t t' : cmp (ν ∘ [_]vty) C} → 
--     t ↝ctm t' →
--     [ t ]ctm ↝+tm [ t' ]ctm
↝/h :
    ∀ {τ : Set} {ν : ty τ → Set} {C} {B} {t t' : cmp (ν ∘ [_]vty) C} → {h : term τ ν ([ C ]⇛ B)} →
    t ↝ctm t' →
    (t / h) ↝+tm (t' / h)

↝/h-aux :
    ∀ {τ} {ν} {E} {A' B'} {C} (opcl : OpCluases _ E C) (i : op A' B' ∈ E) {f'} {v} →
    (λ x → ƛ< B' ⇒ C > lookupₐ opcl i x) [ v ]vtm↦ (ƛ< B' ⇒ C > f') →
    (lookupₐ ([_]opcl-aux {τ} {ν} opcl) (∈-map i) ∙ [ v ]vtm) ↝tm (ƛ< [ B' ]vty ⇒ (Π (λ X → ([ C ]⇛ (` X)) ⇒ (` X))) > (λ x → [ f' x ]ctm))
↝/h-aux {τ} {ν} {E} {A'} {B'} {(A , E')} opcl i {f'} {v} h-subst rewrite lookupₐ[]opcl-aux {τ} {ν} opcl i = β-app ([]vtm-subst-comm h-subst)

-- [↝]ctm {τ} {ν} {C} {.(if true then t' else _)} {t'} β-ifte-true = {!   !} ⊙ {!   !}
-- [↝]ctm {τ} {ν} {C} {.(if false then _ else t')} {t'} β-ifte-false = {!   !}
-- [↝]ctm {τ} {ν} {C} {.(handle _ wiz _)} {.(handle _ wiz _)} (ξ-handle htt') = {!   !}

↝/h {τ} {ν} {C} {B} {.(if true then t' else _)} {t'} {h} β-ifte-true = β-ifte-true ⊙ refl
↝/h {τ} {ν} {C} {B} {.(if false then _ else t')} {t'} {h} β-ifte-false = β-ifte-false ⊙ refl
↝/h {τ} {ν} {C} {B} {.(handle _ wiz _)} {.(handle _ wiz _)} {h} (ξ-handle htt') = ξ[ [∙]∙ h ]+ (ξ[ ([∙]<> B) ]+ ↝/h htt')
↝/h {τ} {ν} {C} {B} {.((ƛ< _ > _) ∙ _)} {t'} {h} (β-app {f = f} h-subst) =
    (ξ[ ([∙]∙ h) ] (ξ[ [∙]<> B ] β-app {t = [ t' ]ctm} ([]ctm-subst-comm h-subst))) ⊙ []ctm↝*/
↝/h {τ} {ν} {C} {B} {.(handle return _ wiz handler _ _)} {t'} {h} (β-handle-return {v = v} h-subst) =
    (ξ[ [∙]∙ h ] (ξ[ ([∙]<> B) ] (ξ[ ([∙]∙ [ v ]vtm) ] β-[1]))) ⊙
    ((ξ[ ([∙]∙ h) ] (ξ[ (([∙]<> B)) ] β-app {t = [ t' ]ctm} ([]ctm-subst-comm h-subst))) ⊙ []ctm↝*/)
↝/h {τ} {ν} {C} {B} {handle_wiz_ (doop i v c) (handler ret opcl)} {t'} {h} (β-handle-doop {_} {A'} {B'} (f' , (h-subst₁ , h-subst₂))) =
    (ξ[ [∙]∙ h ] (ξ[ ([∙]<> B) ] (ξ[ [∙]∙ _ ] (ξ[ [∙]∙ _ ] (ξ[ [∙][ _ ] ] β-[2]))))) ⊙
    ((ξ[ [∙]∙ _ ] (ξ[ ([∙]<> B) ] (ξ[ [∙]∙ _ ] (ξ[ ([∙]∙ _) ] β-[_])))) ⊙
    ((ξ[ [∙]∙ _ ] (ξ[ ([∙]<> B) ] (ξ[ [∙]∙ _ ] ↝/h-aux opcl i h-subst₁))) ⊙
    ((ξ[ ([∙]∙ _) ] (ξ[ (([∙]<> B)) ] (β-app ([]ctm-subst-comm h-subst₂))))
    ⊙ []ctm↝*/)))
        

-- ↝/h {τ} {ν} {C = (A , E)} {B} {handle_wiz_ (doop i v c) (handler ret opcl)} {t'} {h} (β-handle-doop (f' , (h-subst₁ , h-subst₂))) with opcl
-- ... | px ∷ opcl with i
-- ... | here refl  =
--     (ξ[ [∙]∙ h ] (ξ[ ([∙]<> B) ] (ξ[ [∙]∙ _ ] (ξ[ [∙]∙ _ ] (ξ[ [∙][ _ ] ] β-[2]))))) ⊙
--     (((ξ[ [∙]∙ _ ] (ξ[ ([∙]<> B) ] (ξ[ [∙]∙ _ ] (ξ[ ([∙]∙ _) ] β-[_]))))) ⊙
--     (((ξ[ [∙]∙ _ ] (ξ[ ([∙]<> B) ] (ξ[ [∙]∙ _ ] β-app ([]vtm-subst-comm h-subst₁))))) ⊙
--     (((ξ[ ([∙]∙ _) ] (ξ[ (([∙]<> B)) ] (β-app ([]ctm-subst-comm h-subst₂))))) ⊙
--     []ctm↝*/)))
-- ... | there i  =
--     (ξ[ [∙]∙ h ] (ξ[ ([∙]<> B) ] (ξ[ [∙]∙ _ ] (ξ[ [∙]∙ _ ] (ξ[ [∙][ _ ] ] β-[2]))))) ⊙
--     (((ξ[ [∙]∙ _ ] (ξ[ ([∙]<> B) ] (ξ[ [∙]∙ _ ] (ξ[ ([∙]∙ _) ] β-[_]))))) ⊙
--     (((ξ[ [∙]∙ _ ] (ξ[ ([∙]<> B) ] (ξ[ [∙]∙ _ ] {!   !})))) ⊙
--     (((ξ[ ([∙]∙ _) ] (ξ[ (([∙]<> B)) ] (β-app ([]ctm-subst-comm h-subst₂))))) ⊙
--     []ctm↝*/)))        