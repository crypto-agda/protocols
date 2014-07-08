open import libjs
open import proc
open import proto
open import prelude

module Types where

SERIAL = JSValue

SER : Set → Set
SER M = M ≃? SERIAL

data 𝟘 : Set where

_≢_ : {A : Set}(x y : A) → Set₀
x ≢ y = x ≡ y → 𝟘

infixl 5 _,_↦_
data Env : Set₁ where
  ε : Env
  _,_↦_ : (Δ : Env)(d : URI)(P : Proto) → Env

[_↦_] : URI → Proto → Env
[ d ↦ P ] = ε , d ↦ P

infixr 4 _+++_
_+++_ : Env → Env → Env
Δ +++ ε = Δ
Δ +++ (Δ' , d ↦ P) = (Δ +++ Δ') , d ↦ P


data _↦_∈_ (d : URI)(P : Proto) : Env → Set₁ where
  here : ∀ {Δ} → d ↦ P ∈ (Δ , d ↦ P)
  there : ∀ {Δ d' P'} → d ↦ P ∈ Δ
                      → d ↦ P ∈ (Δ , d' ↦ P')

module _ {d c M}{{_ : M ≃? SERIAL}} {P} where
  _[_≔_] : (Δ : Env) → d ↦ com c {M} P ∈ Δ → M → Env
  ._ [ here {Δ} ≔ m ] = Δ , d ↦ P m
  ._ [ there {d' = d'}{P'} var ≔ m ] = _ [ var ≔ m ] , d' ↦ P'

AllEnv : (P : URI → Proto → Set) → Env → Set
AllEnv P ε = 𝟙
AllEnv P (Δ , d ↦ p) = AllEnv P Δ × P d p

Ended : Proto → Set
Ended end = 𝟙
Ended (com _ P) = 𝟘

module _ {M : Set}{{_ : SER M}} where
  _parsesTo_ : SERIAL → M → Set
  s parsesTo m = succeed m ≡ parse s

data _⊢_ (Δ : Env) : JSProc → Set₁ where

  end : {_ : AllEnv (λ _ p → Ended p) Δ}
     → --------------
         Δ ⊢ end

  output : ∀ {d M s m p}{{_ : SER M}}{P : M → Proto}
        → (l : d ↦ send P ∈ Δ) → s parsesTo m → Δ [ l ≔ m ] ⊢ p
        → ------------------
          Δ ⊢ output d s p

  input : ∀ {d p M}{{_ : SER M}}{P : M → Proto}
        → (l : d ↦ recv P ∈ Δ) → (∀ s m → s parsesTo m → Δ [ l ≔ m ] ⊢ p s)
        → --------------------
           Δ ⊢ input d p

  start : ∀ {s p} P
        → [ clientURI ↦ dual P ] ⊢ s → (∀ d → (Δ , d ↦ P) ⊢ p d)
        → -------------------
          Δ ⊢ start s p

toProcWT : ∀ {d} P → (p : ⟦ P ⟧) → [ d ↦ P ] ⊢ toProc d P p
toProcWT end p = end
toProcWT (send P) (m , p) = output here (sym (rinv m)) (toProcWT (P m) p)
toProcWT (recv P) p = input here λ { s m prf → subst (λ X → _ ⊢ [succeed: _ ,fail: _ ] X)
                                                     prf (toProcWT (P m) (p m)) }


-- -}
-- -}
-- -}
-- -}
-- -}
