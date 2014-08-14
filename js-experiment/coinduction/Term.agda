{-# OPTIONS --copatterns #-}
module coinduction.Term where

open import prelude
open import uri
open import coinduction.Proto

data Progress : Proto' → Proto' → Set₁ where
  end  : Progress end end
  com : ∀ {c M P}{m : M} → Progress (com c P) (obs (P m))

-- move later

data TransClos {a r}{A : Set a}(R : A → A → Set r)(x : A) : A → Set (r ⊔ a) where
  nil : ∀ {y} → R x y → TransClos R x y
  _∷_ : ∀ {y z} → R x y → TransClos R y z → TransClos R x z

module _ {a r}{A : Set a}{R : A → A → Set r} where
  _++_ : ∀ {x y z} → TransClos R x y → TransClos R y z → TransClos R x z
  nil x₁ ++ ys = x₁ ∷ ys
  (x₁ ∷ xs) ++ ys = x₁ ∷ (xs ++ ys)

module _ {r}(R : Proto' → Proto' → Set r) where
  data Lift : Env → Env → Set (r ⊔ ₛ ₀) where
    ε : Lift ε ε
    _,_↦_ : ∀ {Δ Δ' P P'} → Lift Δ Δ' → ∀ d → R P P' → Lift (Δ , d ↦ P) (Δ' , d ↦ P')

data P⊢ᶜ (X : Env → Set₁)(Δ : Env) : Set₁ where
  end : (e : X Δ) → P⊢ᶜ X Δ

  output : ∀ {d M P}
         (l : d ↦ send P ∈ Δ) → (m : M)
         (p : P⊢ᶜ X (Δ [ l ≔ m ]))
         --------------------
           → P⊢ᶜ X Δ

  input : ∀ {d M}{P : M → _}
            (l : d ↦ recv P ∈ Δ)
            (p : ∀ m → P⊢ᶜ X (Δ [ l ≔ m ]))
            ----------------------------
                 → P⊢ᶜ X Δ

⊢ᶜ' : Env → Set₁
⊢ᶜ'' : (Env → Set₁) → Env → Set₁

record X⊢ᶜ (X : Env → Set₁)(Δ : Env) : Set₁ where
  coinductive
  constructor mk
  field
    ⊢obs : ⊢ᶜ'' X Δ
open X⊢ᶜ

⊢ᶜ'' X = P⊢ᶜ (λ Δ' → X Δ' × X⊢ᶜ X Δ')

⊢ᶜ' Δ = ⊢ᶜ'' (λ Δ' → Lift (TransClos Progress) Δ Δ') Δ

⊢ᶜ : Env → Set₁
⊢ᶜ Δ = X⊢ᶜ (Lift (TransClos Progress) Δ) Δ

lemma : ∀ {Δ Δ₀ Δ₁}{Δ' Δ₀' Δ₁'} →
        Zip Δ  Δ₀  Δ₁  →
        Zip Δ' Δ₀' Δ₁' →
        Lift (TransClos Progress) Δ₀ Δ₀' →
        Lift (TransClos Progress) Δ₁ Δ₁' → Lift (TransClos Progress) Δ Δ'
lemma ε ε ε ε = ε
lemma (Δₛ , d ↦₀ P) (Δₛ' , .d ↦₀ P') (A , .d ↦ x) (B , .d ↦ x₁) = lemma Δₛ Δₛ' A B , d ↦ x
lemma (Δₛ , d ↦₀ P) (Δₛ' , .d ↦₁ P') (A , .d ↦ x) (B , .d ↦ x₁) = lemma Δₛ Δₛ' A B , d ↦ (x ++ x₁)
lemma (Δₛ , d ↦₁ P) (Δₛ' , .d ↦₀ P') (A , .d ↦ x) (B , .d ↦ x₁) = lemma Δₛ Δₛ' A B , d ↦ (x₁ ++ x)
lemma (Δₛ , d ↦₁ P) (Δₛ' , .d ↦₁ P') (A , .d ↦ x) (B , .d ↦ x₁) = lemma Δₛ Δₛ' A B , d ↦ x₁

module _ {X Y Z}(cont : ∀ {Δ Δ₀ Δ₁} → [ Δ is Δ₀ ⋎ Δ₁ ] → X Δ₀ → Y Δ₁ → Z Δ) where
  mixPᶜ : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
           (p : X⊢ᶜ X Δ₀)
           (q : X⊢ᶜ Y Δ₁)
           -------------
             → X⊢ᶜ Z Δ

  mixPᶜ' : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
           (p : ⊢ᶜ'' X Δ₀)
           (q : ⊢ᶜ'' Y Δ₁)
           -------------
             → ⊢ᶜ'' Z Δ
  mixPᶜ' Δₛ (output l m p) q = output (Zip-com∈₀ Δₛ l) m (mixPᶜ' (Zip-≔₀ l Δₛ) p q)
  mixPᶜ' Δₛ (input l p) q = input (Zip-com∈₀ Δₛ l) λ m → (mixPᶜ' (Zip-≔₀ l Δₛ) (p m) q)
  mixPᶜ' Δₛ (end (e , p)) (end (e₁ , q)) = end (cont Δₛ e e₁ , mixPᶜ Δₛ p q)
  mixPᶜ' Δₛ (end e) (output l m q) = output (Zip-com∈₁ Δₛ l) m (mixPᶜ' (Zip-≔₁ l Δₛ) (end e) q)
  mixPᶜ' Δₛ (end e) (input l q) = input (Zip-com∈₁ Δₛ l) λ m → mixPᶜ' (Zip-≔₁ l Δₛ) (end e) (q m)

  ⊢obs (mixPᶜ Δₛ p q) = mixPᶜ' Δₛ (⊢obs p) (⊢obs q)


mixᶜ : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
         (p : ⊢ᶜ Δ₀)
         (q : ⊢ᶜ Δ₁)
         -------------
           → ⊢ᶜ Δ
mixᶜ Δₛ = mixPᶜ (lemma Δₛ) Δₛ


-- -}
-- -}
-- -}
-- -}
-- -}
