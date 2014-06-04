open import Algebra
open import Type
open import Data.One
open import Data.Two
open import Data.Nat
open import Data.Sum.NP hiding ([_,_]′)
open import Data.Product.NP
open import Data.List
open import Data.List.Properties
open import HoTT
open import Function.NP
open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP

open import Control.Protocol renaming (In to O; Out to J; dualᴵᴼ to O↔J)

module Control.Protocol.GameSemantics where

_∷=_ : ∀ {a}{A : ★_ a}{x y : A}{xs ys} → (x ≡ y) → (xs ≡ ys) → (x ∷ xs) ≡ (y ∷ ys)
_∷=_ e e' = ap₂ _∷_ e e'

data Move s : ★ where
  move : (ms : List (Move (O↔J s))) → Move s

Arena = List ∘ Move

move= : ∀ {s}{xs ys : Arena (O↔J s)} → xs ≡ ys → move xs ≡ move ys
move= = ap move

dualᴹ : ∀ {s} → Move s → Move (O↔J s)
dualᴬ : ∀ {s} → List (Move s) → List (Move (O↔J s))
dualᴹ (move ms) = move (dualᴬ ms)
dualᴬ []        = []
dualᴬ (m ∷ ms)  = dualᴹ m ∷ dualᴬ ms

-- 1-move : ∀ {s} → Move (O↔J s) → Move s
pattern 1-move m = move (m ∷ [])

-- 2-moves : ∀ {s}(a b : Move (O↔J s)) → Move s
pattern 2-moves a b = move (a ∷ b ∷ [])

⊤ᴬ : ∀ {s} → Arena s
⊤ᴬ = []

⊥ᴬ : ∀ {s} → Arena s
⊥ᴬ = move [] ∷ []

2ᴬ : ∀ {s} → Arena s
2ᴬ = move [] ∷ move [] ∷ []

2ᴬ' : ∀ {s} → Arena s
2ᴬ' = move 2ᴬ ∷ []

_×ᴬ_ : ∀ {s} → Arena s → Arena s → Arena s
a ×ᴬ b = a ++ b

_⅋ᴬ_ : ∀ {s} → Arena (O↔J s) → Arena s → Arena s
a ⅋ᴬ []             = []
a ⅋ᴬ (move ms ∷ bs) = move (a ×ᴬ ms) ∷ (a ⅋ᴬ bs)

infixr 4 _→ᴬ_
_→ᴬ_ : ∀ {s} → Arena s → Arena s → Arena s
a →ᴬ b = dualᴬ a ⅋ᴬ b

monoidᴬ : ∀ {s} → Monoid _ _
monoidᴬ {s} = monoid (Move s)
module Monoidᴬ {s} = Monoid (monoidᴬ {s})

Arenaᴰᴰ : ∀ {s} → Arena s ≡ Arena (O↔J (O↔J s))
Arenaᴰᴰ = ap Arena (! dualᴵᴼ-involutive _)

Moveᴰᴰ : ∀ {s} → Move s ≡ Move (O↔J (O↔J s))
Moveᴰᴰ = ap Move (! dualᴵᴼ-involutive _)

dualᴬ-involutive : ∀ {s}(a : Arena s) → dualᴬ (dualᴬ a) ≡ coe Arenaᴰᴰ a
dualᴹ-involutive : ∀ {s}(m : Move s)  → dualᴹ (dualᴹ m) ≡ coe Moveᴰᴰ  m

dualᴬ-involutive {O} [] = refl
dualᴬ-involutive {J} [] = refl
dualᴬ-involutive {O} (m ∷ a) = dualᴹ-involutive m ∷= dualᴬ-involutive a
dualᴬ-involutive {J} (m ∷ a) = dualᴹ-involutive m ∷= dualᴬ-involutive a

dualᴹ-involutive {O} (move ms) = move= (dualᴬ-involutive ms)
dualᴹ-involutive {J} (move ms) = move= (dualᴬ-involutive ms)

¬ᴬ_  : ∀ {s} → Arena s → Arena s
¬¬ᴬ_ : ∀ {s} → Arena s → Arena s

¬ᴬ  a = a →ᴬ ⊥ᴬ
¬¬ᴬ a = ¬ᴬ (¬ᴬ a)

¬-spec : ∀ {s} (a : Arena s) → a →ᴬ ⊥ᴬ ≡ move (dualᴬ a) ∷ []
¬-spec a = move= (snd Monoidᴬ.identity (dualᴬ a)) ∷= refl

¬¬-spec : ∀ {s} (a : Arena s) → (a →ᴬ ⊥ᴬ) →ᴬ ⊥ᴬ ≡ move (move (coe Arenaᴰᴰ a) ∷ []) ∷ []
¬¬-spec a = ¬-spec (a →ᴬ ⊥ᴬ) ∙ move= (move= (ap dualᴬ (snd Monoidᴬ.identity (dualᴬ a)) ∙ dualᴬ-involutive a) ∷= refl) ∷= refl

module Examples where
  a1 : Arena O
  a1 = move ⊥ᴬ ∷ 2-moves (move ⊥ᴬ) (move []) ∷ []

  a2 : Arena O
  a2 = move 2ᴬ ∷ 1-move (move ⊥ᴬ) ∷ []

  a1→a2 : Arena O
  a1→a2 = move (move ⊥ᴬ ∷
                2-moves (move ⊥ᴬ) (move []) ∷
                move [] ∷
                move [] ∷ [])
        ∷ move (move ⊥ᴬ ∷
                2-moves (move ⊥ᴬ) (move []) ∷
                move ⊥ᴬ ∷ []) ∷ []

  a1→a2-ok : a1→a2 ≡ (a1 →ᴬ a2)
  a1→a2-ok = refl

  2ᴬ≡⊥→⊥→⊥ : 2ᴬ' {O} ≡ ⊥ᴬ →ᴬ ⊥ᴬ →ᴬ ⊥ᴬ
  2ᴬ≡⊥→⊥→⊥ = refl

Ty' : ★
{-
data Ty' : ★ where
  `𝟚 : Ty'
  _`→_ : Ty' → Ty' → Ty'
  _`×_ : Ty' → Ty' → Ty'
-}

data Ty : ★ where
  `𝟚 : Ty
  {- _`→_ -}
  _`×_ : Ty → Ty → Ty
  _`→_ : Ty → Ty → Ty

Ty' = Ty

⟦_⟧Ty' : Ty' → ★
{-
⟦ `𝟚     ⟧Ty' = 𝟚
⟦ t `→ u ⟧Ty' = ⟦ t ⟧Ty' → ⟦ u ⟧Ty'
⟦ t `× u ⟧Ty' = ⟦ t ⟧Ty' × ⟦ u ⟧Ty'
-}

⟦_⟧Ty : Ty → ★
⟦ `𝟚     ⟧Ty = 𝟚
⟦ t `→ u ⟧Ty = ⟦ t ⟧Ty → ⟦ u ⟧Ty
⟦ t `× u ⟧Ty = ⟦ t ⟧Ty × ⟦ u ⟧Ty

⟦_⟧Ty' = ⟦_⟧Ty

replicateᴾ-send : ∀ n {A : ★}(f : ℕ → A) → ⟦ replicateᴾ n (send′ A end) ⟧
replicateᴾ-send zero    f = end
replicateᴾ-send (suc n) f = f n , replicateᴾ-send n f

module Steps n where
    P𝟚 = replicateᴾ n (send′ 𝟚 end)

    const-P𝟚 : 𝟚 → ⟦ P𝟚 ⟧
    const-P𝟚 b = replicateᴾ-send n (const b)

    ty'ᴾ : Ty' → Proto
    {-
    ty'ᴾ `𝟚       = P𝟚
    ty'ᴾ (t `→ u) = ty'ᴾ t ⊸ ty'ᴾ u
    ty'ᴾ (t `× u) = ty'ᴾ t ⊗ ty'ᴾ u
    -}

    tyᴾ : Ty → Proto
    tyᴾ `𝟚       = P𝟚
    tyᴾ (t `→ u) = ty'ᴾ t ⊸ tyᴾ u
    tyᴾ (t `× u) = tyᴾ t ⊗ tyᴾ u

    ty'ᴾ t = tyᴾ t

open Steps 1

module SingleRound where
    `_ : ★ → Proto
    ` A = recv′ 𝟙 (send′ A end)

    p-swap : ∀ {A B} → ⟦ (` A ⊗ ` B) ⊸ (` B ⊗ ` A) ⟧
    p-swap (inl 0₁) = inl (inl 0₁) , λ a → inl 0₁ , λ b → b , λ _ → a , end
    p-swap (inr 0₁) = inl (inr 0₁) , λ b → inl 0₁ , λ a → a , λ _ → b , end
                -- OR inl (inl 0₁) , λ a → inl 0₁ , λ b → a , λ _ → b , end

    p-dup : ∀ {A} → ⟦ (` A) ⊸ (` A ⊗ ` A) ⟧
    p-dup (inl 0₁) = inl 0₁ , λ a → a , λ _ → a , end
    p-dup (inr 0₁) = inl 0₁ , λ a → a , λ _ → a , end

    p-ap : ∀ {A B} → ⟦ ((` A ⊸ ` B) ⊗ ` A) ⊸ ` B ⟧
    p-ap 0₁ = inl (inl 0₁) , [inl: (λ _   → inl (inr 0₁) , λ a → inl a , λ b → b , end)
                             ,inr: (λ b _ → inl (inr 0₁) , λ a → inl a , b , end) ]
                             -- ,inr: (λ b _ → inr b , inr 0₁ , λ a → a , end) ]

                             {-
    is-not : ⟦ dual(` 𝟚 ⊸ ` 𝟚) ⅋ ` 𝟚 ⟧
    is-not 0₁ = inl 0₁ , [inl: const (inl 0₂ , [0: 0₂ , end 1: 1₂ , end ])
                         ,inr: [0: const (inr {!!} , {!!})
                                1: const {!!} ] ]
                                -}

module SingleSend where
    `_ : ★ → Proto
    ` A = send′ A end

    p-swap : ∀ {A B} → ⟦ (` A ⊗ ` B) ⊸ (` B ⊗ ` A) ⟧
    p-swap a b = b , a , end

    -- Why what we have is not about linearity!
    p-dup : ∀ {A} → ⟦ (` A) ⊸ (` A ⊗ ` A) ⟧
    p-dup a = a , a , end

    p-ap : ∀ {A B} → ⟦ ((` A ⊸ ` B) ⊗ ` A) ⊸ ` B ⟧
    p-ap a = inl a , λ b → b , end

    p-curry : ∀ {A B C} → ⟦ ((` A ⊗ ` B) ⊸ ` C) ⊸ (` A ⊸ ` B ⊸ ` C) ⟧
    p-curry a b = inl a , inl b , λ c → c , end

    p-arr : ∀ {A B} → (A → B) → ⟦ ` A ⊸ ` B ⟧
    p-arr f a = f a , end

    p-arr' : ∀ {A B C} → (A → B → C) → ⟦ (` A ⊗ ` B) ⊸ ` C ⟧
    p-arr' f a b = f a b , end

    p-arr'' : ∀ {A B C} → (A → B × C) → ⟦ ` A ⊸ (` B ⊗ ` C) ⟧
    p-arr'' f a = fst (f a) , snd (f a) , end

module _ {{_ : FunExt}}{{_ : UA}} where
{-
        opp : ∀ t → ⟦ tyᴾ t ⊥⟧
        opp `𝟚       = _
        opp (t `→ u) = {!!}
        opp (t `× u) = {!!}
-}

        

        {-
        embed : ∀ t → ⟦ t ⟧Ty → ⟦ tyᴾ t ⟧
        reify : ∀ t → ⟦ tyᴾ t ⟧ → ⟦ t ⟧Ty

        {-
        ⟦ dual (P ⊗ Q) ⅋ R ⟧
        ⟦ dual P ⅋ dual Q ⅋ R ⟧
        ⟦ dual P ⅋ (Q ⊸ R) ⟧
        -}
        embed→ : ∀ t u → (⟦ t ⟧Ty' → ⟦ tyᴾ u ⟧) → ⟦ tyᴾ (t `→ u) ⟧
        embed→ `𝟚        u f = f
        embed→ (t `→ t₁) u f = {!λ g → f (reify (t `→ t₁) g)!}
       --  [[A]⅋B]⅋C = ([[A]]⊗[B])⅋C = (A⊗[B])⅋C
        embed→ (t `× t₁) u f = coe (ap ⟦_⟧ Goal) (embed→ t (t₁ `→ u) (embed→ t₁ u ∘ curry f))
          where open ≡-Reasoning
                Goal = dual (ty'ᴾ t) ⅋ (ty'ᴾ t₁ ⊸ tyᴾ u)
                     ≡⟨ ⅋-assoc (dual (ty'ᴾ t)) _ _ ⟩
                       (dual (ty'ᴾ t) ⅋ dual (ty'ᴾ t₁)) ⅋ tyᴾ u
                     ≡⟨ ! ap (flip _⅋_ (tyᴾ u)) (dual-⊗ (ty'ᴾ t) (ty'ᴾ t₁)) ⟩
                       dual (ty'ᴾ t ⊗ ty'ᴾ t₁) ⅋ tyᴾ u
                     ∎

        embed `𝟚       b       = b , end
        embed (t `→ u) f       = embed→ t u (embed u ∘ f)
        embed (t `× u) (x , y) = ⊗-pair {tyᴾ t} {tyᴾ u} (embed t x) (embed u y)

        reify `𝟚       (b , end) = b
        reify (t `→ u) p = λ x → reify u (⊸-apply {tyᴾ t} {tyᴾ u} p (embed t x))
        reify (t `× u) p = reify t (⊗-fst (tyᴾ t) (tyᴾ u) p) , reify u (⊗-snd (tyᴾ t) (tyᴾ u) p)
        -}
-- -}
-- -}
-- -}
-- -}
-- -}
