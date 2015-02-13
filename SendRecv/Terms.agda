{-# OPTIONS --copattern #-}
open import Function.NP
open import Data.Zero
open import Data.One
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Binary.PropositionalEquality.NP

open import Session
open import Types
open import Channel

module Terms where

infix 2 ⊢ˢ_ ⊢_ ⊢ᶜᶠ_ _⊢_

data ⊢_ : (Δ : Env) → Set₁ where
  end : ∀{Δ}{e : EndedEnv Δ}
       ------------------
      → ⊢ Δ

  output : ∀ {Δ d M P}{{_ : MessageType M}}
             (l : d ↦ send P ∈ Δ)(m : M)
             (p : ⊢ Δ [ l ≔ m ])
             -------------------
               → ⊢ Δ

  input : ∀ {Δ d M}{P : M → _}{{_ : MessageType M}}
            (l : d ↦ recv P ∈ Δ)
            (p : ∀ m → ⊢ Δ [ l ≔ m ])
                 ----------------------
                     → ⊢ Δ

  mix : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
          (p : ⊢ Δ₀) (q : ⊢ Δ₁)
          --------------------
        → ⊢ Δ

  cut : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) {P d}
          (p : ⊢ (Δ₀ , d ↦ dual P))
          (q : ⊢ (Δ₁ , d ↦ P))
          ---------------------
        → ⊢ Δ

  fwd : ∀ c d {P} → ⊢ (ε , c ↦ P , d ↦ dual P)

  exch-last :
      ∀ {Δ c d P Q} →
      (p : ⊢ Δ , c ↦ P , d ↦ Q)
      → ⊢ Δ , d ↦ Q , c ↦ P

  wk-last : ∀ {Δ d}
              (p : ⊢ Δ)
              -----------------------
                → ⊢ (Δ , d ↦ end)

  end-last : ∀ {Δ d}
               (p : ⊢ (Δ , d ↦ end))
               ----------------------
                 → ⊢ Δ

data ⊢ᶜᶠ_ (Δ : Env) : Set₁ where
  end : {e : EndedEnv Δ} → ⊢ᶜᶠ Δ

  output : ∀ {d M P}{{_ : MessageType M}}
            (l : d ↦ send P ∈ Δ) → (m : M)
            (p : ⊢ᶜᶠ Δ [ l ≔ m ])
            --------------------
              → ⊢ᶜᶠ Δ

  input : ∀ {d M}{P : M → _}{{_ : MessageType M}}
            (l : d ↦ recv P ∈ Δ)
            (p : ∀ m → ⊢ᶜᶠ Δ [ l ≔ m ])
            ----------------------------
                     → ⊢ᶜᶠ Δ

-- The Δ for the server contains the view point of the clients
-- The point is that the meaning of _,_ in Δ is ⊗ while it
-- is ⅋ in ⊢ᶜᶠ
record ⊢ˢ_ (Δ : Env) : Set₁ where
  coinductive
  field
    server-output :
      ∀ {d M}{{_ : MessageType M}}{P : M → Session}
        (l : d ↦ recv P ∈ Δ) →
        Σ M λ m → ⊢ˢ Δ [ l ≔ m ]
    server-input :
      ∀ {d M}{{_ : MessageType M}}{P : M → Session}
        (l : d ↦ send P ∈ Δ)
        (m : M) → ⊢ˢ Δ [ l ≔ m ]
open ⊢ˢ_ public

record Server (K : Env → Set₁) (Δ : Env) : Set₁ where
  constructor _,_
  field
    srv-output :
      ∀ {d M}{{_ : MessageType M}}{P : M → Session}
        (l : d ↦ recv P ∈ Δ) →
        Σ M λ m → K (Δ [ l ≔ m ])
    srv-input :
      ∀ {d M}{{_ : MessageType M}}{P : M → Session}
        (l : d ↦ send P ∈ Δ)
        (m : M) → K (Δ [ l ≔ m ])
open Server public

data _⊢_ (Γ Δ : Env) : Set₁ where
  end : {eΓ : EndedEnv Γ} {eΔ : EndedEnv Δ} → Γ ⊢ Δ

  output : ∀ {d M P}{{_ : MessageType M}}
            (l : d ↦ send P ∈ Δ) → (m : M)
            (p : Γ ⊢ Δ [ l ≔ m ])
            --------------------
              → Γ ⊢ Δ

  input : ∀ {d M}{P : M → _}{{_ : MessageType M}}
            (l : d ↦ recv P ∈ Δ)
            (p : ∀ m → Γ ⊢ Δ [ l ≔ m ])
            ----------------------------
                     → Γ ⊢ Δ

  select : Server (λ Γ' → Γ' ⊢ Δ) Γ
            ----------------------------
                     → Γ ⊢ Δ

split-∈-,, : ∀ {c P Δ₀} Δ₁
               (l : c ↦ P ∈ (Δ₀ ,, Δ₁))
          → (Σ (c ↦ P ∈ Δ₀) λ l₀ → ∀ {d Q} → (Δ₀ ,, Δ₁) [ l ≔ d ↦ Q ] ≡ (Δ₀ [ l₀ ≔ d ↦ Q ] ,, Δ₁))
          ⊎ (Σ (c ↦ P ∈ Δ₁) λ l₁ → ∀ {d Q} → (Δ₀ ,, Δ₁) [ l ≔ d ↦ Q ] ≡ (Δ₀ ,, Δ₁ [ l₁ ≔ d ↦ Q ]))
split-∈-,, ε l = inl (l , refl)
split-∈-,, (Δ₁ , c ↦ P) here = inr (here , refl)
split-∈-,, (Δ₁ , d ↦ P) (there l) with split-∈-,, Δ₁ l
... | inl (r , e) = inl (r , ap (λ Δ → Δ , d ↦ P) e)
... | inr (r , e) = inr (there r , ap (λ Δ → Δ , d ↦ P) e)

split-∈-⋎ : ∀ {c P Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) → c ↦ P ∈ Δ → (c ↦ P ∈ Δ₀) ⊎ (c ↦ P ∈ Δ₁)
split-∈-⋎ (Δₛ , c ↦₀ P) here = inl here
split-∈-⋎ (Δₛ , c ↦₁ P) here = inr here
split-∈-⋎ (Δₛ , d' ↦₀ P') (there l) with split-∈-⋎ Δₛ l
... | inl r = inl (there r)
... | inr r = inr (there r)
split-∈-⋎ (Δₛ , d' ↦₁ P') (there l) with split-∈-⋎ Δₛ l
... | inl r = inl (there r)
... | inr r = inr (there r)

embedᶜᶠ : ∀ {Δ} → ⊢ᶜᶠ Δ → ⊢ Δ
embedᶜᶠ (end {e = e}) = end {e = e}
embedᶜᶠ (output l m p) = output l m (embedᶜᶠ p)
embedᶜᶠ (input l p) = input l λ m → embedᶜᶠ (p m)

mixᶜᶠ : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
         (p : ⊢ᶜᶠ Δ₀)
         (q : ⊢ᶜᶠ Δ₁)
         -------------
           → ⊢ᶜᶠ Δ
mixᶜᶠ Δₛ end q = tr ⊢ᶜᶠ_ (Zip-identity  Δₛ) q
mixᶜᶠ Δₛ (output l m p) q
  = output (Zip-com∈₀ Δₛ l) m (mixᶜᶠ (Zip-≔₀ l Δₛ) p q)
mixᶜᶠ Δₛ (input l p) q
  = input (Zip-com∈₀ Δₛ l) λ m → mixᶜᶠ (Zip-≔₀ l Δₛ) (p m) q

cutᶜᶠ : ∀ {Δ Δ₀ Δ₁}
         (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) d P
         (p : ⊢ᶜᶠ (Δ₀ , d ↦ dual P))
         (q : ⊢ᶜᶠ (Δ₁ , d ↦ P))
         ---------------------------
           → ⊢ᶜᶠ (Δ , d ↦ end)

cutᶜᶠ Δₛ d (recv P) (output here m p) (input here q) = cutᶜᶠ Δₛ d (P m) p (q m)
cutᶜᶠ Δₛ d (send P) (input here p) (output here m q) = cutᶜᶠ Δₛ d (P m) (p m) q

cutᶜᶠ Δₛ d P (output (there l) m p) q
  = output (there (Zip-com∈₀ Δₛ l)) m (cutᶜᶠ (Zip-≔₀ l Δₛ) d _ p q)
cutᶜᶠ Δₛ d P (input (there l) p) q
  = input (there (Zip-com∈₀ Δₛ l)) λ m → cutᶜᶠ (Zip-≔₀ l Δₛ) d _ (p m) q
cutᶜᶠ Δₛ d P p (output (there l) m q)
  = output (there (Zip-com∈₁ Δₛ l)) m (cutᶜᶠ (Zip-≔₁ l Δₛ) d _ p q)
cutᶜᶠ Δₛ d P p (input (there l) q)
  = input (there (Zip-com∈₁ Δₛ l)) λ m → cutᶜᶠ (Zip-≔₁ l Δₛ) d _ p (q m)

cutᶜᶠ Δₛ d end p q = mixᶜᶠ (Δₛ , d ↦₀ end) p q
cutᶜᶠ _ _ (com _ _) (end {e = _ , ()}) _
cutᶜᶠ _ _ (com _ _) _ (end {e = _ , ()})


end-lastᶜᶠ : ∀ {Δ d}
              (p : ⊢ᶜᶠ (Δ , d ↦ end))
              -----------------------
                → ⊢ᶜᶠ Δ
end-lastᶜᶠ (end {e = e , _}) = end {e = e}
end-lastᶜᶠ (output (there l) m p) = output l m (end-lastᶜᶠ p)
end-lastᶜᶠ (input (there l) p) = input l λ m → end-lastᶜᶠ (p m)

wk-lastᶜᶠ : ∀ {Δ d}
             (p : ⊢ᶜᶠ Δ)
             -----------------------
               → ⊢ᶜᶠ (Δ , d ↦ end)
wk-lastᶜᶠ end = end {e = it , _}
wk-lastᶜᶠ (output l m p) = output (there l) m (wk-lastᶜᶠ p)
wk-lastᶜᶠ (input l p) = input (there l) λ m → wk-lastᶜᶠ (p m)

wk-,,ᶜᶠ : ∀ {Δ₀ Δ₁} → ⊢ᶜᶠ Δ₀ → EndedEnv Δ₁ → ⊢ᶜᶠ Δ₀ ,, Δ₁
wk-,,ᶜᶠ {Δ₁ = ε} p E = p
wk-,,ᶜᶠ {Δ₁ = Δ₁ , d ↦ P} p (E , e) rewrite Ended-≡end e
  = wk-lastᶜᶠ (wk-,,ᶜᶠ p E)

module _ {d P Δ₀} where
  pre-wk-∈ : ∀ {Δ₁} → d ↦ P ∈ Δ₁ → d ↦ P ∈ (Δ₀ ,, Δ₁)
  pre-wk-∈ here = here
  pre-wk-∈ (there l) = there (pre-wk-∈ l)

fwd-mixᶜᶠ : ∀ {Δ c d} P → ⊢ᶜᶠ Δ → ⊢ᶜᶠ (Δ , c ↦ P , d ↦ dual P)
fwd-mixᶜᶠ end p = wk-lastᶜᶠ (wk-lastᶜᶠ p)
fwd-mixᶜᶠ (recv P) p = input (there here) λ m → output here m (fwd-mixᶜᶠ (P m) p)
fwd-mixᶜᶠ (send P) p = input here λ m → output (there here) m (fwd-mixᶜᶠ (P m) p)

fwdᶜᶠ : ∀ c d {P} → ⊢ᶜᶠ (ε , c ↦ P , d ↦ dual P)
fwdᶜᶠ _ _ {P} = fwd-mixᶜᶠ {ε} P end

ε,, : ∀ Δ → ε ,, Δ ≡ Δ
ε,, ε = refl
ε,, (Δ , d ↦ P) rewrite ε,, Δ = refl

-- only the last two are exchanged, some more has to be done
exch-lastᶜᶠ :
  ∀ {Δ c d P Q} →
  (p : ⊢ᶜᶠ Δ , c ↦ P , d ↦ Q)
  → ⊢ᶜᶠ Δ , d ↦ Q , c ↦ P
exch-lastᶜᶠ (end {e = (a , b) , c}) = end {e = (a , c) , b}
exch-lastᶜᶠ (output here m p) = output (there here) m (exch-lastᶜᶠ p)
exch-lastᶜᶠ (output (there here) m p) = output here m (exch-lastᶜᶠ p)
exch-lastᶜᶠ (output (there (there l)) m p) = output (there (there l)) m (exch-lastᶜᶠ p)
exch-lastᶜᶠ (input here p) = input (there here) λ m → exch-lastᶜᶠ (p m)
exch-lastᶜᶠ (input (there here) p) = input here λ m → exch-lastᶜᶠ (p m)
exch-lastᶜᶠ (input (there (there l)) p) = input (there (there l)) λ m → exch-lastᶜᶠ (p  m)

exchᶜᶠ :
  ∀ {Δ c d P Q} Δ' →
  (p : ⊢ᶜᶠ Δ , c ↦ P , d ↦ Q ,, Δ')
  → ⊢ᶜᶠ Δ , d ↦ Q , c ↦ P ,, Δ'
exchᶜᶠ ε p = exch-lastᶜᶠ p
exchᶜᶠ (Δ' , e ↦ R) (end {e = E}) = end {_} {{!!}}
exchᶜᶠ (Δ' , e ↦ R) (output l m p) = {!!}
exchᶜᶠ (Δ' , e ↦ ._) (input here p) = input here (λ m → {!let p' = exchᶜᶠ Δ' (p m) in ?!})
exchᶜᶠ (ε , e ↦ R) (input (there l) p) = {!!}
exchᶜᶠ (Δ' , f ↦ ._ , e ↦ R) (input (there here) p) = input (there here) (λ m → {!exchᶜᶠ (Δ' , _ ↦ _) (p m)!})
exchᶜᶠ (Δ' , f ↦ S , e ↦ R) (input (there (there l)) p) = {!!}

{-
exchᶜᶠ :
  ∀ {Δ c d P Q} →
  (l : c ↦ P ∈ Δ)
  (p : ⊢ᶜᶠ Δ , d ↦ Q)
  → ⊢ᶜᶠ Δ [ l ≔ d ↦ Q ] , c ↦ P
exchᶜᶠ here p = exch-lastᶜᶠ p
exchᶜᶠ {Q = Q} (there l) p = exch-lastᶜᶠ ( let p' = exch-lastᶜᶠ p in {!exchᶜᶠ {Q = Q} l!})

{-
postulate
 exchᶜᶠ :
  ∀ Δ₀ Δ₁ →
  (p : ⊢ᶜᶠ Δ₁ ,, Δ₀)
  → ⊢ᶜᶠ Δ₀ ,, Δ₁
  {-
exchᶜᶠ ε Δ₁ p rewrite ε,, Δ₁ = p
exchᶜᶠ Δ₀ ε p rewrite ε,, Δ₀ = p
exchᶜᶠ (Δ₀ , d ↦ P) (Δ₁ , d₁ ↦ P₁) end = {!!}
exchᶜᶠ (Δ₀ , d ↦ ._) (Δ₁ , d₁ ↦ P₁) (output here m p) = {!exchᶜᶠ!}
exchᶜᶠ (Δ₀ , d ↦ P) (Δ₁ , d₁ ↦ P₁) (output (there l) m p) = {!!}
exchᶜᶠ (Δ₀ , d ↦ P) (Δ₁ , d₁ ↦ P₁) (input l p) = {!!}
-}

pre-wkᶜᶠ : ∀ {Δ₀ Δ₁} → EndedEnv Δ₀ → ⊢ᶜᶠ Δ₁ → ⊢ᶜᶠ Δ₀ ,, Δ₁
pre-wkᶜᶠ {Δ₀} {Δ₁} E p = exchᶜᶠ Δ₀ Δ₁ (wk-,,ᶜᶠ p E)

end-of : Env → Env
end-of ε = ε
end-of (Δ , d ↦ P) = end-of Δ , d ↦ end

end-of-Ended : ∀ Δ → EndedEnv (end-of Δ)
end-of-Ended ε = _
end-of-Ended (Δ , d ↦ P) = end-of-Ended Δ , _

end-of-⋎ : ∀ Δ → [ Δ is Δ ⋎ end-of Δ ]
end-of-⋎ ε = ε
end-of-⋎ (Δ , d ↦ P) = end-of-⋎ Δ , d ↦₀ P

end-of-,,-⋎ : ∀ Δ₀ Δ₁ → [ Δ₀ ,, Δ₁ is Δ₀ ,, end-of Δ₁ ⋎ end-of Δ₀ ,, Δ₁ ]
end-of-,,-⋎ Δ₀ ε = end-of-⋎ Δ₀
end-of-,,-⋎ Δ₀ (Δ₁ , d ↦ P) = end-of-,,-⋎ Δ₀ Δ₁ , d ↦₁ P

,,-assoc : ∀ {Δ₀ Δ₁ Δ₂} → Δ₀ ,, (Δ₁ ,, Δ₂) ≡ (Δ₀ ,, Δ₁) ,, Δ₂
,,-assoc {Δ₂ = ε} = refl
,,-assoc {Δ₀} {Δ₁} {Δ₂ , d ↦ P} rewrite ,,-assoc {Δ₀} {Δ₁} {Δ₂} = refl

cut,,ᶜᶠ : ∀ {Δ₀ Δ₁} d P
            (p : ⊢ᶜᶠ (Δ₀ , d ↦ dual P))
            (q : ⊢ᶜᶠ (Δ₁ , d ↦ P))
           ---------------------------
              → ⊢ᶜᶠ Δ₀ ,, Δ₁
cut,,ᶜᶠ {Δ₀}{Δ₁} d P p q =
  end-lastᶜᶠ
    (cutᶜᶠ Δₛ d P
       (exchᶜᶠ (Δ₀ ,, end-of Δ₁) (ε , d ↦ dual P)
              (tr ⊢ᶜᶠ_ (! (,,-assoc {ε , d ↦ dual P} {Δ₀} {end-of Δ₁}))
                 (wk-,,ᶜᶠ {_} {end-of Δ₁}
                   (exchᶜᶠ (ε , d ↦ dual P) _ p) (end-of-Ended _))))
       (pre-wkᶜᶠ (end-of-Ended _) q))
  where Δₛ = end-of-,,-⋎ Δ₀ Δ₁

{-
postulate
  !cut,,ᶜᶠ : ∀ {Δ₀ Δ₁} d P
            (p : ⊢ᶜᶠ (Δ₀ , d ↦ P))
            (q : ⊢ᶜᶠ (Δ₁ , d ↦ dual P))
           ---------------------------
              → ⊢ᶜᶠ Δ₀ ,, Δ₁
-- !cut,,ᶜᶠ {Δ₀}{Δ₁} d P p q = {!!}
-}

{-
module _ {c d cd} where
    bi-fwd : ∀ P Q → ⊢ᶜᶠ (ε , cd ↦ P ⊗ Q , c ↦ dual P , d ↦ dual Q)

    private
      module _ {M} {{_ : MessageType M}} {P : M → Session} {Q} where
        goL : ∀ x → ⊢ᶜᶠ ε , cd ↦ com x (λ m → P m ⊗ Q)
                          , c  ↦ dual (com x P)
                          , d  ↦ dual Q

        goL IN  = input (there (there here)) λ m → output (there here) m (bi-fwd _ _)
        goL OUT = input (there here) λ m → output (there (there here)) m (bi-fwd _ _)

        goR : ∀ x → ⊢ᶜᶠ ε , cd ↦ com x (λ m → Q ⊗ P m)
                          , c  ↦ dual Q
                          , d  ↦ dual (com x P)
        goR IN  = input (there (there here)) λ m → output here m (bi-fwd _ _)
        goR OUT = input here λ m → output (there (there here)) m (bi-fwd _ _)

    bi-fwd end Q = exch-lastᶜᶠ (wk-lastᶜᶠ (fwdᶜᶠ _ _))
    bi-fwd (com x P) end = wk-lastᶜᶠ (fwdᶜᶠ _ _)
    bi-fwd (com x P) (com y Q) = input (there (there here)) [L: goL x ,R: goR y ]

    module _ {Δ₀ Δ₁ P Q} where
        ⊗ᶜᶠ : (p : ⊢ᶜᶠ (Δ₀ , c ↦ P))
             (q : ⊢ᶜᶠ (Δ₁ , d ↦ Q))
             ----------------------------------
               → ⊢ᶜᶠ (Δ₀ ,, Δ₁ , cd ↦ (P ⊗ Q))
        ⊗ᶜᶠ p q = !cut,,ᶜᶠ _ _ p (!cut,,ᶜᶠ _ _ q (bi-fwd P Q))
-}

  {-
-}

{-
rotᶜᶠ : ∀ Δ {c P} →
         (p : ⊢ᶜᶠ Δ , c ↦ P)
      → ⊢ᶜᶠ ε , c ↦ P ,, Δ
rotᶜᶠ ε p = p
rotᶜᶠ (Δ , d ↦ P) p = {!rotᶜᶠ Δ p!}

exchᶜᶠ :
  ∀ {Δ₀} Δ₁ {c d P Q} →
  (p : ⊢ᶜᶠ Δ₀ , c ↦ P , d ↦ Q ,, Δ₁)
  → ⊢ᶜᶠ Δ₀ , d ↦ Q , c ↦ P ,, Δ₁
exchᶜᶠ ε p = exch-lastᶜᶠ p
exchᶜᶠ (Δ₁ , d ↦ P)  (end e) = end {!!}
exchᶜᶠ (Δ₁ , d₁ ↦ ._) (output here m p) = output here m ({!exchᶜᶠ Δ₁ p!})
exchᶜᶠ (Δ₁ , d ↦ P)  (output (there l) m p) = {!!}
exchᶜᶠ (Δ₁ , d ↦ P)  (input l p) = {!!}
-}

_⊆_ : (Δ₀ Δ₁ : Env) → Set₁
_⊇_ : (Δ₀ Δ₁ : Env) → Set₁

Δ₀ ⊆ Δ₁ = ∀ {d P} → d ↦ P ∈ Δ₀ → d ↦ P ∈ Δ₁
Δ₀ ⊇ Δ₁ = Δ₁ ⊆ Δ₀

get-put : ∀ {d P Δ c Q} →
        (l : d ↦ P ∈ Δ) → c ↦ Q ∈ (Δ [ l ≔ c ↦ Q ])
get-put here = here
get-put (there l) = there (get-put l)

{-
⊆_[_≔_↦_] : ∀ {Δ₀ Δ₁} (f : Δ₀ ⊆ Δ₁)
               {d P} (l : d ↦ P ∈ Δ₀) (c : Channel) (Q : Session)
             → (Δ₀ [ l ≔ c ↦ Q ]) ⊆ (Δ₁ [ f l ≔ c ↦ Q ])
⊆ f [ l ≔ c ↦ Q ] {d'} {P'} l' = {!!}

(l : d ↦ P ∈ Δ)
→ Δ [ l ≔ ]

record _≈_ (Δ₀ Δ₁ : Env) : Set₁ where
  constructor _,_
  field
    ≈⊆ : Δ₀ ⊆ Δ₁
    ≈⊇ : Δ₀ ⊇ Δ₁
open _≈_ public

≈_[_≔_↦_] : ∀ {Δ₀ Δ₁} (Δₑ : Δ₀ ≈ Δ₁)
               {d P} (l : d ↦ P ∈ Δ₀) (c : Channel) (Q : Session)
             → (Δ₀ [ l ≔ c ↦ Q ]) ≈ (Δ₁ [ ≈⊆ Δₑ l ≔ m ])
≈ Δₑ [ here ≔ m ] = {!!}
≈ Δₑ [ there l ≔ m ] = {!!}

{-(λ l' → {!≈⊆ Δₑ!}) , from
  where
    from : ∀ {Δ₀ Δ₁ d io M} {P : M → Session} {ser : MessageType M}
             {Δₑ : Δ₀ ≈ Δ₁} {l : d ↦ com io P ∈ Δ₀} {m : M} {d₁} {P₁} →
           d₁ ↦ P₁ ∈ (Δ₁ [ ≈⊆ Δₑ l ≔ m ]) → d₁ ↦ P₁ ∈ (Δ₀ [ l ≔ m ])
    from = {!!}

≈ᶜᶠ : ∀ {Δ₀ Δ₁}
       (Δₑ : Δ₀ ≈ Δ₁)
       (p : ⊢ᶜᶠ Δ₀)
       -----------
         → ⊢ᶜᶠ Δ₁
≈ᶜᶠ Δₑ (end {e = e}) = end {e = {!!}}
≈ᶜᶠ Δₑ (output l m p) = output (≈⊆ Δₑ l) m (≈ᶜᶠ (≈ Δₑ [ l ≔ m ]) p)
≈ᶜᶠ Δₑ (input l p) = {!!}
-}
-}

cut-elim : ∀ {Δ} (p : ⊢ Δ)
                 ------------
                   → ⊢ᶜᶠ Δ
cut-elim (end {e = e}) = end {e = e}
cut-elim (output l m p) = output l m (cut-elim p)
cut-elim (input l p) = input l (λ m → cut-elim (p m))
cut-elim (mix Δₛ p q) = mixᶜᶠ Δₛ (cut-elim p) (cut-elim q)
cut-elim (cut Δₛ {P} {d} p q) = end-lastᶜᶠ (cutᶜᶠ Δₛ d P (cut-elim p) (cut-elim q))
cut-elim (end-last p) = end-lastᶜᶠ (cut-elim p)
cut-elim (wk-last p) = wk-lastᶜᶠ (cut-elim p)
cut-elim (fwd c d) = fwdᶜᶠ c d
cut-elim (exch-last p) = exch-lastᶜᶠ (cut-elim p)

⊢ᶜᶠ→⟦⟧ : ∀ {P d} → ⊢ᶜᶠ [ d ↦ P ] → ⟦ P ⟧ 𝟙
⊢ᶜᶠ→⟦⟧ {end} end = _
⊢ᶜᶠ→⟦⟧ {com x P} (end {e = _ , ()})
⊢ᶜᶠ→⟦⟧ (output here m der) = m , ⊢ᶜᶠ→⟦⟧ der
⊢ᶜᶠ→⟦⟧ (output (there ()) m der)
⊢ᶜᶠ→⟦⟧ (input here x₁) m = ⊢ᶜᶠ→⟦⟧ (x₁ m)
⊢ᶜᶠ→⟦⟧ (input (there ()) x₁)

Satisfy : ∀ {p d} P → (R : ⟦ log P ⟧ (𝟙 × 𝟙) → Set p) → ⊢ [ d ↦ P ] → Set p
Satisfy P Rel d = (d' : ⟦ dual P ⟧ 𝟙) → Rel (telecom P (⊢ᶜᶠ→⟦⟧ (cut-elim d)) d')

⟦⟧→⊢ᶜᶠ : ∀ {P d} → ⟦ P ⟧ 𝟙 → ⊢ᶜᶠ [ d ↦ P ]
⟦⟧→⊢ᶜᶠ {end} p = end
⟦⟧→⊢ᶜᶠ {recv P} p = input here (λ m → ⟦⟧→⊢ᶜᶠ (p m))
⟦⟧→⊢ᶜᶠ {send P} (m , p) = output here m (⟦⟧→⊢ᶜᶠ p)

⟦⟧→⊢ : ∀ {P d} → ⟦ P ⟧ 𝟙 → ⊢ [ d ↦ P ]
⟦⟧→⊢ {end} p = end
⟦⟧→⊢ {recv P} p = input here (λ m → ⟦⟧→⊢ (p m))
⟦⟧→⊢ {send P} (m , p) = output here m (⟦⟧→⊢ p)

⟦_⟧E : Env → Set
⟦ ε ⟧E = 𝟙
⟦ Δ , d ↦ P ⟧E = ⟦ Δ ⟧E × ⟦ P ⟧ 𝟙

mapEnv : (Session → Session) → Env → Env
mapEnv f ε = ε
mapEnv f (Δ , d ↦ P) = mapEnv f Δ , d ↦ f P

mapEnv-all : ∀ {P Q : Channel → Session → Set}{Δ}{f : Session → Session}
  → (∀ d x → P d x → Q d (f x))
  → AllEnv P Δ → AllEnv Q (mapEnv f Δ)
mapEnv-all {Δ = ε} f₁ ∀Δ = ∀Δ
mapEnv-all {Δ = Δ , d ↦ P₁} f₁ (∀Δ , P) = (mapEnv-all f₁ ∀Δ) , f₁ d P₁ P

mapEnv-Ended : ∀ {f : Session → Session}{Δ} → Ended (f end)
  → AllEnv (λ _ → Ended) Δ → AllEnv (λ _ → Ended) (mapEnv f Δ)
mapEnv-Ended eq = mapEnv-all (λ { d end _ → eq ; d (send P) () ; d (recv P) () })

mapEnv-∈ : ∀ {d P f Δ} → d ↦ P ∈ Δ → d ↦ f P ∈ mapEnv f Δ
mapEnv-∈ here = here
mapEnv-∈ (there der) = there (mapEnv-∈ der)

module _ {d : Channel}{c M}{cf : Com → Com}{m : M}{{MT : MessageType M}}{p} where
  private
    S = com c {M} {{MT}} p
  subst-lemma-one-point-four : ∀ {Δ}( l : d ↦ S ∈ Δ ) →
    let f = mapSession cf
    in (mapEnv f (Δ [ l ≔ m ])) ≡ (_[_≔_]{c = cf c} (mapEnv f Δ) (mapEnv-∈ l) m)
  subst-lemma-one-point-four here = refl
  subst-lemma-one-point-four (there {d' = d'}{P'} l) = ap (λ X → X , d' ↦ mapSession cf P') (subst-lemma-one-point-four l)

module _ {d P} where
  project : ∀ {Δ} → d ↦ P ∈ Δ → ⟦ Δ ⟧E → ⟦ P ⟧ 𝟙
  project here env = snd env
  project (there mem) env = project mem (fst env)

empty : ∀ {Δ} → AllEnv (λ _ → Ended) Δ → ⟦ Δ ⟧E
empty {ε} <> = _
empty {Δ , d ↦ end} (fst , <>) = empty fst , _
empty {Δ , d ↦ com x P} (fst , ())

noRecvInLog : ∀ {d M}{{_ : MessageType M}}{P : M → _}{Δ} → d ↦ recv P ∈ mapEnv log Δ → 𝟘
noRecvInLog {Δ = ε} ()
noRecvInLog {Δ = Δ , d₁ ↦ end} (there l) = noRecvInLog l
noRecvInLog {Δ = Δ , d₁ ↦ com x₁ P₁} (there l) = noRecvInLog l

module _ {d M P}{{_ : MessageType M}} where
  lookup : ∀ {Δ}(l : d ↦ send P ∈ Δ) → ⟦ Δ ⟧E → Σ M λ m → ⟦ Δ [ l ≔ m ] ⟧E
  lookup here (env , (m , p)) = m , (env , p)
  lookup (there l) (env , P') = let (m , env') = lookup l env in m , (env' , P')

  set : ∀ {Δ}(l : d ↦ recv P ∈ Δ) → ⟦ Δ ⟧E → (m : M) → ⟦ Δ [ l ≔ m ] ⟧E
  set here (env , f) m = env , f m
  set (there l) (env , P') m = set l env m , P'

  setΣ : ∀ {Δ}(l : d ↦ send P ∈ Δ) → (m : M) → ⟦ Δ [ l ≔ m ] ⟧E → ⟦ Δ ⟧E
  setΣ here m env = fst env , (m , snd env)
  setΣ (there l) m env = setΣ l m (fst env) , snd env

⊢telecom : ∀ {Δ} → ⊢ᶜᶠ Δ → ⟦ mapEnv dual Δ ⟧E → ⊢ mapEnv log Δ
⊢telecom end env = end {e = mapEnv-Ended _ it}
⊢telecom (output l m der) env = output (mapEnv-∈ l) m (tr (⊢_)
  (subst-lemma-one-point-four l) (⊢telecom der (tr ⟦_⟧E (sym (subst-lemma-one-point-four l)) (set (mapEnv-∈ l) env m))))
⊢telecom (input l x₁) env = let (m , env') = lookup (mapEnv-∈ l) env
                                hyp = ⊢telecom (x₁ m) (tr (⟦_⟧E) (sym (subst-lemma-one-point-four l)) env')
                             in output (mapEnv-∈ l) m
                             (tr (⊢_) (subst-lemma-one-point-four l) hyp)



-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
