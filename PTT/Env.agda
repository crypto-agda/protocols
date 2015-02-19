{-# OPTIONS --copatterns #-}
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Product renaming (proj₁ to fst; proj₂ to snd; _,_ to ⟨_,_⟩) hiding (map)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP
open import PTT.Dom as Dom
open import PTT.Session as Session hiding (Ended)

module PTT.Env where

open import PTT.Map as Map public

private
    M = MSession

Env : Dom → Set₁
Env = Map MSession

module _ {δ c}(E : Env δ) where
  infixl 4 _/'_ _/D_
  _/D_ :  c ∈D δ → Env δ
  _/D_ l = E [ l ]≔' end

  _/'_ : ∀ {S} → c ↦ S ∈ E → Env δ
  _/'_ l = _/D_ (_↦_∈_.lA l)

infixr 4 _♦Env_
_♦Env_ : ∀ {D₀ D₁} → Env D₀ → Env D₁ → Env (D₀ ♦Dom D₁)
_♦Env_ = _♦Map_

-- open With-end {_} {MSession} end public
-- module With-end {a}{M : Set a}(end : M) where

module _ {δ}(Δ : Env δ) where
    _/* : Env δ
    _/* = map (λ _ → end) Δ

EnvSelectionAll≡ : ∀ {δ}(b : 𝟚) → Env δ → Selection δ → Set
EnvSelectionAll≡ b ε ε = 𝟙
EnvSelectionAll≡ b (E , c ↦ « S ») (σ , .c ↦ v₁) = EnvSelectionAll≡ b E σ × b ≡ v₁
EnvSelectionAll≡ b (E , c ↦ end) (σ , .c ↦ v₁) = EnvSelectionAll≡ b E σ

pureEnvAll : ∀ {δ}(Δ : Env δ)(b : 𝟚)
  → EnvSelectionAll≡ b Δ (constMap δ b)
pureEnvAll ε b = _
pureEnvAll (Δ , c ↦ « S ») b = ⟨ pureEnvAll Δ b , refl ⟩
pureEnvAll (Δ , c ↦ end) b = pureEnvAll Δ b

Ended : ∀ {δ}(E : Env δ) → Set
Ended = Map.All (λ _ → Session.Ended)

abstract
    _/[_]_ : ∀ {δ}(Δ : Env δ)(b : 𝟚)(σ : Selection δ) → Env δ
    Δ /[ b ] σ = zipWith (selectProj b) Δ σ

    /[]-def : ∀ {δ}(Δ : Env δ)(b : 𝟚)(σ : Selection δ)
      → Δ /[ b ] σ ≡ zipWith (selectProj b) Δ σ
    /[]-def Δ b σ = refl

    select-Map : ∀ {c δE}(Δ : Env δE)(σ : Selection δE)(lA : c ∈D δE)
      → Δ ‼ lA ≡ Δ /[ σ ‼ lA ] σ ‼ lA
    select-Map (Δ , c ↦ v) (σ , .c ↦ 1₂) here = refl
    select-Map (Δ , c ↦ v) (σ , .c ↦ 0₂) here = refl
    select-Map (Δ , c₁ ↦ v) (σ , .c₁ ↦ v₁) (there lA) = select-Map Δ σ lA

    All/same : ∀ {δE}(E : Env δE)(σ : Selection δE)(b : 𝟚)
      → EnvSelectionAll≡ b E σ → E /[ b ] σ ≡ E
    All/same ε ε 1₂ all = refl
    All/same ε ε 0₂ all = refl
    All/same (E , c ↦ « S ») (σ , .c ↦ .1₂) 1₂ ⟨ all , refl ⟩ rewrite All/same E σ 1₂ all = refl
    All/same (E , c ↦ « S ») (σ , .c ↦ .0₂) 0₂ ⟨ all , refl ⟩ rewrite All/same E σ 0₂ all = refl
    All/same (E , c ↦ end) (σ , .c ↦ 1₂) 1₂ all rewrite All/same E σ 1₂ all = refl
    All/same (E , c ↦ end) (σ , .c ↦ 0₂) 1₂ all rewrite All/same E σ 1₂ all = refl
    All/same (E , c ↦ end) (σ , .c ↦ 1₂) 0₂ all rewrite All/same E σ 0₂ all = refl
    All/same (E , c ↦ end) (σ , .c ↦ 0₂) 0₂ all rewrite All/same E σ 0₂ all = refl

    All/not : ∀ {δE}(E : Env δE)(σ : Selection δE)(b : 𝟚)
      → EnvSelectionAll≡ b E σ → Ended (E /[ not b ] σ)
    All/not ε ε b all = _
    All/not (E , c ↦ « S ») (σ , .c ↦ .1₂) 1₂ ⟨ all , refl ⟩ = ⟨ (All/not E σ 1₂ all) , _ ⟩
    All/not (E , c ↦ « S ») (σ , .c ↦ .0₂) 0₂ ⟨ all , refl ⟩ = ⟨ (All/not E σ 0₂ all) , _ ⟩
    All/not (E , c ↦ end) (σ , .c ↦ 1₂) 1₂ all = ⟨ All/not E σ 1₂ all , _ ⟩
    All/not (E , c ↦ end) (σ , .c ↦ 0₂) 1₂ all = ⟨ All/not E σ 1₂ all , _ ⟩
    All/not (E , c ↦ end) (σ , .c ↦ 1₂) 0₂ all = ⟨ All/not E σ 0₂ all , _ ⟩
    All/not (E , c ↦ end) (σ , .c ↦ 0₂) 0₂ all = ⟨ All/not E σ 0₂ all , _ ⟩ -- ⟨ {!!} , {!!} ⟩

    End/[_] : ∀ {δ}{E : Env δ}(b : 𝟚)(σ : Selection δ) → Ended E → Ended (E /[ b ] σ)
    End/[_] {E = ε} b ε EE = _
    End/[_] {E = E , .c ↦ v} 1₂ (σ , c ↦ 1₂) ⟨ EE , Ev ⟩ = ⟨ (End/[_] 1₂ σ EE) , Ev ⟩
    End/[_] {E = E , .c ↦ v} 1₂ (σ , c ↦ 0₂) ⟨ EE , Ev ⟩ = ⟨ (End/[_] 1₂ σ EE) , _ ⟩
    End/[_] {E = E , .c ↦ v} 0₂ (σ , c ↦ 1₂) ⟨ EE , Ev ⟩ = ⟨ (End/[_] 0₂ σ EE) , _ ⟩
    End/[_] {E = E , .c ↦ v} 0₂ (σ , c ↦ 0₂) ⟨ EE , Ev ⟩ = ⟨ (End/[_] 0₂ σ EE) , Ev ⟩

    /pure : ∀ {δ}(E : Env δ)(b : 𝟚) → E /[ b ] pure δ (λ _ → b) ≡ E
    /pure ε b = refl
    /pure (E , c ↦ v) 1₂ rewrite /pure E 1₂ = refl
    /pure (E , c ↦ v) 0₂ rewrite /pure E 0₂ = refl

module _ {δ}(Δ : Env δ)(σ : Selection δ) where
    _/₀_ : Env δ
    _/₀_ = Δ /[ 0₂ ] σ

    _/₁_ : Env δ
    _/₁_ = Δ /[ 1₂ ] σ

data Zip : ∀ {δ} → Env δ → Env δ → Env δ → Set₁ where
  ε : Zip ε ε ε
  _,_↦₀_ : ∀ {δ Δ₀ Δ₁} {Δ : Env δ}(Z : Zip Δ Δ₀ Δ₁) d S → Zip (Δ , d ↦ S) (Δ₀ , d ↦ S)   (Δ₁ , d ↦ end)
  _,_↦₁_ : ∀ {δ Δ₀ Δ₁} {Δ : Env δ}(Z : Zip Δ Δ₀ Δ₁) d S → Zip (Δ , d ↦ S) (Δ₀ , d ↦ end) (Δ₁ , d ↦ S)

[_is_⋎_] : ∀ {δ} → Env δ → Env δ → Env δ → Set₁
[_is_⋎_] = Zip


Ended-/* : ∀ {δ}(E : Env δ) → Ended (E /*)
Ended-/* ε = _
Ended-/* (E , c ↦ v) = ⟨ Ended-/* E , _ ⟩

Ended-∈D : ∀ {δE c}{E : Env δE} (l : c ∈D δE) → Ended E → Session.Ended (lookup E l)
Ended-∈D {E = _ , _ ↦ _} here      EE = snd EE
Ended-∈D {E = _ , _ ↦ _} (there l) EE = Ended-∈D l (fst EE)

Ended-↦∈ : ∀ {δE c S}{E : Env δE} (l : c ↦ S ∈ E) (EE : Ended E) → Session.Ended S
Ended-↦∈ ⟨ l R⟩ = Ended-∈D l

{-
infix 0 _⊆_
record _⊆_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor mk
  field
    un-⊆ : ∀ {c S}(NES : ¬(Session.Ended S))(l : c ↦ S ∈ E) → c ↦ S ∈ F
open _⊆_ public

⊆-refl : ∀ {δE}{E : Env δE} → E ⊆ E
un-⊆ ⊆-refl NES l = l

⊆-there : ∀ {δE}{E : Env δE}{c S} → E ⊆ E , c ↦ S
un-⊆ ⊆-there _ = there'

⊆-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ⊆ F → F ⊆ G → E ⊆ G
un-⊆ (⊆-trans p q) NES l = un-⊆ q NES (un-⊆ p NES l)

_⊆-∙_ = ⊆-trans

⊆,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ⊆ F → E , c ↦ S ⊆ F , c ↦ S
un-⊆ (⊆,↦ E∼F) NES  heRe = heRe
un-⊆ (⊆,↦ E∼F) NES (theRe lA) = there' (un-⊆ E∼F NES ⟨ lA R⟩)

⊆,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ⊆ E
un-⊆ ⊆,↦end NES heRe = 𝟘-elim (NES _)
un-⊆ ⊆,↦end NES (theRe lA) = ⟨ lA R⟩

infix 0 _∼_
record _∼_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor ⟨_,_⟩
  field
    get-⊆ : E ⊆ F
    get-⊇ : F ⊆ E
open _∼_ public

∼-refl : ∀ {δE}{E : Env δE} → E ∼ E
∼-refl = ⟨ ⊆-refl , ⊆-refl ⟩


∼-sym : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → F ∼ E
∼-sym ⟨ p , q ⟩ = ⟨ q , p ⟩


∼-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ∼ F → F ∼ G → E ∼ G
∼-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ p ⊆-∙ r , s ⊆-∙ q ⟩


∼,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ∼ F → E , c ↦ S ∼ F , c ↦ S
∼,↦ ⟨ p , q ⟩ = ⟨ ⊆,↦ p , ⊆,↦ q ⟩

∼,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ∼ E
∼,↦end = ⟨ ⊆,↦end , ⊆-there ⟩
-}

infix 0 _∼_
data _∼_ : ∀ {δE δF}(E : Env δE)(F : Env δF) → Set₁ where
  ∼-refl : ∀ {δE}{E : Env δE} → E ∼ E
  ∼-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
            → E ∼ F → F ∼ G → E ∼ G
  ∼,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
         → E ∼ F → E , c ↦ S ∼ F , c ↦ S
  ∼,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ∼ E
  ∼,↦end' : ∀ {δE}{E : Env δE}{c} → E ∼ E , c ↦ end
  ∼,[swap] : ∀ {δE c d A B}{E : Env δE} → E , c ↦ A , d ↦ B ∼ E , d ↦ B , c ↦ A

∼-reflexive : ∀ {δE}{E F : Env δE} → E ≡ F → E ∼ F
∼-reflexive refl = ∼-refl

∼-sym : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → F ∼ E
∼-sym ∼-refl = ∼-refl
∼-sym (∼-trans eq eq₁) = ∼-trans (∼-sym eq₁) (∼-sym eq)
∼-sym (∼,↦ eq) = ∼,↦ (∼-sym eq)
∼-sym ∼,↦end = ∼,↦end'
∼-sym ∼,↦end' = ∼,↦end
∼-sym ∼,[swap] = ∼,[swap]

∼-! : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → F ∼ E
∼-! = ∼-sym

infixr 8 _∼-∙_
_∼-∙_ : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
            → E ∼ F → F ∼ G → E ∼ G
_∼-∙_ = ∼-trans

∼-Ended : ∀ {δE}{E : Env δE} → Ended E → ε ∼ E
∼-Ended {E = ε} EE = ∼-refl
∼-Ended {E = E , c ↦ « _ »} ⟨ _ , () ⟩
∼-Ended {E = E , c ↦ end} ⟨ x , _ ⟩ = ∼-Ended x ∼-∙ (∼-! ∼,↦end)

_∼-End_ : ∀ {δE δF}{E : Env δE}{F : Env δF} → Ended E → Ended F → E ∼ F
EE ∼-End EF = ∼-! (∼-Ended EE) ∼-∙ ∼-Ended EF

_≡-End_ : ∀ {δE}{E F : Env δE} → Ended E → Ended F → E ≡ F
_≡-End_ {E = ε} {ε} 0₁ 0₁ = refl
_≡-End_ {E = E , c ↦ v} {F , .c ↦ v₁} ⟨ EE , x ⟩ ⟨ EF , y ⟩
  rewrite EE ≡-End EF
  | Ended-≡end x
  | Ended-≡end y = refl

--  End/₀ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Ended E → Ended (E /₀ σ)
--  End/₁ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Ended E → Ended (E /₁ σ)

/*-End : ∀ {δE}(E : Env δE) → Ended (E /*)
/*-End E = mapAll (λ _ → _) E

End/D : ∀ {c δE}(E : Env δE)(l : c ∈D δE) → Ended E → Ended (E /D l)
End/D (E , c ↦ v) here EE = ⟨ (fst EE) , _ ⟩
End/D (E , c₁ ↦ v) (there l) EE = ⟨ (End/D E l (fst EE)) , (snd EE) ⟩

-- Really clever proof yay!
SEnd// :(b : 𝟚)(S : MSession)(σ : 𝟚) → Session.Ended (selectProj (not b) (selectProj b S σ) σ)
SEnd// 1₂ S 1₂ = 0₁
SEnd// 1₂ S 0₂ = 0₁
SEnd// 0₂ S 1₂ = 0₁
SEnd// 0₂ S 0₂ = 0₁

E-lookup-diff : ∀ {c d δE}{lA : c ∈D δE}{lB : d ∈D δE}(E : Env δE)
  → DiffDom lA lB → (E [ lA ]≔' end) ‼ lB ≡ E ‼ lB
E-lookup-diff (E , c₁ ↦ v) (h/t l) = refl
E-lookup-diff (E , c₁ ↦ v) (t/h l) = refl
E-lookup-diff (E , c₁ ↦ v) (t/t df) = E-lookup-diff E df


abstract
    -- Really clever proof yay!
    /D/[] : ∀ {c δE}(E : Env δE)(l : c ∈D δE)(b : 𝟚)(σ : Selection δE)
      → (E /D l) /[ b ] σ ∼ (E /[ b ] σ) /D l
    /D/[] (E , c ↦ v) here 1₂ (σ , .c ↦ 1₂) = ∼-refl
    /D/[] (E , c ↦ v) here 1₂ (σ , .c ↦ 0₂) = ∼-refl
    /D/[] (E , c ↦ v) here 0₂ (σ , .c ↦ 1₂) = ∼-refl
    /D/[] (E , c ↦ v) here 0₂ (σ , .c ↦ 0₂) = ∼-refl
    /D/[] (E , c₁ ↦ v) (there l) b (σ , .c₁ ↦ v₁) = ∼,↦ (/D/[] E l b σ)

    []≔/[]≡ : ∀ {δE c} b (Δ : Map MSession δE) (σ : Map 𝟚 δE)
           (lc : c ∈D δE) →
         (Δ [ lc ]≔' end) /[ b ] σ ≡ Δ /[ b ] σ [ lc ]≔' end
    []≔/[]≡ 1₂ (Δ , c ↦ v) (σ , .c ↦ 1₂) here = refl
    []≔/[]≡ 1₂ (Δ , c ↦ v) (σ , .c ↦ 0₂) here = refl
    []≔/[]≡ 0₂ (Δ , c ↦ v) (σ , .c ↦ 1₂) here = refl
    []≔/[]≡ 0₂ (Δ , c ↦ v) (σ , .c ↦ 0₂) here = refl
    []≔/[]≡ b (Δ , c₁ ↦ v) (σ , .c₁ ↦ v₁) (there lc) rewrite []≔/[]≡ b Δ σ lc = refl


    End// : ∀ {δE}(b : 𝟚)(E : Env δE)(σ : Selection δE) → Ended ((E /[ b ] σ) /[ not b ] σ)
    End// b ε ε = _
    End// b (E , c ↦ v) (σ , .c ↦ v₁) = ⟨ (End// b E σ) , SEnd// b v v₁ ⟩

    End→/[] : ∀ {δE}(b : 𝟚)(E : Env δE)(σ : Selection δE) → Ended E → Ended (E /[ b ] σ)
    End→/[] b ε ε EE = _
    End→/[] 1₂ (E , c ↦ v) (σ , .c ↦ 1₂) ⟨ EE , Ev ⟩ = ⟨ (End→/[] 1₂ E σ EE) , Ev ⟩
    End→/[] 1₂ (E , c ↦ v) (σ , .c ↦ 0₂) ⟨ EE , Ev ⟩ = ⟨ (End→/[] 1₂ E σ EE) , _ ⟩
    End→/[] 0₂ (E , c ↦ v) (σ , .c ↦ 1₂) ⟨ EE , Ev ⟩ = ⟨ (End→/[] 0₂ E σ EE) , _ ⟩
    End→/[] 0₂ (E , c ↦ v) (σ , .c ↦ 0₂) ⟨ EE , Ev ⟩ = ⟨ (End→/[] 0₂ E σ EE) , Ev ⟩

    ∼-select-com : ∀ {c δE}(E : Env δE)(σ : Selection δE)(lA : c ∈D δE)
      → let b = not (σ ‼ lA)
        in E /[ b ] σ ∼ (E /D lA) /[ b ] σ
    ∼-select-com (E , c ↦ v) (σ , .c ↦ 1₂) here = ∼-refl
    ∼-select-com (E , c ↦ v) (σ , .c ↦ 0₂) here = ∼-refl
    ∼-select-com (E , c₁ ↦ v) (σ , .c₁ ↦ v₁) (there lA) = ∼,↦ (∼-select-com E σ lA)

    Selection/[]same : ∀ {δ}(Δ : Env δ)(b : 𝟚)
      → Δ /[ b ] (constMap δ b) ∼ Δ
    Selection/[]same ε b = ∼-refl
    Selection/[]same (Δ , c ↦ v) 1₂ = ∼,↦ (Selection/[]same Δ 1₂)
    Selection/[]same (Δ , c ↦ v) 0₂ = ∼,↦ (Selection/[]same Δ 0₂)

    Selection/[]not : ∀ {δ}(Δ : Env δ)(b : 𝟚)
      → Ended (Δ /[ b ] (constMap δ (not b)))
    Selection/[]not ε b = _
    Selection/[]not (Δ , c ↦ v) 1₂ = ⟨ (Selection/[]not Δ 1₂) , _ ⟩
    Selection/[]not (Δ , c ↦ v) 0₂ = ⟨ (Selection/[]not Δ 0₂) , _ ⟩

{-
ZipAll : ∀ {S Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → All S Δ₀ → All S Δ₁ → All S Δ
ZipAll ε A₀ A₁ = 0₁
ZipAll (Z , d ↦₀ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₀
ZipAll (Z , d ↦₁ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₁

ZipEnded : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → Ended Δ₀ → Ended Δ₁ → Ended Δ
ZipEnded = ZipAll

Zip-comm : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → [ Δ is Δ₁ ⋎ Δ₀ ]
Zip-comm ε = ε
Zip-comm (Z , d ↦₀ P) = Zip-comm Z , d ↦₁ P
Zip-comm (Z , d ↦₁ P) = Zip-comm Z , d ↦₀ P

Zip-identity : ∀ {Δ₀ Δ₁ Δ} {{Δ₀E : Ended Δ₀}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₁ ≡ Δ
Zip-identity ε = refl
Zip-identity {{E , e}} (Z , d ↦₀ P) = ap₂ (λ Δ P → Δ , d ↦ P) (Zip-identity Z) (! (Ended-≡end e))
Zip-identity {{E , e}} (Z , d ↦₁ P) = ap (λ Δ → Δ , d ↦ P) (Zip-identity Z)

Zip-identity' : ∀ {Δ₀ Δ₁ Δ} {{Δ₁E : Ended Δ₁}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₀ ≡ Δ
Zip-identity' Z = Zip-identity (Zip-comm Z)

module _ {d io M} {P : M → Session} where
    Zip-com∈₀ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → d ↦ act (com io P) ∈ Δ₀ → d ↦ act (com io P) ∈ Δ
    Zip-com∈₀ (Z , ._ ↦₀ ._) here = here
    Zip-com∈₀ (Z , c ↦₀ Q)  (there l) = there (Zip-com∈₀ Z l)
    Zip-com∈₀ (Z , c ↦₁ Q)  (there l) = there (Zip-com∈₀ Z l)

    Zip-com∈₁ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → d ↦ act (com io P) ∈ Δ₁ → d ↦ act (com io P) ∈ Δ
    Zip-com∈₁ Z = Zip-com∈₀ (Zip-comm Z)

    Zip-≔₀ : ∀ {Δ Δ₀ Δ₁}
              (l : d ↦ act (com io P) ∈ Δ₀) {m : M}
              (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
              [ Δ [ Zip-com∈₀ Δₛ l ≔ m ] is Δ₀ [ l ≔ m ] ⋎ Δ₁ ]
    Zip-≔₀ here (Δₛ , ._ ↦₀ ._) = Δₛ , d ↦₀ _
    Zip-≔₀ (there l) (Δₛ , c ↦₀ Q) = Zip-≔₀ l Δₛ , c ↦₀ Q
    Zip-≔₀ (there l) (Δₛ , c ↦₁ Q) = Zip-≔₀ l Δₛ , c ↦₁ Q

    Zip-≔₁ : ∀ {Δ Δ₀ Δ₁}
               (l : d ↦ act (com io P) ∈ Δ₁) {m : M} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
             [ Δ [ Zip-com∈₁ Δₛ l ≔ m ] is Δ₀ ⋎ Δ₁ [ l ≔ m ] ]
    Zip-≔₁ l Δₛ = Zip-comm (Zip-≔₀ l (Zip-comm Δₛ))
-- -}
-- -}
-- -}
-- -}
-- -}
