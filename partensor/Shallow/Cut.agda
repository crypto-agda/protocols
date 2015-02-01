{-# OPTIONS --copatterns #-}
open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Sum
open import Data.Nat
{-
open import Data.Vec
open import Data.Fin
-}
-- open import Data.List

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP hiding ([_]; J)
open import partensor.Shallow.Dom
import partensor.Shallow.Session as Session
import partensor.Shallow.Map as Map
import partensor.Shallow.Env as Env
import partensor.Shallow.Proto as Proto
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; _/[_]_; _/_; Ended)
open Proto   hiding ()
open import partensor.Shallow.Equiv' hiding (♦-assoc ; ♦-com ; ♦-com, ; /Ds-com)
open import partensor.Shallow.Term

module partensor.Shallow.Cut where
infixl 4 _♦Proto'_
-- things we have but I want better unification
{-
  _≈'_ : ∀ {δI δJ} → Proto δI → Proto δJ → Set₁
  ≈'-refl : ∀ {δI}{I : Proto δI} → I ≈' I
  ≈'-sym : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈' J → J ≈' I
  ≈'-trans : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ≈' B → B ≈' C → A ≈' C
-}
postulate
  _♦Proto'_ : ∀ {δa δb}(A : Proto δa)(B : Proto δb) → Proto (δa ♦Doms δb)

{-
data DifferentVarsDoms : ∀ {δI c d} → Doms'.[ c ]∈ δI → Doms'.[ d ]∈ δI → Set where
  h/t : ∀ {a b Db l}
   → DifferentVarsDoms {Db ,[ a ]}{a}{b} Doms'.here (Doms'.there l)
  t/h : ∀ {a b Db l}
   → DifferentVarsDoms {Db ,[ a ]}{b}{a} (Doms'.there l) Doms'.here
  t/t : ∀ {a c d D l l'} → DifferentVarsDoms {D ,[ a ]}{c}{d} (Doms'.there l) (Doms'.there l')

-- Need to update this, they may point to the same tensor block but different inside it...
-- boring I know!
DifferentVars : ∀ {δI}{I : Proto δI}{c d A B} → [ c ↦ A ]∈ I → [ d ↦ B ]∈ I → Set
DifferentVars l l' = DifferentVarsDoms (Proto.forget ([↦]∈.lI l)) (Proto.forget ([↦]∈.lI l'))
-}


postulate
  DifferentVars… : ∀ {δI}{I : Proto δI}{c d A B} → [ c ↦ A …]∈' I → [ d ↦ B …]∈' I → Set
  Diff-sym… : ∀ {δI}{I : Proto δI}{c d A B}{l : [ c ↦ A …]∈' I}{l' : [ d ↦ B …]∈' I}
    → DifferentVars… l l' → DifferentVars… l' l

record DifferentVars {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈' I)(l' : [ d ↦ B ]∈' I) : Set where
  constructor mk
  field
    Diff… : DifferentVars… ([↦]∈'.l… l) ([↦]∈'.l… l')
open DifferentVars

Diff-sym : ∀ {δI}{I : Proto δI}{c d A B}{l : [ c ↦ A ]∈' I}{l' : [ d ↦ B ]∈' I}
    → DifferentVars l l' → DifferentVars l' l
Diff… (Diff-sym df) = Diff-sym… (Diff… df)

data SameVar? {δI}{I : Proto δI} : ∀ {c c' A A'} → [ c ↦ A …]∈' I → [ c' ↦ A' …]∈' I → Set₁ where
  same : ∀ {c A}{l : [ c ↦ A …]∈' I} → SameVar? l l
  diff : ∀ {c c' A B}{l : [ c ↦ A …]∈' I}{l' : [ c' ↦ B …]∈' I} → DifferentVars… l l' → SameVar? l l'

postulate
  sameVar? : ∀ {δI}{I : Proto δI}{c c' A A'}(l : [ c ↦ A …]∈' I)(l' : [ c' ↦ A' …]∈' I) → SameVar? l l'

postulate
  TC-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}
    → I ≈ J → TC'⟨ I ⟩ → TC'⟨ J ⟩

  ♦-assoc : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ♦Proto' (B ♦Proto' C) ≈ (A ♦Proto' B) ♦Proto' C
  ♦-com : ∀ {δa δb}{A : Proto δa}{B : Proto δb} → (A ♦Proto' B) ≈ (B ♦Proto' A)
  ♦-cong₂ : ∀ {δa δb δc δd}{A : Proto δa}{B : Proto δb}{C : Proto δc}{D : Proto δd}
          → A ≈ B → C ≈ D → A ♦Proto' C ≈ B ♦Proto' D
  ♦-com, : ∀ {δa δ δb}{A : Proto δa}{B : Proto δb}{E : Env δ} → (A ,[ E ]) ♦Proto' B ≈ (A ♦Proto' B),[ E ]
  ∈♦₀… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A …]∈' I₀ → [ c ↦ A …]∈' (I₀ ♦Proto' I₁)
  ∈♦₁… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A …]∈' I₁ → [ c ↦ A …]∈' (I₀ ♦Proto' I₁)

  /Ds-com : ∀ {δs δ δ'}{I : Proto δs}(l : Doms'.[ δ ]∈ δs)(l' : Doms'.[ δ' ]∈ δs)
    → I /Ds l /Ds l' ≈ I /Ds l' /Ds l


  move… : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈' I)(l' : [ d ↦ B …]∈' I) → DifferentVars… l l'
          → [ d ↦ B …]∈' (I [/…]' l)
  move-compute… : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈' I)(l' : [ d ↦ B …]∈' I)(l/=l' : DifferentVars… l l')
    → (I [/…]' l) [/…]' move… l l' l/=l' ≈ (I [/…]' l) /Ds [↦…]∈'.lΔ l'

∈♦₀ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈' I₀ → [ c ↦ A ]∈' (I₀ ♦Proto' I₁)
∈♦₀ (mk l… E/c) = mk (∈♦₀… l…) {!!}

∈♦₁ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈' I₁ → [ c ↦ A ]∈' (I₀ ♦Proto' I₁)
∈♦₁ (mk l… E/c) = {!!}

∈♦₀-compute : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈' I₀) →
          (I₀ ♦Proto' I₁) [/]' (∈♦₀ l) ≈ (I₀ [/]' l) ♦Proto' I₁
∈♦₀-compute = {!!}

∈♦₁-compute : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈' I₁) →
          (I₀ ♦Proto' I₁) [/]' (∈♦₁ l) ≈ I₀ ♦Proto' (I₁ [/]' l)
∈♦₁-compute = {!!}

move : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈' I)(l' : [ d ↦ B ]∈' I) → DifferentVars l l'
          → [ d ↦ B ]∈' (I [/]' l)
move (mk l X) (mk l' Y) df = mk (move… l l' (Diff… df)) {!!}

record TC-Split (A : Session) {δK}(K : Proto δK) : Set₁ where
  field
    NES : ¬ (Session.Ended A)
    cont-⅋ : ∀ {S T} → A ≡ S ⅋ T → ∀ {d e δJ}{J : Proto δJ}(l : [ d ↦ S ]∈' J)(l' : [ e ↦ T ]∈' J)
      → DifferentVars l l' → TC'⟨ J ⟩ → TC'⟨ (J /Ds [↦]∈'.lΔ l /Ds [↦]∈'.lΔ l') ♦Proto' K ⟩
    cont-⊗ : ∀ {S T} → A ≡ S ⊗ T → ∀ {d e δ₀ δ₁}{J₀ : Proto δ₀}{J₁ : Proto δ₁}(l : [ d ↦ S …]∈' J₀)(l' : [ e ↦ T …]∈' J₁)
      → TC'⟨ J₀ ⟩ → TC'⟨ J₁ ⟩ → TC'⟨ (J₀ Proto./' [↦…]∈'.lI l ♦Proto' J₁ Proto./' ([↦…]∈'.lI l')) ♦Proto' K ⟩
open TC-Split

postulate
  End/₀ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./₀ σ)
  End/₁ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./₁ σ)
  End/[b] : ∀ {δ}{E : Env δ}(b : 𝟚)(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./[ b ] σ)
  Sel♦ : ∀ {δs}{I : Proto δs}(σ : Selections δs) → I /₀ σ ♦Proto' I /₁ σ ≈ I

postulate
  select : ∀ {c δI δE}{I : Proto δI}(σ : Selections δI)(lΔ : Doms'.[ δE ]∈ δI)(lA : c Dom'.∈ δE)
    → Env.Ended (Proto.lookup I lΔ Env./D lA)
    → Proto.lookup I lΔ
    ≡ Proto.lookup (I /[ Map.lookup (Proto.lookup σ lΔ) lA ] σ) lΔ

module _ {δI}(b : 𝟚)(σ : Selections δI) where
  Selections♦ : ∀ δK → Selections (δI ♦Doms δK)
  Selections♦ · = σ
  Selections♦ (δK ,[ x ]) = Selections♦ δK ,[ constMap x b ]

  atMost♦ : ∀ {n} δK → AtMost n σ → AtMost n (Selections♦ δK)
  atMost♦ · A = A
  atMost♦ (δK ,[ x ]) A = atMost♦ δK A ,[ (₀₁ b (pureAll x (λ _ → refl))) ]

postulate
  Selections♦/same : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto' K) /[ b ] (Selections♦ b σ δK) ≈ (I /[ b ] σ) ♦Proto' K

  Selections♦/not : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto' K) /[ b ] (Selections♦ (not b) σ δK) ≈ I /[ b ] σ

  /[]-/Ds : ∀ {δE δI}(b : 𝟚)(I : Proto δI)(σ : Selections δI)(l : Doms'.[ δE ]∈ δI)
    → (I /Ds l) /[ b ] σ ≈ (I /[ b ] σ) /Ds l

/*-End : ∀ {δE}(E : Env δE) → Env.Ended (E /*)
/*-End ε = _
/*-End (E , c ↦ v) = ⟨ (/*-End E) , _ ⟩

/Ds-/[] : ∀ {δE δI}(b : 𝟚)(I : Proto δI)(lΔ : Doms'.[ δE ]∈ δI)(σ : Selections δI)
  → Env.Ended (Proto.lookup I lΔ Env./[ b ] Proto.lookup σ lΔ)
  → (I /Ds lΔ) /[ b ] σ ≈ I /[ b ] σ
/Ds-/[] b (I ,[ Δ ]) Doms'.here (σ ,[ Δ₁ ]) En = ≈,[] ≈-refl (End/[b] b Δ₁ (/*-End Δ) ∼-End En)
/Ds-/[] b (I ,[ Δ ]) (Doms'.there lΔ) (σ ,[ Δ₁ ]) En = ≈,[] (/Ds-/[] b I lΔ σ En) ∼-refl

-- Really clever proof yay!
SEnd// :(b : 𝟚)(S : Session)(σ : 𝟚) → Session.Ended (Env.selectProj (not b) (Env.selectProj b S σ) σ)
SEnd// 1₂ S 1₂ = 0₁
SEnd// 1₂ S 0₂ = 0₁
SEnd// 0₂ S 1₂ = 0₁
SEnd// 0₂ S 0₂ = 0₁

End// : ∀ {δE}(b : 𝟚)(E : Env δE)(σ : Selection δE) → Env.Ended ((E Env./[ b ] σ) Env./[ not b ] σ)
End// b ε ε = _
End// b (E , c ↦ v) (σ , .c ↦ v₁) = ⟨ (End// b E σ) , SEnd// b v v₁ ⟩

TC-∈Split : ∀ {δI δK c A}{I : Proto δI}{K : Proto δK} → TC-Split A K → (l : [ c ↦ A ]∈' I)
  → TC'⟨ I ⟩ → TC'⟨ I [/]' l ♦Proto' K ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) with sameVar? ([↦]∈'.l… l) l₁
TC-∈Split cont (mk l X) (TC-⊗-out .l σs σE A0 P₀ P₁) | same = TC-conv
  (♦-cong₂ (≈-trans (♦-cong₂ (≈,[end] ⟨ mapAll (λ _ → _) _ , _ ⟩)
                             (≈,[end] ⟨ (mapAll (λ _ → _) _) , _ ⟩))
                    (Sel♦ σs))
   ≈-refl)
  (cont-⊗ cont refl (mk (mk Doms'.here refl) (mk here refl))
                    (mk (mk Doms'.here refl) (mk here refl))
                    (P₀ c₀) (P₁ c₁))
  where postulate c₀ c₁ : _
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) | diff x = {!!}
TC-∈Split cont l (TC-⅋-inp l₁ P) with sameVar? ([↦]∈'.l… l) ([↦]∈'.l… l₁)
TC-∈Split cont (mk l… E/c) (TC-⅋-inp (mk .l… E/c₁) P) | same = TC-conv
  (♦-cong₂ (≈-trans (≈,[end] _) (≈,[end] _)) ≈-refl)
  (cont-⅋ cont refl (mk (mk (mk (Doms'.there Doms'.here) refl) (mk here refl)) _)
                    (mk (mk (mk Doms'.here refl) (mk here refl)) _)
                    {!!} (P c₀ c₁))
  -- postulate for channels.. grr
  where postulate c₀ c₁ : _
TC-∈Split cont l (TC-⅋-inp l₁ P) | diff x = TC-⅋-inp (∈♦₀ (move l l₁ (mk x))) λ c₀ c₁ →
  TC-conv (≈-trans ♦-com,
          (≈,[] (≈-trans ♦-com, (≈,[]
           (≈-sym (≈-trans (∈♦₀-compute (move l l₁ (mk x)))
           (♦-cong₂ (≈-trans (move-compute… _ _ _)
           (≈-trans (/Ds-com ([↦]∈'.lΔ l) ([↦]∈'.lΔ l₁))
           (≈-sym (move-compute… _ _ _))))
           ≈-refl)))
           ∼-refl))
           ∼-refl))
  (TC-∈Split cont (there[]' (there[]' (move l₁ l (Diff-sym (mk x))))) (P c₀ c₁))
TC-∈Split cont l (TC-end E) = 𝟘-elim (NES cont (Map.All∈' (Proto.All∈' E ([↦]∈'.lI l)) ([↦]∈'.lE l)))
TC-∈Split {I = I} cont (mk (mk (mk lΔ ↦Δ) (mk lA ↦A)) E/c) (TC-split σs A1 P P₁)
    with Map.lookup (Proto.lookup σs lΔ) lA
    | select {I = I} σs lΔ lA
TC-∈Split {δK = δK}{I = I}{K} cont (mk (mk (mk lΔ refl) (mk lA refl)) E/c) (TC-split σs A1 P P₁)
  | 0₂ | x  = TC-split (Selections♦ 0₂ σs δK) (atMost♦ 0₂ σs δK A1)
  (TC-conv (≈-sym (≈-trans (Selections♦/same {I = I /Ds lΔ} {K} 0₂ σs)
                  (♦-cong₂ (/[]-/Ds 0₂ I σs lΔ) ≈-refl)))
           (TC-∈Split cont (mk (mk (mk lΔ refl) (mk lA (! ap (λ M → Map.lookup M lA) (x E/c))))
                      (tr Env.Ended (ap (λ M → M [ lA ]≔' end) (x E/c)) E/c)) P))
  (TC-conv (≈-sym (≈-trans (Selections♦/not {I = I /Ds lΔ} {K} 1₂ σs)
             (/Ds-/[] 1₂ I lΔ σs (let X = x E/c ∙ lookup/zipWith _ I σs lΔ
               in tr Env.Ended (ap (flip Env._/₁_ (Proto.lookup σs lΔ)) (! X))
                               (End// 0₂ (Proto.lookup I lΔ) (Proto.lookup σs lΔ))))))
           P₁)
TC-∈Split {δK = δK}{I = I}{K} cont (mk (mk (mk lΔ refl) (mk lA refl)) E/c) (TC-split σs A1 P P₁)
  | 1₂ | x = TC-split (Selections♦ 1₂ σs δK) (atMost♦ 1₂ σs δK A1)
  (TC-conv (≈-sym (≈-trans (Selections♦/not {I = I /Ds lΔ} {K} 0₂ σs)
             (/Ds-/[] 0₂ I lΔ σs (let X = x E/c ∙ lookup/zipWith _ I σs lΔ
               in tr Env.Ended (ap (flip Env._/₀_ (Proto.lookup σs lΔ)) (! X))
                               (End// 1₂ (Proto.lookup I lΔ) (Proto.lookup σs lΔ))))))
           P)
  (TC-conv (≈-sym (≈-trans (Selections♦/same {I = I /Ds lΔ} {K} 1₂ σs)
                  (♦-cong₂ (/[]-/Ds 1₂ I σs lΔ) ≈-refl)))
           (TC-∈Split cont (mk (mk (mk lΔ refl) (mk lA (! ap (λ M → Map.lookup M lA) (x E/c))))
                      (tr Env.Ended (ap (λ M → M [ lA ]≔' end) (x E/c)) E/c)) P₁))

TC-∈⅋ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⅋ B ]∈' I)
  → (∀ {d e δJ}{J : Proto δJ} (l : [ d ↦ A ]∈' J)(l' : [ e ↦  B ]∈' J) → DifferentVars l l' → TC'⟨ J ⟩
     → TC'⟨ ((J Proto./' [↦]∈'.lI l) /Ds [↦]∈'.lΔ l') ♦Proto' K ⟩)
  → TC'⟨ I ⟩ →  TC'⟨ I [/]' l ♦Proto' K ⟩
TC-∈⅋ = {!!}

TC-∈⊗ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⊗ B ]∈' I)
  → (∀ {d e δJ₀ δJ₁}{J₀ : Proto δJ₀}{J₁ : Proto δJ₁}
       (l₀ : [ d ↦ A …]∈' J₀)(l₁ : [ e ↦ B …]∈' J₁) → TC'⟨ J₀ ⟩ → TC'⟨ J₁ ⟩
        → TC'⟨ (J₀ [/…]' l₀ ♦Proto' J₁ [/…]' l₁) ♦Proto' K ⟩)
  → TC'⟨ I ⟩ → TC'⟨ I [/]' l ♦Proto' K ⟩
TC-∈⊗ {A = A}{B}{K = K} l cont = TC-∈Split cont' l
  where
     cont' : TC-Split (A ⊗ B) K
     NES cont' x = x
     cont-⅋ cont' () l₁ l' x₁ x₂
     cont-⊗ cont' refl = cont -- l₁ l' x₁ x₂ = {!!}

TC-cut :
    ∀ {c₀ c₁ S₀ S₁ δ₀ δ₁}{I₀ : Proto δ₀}{I₁ : Proto δ₁}
      (D : Dual S₀ S₁)
      (l₀ : [ c₀ ↦ S₀ ]∈' I₀)(l₁ : [ c₁ ↦ S₁ ]∈' I₁)
      (P₀ : TC'⟨ I₀ ⟩) (P₁ : TC'⟨ I₁ ⟩)
    → TC'⟨ (I₀ [/]' l₀) ♦Proto' (I₁ [/]' l₁) ⟩
TC-cut end l₀ l₁ P₀ P₁ = {!TC-split σs A0 P₀ P₁!}
TC-cut (⊗⅋ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = ?
{-TC-conv ♦-com
  (TC-∈⅋ l₁ (λ d e d/=e a'b' → TC-conv (≈-trans ♦-com (♦-cong₂ (≈-trans {!move-compute {!e!} {!d!} {!(Diff-sym d/=e)!}!} {!Proto.forget!}) ≈-refl))
   (TC-∈⊗ l₀ (λ d' e' a b → TC-conv (≈-trans (♦-cong₂ ≈-refl
               (∈♦₁-compute (move {!e!} {!d!} {!(Diff-sym d/=e)!}))) ♦-assoc)
     (TC-cut  D d' (∈♦₁ (move {!e!} {!d!} {!(Diff-sym d/=e)!})) a (TC-cut D₂ e' e b a'b')))
   P₀))
  P₁)
  -}
TC-cut (⅋⊗ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-conv ≈-refl
  (TC-∈⅋ l₀ (λ {_}{_}{_}{J} d e d/=e ab → TC-conv ♦-com
  (TC-∈⊗ l₁ (λ {_}{_}{_}{_}{J₀}{J₁} d' e' a b → let X = TC-cut D₁ d' d a ab
       in TC-conv (≈-trans (♦-cong₂ ≈-refl (∈♦₁-compute (move d e d/=e)))
               (≈-trans ♦-assoc (♦-cong₂ ♦-com (move-compute… ([↦]∈'.l… d) ([↦]∈'.l… e) (Diff… d/=e)))))
          (TC-cut D₃ e' (∈♦₁ (move d e d/=e)) b X))
   P₁)) P₀)

{-
TC-∈Split {I = I} cont (mk (mk (mk lΔ ↦Δ) (mk lA ↦A)) E/c) (TC-split σs A1 P P₁) with select {I = I} σs lΔ lA
TC-∈Split {δK = δK}{I = I}{K} cont (mk (mk (mk lΔ refl) (mk lA refl)) E/c) (TC-split σs A1 P P₁)
  | inj₁ x = TC-split (Selections♦ 0₂ σs δK) (atMost♦ 0₂ σs δK A1)
  (TC-conv (≈-sym (≈-trans (Selections♦/same {I = I /Ds lΔ} {K} 0₂ σs)
                  (♦-cong₂ (/[]-/Ds 0₂ I σs lΔ) ≈-refl)))
           (TC-∈Split cont (mk (mk (mk lΔ refl) (mk lA (! x))) {!!}) P))
  (TC-conv (≈-sym (≈-trans (Selections♦/not {I = I /Ds lΔ} {K} 1₂ σs) {!!}))
           P₁)
TC-∈Split cont (mk (mk (mk lΔ ↦Δ) (mk lA ↦A)) E/c) (TC-split σs A1 P P₁)
  | inj₂ y = {!!}

{-
-- selection style
record TC-Split (A : Session) {δK}(K : Proto δK) : Set₁ where
  field
    NES : ¬ (Session.Ended A)
    cont-⅋ : ∀ {S T} → A ≡ S ⅋ T → ∀ {d e δJ}{J : Proto δJ}(σ : Selections δJ)
      → K ≈ J /₁ σ →
      (l : [ d ↦ S ]∈ J /₀ σ)(l' : [ e ↦ T ]∈ J /₀ σ)
      → DifferentVars l l' → TC⟨ J /₀ σ ⟩ → TC⟨ J /₁ σ ⟩
      → TC⟨ (J /Ds Proto.forget ([↦]∈.lI l) /Ds Proto.forget ([↦]∈.lI l')) ⟩
open TC-Split

TC-∈Split : ∀ {δI c A}{I : Proto δI}(σ : Selections δI) → TC-Split A (I /₁ σ) → (l : [ c ↦ A ]∈ I /₀ σ)
  → TC⟨ I /₀ σ ⟩ → TC⟨ I /Ds Proto.forget ([↦]∈.lI l) ⟩
TC-∈Split σ cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) = {!!}
TC-∈Split σ cont l (TC-⅋-inp l₁ P) with sameVar? ([↦]∈.l… l) ([↦]∈.l… l₁)
TC-∈Split σ cont (mk l X) (TC-⅋-inp (mk .l X₁) P) | same =
  let X = cont-⅋ cont refl {c₀}{c₁} ((σ ,[ ε , _ ↦ 0₂ ]) ,[ ε , _ ↦ 0₂ ])
          (≈-sym (≈-trans (≈,[end] _) (≈-trans (≈,[end] _) {!!})))
          (there[] (mk (mk here here) {!!})) (mk (mk here here) {!!}) {!!} (TC-conv {!≈-refl!} (P c₀ c₁)) {!!}
   in TC-conv (≈-trans (≈,[end] _) (≈,[end] _)) X
   where postulate c₀ c₁ : _
TC-∈Split σ cont l (TC-⅋-inp l₁ P) | diff x = TC-⅋-inp {!l₁!} {!!}
TC-∈Split σ cont l (TC-end E) = {!!}
TC-∈Split σ cont l (TC-split σs A1 P P₁) = {!!}
-}

-- OLD ATTEMPT
{-


record TC-Split (A : Session) {δK}(K : Proto δK) : Set₁ where
  field
    NES : ¬ (Session.Ended A)
    cont-⅋ : ∀ {S T} → A ≡ S ⅋ T → ∀ {d e δJ}{J : Proto δJ}(l : [ d ↦ S ]∈ J)(l' : [ e ↦ T ]∈ J)
      → DifferentVars l l' → TC⟨ J ⟩ → TC⟨ (J / [↦]∈.lI l /Ds Proto.forget ([↦]∈.lI l')) ♦Proto' K ⟩
    cont-⊗ : ∀ {S T} → A ≡ S ⊗ T → ∀ {d e δ₀ δ₁}{J₀ : Proto δ₀}{J₁ : Proto δ₁}(l : [ d ↦ S ]∈ J₀)(l' : [ e ↦ T ]∈ J₁)
      → TC⟨ J₀ ⟩ → TC⟨ J₁ ⟩ → TC⟨ (J₀ / [↦]∈.lI l ♦Proto' J₁ / ([↦]∈.lI l')) ♦Proto' K ⟩
open TC-Split

{-
-- need to add that the erasure of the result is the same
postulate
  ∈-selections : ∀ {c A δI}{I : Proto δI}(σ : Selections δI)(l : [ c ↦ A ]∈ I)
    → (c ↦ A ∈ (([↦]∈.E l) Env./₀ σ))
    ⊎ ([ c ↦ A ]∈ I /₁ σ)
-}

data ∈-select {c A}{δI}{I : Proto δI}:(σ : Selections δI) → [ c ↦ A ]∈ I → Set where

postulate
  End/₀ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./₀ σ)
  End/₁ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./₁ σ)
  Sel♦ : ∀ {δs}{I : Proto δs}(σ : Selections δs) → I /₀ σ ♦Proto' I /₁ σ ≈ I

--need continuation for ⊗
TC-∈Split : ∀ {δI δK c A}{I : Proto δI}{K : Proto δK} → TC-Split A K → (l : [ c ↦ A ]∈ I)
  → TC⟨ I ⟩ → TC⟨ I [/] l ♦Proto' K ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) with sameVar? ([↦]∈.l… l) l₁
TC-∈Split cont (mk l X) (TC-⊗-out .l σs σE A0 P₀ P₁) | same = TC-conv
  (♦-cong₂ (≈-trans (♦-cong₂ (≈,[end] ⟨ mapAll _ _ , _ ⟩) (≈,[end] ⟨ mapAll _ _ , _ ⟩))
  (Sel♦ σs))
  ≈-refl)
  (cont-⊗ cont refl (mk (mk here here) E₀) (mk (mk here here) ⟨ End/₁ σE X , _ ⟩) (P₀ c₀) (P₁ c₁))
  where postulate c₀ c₁ : _
        E₀ = ⟨ End/₀ σE X , _ ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) | diff x = {!!}
TC-∈Split cont l (TC-⅋-inp l₁ P) with sameVar? ([↦]∈.l… l) ([↦]∈.l… l₁)
TC-∈Split cont (mk l X) (TC-⅋-inp (mk .l Y) P) | same = TC-conv
  (♦-cong₂ (≈-trans (≈,[end] _) (≈,[end] _)) ≈-refl)
  (cont-⅋ cont refl (there[] (mk (mk here here) _)) (mk (mk here here) _) {!!} (P c₀ c₁))
  -- postulate for channels.. grr
  where postulate c₀ c₁ : _
TC-∈Split cont l (TC-⅋-inp l₁ P) | diff x = TC-⅋-inp (∈♦₀ (move l l₁ (mk x))) λ c₀ c₁ →
  TC-conv (≈-trans ♦-com,
          (≈,[] (≈-trans ♦-com, (≈,[]
           (≈-sym (≈-trans (∈♦₀-compute (move l l₁ (mk x)))
           (♦-cong₂ (≈-trans (move-compute… _ _ _)
           (≈-trans (/Ds-com (Proto.forget ([↦]∈.lI l)) (Proto.forget ([↦]∈.lI l₁)))
           (≈-sym (move-compute… _ _ _))))
           ≈-refl)))
           ∼-refl))
           ∼-refl))
  (TC-∈Split cont (there[] (there[] (move l₁ l (Diff-sym (mk x))))) (P c₀ c₁))
TC-∈Split cont l (TC-end E) = 𝟘-elim (NES cont (Map.All∈ (Proto.All∈ E ([↦]∈.lI l)) ([↦]∈.lE l)))
TC-∈Split cont l (TC-split σs A1 P P₁) = {!!}

{-with ∈-selections σs l
TC-∈Split {δK = δK} cont l (TC-split σs A1 P P₁) | inj₁ x = TC-split (allLeft δK σs) {!!} (TC-conv {!!} (TC-∈Split cont x P)) (TC-conv {!!} P₁)
TC-∈Split cont l (TC-split σs A1 P P₁) | inj₂ y = {!!}

-}
-}
{-
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) with sameVar? ([↦]∈.l… l) l₁
TC-∈Split cont (mk l X) (TC-⊗-out .l σs σE A0 P₀ P₁) | same = TC-conv
  (♦-cong₂ (≈-trans (♦-cong₂ (≈,[end] ⟨ mapAll _ _ , _ ⟩) (≈,[end] ⟨ mapAll _ _ , _ ⟩))
  (Sel♦ σs))
  ≈-refl)
  (cont-⊗ cont refl (mk (mk here here) E₀) (mk (mk here here) ⟨ End/₁ σE X , _ ⟩) (P₀ c₀) (P₁ c₁))
  where postulate c₀ c₁ : _
        E₀ = ⟨ End/₀ σE X , _ ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) | diff x = {!!}
TC-∈Split cont l (TC-⅋-inp l₁ P) with sameVar? ([↦]∈.l… l) ([↦]∈.l… l₁)
TC-∈Split cont (mk l X) (TC-⅋-inp (mk .l Y) P) | same = TC-conv
  (♦-cong₂ (≈-trans (≈,[end] _) (≈,[end] _)) ≈-refl)
  (cont-⅋ cont refl (there[] (mk (mk here here) _)) (mk (mk here here) _) {!!} (P c₀ c₁))
  -- postulate for channels.. grr
  where postulate c₀ c₁ : _
TC-∈Split cont l (TC-⅋-inp l₁ P) | diff x = TC-⅋-inp (∈♦₀ (move l l₁ (mk x))) λ c₀ c₁ →
  TC-conv (≈-trans ♦-com,
          (≈,[] (≈-trans ♦-com, (≈,[]
           (≈-sym (≈-trans (∈♦₀-compute (move l l₁ (mk x)))
           (♦-cong₂ (≈-trans (move-compute… _ _ _)
           (≈-trans (/Ds-com (Proto.forget ([↦]∈.lI l)) (Proto.forget ([↦]∈.lI l₁)))
           (≈-sym (move-compute… _ _ _))))
           ≈-refl)))
           ∼-refl))
           ∼-refl))
  (TC-∈Split cont (there[] (there[] (move l₁ l (Diff-sym (mk x))))) (P c₀ c₁))
TC-∈Split cont l (TC-end E) = 𝟘-elim (NES cont (Map.All∈ (Proto.All∈ E ([↦]∈.lI l)) ([↦]∈.lE l)))
TC-∈Split cont l (TC-split σs A1 P P₁) = {!!}
-}




{-

TC-∈⅋ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⅋ B ]∈ I)
  → (∀ {d e δJ}{J : Proto δJ} (l : [ d ↦ A ]∈ J)(l' : [ e ↦  B ]∈ J) → DifferentVars l l' → TC⟨ J ⟩
     → TC⟨ ((J / [↦]∈.lI l) /Ds Proto.forget ([↦]∈.lI l')) ♦Proto' K ⟩)
  → TC⟨ I ⟩ →  TC⟨ I [/] l ♦Proto' K ⟩
TC-∈⅋ l cont (TC-⊗-out l₁ σs σE A0 P₀ P₁) with sameVar? ([↦]∈.l… l) l₁
... | X = {!!}
TC-∈⅋ l cont (TC-⅋-inp l₁ P) with sameVar? ([↦]∈.l… l) ([↦]∈.l… l₁)
TC-∈⅋ (mk l y) cont (TC-⅋-inp (mk .l x) P) | same = TC-conv (♦-cong₂ (≈-trans (≈,[end] _) (≈,[end] _)) ≈-refl) (cont (mk (mk (there here) here) _) (mk (mk here here) _) {!!} (TC-conv ≈-refl (P c₀ c₁)))
  where
    postulate
      c₀ c₁ : _
TC-∈⅋ l cont (TC-⅋-inp l₁ P) | diff l/=l₁ = TC-⅋-inp (∈♦₀ (move  l l₁ (mk l/=l₁))) (λ c₀ c₁ →
   TC-conv (≈-trans ♦-com, (≈,[] (≈-trans ♦-com, (≈,[] (≈-sym (≈-trans (∈♦₀-compute (move l l₁ (mk l/=l₁)))
           (♦-cong₂ (≈-trans (move-compute… ([↦]∈.l… l) ([↦]∈.l… l₁) l/=l₁)
           (≈-trans {!!}
            (≈-sym (move-compute… _ _ _)))) ≈-refl))) ∼-refl)) ∼-refl))
  (TC-∈⅋ (there[] (there[] (move l₁ l (Diff-sym (mk l/=l₁))))) cont (P c₀ c₁)))
TC-∈⅋ l cont (TC-end E) = {!!}
TC-∈⅋ l cont (TC-split σs A1 P P₁) = {!!}

{-
TC-∈⊗ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⊗ B ]∈ I)
  → (∀ {d e δJ₀ δJ₁}{J₀ : Proto δJ₀}{J₁ : Proto δJ₁}
       (l₀ : [ d ↦ A ]∈ J₀)(l₁ : [ e ↦ B ]∈ J₁) → TC⟨ J₀ ⟩ → TC⟨ J₁ ⟩
        → TC⟨ (J₀ [/] l₀ ♦Proto' J₁ [/] l₁) ♦Proto' K ⟩)
  → TC⟨ I ⟩ → TC⟨ I [/] l ♦Proto' K ⟩
TC-∈⊗ = {!!}


{-
TC-cut :
    ∀ {c₀ c₁ S₀ S₁ δ₀ δ₁}{I₀ : Proto δ₀}{I₁ : Proto δ₁}
      (D : Dual S₀ S₁)
      (l₀ : [ c₀ ↦ S₀ ]∈ I₀)(l₁ : [ c₁ ↦ S₁ ]∈ I₁)
      (P₀ : TC⟨ I₀ ⟩) (P₁ : TC⟨ I₁ ⟩)
    → TC⟨ (I₀ [/] l₀) ♦Proto' (I₁ [/] l₁) ⟩
TC-cut end σs A0 P₀ P₁ = {!TC-split σs A0 P₀ P₁!}
TC-cut (⊗⅋ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-conv ♦-com
  (TC-∈⅋ l₁ (λ d e d/=e a'b' → TC-conv (≈-trans ♦-com (♦-cong₂ (≈-trans (move-compute {!e!} {!d!} {!(Diff-sym d/=e)!}) {!Proto.forget!}) ≈-refl))
   (TC-∈⊗ l₀ (λ d' e' a b → TC-conv (≈-trans (♦-cong₂ ≈-refl
               (∈♦₁-compute (move {!e!} {!d!} {!(Diff-sym d/=e)!}))) ♦-assoc)
     (TC-cut  D d' (∈♦₁ (move {!e!} {!d!} {!(Diff-sym d/=e)!})) a (TC-cut D₂ e' e b a'b')))
   P₀))
  P₁)
TC-cut (⅋⊗ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-conv ≈-refl
  (TC-∈⅋ l₀ (λ {_}{_}{_}{J} d e d/=e ab → TC-conv ♦-com
  (TC-∈⊗ l₁ (λ {_}{_}{_}{_}{J₀}{J₁} d' e' a b → let X = TC-cut D₁ d' d a ab
       in TC-conv (≈-trans (♦-cong₂ ≈-refl (∈♦₁-compute (move d e d/=e)))
               (≈-trans ♦-assoc (♦-cong₂ ♦-com (move-compute d e (mk d/=e)))))
          (TC-cut D₃ e' (∈♦₁ (move d e d/=e)) b X))
   P₁)) P₀)

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
-- -}
-- -}
-- -}
-- -}
