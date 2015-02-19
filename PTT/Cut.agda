
{-# OPTIONS --copatterns #-}
open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Nat

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP hiding ([_]; J)
open import PTT.Dom hiding (∈♦₀)
import PTT.Session as Session
import PTT.Map as Map
import PTT.Env as Env
import PTT.Proto as Proto
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; _/[_]_; Ended)
open Proto   hiding (♦-assoc ; ♦-com ; ♦-com, ; /Ds-com ; ♦-cong₂)
open import PTT.Term
open import PTT.Vars
open import PTT.Conversion
open import PTT.Split

module PTT.Cut where

TC-cut :
    ∀ {c₀ c₁ S₀ S₁ δ₀ δ₁}{I₀ : Proto δ₀}{I₁ : Proto δ₁}
      (D : Dual S₀ S₁)
      (l₀ : [ c₀ ↦ S₀ ]∈ I₀)(l₁ : [ c₁ ↦ S₁ ]∈ I₁)
      (P₀ : TC'⟨ I₀ ⟩) (P₁ : TC'⟨ I₁ ⟩)
    → TC'⟨ (I₀ / l₀) ♦Proto' (I₁ / l₁) ⟩
TC-cut 𝟙⊥ l₀ l₁ P₀ P₁ = {!!}
TC-cut ⊥𝟙 l₀ l₁ P₀ P₁ = {!!}
TC-cut (act (?! {F = F} x x₁)) l₀ l₁ P₀ P₁ = TC-∈? l₀ P₀ λ {_}{_}{_}{I}{E} lI lA E₁ C →
  TC-conv ♦-com
    (TC-∈! l₁ P₁ λ m l x₂ →
      TC-conv (♦-com ≈-∙ ♦-cong₂ ≈-refl (≈-reflexive ([≔][≔] _ _ (λ Δ → ≔'≔' Δ lA) I ([]∈.lΔ lI))))
       (TC-cut (x m) (mk (mk ⟨ ([]∈.lΔ lI) , lookup-same I ([]∈.lΔ lI) _ ⟩ ⟨ lA , lookup-[]≔ _ lA ⟩)
                         (tr Env.Ended (! (ap (λ E → E [ lA ]≔' end) (ap (λ E → E [ lA ]≔' « F m ») ([]∈.↦Δ lI)) ∙ ≔'≔' E lA)) E₁))
               l (C m) x₂))
TC-cut (act (!? {G = G} x x₁)) l₀ l₁ P₀ P₁ = TC-∈! l₀ P₀ λ m l x₂ →
  TC-conv ♦-com
    (TC-∈? l₁ P₁ (λ {_}{_}{_}{I}{E} lI lA E₁ C → TC-conv (♦-com ≈-∙ ♦-cong₂
                        (≈-reflexive ([≔][≔] _ _ (λ Δ → ≔'≔' Δ lA ) I ([]∈.lΔ lI))) ≈-refl)
      (TC-cut (x m) l (mk (mk ⟨ ([]∈.lΔ lI) , lookup-same I ([]∈.lΔ lI) _ ⟩ ⟨ lA , lookup-[]≔ _ lA ⟩)
                          (tr Env.Ended (! (ap (λ E → E [ lA ]≔' end) (ap (λ E → E [ lA ]≔' « G m ») ([]∈.↦Δ lI)) ∙ ≔'≔' E lA)) E₁))
                    x₂ (C m))))
TC-cut (⊗⅋ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-∈⊗ l₀ P₀ λ d' e' a b →
  TC-conv ♦-com
    (TC-∈⅋ l₁ P₁ λ {_}{_}{_}{J} d e d/=e ab →
      TC-conv (♦-cong₂ ≈-refl (∈♦₁-compute (move d e (mk d/=e)))
              ≈-∙ ♦-assoc ≈-∙ ♦-com ≈-∙ ♦-cong₂ ≈-refl ♦-com )
        (TC-cut D₂ e' (∈♦₁ (move d e (mk d/=e))) b (TC-cut D d' d a ab)))
TC-cut (⅋⊗ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-∈⅋ l₀ P₀ λ {_}{_}{_}{J}d e d/=e ab →
 TC-conv ♦-com
 (TC-∈⊗ l₁ P₁ λ d' e' a b →
  TC-conv (♦-cong₂ ≈-refl (∈♦₁-compute (move d e (mk d/=e)))
          ≈-∙ ♦-assoc ≈-∙ ♦-cong₂ ♦-com ≈-refl)
     (TC-cut D₃ e' (∈♦₁ (move d e (mk d/=e))) b (TC-cut D₁ d' d a ab)))


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
