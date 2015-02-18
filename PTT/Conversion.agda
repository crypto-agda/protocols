
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
open Proto   hiding (♦-assoc ; ♦-com ; ♦-com, ; /Ds-com)
open import PTT.Term
open import PTT.Vars

module PTT.Conversion where

infix 0 _∼'_
data _∼'_ : Dom → Dom → Set where
  ∼-refl : ∀ {E} → E ∼' E
  ∼-trans : ∀ {E F G} → E ∼' F → F ∼' G → E ∼' G
  ∼,↦ : ∀ {E F c} → E ∼' F → E , c ↦* ∼' F , c ↦*
  ∼,↦end : ∀ {E c} → E , c ↦* ∼' E
  ∼,↦end' : ∀ {E c} → E ∼' E , c ↦*
  ∼,[swap] : ∀ {E c d} → E , c ↦* , d ↦* ∼' E , d ↦* , c ↦*

infix 0 _≈'_
data _≈'_ : Doms → Doms → Set where
  ≈-refl : ∀ {I} → I ≈' I
  ≈-trans : ∀ {I J K} → I ≈' J → J ≈' K → I ≈' K
  ≈,[] : ∀ {E F I J} → I ≈' J → E ∼' F → I ,[ E ] ≈' J ,[ F ]
  ≈,[ε] : ∀ {I} → I ,[ ε ] ≈' I
  ≈,[ε]' : ∀ {I} → I ≈' I ,[ ε ]
  ≈,[swap] : ∀ {E F I} → I ,[ E ] ,[ F ] ≈' I ,[ F ] ,[ E ]

∼-forget : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → δE ∼' δF
∼-forget ∼-refl = ∼-refl
∼-forget (∼-trans eq eq₁) = ∼-trans (∼-forget eq) (∼-forget eq₁)
∼-forget (∼,↦ eq) = ∼,↦ (∼-forget eq)
∼-forget ∼,↦end = ∼,↦end
∼-forget ∼,↦end' = ∼,↦end'
∼-forget ∼,[swap] = ∼,[swap]

∼'-apply : ∀ {δE δF} → δE ∼' δF → Env δE → Env δF
∼'-apply ∼-refl env = env
∼'-apply (∼-trans eq eq₁) env = ∼'-apply eq₁ (∼'-apply eq env)
∼'-apply (∼,↦ eq) (env , c ↦ v) = (∼'-apply eq env) , c ↦ v
∼'-apply ∼,↦end (env , c ↦ v) = env
∼'-apply ∼,↦end' env = env , _ ↦ end
∼'-apply ∼,[swap] (env , c ↦ v , c₁ ↦ v₁) = env , c₁ ↦ v₁ , c ↦ v

∼-for-app : ∀ {δE δF}{E : Env δE}{F : Env δF}(eq : E ∼ F) → ∼'-apply (∼-forget eq) E ≡ F
∼-for-app ∼-refl = refl
∼-for-app (∼-trans eq eq₁)
  rewrite ∼-for-app eq
        | ∼-for-app eq₁
  = refl
∼-for-app (∼,↦ eq) rewrite ∼-for-app eq = refl
∼-for-app ∼,↦end = refl
∼-for-app ∼,↦end' = refl
∼-for-app ∼,[swap] = refl


≈-forget : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈ J → δI ≈' δJ
≈-forget ≈-refl = ≈-refl
≈-forget (≈-trans eq eq₁) = ≈-trans (≈-forget eq) (≈-forget eq₁)
≈-forget (≈,[] eq x) = ≈,[] (≈-forget eq) (∼-forget x)
≈-forget ≈,[ε] = ≈,[ε]
≈-forget ≈,[ε]' = ≈,[ε]'
≈-forget ≈,[swap] = ≈,[swap]

≈'-apply : ∀ {δI δJ} → δI ≈' δJ → Proto δI → Proto δJ
≈'-apply ≈-refl I = I
≈'-apply (≈-trans eq eq₁) I₁ = ≈'-apply eq₁ (≈'-apply eq I₁)
≈'-apply (≈,[] eq x) (I₁ ,[ Δ ]) = ≈'-apply eq I₁ ,[ ∼'-apply x Δ ]
≈'-apply ≈,[ε] (I ,[ Δ ]) = I
≈'-apply ≈,[ε]' I = I ,[ ε ]
≈'-apply ≈,[swap] (I₁ ,[ Δ ] ,[ Δ₁ ]) = I₁ ,[ Δ₁ ] ,[ Δ ]

≈-for-app : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}(eq : I ≈ J) → ≈'-apply (≈-forget eq) I ≡ J
≈-for-app ≈-refl = refl
≈-for-app (≈-trans eq eq₁)
  rewrite ≈-for-app eq
        | ≈-for-app eq₁
  = refl
≈-for-app (≈,[] eq x)
  rewrite ≈-for-app eq
        | ∼-for-app x
  = refl
≈-for-app ≈,[ε] = refl
≈-for-app ≈,[ε]' = refl
≈-for-app ≈,[swap] = refl

EEnded-conv : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → Env.Ended E → Env.Ended F
EEnded-conv ∼-refl EE = EE
EEnded-conv (∼-trans eq eq₁) EE = EEnded-conv eq₁ (EEnded-conv eq EE)
EEnded-conv (∼,↦ eq) EE = ⟨ EEnded-conv eq (fst EE) , snd EE ⟩
EEnded-conv ∼,↦end EE = fst EE
EEnded-conv ∼,↦end' EE = ⟨ EE , _ ⟩
EEnded-conv ∼,[swap] EE = ⟨ ⟨ (fst (fst EE)) , (snd EE) ⟩ , (snd (fst EE)) ⟩

Ended-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈ J → Ended I → Ended J
Ended-conv ≈-refl EI = EI
Ended-conv (≈-trans eq eq₁) EI = Ended-conv eq₁ (Ended-conv eq EI)
Ended-conv (≈,[] eq x) ⟨ proj₁ , proj₂ ⟩ = ⟨ Ended-conv eq proj₁ , EEnded-conv x proj₂ ⟩
Ended-conv ≈,[ε] EI = fst EI
Ended-conv ≈,[ε]' EI = ⟨ EI , _ ⟩
Ended-conv ≈,[swap] EI = ⟨ ⟨ (fst (fst EI)) , (snd EI) ⟩ , (snd (fst EI)) ⟩

mutual
  ∈D-conv : ∀ {c δE δF A}{E : Env δE}{F : Env δF} → E ∼ F → (l : c ∈D δE) → E ‼ l ≡ « A »
    → c ∈D δF
  ∈D-conv ∼-refl l _ = l
  ∈D-conv (∼-trans eq eq₁) l El = ∈D-conv eq₁ (∈D-conv eq l El) (∈D-conv‼ eq l El ∙ El) -- ∈D-conv eq₁ (∈D-conv eq l)
  ∈D-conv (∼,↦ eq) here _ = here
  ∈D-conv (∼,↦ eq) (there l) El = there (∈D-conv eq l El)
  ∈D-conv ∼,↦end here ()
  ∈D-conv ∼,↦end (there l) El = l
  ∈D-conv ∼,↦end' l El = there l
  ∈D-conv ∼,[swap] here El = there here
  ∈D-conv ∼,[swap] (there here) El = here
  ∈D-conv ∼,[swap] (there (there l)) El = there (there l)

  ∈D-conv‼ :  ∀ {c δE δF A}{E : Env δE}{F : Env δF}(eq : E ∼ F)(l : c ∈D δE)(El : E ‼ l ≡ « A »)
   → F ‼ ∈D-conv eq l El ≡ E ‼ l
  ∈D-conv‼ ∼-refl l El = refl
  ∈D-conv‼ (∼-trans eq eq₁) l El = ∈D-conv‼ eq₁ (∈D-conv eq l El) (∈D-conv‼ eq l El ∙ El)
    ∙ ∈D-conv‼ eq l El
  ∈D-conv‼ (∼,↦ eq) here El = refl
  ∈D-conv‼ (∼,↦ eq) (there l) El = ∈D-conv‼ eq l El
  ∈D-conv‼ ∼,↦end here ()
  ∈D-conv‼ ∼,↦end (there l) El = refl
  ∈D-conv‼ ∼,↦end' l El = refl
  ∈D-conv‼ ∼,[swap] here El = refl
  ∈D-conv‼ ∼,[swap] (there here) El = refl
  ∈D-conv‼ ∼,[swap] (there (there l)) El = refl

∈D≔-conv :  ∀ {c δE δF A}{E : Env δE}{F : Env δF}(eq : E ∼ F)(lA : c ∈D δE)(↦A : E ‼ lA ≡ « A »)
    → E [ lA ]≔' end ∼ F [ ∈D-conv eq lA ↦A ]≔' end
∈D≔-conv ∼-refl lA ↦A = ∼-refl
∈D≔-conv (∼-trans eq eq₁) lA ↦A = ∼-trans (∈D≔-conv eq lA ↦A)
                                    (∈D≔-conv eq₁ (∈D-conv eq lA ↦A) (∈D-conv‼ eq lA ↦A ∙ ↦A))
∈D≔-conv (∼,↦ eq) here ↦A = ∼,↦ eq
∈D≔-conv (∼,↦ eq) (there lA) ↦A = ∼,↦ (∈D≔-conv eq lA ↦A)
∈D≔-conv ∼,↦end here ()
∈D≔-conv ∼,↦end (there lA) ↦A = ∼,↦end
∈D≔-conv ∼,↦end' lA ↦A = ∼,↦end'
∈D≔-conv ∼,[swap] here ↦A = ∼,[swap]
∈D≔-conv ∼,[swap] (there here) ↦A = ∼,[swap]
∈D≔-conv ∼,[swap] (there (there lA)) ↦A = ∼,[swap]

[↦]∈-conv : ∀ {c A}{δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈ J → [ c ↦ A ]∈ I → [ c ↦ A ]∈ J
[↦]∈-conv ≈-refl l = l
[↦]∈-conv (≈-trans eq eq₁) l = [↦]∈-conv eq₁ ([↦]∈-conv eq l)
[↦]∈-conv (≈,[] eq x) (mk5 here refl lA ↦A E/c) = mk5 here refl (∈D-conv x lA ↦A)
      (∈D-conv‼ x lA ↦A ∙ ↦A) (EEnded-conv (∈D≔-conv x lA ↦A) E/c)
[↦]∈-conv (≈,[] eq x) (mk5 (there lΔ) ↦Δ lA ↦A E/c) = there[]' ([↦]∈-conv eq (mk5 lΔ ↦Δ lA ↦A E/c))
[↦]∈-conv ≈,[ε] (mk (mk ⟨ here , refl ⟩ ⟨ () , ↦A ⟩) E/c)
[↦]∈-conv ≈,[ε] (mk (mk ⟨ there lΔ , ↦Δ ⟩ ⟨ lA , ↦A ⟩) E/c) = mk5 lΔ ↦Δ lA ↦A E/c
[↦]∈-conv ≈,[ε]' l = there[]' l
[↦]∈-conv ≈,[swap] (mk5 here ↦Δ lA ↦A E/c) = mk5 (there here) ↦Δ lA ↦A E/c
[↦]∈-conv ≈,[swap] (mk5 (there here) ↦Δ lA ↦A E/c) = mk5 here ↦Δ lA ↦A E/c
[↦]∈-conv ≈,[swap] (mk5 (there (there lΔ)) ↦Δ lA ↦A E/c) = mk5 (there (there lΔ)) ↦Δ lA ↦A E/c

Selection-conv' : ∀ {δE δF} → δE ∼' δF → Selection δE → Selection δF
Selection-conv' ∼-refl Δ = Δ
Selection-conv' (∼-trans eq eq₁) Δ = Selection-conv' eq₁ (Selection-conv' eq Δ)
Selection-conv' (∼,↦ eq) (Δ , c ↦ v) = Selection-conv' eq Δ , c ↦ v
Selection-conv' ∼,↦end (Δ , c ↦ v) = Δ
Selection-conv' ∼,↦end' Δ = Δ , _ ↦ 1₂ --somewhat arbitrary
Selection-conv' ∼,[swap] (Δ , c ↦ v , c₁ ↦ v₁) = Δ , c₁ ↦ v₁ , c ↦ v

Selection-conv : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → Selection δE → Selection δF
Selection-conv eq Δ = Selection-conv' (∼-forget eq) Δ

Selection/[]-conv : ∀ {δE δF}{E : Env δE}{F : Env δF}(eq : E ∼ F)(σ : Selection δE)(b : 𝟚)
   → E Env./[ b ] σ ∼ F Env./[ b ] Selection-conv eq σ
Selection/[]-conv ∼-refl σs b = ∼-refl
Selection/[]-conv (∼-trans eq eq₁) σs b = ∼-trans (Selection/[]-conv eq σs b)
                                            (Selection/[]-conv eq₁ (Selection-conv eq σs) b)
Selection/[]-conv {E = E , ._ ↦ S}{F , ._ ↦ .S} (∼,↦ eq) (σs , c ↦ v) b
  rewrite /[]-def (E , c ↦ S) b (σs , c ↦ v)
        | /[]-def (F , c ↦ S) b (Selection-conv eq σs , c ↦ v)
  = ∼,↦ (∼-reflexive (! /[]-def E b σs) ∼-∙ Selection/[]-conv eq σs b ∼-∙ ∼-reflexive (/[]-def F b (Selection-conv eq σs)))
Selection/[]-conv {E = E , .c ↦ end} ∼,↦end (σs , c ↦ v) b
  rewrite /[]-def (E , c ↦ end) b (σs , c ↦ v)
        | /[]-def E b σs
        | selectProjEnd b v
  = ∼,↦end
Selection/[]-conv {E = E}{.E , c ↦ end} ∼,↦end' σs b
  rewrite /[]-def E b σs
        | /[]-def (E , c ↦ end) b (σs , c ↦ 1₂)
        | selectProjEnd b 1₂
  = ∼,↦end'
Selection/[]-conv {E = E , c ↦ A , c₁ ↦ B} ∼,[swap] (σs , .c ↦ v , .c₁ ↦ v₁) b
  rewrite /[]-def (E , c ↦ A , c₁ ↦ B) b (σs , c ↦ v , c₁ ↦ v₁)
        | /[]-def (E , c₁ ↦ B , c ↦ A) b (σs , c₁ ↦ v₁ , c ↦ v)
  = ∼,[swap]

Selections-conv' : ∀ {δI δJ} → δI ≈' δJ → Selections δI → Selections δJ
Selections-conv' ≈-refl σs = σs
Selections-conv' (≈-trans eq eq₁) σs = Selections-conv' eq₁ (Selections-conv' eq σs)
Selections-conv' (≈,[] eq x) (σs ,[ Δ ]) = Selections-conv' eq σs ,[ Selection-conv' x Δ ]
Selections-conv' ≈,[ε] (σs ,[ Δ ]) = σs
Selections-conv' ≈,[ε]' σs = σs ,[ ε ]
Selections-conv' ≈,[swap] (σs ,[ Δ ] ,[ Δ₁ ]) = σs ,[ Δ₁ ] ,[ Δ ]

Selections-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈ J → Selections δI → Selections δJ
Selections-conv eq = Selections-conv' (≈-forget eq)


EnvSelectionAll-conv : ∀ {δE δF} {E : Env δE} {F : Env δF} b
                         (eq : E ∼ F) (Δ : Map 𝟚 δE) →
                       EnvSelectionAll≡ b E Δ →
                       EnvSelectionAll≡ b F (Selection-conv' (∼-forget eq) Δ)
EnvSelectionAll-conv b ∼-refl Δ all = all
EnvSelectionAll-conv b (∼-trans eq eq₁) Δ all = EnvSelectionAll-conv b eq₁ (Selection-conv eq Δ)
                                                  (EnvSelectionAll-conv b eq Δ all)
EnvSelectionAll-conv b (∼,↦ {S = « S »} eq) (Δ , c ↦ v) all = ⟨ (EnvSelectionAll-conv b eq Δ (fst all)) , (snd all) ⟩
EnvSelectionAll-conv b (∼,↦ {S = end} eq) (Δ , c ↦ v) all = EnvSelectionAll-conv b eq Δ all
EnvSelectionAll-conv b ∼,↦end (Δ , c ↦ v) all = all
EnvSelectionAll-conv b ∼,↦end' Δ all = all
EnvSelectionAll-conv b (∼,[swap] {A = « S »} {« S₁ »}) (Δ , c ↦ v , c₁ ↦ v₁) all = ⟨ ⟨ (fst (fst all)) , (snd all) ⟩ , (snd (fst all)) ⟩
EnvSelectionAll-conv b (∼,[swap] {A = end} {« S »}) (Δ , c ↦ v , c₁ ↦ v₁) all = all
EnvSelectionAll-conv b (∼,[swap] {A = « S »} {end}) (Δ , c ↦ v , c₁ ↦ v₁) all = all
EnvSelectionAll-conv b (∼,[swap] {A = end} {end}) (Δ , c ↦ v , c₁ ↦ v₁) all = all

SelAtMost-conv : ∀ {n m δE δF}{E : Env δE}{F : Env δF}(eq : E ∼ F)(Δ : Selection δE)
  → SelAtMost n E Δ m → SelAtMost n F (Selection-conv eq Δ) m
SelAtMost-conv eq Δ (₀₁ b x) = ₀₁ b (EnvSelectionAll-conv b eq Δ x) -- let ⟨ b' , x' ⟩ = SelectionAll≡-conv eq Δ b x in ₀₁ b' x'
SelAtMost-conv eq Δ ₘ = ₘ

AtMost-conv : ∀ {δI δJ n}{I : Proto δI}{J : Proto δJ}(eq : I ≈ J)(σs : Selections δI)
  → AtMost n I σs → AtMost n J (Selections-conv eq σs)
AtMost-conv ≈-refl σs An = An
AtMost-conv (≈-trans eq eq₁) σs An = AtMost-conv eq₁ (Selections-conv eq σs) (AtMost-conv eq σs An)
AtMost-conv (≈,[] eq x) (σs ,[ Δ ]) (An ,[ x₁ ]) = (AtMost-conv eq σs An) ,[ SelAtMost-conv x Δ x₁ ] -- {!AtMost-conv eq σs!} ,[ {!!} ]
AtMost-conv ≈,[ε] (σs ,[ Δ ]) (An ,[ ₀₁ b x ]) = An
AtMost-conv ≈,[ε] (σs ,[ Δ ]) (An ,[ ₘ ]) = AtMost-wk An
AtMost-conv ≈,[ε]' σs An = An ,[ (₀₁ 0₂ 0₁) ]
AtMost-conv ≈,[swap] (σs ,[ Δ ] ,[ Δ₁ ]) (An ,[ ₀₁ b x ] ,[ ₀₁ b₁ x₁ ]) = An ,[ ₀₁ b₁ x₁ ] ,[ ₀₁ b x ]
AtMost-conv ≈,[swap] (σs ,[ Δ ] ,[ Δ₁ ]) (An ,[ ₀₁ b x ] ,[ ₘ ]) = An ,[ ₘ ] ,[ ₀₁ b x ]
AtMost-conv ≈,[swap] (σs ,[ Δ ] ,[ Δ₁ ]) (An ,[ ₘ ] ,[ ₀₁ b x ]) = An ,[ ₀₁ b x ] ,[ ₘ ]
AtMost-conv ≈,[swap] (σs ,[ Δ ] ,[ Δ₁ ]) (An ,[ ₘ ] ,[ ₘ ]) = An ,[ ₘ ] ,[ ₘ ]

≈-[/] : ∀ {δI δJ c A}{I : Proto δI}{J : Proto δJ}(eq : I ≈ J)(l : [ c ↦ A ]∈ I)
  → I / l ≈ J / [↦]∈-conv eq l
≈-[/] ≈-refl l = ≈-refl
≈-[/] (≈-trans eq eq₁) l = ≈-trans (≈-[/] eq l) (≈-[/] eq₁ ([↦]∈-conv eq l))
≈-[/] (≈,[] eq x) (mk5 here refl lA ↦A E/c) = ≈,[] eq (∈D≔-conv x lA ↦A)
≈-[/] (≈,[] eq x) (mk5 (there lΔ) ↦Δ lA ↦A E/c) = ≈,[] (≈-[/] eq (mk5 lΔ ↦Δ lA ↦A E/c)) x
≈-[/] ≈,[ε] (mk5 here refl () ↦A E/c)
≈-[/] ≈,[ε] (mk5 (there lΔ) ↦Δ lA ↦A E/c) = ≈,[ε]
≈-[/] ≈,[ε]' l = ≈,[ε]'
≈-[/] ≈,[swap] (mk5 here ↦Δ lA ↦A E/c) = ≈,[swap]
≈-[/] ≈,[swap] (mk5 (there here) ↦Δ lA ↦A E/c) = ≈,[swap]
≈-[/] ≈,[swap] (mk5 (there (there lΔ)) ↦Δ lA ↦A E/c) = ≈,[swap]

≈-[]/[] : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}(b : 𝟚)(eq : I ≈ J)(σs : Selections δI)
    → I []/[ b ] σs ≈ J []/[ b ] Selections-conv eq σs
≈-[]/[] b ≈-refl σs = ≈-refl
≈-[]/[] b (≈-trans eq eq₁) σs = ≈-trans (≈-[]/[] b eq σs) (≈-[]/[] b eq₁ (Selections-conv eq σs))
≈-[]/[] {I = I ,[ E ]}{J ,[ F ]} b (≈,[] eq x) (σs ,[ Δ ])
  rewrite []/[]-def (I ,[ E ]) b (σs ,[ Δ ])
        | []/[]-def (J ,[ F ]) b (Selections-conv eq σs ,[ Selection-conv x Δ ])
  = ≈,[] (≈-reflexive (! []/[]-def I b σs) ≈-∙ ≈-[]/[] b eq σs ≈-∙ ≈-reflexive ([]/[]-def J b (Selections-conv eq σs)))
         (Selection/[]-conv x Δ b)
≈-[]/[] {J = I} 0₂ ≈,[ε] (σs ,[ ε ])
  rewrite []/[]-def I 0₂ σs
        | []/[]-def (I ,[ ε ]) 0₂ (σs ,[ ε ])
        | /[]-def ε 0₂ ε
  = ≈,[ε]
≈-[]/[] {J = I} 1₂ ≈,[ε] (σs ,[ ε ])
  rewrite []/[]-def I 1₂ σs
        | []/[]-def (I ,[ ε ]) 1₂ (σs ,[ ε ])
        | /[]-def ε 1₂ ε
  = ≈,[ε]
≈-[]/[] {I = I} 0₂ ≈,[ε]' σs
  rewrite []/[]-def I 0₂ σs
        | []/[]-def (I ,[ ε ]) 0₂ (σs ,[ ε ])
        | /[]-def ε 0₂ ε
  = ≈,[ε]'
≈-[]/[] {I = I} 1₂ ≈,[ε]' σs
  rewrite []/[]-def I 1₂ σs
        | []/[]-def (I ,[ ε ]) 1₂ (σs ,[ ε ])
        | /[]-def ε 1₂ ε
  = ≈,[ε]'
≈-[]/[] {I = I ,[ E ] ,[ F ]} b ≈,[swap] (σs ,[ Δ ] ,[ Δ₁ ])
  rewrite []/[]-def (I ,[ E ] ,[ F ]) b (σs ,[ Δ ] ,[ Δ₁ ])
        | []/[]-def (I ,[ F ] ,[ E ]) b (σs ,[ Δ₁ ] ,[ Δ ])
  = ≈,[swap]

TC-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}
    → I ≈ J → TC'⟨ I ⟩ → TC'⟨ J ⟩
TC-conv eq (TC-⊗-out l σs A0 P₀ P₁) = TC-⊗-out ([↦]∈-conv eq l) (Selections-conv (≈-[/] eq l) σs)
  (AtMost-conv (≈-[/] eq l) σs A0) (λ c₀ → TC-conv (≈,[] (≈-[]/[] 0₂ (≈-[/] eq l) σs) ∼-refl) (P₀ c₀))
                                   (λ c₁ → TC-conv (≈,[] (≈-[]/[] 1₂ (≈-[/] eq l) σs) ∼-refl) (P₁ c₁))
TC-conv eq (TC-⅋-inp l P) = TC-⅋-inp ([↦]∈-conv eq l) λ c₀ c₁ →
  TC-conv (≈,[] (≈,[] (≈-[/] eq l) ∼-refl) ∼-refl) (P c₀ c₁)
TC-conv eq (TC-?-inp l P) = TC-?-inp ([↦]∈-conv eq l) λ m →
  TC-conv (≈,[] (≈-[/] eq l) ∼-refl) (P m)
TC-conv eq (TC-!-out l m P) = TC-!-out ([↦]∈-conv eq l) m (TC-conv (≈,[] (≈-[/] eq l) ∼-refl) P)
TC-conv eq (TC-end E) = TC-end (Ended-conv eq E)
TC-conv eq (TC-split σs A1 P P₁) = TC-split (Selections-conv eq σs) (AtMost-conv eq σs A1)
  (TC-conv (≈-[]/[] 0₂ eq σs) P) (TC-conv (≈-[]/[] 1₂ eq σs) P₁)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
