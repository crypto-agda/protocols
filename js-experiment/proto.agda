module _ where

open import prelude
open import libjs
open import libjs.Properties

SERIAL = JSValue

SER : Set → Set
SER M = M ≃? SERIAL

module _ {A B} {{AS : A ≃? JSValue}}{{BS : B ≃? JSValue}}where

  serial : A ⊎ B → JSValue
  serial (inl a) = fromObject [ "inl" , serialize a ]
  serial (inr b) = fromObject [ "inr" , serialize b ]

  pars : JSValue → Error (A ⊎ B)
  pars s with fromJSValue s
  ... | object (("inl" , x) ∷ []) = mapE inl (parse x)
  ... | object (("inr" , x) ∷ []) = mapE inr (parse x)
  ... | _ = fail ""

  postulate
    linv' : (x : JSValue) → All (_≡_ x ∘ serial) (pars x)

  rinv' : (x : A ⊎ B) → pars (serial x) ≡ succeed x
  rinv' (inl a) rewrite tofromObject [ "inl" , serialize a ]
                      | rinv a = refl
  rinv' (inr b) rewrite tofromObject [ "inr" , serialize b ]
                      | rinv b = refl

  ⊎-≃? : (A ⊎ B) ≃? JSValue
  ⊎-≃? = record { serialize = serial ; parse = pars ; linv = linv' ; rinv = rinv' }


postulate
  LR-Ser : LR ≃? JSValue

data Com : Set where IN OUT : Com

data Proto : Set₁ where
  end : Proto
  com : Com → {M : Set} {{M≃S : M ≃? JSValue}} (P : M → Proto) → Proto
  {-
  send : {M : Set} {{M≃S : M ≃? JSValue}} (P : M → Proto) → Proto
  recv : {M : Set} {{M≃S : M ≃? JSValue}} (P : M → Proto) → Proto

com : Com → {M : Set} {{M≃S : M ≃? JSValue}} (P : M → Proto) → Proto
com IN  = recv
com OUT = send

dual : Proto → Proto
dual end = end
dual (send P) = recv λ m → dual (P m)
dual (recv P) = send λ m → dual (P m)
  -}

pattern send P = com OUT P
pattern recv P = com IN P

[send:_recv:_end:_] :
  ∀ {ℓ}{X : Set ℓ}
  (s r : {M : Set}{{_ : SER M}}(P : M → Proto) → X)
  (end : X) → Proto → X
[send: s recv: r end: e ] end = e
[send: s recv: r end: e ] (send P) = s P
[send: s recv: r end: e ] (recv P) = r P

mapProto : (Com → Com) → Proto → Proto
mapProto f end = end
mapProto f (com c P) = com (f c) (λ m → mapProto f (P m))

dualC : Com → Com
dualC IN = OUT
dualC OUT = IN

dual : Proto → Proto
dual = mapProto dualC

logC : Com → Com
logC _ = OUT

log : Proto → Proto
log = mapProto logC

⟦_⟧ : Proto → Set
⟦ end ⟧ = 𝟙
⟦ send P ⟧ = Σ _ λ m → ⟦ P m ⟧
⟦ recv P ⟧ = (m : _) → ⟦ P m ⟧

⟦_⟧D : Proto → Set → Set
⟦ end ⟧D D = 𝟙
⟦ send P ⟧D D = D × Σ _ λ m → ⟦ P m ⟧D D
⟦ recv P ⟧D D = D × ((m : _) → ⟦ P m ⟧D D)

_⅋_ : Proto → Proto → Proto
end    ⅋ Q      = Q
recv P ⅋ Q      = recv λ m → P m ⅋ Q
P      ⅋ end    = P
P      ⅋ recv Q = recv λ m → P ⅋ Q m
send P ⅋ send Q = com OUT {{⊎-≃?}}
   [inl: (λ m → P m ⅋ send Q)
   ,inr: (λ n → send P ⅋ Q n) ]

_⅋'_ : Proto → Proto → Proto
end ⅋' Q = Q
com x P ⅋' end = com x P
com x P ⅋' com y Q = send [L: com x (λ m → P m ⅋' com y Q)
                          ,R: com y (λ m → com x P ⅋' Q m) ]

                             {-
_⊗_ : Proto → Proto → Proto
end    ⊗ Q      = Q
send P ⊗ Q      = send λ m → P m ⊗ Q
P      ⊗ end    = P
P      ⊗ send Q = send λ m → P ⊗ Q m
recv P ⊗ recv Q = recv [inl: (λ m → P m ⊗ recv Q)
                       ,inr: (λ n → recv P ⊗ Q n) ]
-}

_⊗_ : Proto → Proto → Proto
end ⊗ Q = Q
com x P ⊗ end = com x P
com x P ⊗ com y Q = recv [L: com x (λ m → P m ⊗ com y Q)
                         ,R: com y (λ m → com x P ⊗ Q m) ]

telecom : (P : Proto) (p : ⟦ P ⟧) (q : ⟦ dual P ⟧) → ⟦ log P ⟧
telecom end p q = _
telecom (send P) (m , p) q = m , telecom (P m) p (q m)
telecom (recv P) p (m , q) = m , telecom (P m) (p m) q
