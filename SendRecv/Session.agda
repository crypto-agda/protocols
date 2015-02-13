module _ where

open import Data.One
open import Data.Product

{-
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
 instance -- Just comment out this line if you have an earlier version of Agda
  LR-Ser : LR ≃? JSValue
  -}

record DummyMessageType : Set where
  instance
    constructor mk
MessageType : Set → Set
MessageType _ = DummyMessageType

data Com : Set where IN OUT : Com

data Session : Set₁ where
  end : Session
  com : Com → {M : Set} {{MT : MessageType M}} (P : M → Session) → Session
  {-
  send : {M : Set} {{M≃S : M ≃? JSValue}} (P : M → Session) → Session
  recv : {M : Set} {{M≃S : M ≃? JSValue}} (P : M → Session) → Session
  -}

{-
com : Com → {M : Set} {{M≃S : M ≃? JSValue}} (P : M → Session) → Session
com IN  = recv
com OUT = send
-}

{-
dual : Session → Session
dual end = end
dual (send P) = recv λ m → dual (P m)
dual (recv P) = send λ m → dual (P m)
-}

pattern send P = com OUT P
pattern recv P = com IN P

[send:_recv:_end:_] :
  ∀ {ℓ}{X : Set ℓ}
  (s r : {M : Set}{{_ : MessageType M}}(P : M → Session) → X)
  (end : X) → Session → X
[send: s recv: r end: e ] end = e
[send: s recv: r end: e ] (com OUT {M} {{MT}} P) = s {M} {{MT}} P -- <- why instance arguments!!!
[send: s recv: r end: e ] (com IN  {M} {{MT}} P) = r {M} {{MT}} P

mapSession : (Com → Com) → Session → Session
mapSession f end = end
mapSession f (com c {{MT}} P) = com (f c) {{MT}} (λ m → mapSession f (P m))

dualC : Com → Com
dualC IN  = OUT
dualC OUT = IN

dual : Session → Session
dual = mapSession dualC

logC : Com → Com
logC _ = OUT

log : Session → Session
log = mapSession logC

⟦_⟧ : Session → Set → Set
⟦ end ⟧    X = X
⟦ send P ⟧ X = Σ _ λ m → ⟦ P m ⟧ X
⟦ recv P ⟧ X = (m : _) → ⟦ P m ⟧ X

telecom : {X Y : Set}(P : Session) (p : ⟦ P ⟧ X) (q : ⟦ dual P ⟧ Y) → ⟦ log P ⟧ (X × Y)
telecom end p q = p , q
telecom (send P) (m , p) q = m , telecom (P m) p (q m)
telecom (recv P) p (m , q) = m , telecom (P m) (p m) q
