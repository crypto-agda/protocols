module _ where

open import prelude
open import libjs
open import proto

data Proc (D : Set₀) (M : Set₀) : Set₀ where
  end    : Proc D M
  output : (d : D) (m : M) (p : Proc D M) → Proc D M
  input  : (d : D) (p : M → Proc D M) → Proc D M
  start  : (p : Proc D M) (q : D → Proc D M) → Proc D M
  error  : (err : String) → Proc D M

abstract
  URI = String
  showURI : URI → String
  showURI = id
  readURI : String → URI
  readURI = id
  clientURI : URI
  clientURI = ""

JSProc = Proc URI JSValue

module _ {A B : Set} (f : Prism' A B) where
  mapProc : ∀ {D} → Proc D B → Proc D A
  mapProc end = end
  mapProc (output d m p) = output d (f # m) (mapProc p)
  mapProc (input d p) = input d ([inl: (λ _ → error "mapProc/input")
                                 ,inr: (λ b → mapProc (p b)) ]
                                 ∘ snd f)
  mapProc (start p q) = start (mapProc p) (λ d → mapProc (q d))
  mapProc (error err) = error err

module _ {D : Set} d where
    toProc : (P : Proto) → ⟦ P ⟧ → Proc D JSValue
    toProc end      _       = end
    toProc (send P) (m , p) = output d (serialize m) (toProc (P m) p)
    toProc (recv P) p       = input d λ s → [succeed: (λ m → toProc (P m) (p m)) ,fail: error ] (parse s)

toProcLog : (P : Proto) → ⟦ log P ⟧ → List JSValue
toProcLog end      _       = []
toProcLog (send P) (m , p) = serialize m ∷ toProcLog (P m) p
toProcLog (recv P) (m , p) = serialize m ∷ toProcLog (P m) p

telecomProc : ∀ {D M} → Proc D M → Proc D M → List M
-- telecomProc (start p q) r = {!!}
telecomProc end end = []
telecomProc (output _ m p) (input _ q) = m ∷ telecomProc p (q m)
telecomProc (input _ p) (output _ m q) = m ∷ telecomProc (p m) q
telecomProc _ _ = []

    {-
postulate
    viewString : String → Error (Char × String)

foo : {A B : Set} → A ≃? String → B ≃? String → (A ⊎ B) ≃? String
foo AS BS = record { serialize = [inl: _++_ "L" ∘ serialize ,inr: _++_ "R" ∘ serialize ]
                   ; parse = λ s → f (viewString s)
                   ; linv = {!!}
                   ; rinv = [inl: (λ x → {!rinv x!}) ,inr: {!!} ] }
                   where f : Error (Char × String) → _
                         f (fail x) = fail "too short"
                         f (succeed ('L' , s)) = mapE inl (parse s)
                         f (succeed ('R' , s)) = mapE inr (parse s)
                         f (succeed (c , _)) = fail (List▹String (c ∷ []) ++ " is neither L nor R")
-}

{-
foo : (P : Proto) (p : ⟦ P ⟧) (q : ⟦ dual P ⟧) → toProcLog P (telecom P p q) ≡ telecomProc (toProc _ p) (toProc _ q)
foo end p q = refl
foo (send {{M≃S = M≃S}} P) (m , p) q = ap (_∷_ (serialize m)) {!foo (P m) p (q m)!}
foo (recv {{M≃S = M≃S}} P) p (m , q) = ap (_∷_ (serialize m)) {!foo (P m) (p m) q!}
-}

{-
ToProc : (D : Set) (P : Proto) → Set
ToProc D P = ⟦ P ⟧ → Proc D String

module _ {D} (dP dQ : D) where
    toProc-⅋ : (P Q : Proto) → ⟦ P ⅋ Q ⟧ → Proc D String
    toProc-⅋ end      Q r = toProc dQ Q r
    toProc-⅋ (recv P) Q r
      = input dP λ s → [succeed: (λ m → toProc-⅋ (P m) Q (r m)) ,fail: error ] (parse s)
    toProc-⅋ (send P) end r = toProc dP (send P) r
    toProc-⅋ (send P) (recv Q) r
      = input dQ λ s → [succeed: (λ m → toProc-⅋ (send P) (Q m) (r m)) ,fail: error ] (parse s)
    toProc-⅋ (send P) (send Q) (inl x , r) = output dP (serialize x) (toProc-⅋ (P x) (send Q) r)
    toProc-⅋ (send P) (send Q) (inr x , r) = output dQ (serialize x) (toProc-⅋ (send P) (Q x) r)
-}

postulate
  HTTPServer : Set

data JSCmd : Set where
  server : (ip port : String)(proc : JSProc)
           (callback : HTTPServer → URI → JSCmd) → JSCmd
  client : JSProc → JSCmd → JSCmd

  end         : JSCmd
  console_log : String → JSCmd → JSCmd
