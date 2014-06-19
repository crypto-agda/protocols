module runningtest where

-- open import Level.NP

-- open import Function.NP
id : ∀ {a} {A : Set a} (x : A) → A
id x = x

infixr 9 _∘_
_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

infixr 0 _$_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

-- open import Data.One
record 𝟙 : Set₀ where

data Bool : Set where
  true false : Bool

-- open import Data.Product.NP
record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

-- open import Data.Sum.NP
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

[inl:_,inr:_] : ∀ {c} {A B : Set} {C : A ⊎ B → Set c} →
        ((x : A) → C (inl x)) → ((x : B) → C (inr x)) →
        ((x : A ⊎ B) → C x)
[inl: f ,inr: g ] (inl x) = f x
[inl: f ,inr: g ] (inr y) = g y

-- open import Data.List using (List; []; _∷_)
infixr 5 _∷_

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

-- open import Relation.Binary.PropositionalEquality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

ap : {A B : Set} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
ap f refl = refl

infixr 5 _++_

postulate
    Char        : Set
    String      : Set
    Number      : Set
    zero        : Number
    one         : Number
    _+_         : Number  → Number  → Number
    _++_        : String → String → String
    reverse     : String → String
    sort        : String → String
    take-half   : String → String
    drop-half   : String → String
    String▹List : String → List Char
    List▹String : List Char → String
    _≤Char_     : Char → Char → Bool

    JSValue : Set
    _+JS_       : JSValue → JSValue → JSValue
    JSON-stringify : JSValue → String
    fromString : String → JSValue
    fromNumber : Number → JSValue
    -- fromBool   : Bool → JSValue
    nullJS     : JSValue
    -- JSON-parse :
    onString : (String → String) → JSValue → JSValue
    onString2 : (String → String → String) → JSValue → JSValue → JSValue

{-# BUILTIN STRING String #-}
{-# BUILTIN CHAR   Char #-}

{-# COMPILED_JS zero      0 #-}
{-# COMPILED_JS one       1 #-}
{-# COMPILED_JS _+_       function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS _++_      function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS _+JS_     function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS reverse   function(x) { return x.split("").reverse().join(""); } #-}
{-# COMPILED_JS sort      function(x) { return x.split("").sort().join(""); }    #-}
{-# COMPILED_JS take-half function(x) { return x.substring(0,x.length/2); }      #-}
{-# COMPILED_JS drop-half function(x) { return x.substring(x.length/2); }        #-}
{-# COMPILED_JS _≤Char_   function(x) { return function(y) { return exports["fromJSBool"](x <= y); }; } #-}
{-# COMPILED_JS JSON-stringify function(x) { return JSON.stringify(x); } #-}
{-# COMPILED_JS fromString function(x) { return x; } #-}
{-# COMPILED_JS fromNumber function(x) { return x; } #-}
{-# COMPILED_JS nullJS     null #-}

data Value : Set₀ where
  array  : List Value → Value
  object : List (String × Value) → Value
  string : String → Value
  number : Number  → Value
  bool   : Bool → Value
  null   : Value

postulate
    fromValue : Value → JSValue

test-value = object (("array"  , array (array [] ∷ array (array [] ∷ []) ∷ [])) ∷
                     ("object" , array (object [] ∷ object (("a", string "b") ∷ []) ∷ [])) ∷
                     ("string" , array (string "" ∷ string "a" ∷ [])) ∷
                     ("number" , array (number zero ∷ number one ∷ [])) ∷
                     ("bool"   , array (bool true ∷ bool false ∷ [])) ∷
                     ("null"   , array (null ∷ [])) ∷ [])


module _ {A : Set} (_≤_ : A → A → Bool) where

    merge-sort-list : (l₀ l₁ : List A) → List A
    merge-sort-list [] l₁ = l₁
    merge-sort-list l₀ [] = l₀
    merge-sort-list (x₀ ∷ l₀) (x₁ ∷ l₁) with x₀ ≤ x₁
    ... | true  = x₀ ∷ merge-sort-list l₀ (x₁ ∷ l₁)
    ... | false = x₁ ∷ merge-sort-list (x₀ ∷ l₀) l₁

merge-sort : String → String → String
merge-sort s₀ s₁ = List▹String (merge-sort-list _≤Char_ (String▹List s₀) (String▹List s₁))

data Error (A : Set) : Set where
  succeed : A → Error A
  fail    : (err : String) → Error A

[succeed:_,fail:_] : ∀ {c} {A : Set} {C : Error A → Set c} →
        ((x : A) → C (succeed x)) → ((x : String) → C (fail x)) →
        ((x : Error A) → C x)
[succeed: f ,fail: g ] (succeed x) = f x
[succeed: f ,fail: g ] (fail y) = g y

mapE : {A B : Set} → (A → B) → Error A → Error B
mapE f (fail err) = fail err
mapE f (succeed x) = succeed (f x)

data All {A : Set} (P : A → Set) : Error A → Set where
  fail    : ∀ s → All P (fail s)
  succeed : ∀ {x} → P x → All P (succeed x)

record _≃?_ (A B : Set) : Set where
  field
    serialize : A → B
    parse     : B → Error A
    linv      : ∀ x → All (_≡_ x ∘ serialize) (parse x)
    rinv      : ∀ x → parse (serialize x) ≡ succeed x
open _≃?_ {{...}}

data Proto : Set₁ where
  end : Proto
  send recv : {M : Set} {{M≃S : M ≃? String}} (P : M → Proto) → Proto

dual : Proto → Proto
dual end      = end
dual (send P) = recv λ m → dual (P m)
dual (recv P) = send λ m → dual (P m)

log : Proto → Proto
log end      = end
log (send P) = send λ m → log (P m)
log (recv P) = send λ m → log (P m)

⟦_⟧ : Proto → Set
⟦ end ⟧ = 𝟙
⟦ send P ⟧ = Σ _ λ m → ⟦ P m ⟧
⟦ recv P ⟧ = (m : _) → ⟦ P m ⟧

⟦_⟧D : Proto → Set → Set
⟦ end ⟧D D = 𝟙
⟦ send P ⟧D D = D × Σ _ λ m → ⟦ P m ⟧D D
⟦ recv P ⟧D D = D × ((m : _) → ⟦ P m ⟧D D)

[true:_,false:_] : ∀ {c} {C : Bool → Set c} →
        C true → C false →
        ((x : Bool) → C x)
[true: f ,false: g ] true  = f
[true: f ,false: g ] false = g

postulate
    viewString : String → Error (Char × String)

    {-
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

_⅋_ : Proto → Proto → Proto
end    ⅋ Q      = Q
recv P ⅋ Q      = recv λ m → P m ⅋ Q
P      ⅋ end    = P
P      ⅋ recv Q = recv λ m → P ⅋ Q m
send P ⅋ send Q = send {{{!!}}} [inl: (λ m → P m ⅋ send Q)
                                ,inr: (λ n → send P ⅋ Q n) ]
-}

                             {-
_⊗_ : Proto → Proto → Proto
end    ⊗ Q      = Q
send P ⊗ Q      = send λ m → P m ⊗ Q
P      ⊗ end    = P
P      ⊗ send Q = send λ m → P ⊗ Q m
recv P ⊗ recv Q = recv [inl: (λ m → P m ⊗ recv Q)
                       ,inr: (λ n → recv P ⊗ Q n) ]
-}

telecom : (P : Proto) (p : ⟦ P ⟧) (q : ⟦ dual P ⟧) → ⟦ log P ⟧
telecom end p q = _
telecom (send P) (m , p) q = m , telecom (P m) p (q m)
telecom (recv P) p (m , q) = m , telecom (P m) (p m) q

{-
open import Category.Profunctor

Prism : (S T A B : Set) → Set₁
Prism S T A B = ∀ {_↝_}{{_ : Choice {₀} _↝_}} → (A ↝ B) → (S ↝ T)

Prism' : (S A : Set) → Set₁
Prism' S A = Prism S S A A

module _ {S T A B : Set} where
    prism : (B → T) → (S → T ⊎ A) → Prism S T A B
    prism bt sta = dimap sta [inl: id ,inr: bt ] ∘ right
      where open Choice {{...}}
-}

Prism : (S T A B : Set) → Set
Prism S T A B = (B → T) × (S → T ⊎ A)

Prism' : (S A : Set) → Set
Prism' S A = Prism S S A A

module _ {S T A B : Set} where
    prism : (B → T) → (S → T ⊎ A) → Prism S T A B
    prism = _,_

    -- This is particular case of lens' _#_
    _#_ : Prism S T A B → B → T
    _#_ = fst

    -- This is particular case of lens' review
    review = _#_

    -- _^._ : Prism S T A B → S → ...

module _ {S A : Set} where
    prism' : (A → S) → (S → S ⊎ A) → Prism' S A
    prism' = prism

data Proc (D : Set₀) (M : Set₀) : Set₀ where
  end    : Proc D M
  output : (d : D) (m : M) (p : Proc D M) → Proc D M
  input  : (d : D) (p : M → Proc D M) → Proc D M
  start  : (p : Proc 𝟙 M) (q : D → Proc D M) → Proc D M
  error  : (err : String) → Proc D M

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
    toProc : (P : Proto) → ⟦ P ⟧ → Proc D String
    toProc end      _       = end
    toProc (send P) (m , p) = output d (serialize m) (toProc (P m) p)
    toProc (recv P) p       = input d λ s → f (parse s)
      where f : Error _ → Proc D String
            f (succeed m) = toProc (P m) (p m)
            f (fail err)  = error err

toProcLog : (P : Proto) → ⟦ log P ⟧ → List String
toProcLog end      _       = []
toProcLog (send P) (m , p) = serialize m ∷ toProcLog (P m) p
toProcLog (recv P) (m , p) = serialize m ∷ toProcLog (P m) p

telecomProc : ∀ {M} → Proc 𝟙 M → Proc 𝟙 M → List M
-- telecomProc (start p q) r = {!!}
telecomProc end end = []
telecomProc (output _ m p) (input _ q) = m ∷ telecomProc p (q m)
telecomProc (input _ p) (output _ m q) = m ∷ telecomProc (p m) q
telecomProc _ _ = []

{-
foo : (P : Proto) (p : ⟦ P ⟧) (q : ⟦ dual P ⟧) → toProcLog P (telecom P p q) ≡ telecomProc (toProc _ p) (toProc _ q)
foo end p q = refl
foo (send {{M≃S = M≃S}} P) (m , p) q = ap (_∷_ (serialize m)) {!foo (P m) p (q m)!}
foo (recv {{M≃S = M≃S}} P) p (m , q) = ap (_∷_ (serialize m)) {!foo (P m) (p m) q!}
-}

ToProc : (D : Set) (P : Proto) → Set
ToProc D P = ⟦ P ⟧ → Proc D String

{-
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

reverser : Proc 𝟙 JSValue
reverser = input _ λ s → output _ (onString reverse s) end

adder : Proc 𝟙 JSValue
adder = input _ λ s₀ → input _ λ s₁ → output _ (s₀ +JS s₁) end

adder-client : ∀ {D} → D → JSValue → JSValue → Proc D JSValue
adder-client d s₀ s₁ = output d s₀ (output d s₁ (input d λ _ → end))

adder-reverser-client : ∀ {D} → D → D → JSValue → Proc D JSValue
adder-reverser-client adder-addr reverser-addr s =
  output reverser-addr s $
  output adder-addr s $
  input reverser-addr λ rs →
  output adder-addr rs $
  input adder-addr λ res →
  end

str-sorter₀ : ∀ {D} → D → Proc D JSValue
str-sorter₀ d = input d λ s → output d (onString sort s) end

str-sorter-client : ∀ {D} → D → JSValue → Proc D JSValue
str-sorter-client d s = output d s $ input d λ _ → end

str-merger : ∀ {D} (upstream helper₀ helper₁ : D) → Proc D JSValue
str-merger upstream helper₀ helper₁ =
  input upstream λ s →
  output helper₀ (onString take-half s) $
  output helper₁ (onString drop-half s) $
  input helper₀ λ ss₀ →
  input helper₁ λ ss₁ →
  output upstream (onString2 merge-sort ss₀ ss₁)
  end

dyn-merger : ∀ {D} → D → Proc 𝟙 JSValue → Proc D JSValue
dyn-merger upstream helper =
  start helper λ helper₀ →
  start helper λ helper₁ →
  str-merger upstream helper₀ helper₁

str-sorter₁ : ∀ {D} → D → Proc D JSValue
str-sorter₁ upstream = dyn-merger upstream (str-sorter₀ _)

str-sorter₂ : ∀ {D} → D → Proc D JSValue
str-sorter₂ upstream = dyn-merger upstream (str-sorter₁ _)

stringifier : Proc 𝟙 JSValue
stringifier = input _ λ v → output _ (fromString (JSON-stringify v)) end

stringifier-client : ∀ {D} → D → JSValue → Proc D JSValue
stringifier-client d v = output d v $ input d λ _ → end

postulate
  HTTPServer : Set

data JSCmd : Set where
  server : (ip port : String)(proc : Proc 𝟙 JSValue)
           (callback : HTTPServer → (uri : String) → JSCmd) → JSCmd
  client : Proc String JSValue → JSCmd → JSCmd
  end : JSCmd
  console-log : String → JSCmd → JSCmd

main : 𝟙 → JSCmd
main _ =
  console-log (JSON-stringify (fromValue test-value)) $

  console-log "server(adder):" $
  server "127.0.0.1" "1337" adder λ _ adder-uri →
  console-log "client(adderclient):" $
  client (adder-client adder-uri (fromString "Hello ") (fromString "World!")) $
  client (adder-client adder-uri (fromString "Bonjour ") (fromString "monde!")) $
  console-log "server(reverser):" $
  server "127.0.0.1" "1338" reverser λ _ reverser-uri →
  console-log "client(adder-reverser-client):" $
  client (adder-reverser-client adder-uri reverser-uri (fromString "red")) $

  server "127.0.0.1" "1342" (str-sorter₂ _) λ http_server str-sorter₂-uri →
  console-log "str-sorter-client:" $
  client (str-sorter-client str-sorter₂-uri (fromString "Something to be sorted!")) $

  server "127.0.0.1" "1343" stringifier λ _ stringifier-uri →
  client (stringifier-client stringifier-uri (fromValue test-value)) $
  end
-- -}
-- -}
-- -}
-- -}
