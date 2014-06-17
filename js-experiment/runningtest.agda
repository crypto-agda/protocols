module runningtest where

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

record 𝟙 : Set₀ where

data Bool : Set where
  true false : Bool

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

[inl:_,inr:_] : ∀ {c} {A B : Set} {C : A ⊎ B → Set c} →
        ((x : A) → C (inl x)) → ((x : B) → C (inr x)) →
        ((x : A ⊎ B) → C x)
[inl: f ,inr: g ] (inl x) = f x
[inl: f ,inr: g ] (inr y) = g y

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}

infixr 5 _∷_

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

infixr 5 _++_

postulate
    String      : Set
    Integer     : Set
    zero        : Integer
    one         : Integer
    _+_         : Integer → Integer → Integer
    _++_        : String → String → String
    reverse     : String → String
    sort        : String → String
    take-half   : String → String
    drop-half   : String → String
    String▹List : String → List Char
    List▹String : List Char → String
    _≤Char_     : Char → Char → Bool

{-# BUILTIN STRING String #-}

{-# COMPILED_JS zero      0 #-}
{-# COMPILED_JS one       1 #-}
{-# COMPILED_JS _+_       function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS _++_      function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS reverse   function(x) { return x.split("").reverse().join(""); } #-}
{-# COMPILED_JS sort      function(x) { return x.split("").sort().join(""); }    #-}
{-# COMPILED_JS take-half function(x) { return x.substring(0,x.length/2); }      #-}
{-# COMPILED_JS drop-half function(x) { return x.substring(x.length/2); }        #-}
{-# COMPILED_JS _≤Char_   function(x) { return function(y) { return exports["fromJSBool"](x <= y); }; } #-}


data Value : Set₀ where
  array  : List Value → Value
  object : List (String × Value) → Value
  string : String → Value
  number : Integer → Value
  bool   : Bool → Value
  null   : Value

postulate
    JSValue : Set
    JSON-stringify : JSValue → String
    fromValue : Value → JSValue
    -- JSON-parse :
{-# COMPILED_JS JSON-stringify function(x) { return JSON.stringify(x); } #-}

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

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

ap : {A B : Set} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
ap f refl = refl

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

data Proc (D : Set₀) (M : Set₀) : Set₀ where
  end    : Proc D M
  output : (d : D) (m : M) (p : Proc D M) → Proc D M
  input  : (d : D) (p : M → Proc D M) → Proc D M
  start  : (p : Proc 𝟙 M) (q : D → Proc D M) → Proc D M
  error  : (err : String) → Proc D M

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

reverser : Proc 𝟙 String
reverser = input _ λ s → output _ (reverse s) end

cater : Proc 𝟙 String
cater = input _ λ s₀ → input _ λ s₁ → output _ (s₀ ++ s₁) end

cater-client : ∀ {D} → D → String → String → Proc D String
cater-client d s₀ s₁ = output d s₀ (output d s₁ (input d λ _ → end))

cater-reverser-client : ∀ {D} → D → D → String → Proc D String
cater-reverser-client cater-addr reverser-addr s =
  output reverser-addr s $
  output cater-addr s $
  input reverser-addr λ rs →
  output cater-addr rs $
  input cater-addr λ res →
  end

str-sorter₀ : ∀ {D} → D → Proc D String
str-sorter₀ d = input d λ s → output d (sort s) end

str-sorter-client : ∀ {D} → D → String → Proc D String
str-sorter-client d s = output d s $ input d λ _ → end

str-merger : ∀ {D} (upstream helper₀ helper₁ : D) → Proc D String
str-merger upstream helper₀ helper₁ =
  input upstream λ s →
  output helper₀ (take-half s) $
  output helper₁ (drop-half s) $
  input helper₀ λ ss₀ →
  input helper₁ λ ss₁ →
  output upstream (merge-sort ss₀ ss₁)
  end

dyn-merger : ∀ {D} → D → Proc 𝟙 String → Proc D String
dyn-merger upstream helper =
  start helper λ helper₀ →
  start helper λ helper₁ →
  str-merger upstream helper₀ helper₁

str-sorter₁ : ∀ {D} → D → Proc D String
str-sorter₁ upstream = dyn-merger upstream (str-sorter₀ _)

str-sorter₂ : ∀ {D} → D → Proc D String
str-sorter₂ upstream = dyn-merger upstream (str-sorter₁ _)

postulate
  HTTPServer : Set

data JSCmd : Set where
  server : (ip port : String)(proc : Proc 𝟙 String)
           (callback : HTTPServer → (uri : String) → JSCmd) → JSCmd
  client : Proc String String → JSCmd → JSCmd
  end : JSCmd
  console-log : String → JSCmd → JSCmd

main : 𝟙 → JSCmd
main _ =
  console-log (JSON-stringify (fromValue test-value)) $
  server "127.0.0.1" "1342" (str-sorter₂ _) λ http_server uri →
  console-log "str-sorter-client:" $
  client (str-sorter-client "http://127.0.0.1:1342/" "Something to be sorted!")
  end
-- -}
-- -}
-- -}
-- -}
