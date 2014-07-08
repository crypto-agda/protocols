module _ where

open import prelude

data JSType : Set where
  array object number string bool null : JSType

infixr 5 _++_

postulate
    Number      : Set
    readNumber  : String  → Number
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

    JSValue        : Set
    _+JS_          : JSValue → JSValue → JSValue
    _≤JS_          : JSValue → JSValue → Bool
    _===_          : JSValue → JSValue → Bool
    JSON-stringify : JSValue → String
    JSON-parse     : String → JSValue
    fromString     : String → JSValue
    fromChar       : Char   → JSValue
    fromNumber     : Number → JSValue
    objectFromList : {A : Set} → List (A) → (A → String) → (A → JSValue) → JSValue
    castNumber     : JSValue → Number
    castString     : JSValue → String
    nullJS         : JSValue
    trueJS         : JSValue
    falseJS        : JSValue
    readJSType     : String → JSType
    showJSType     : JSType → String
    typeof         : JSValue → JSType

    onString : {A : Set} (f : String → A) → JSValue → A

{-# COMPILED_JS zero      0 #-}
{-# COMPILED_JS one       1 #-}
{-# COMPILED_JS readNumber Number #-}
{-# COMPILED_JS _+_       function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS _++_      function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS _+JS_     function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS reverse   function(x) { return x.split("").reverse().join(""); } #-}
{-# COMPILED_JS sort      function(x) { return x.split("").sort().join(""); }    #-}
{-# COMPILED_JS take-half function(x) { return x.substring(0,x.length/2); }      #-}
{-# COMPILED_JS drop-half function(x) { return x.substring(x.length/2); }        #-}
{-# COMPILED_JS List▹String function(x) { return (require("libagda").fromList(x, function(y) { return y; })).join(""); } #-}
{-# COMPILED_JS String▹List function(x) { return require("libagda").fromJSArray(x.split("")); } #-}
{-# COMPILED_JS _≤JS_     function(x) { return function(y) { return require("libagda").fromJSBool(x <= y); }; } #-}
{-# COMPILED_JS _===_     function(x) { return function(y) { return require("libagda").fromJSBool(x === y); }; } #-}
{-# COMPILED_JS JSON-stringify JSON.stringify #-}
{-# COMPILED_JS JSON-parse JSON.parse #-}
{-# COMPILED_JS fromString function(x) { return x; } #-}
{-# COMPILED_JS fromChar   function(x) { return x; } #-}
{-# COMPILED_JS fromNumber function(x) { return x; } #-}
{-# COMPILED_JS castNumber Number #-}
{-# COMPILED_JS castString String #-}
{-# COMPILED_JS nullJS     null #-}
{-# COMPILED_JS trueJS     true #-}
{-# COMPILED_JS falseJS    false #-}
{-# COMPILED_JS typeof     function(x) { return typeof(x); } #-}
{-# COMPILED_JS onString   function(t) { return require("libagda").onString; } #-}

data Value : Set₀ where
  array  : List Value → Value
  object : List (String × Value) → Value
  string : String → Value
  number : Number  → Value
  bool   : Bool → Value
  null   : Value

postulate
    fromValue : Value → JSValue

data ValueView : Set₀ where
  array  : List JSValue → ValueView
  object : List (String × JSValue) → ValueView
  string : String → ValueView
  number : Number  → ValueView
  bool   : Bool → ValueView
  null   : ValueView


postulate
    fromJSValue : JSValue → ValueView

{-# COMPILED_JS fromValue require("libagda").fromValue #-}

fromBool : Bool → JSValue
fromBool true  = trueJS
fromBool false = falseJS

Object = List (String × JSValue)

fromObject : Object → JSValue
fromObject o = objectFromList o fst snd

_≤Char_ : Char → Char → Bool
x ≤Char y = fromChar x ≤JS fromChar y

_≤String_ : String → String → Bool
x ≤String y = fromString x ≤JS fromString y

_≤Number_ : Number → Number → Bool
x ≤Number y = fromNumber x ≤JS fromNumber y
