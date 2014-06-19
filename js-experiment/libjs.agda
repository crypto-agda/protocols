module _ where

open import prelude

infixr 5 _++_

postulate
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

{-# COMPILED_JS zero      0 #-}
{-# COMPILED_JS one       1 #-}
{-# COMPILED_JS _+_       function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS _++_      function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS _+JS_     function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS reverse   function(x) { return x.split("").reverse().join(""); } #-}
{-# COMPILED_JS sort      function(x) { return x.split("").sort().join(""); }    #-}
{-# COMPILED_JS take-half function(x) { return x.substring(0,x.length/2); }      #-}
{-# COMPILED_JS drop-half function(x) { return x.substring(x.length/2); }        #-}
{-# COMPILED_JS List▹String require("libagda").listToString #-}
{-# COMPILED_JS String▹List require("libagda").stringToList #-}
{-# COMPILED_JS _≤Char_   function(x) { return function(y) { return require("libagda").fromJSBool(x <= y); }; } #-}
{-# COMPILED_JS JSON-stringify function(x) { return JSON.stringify(x); } #-}
{-# COMPILED_JS fromString function(x) { return x; } #-}
{-# COMPILED_JS fromNumber function(x) { return x; } #-}
{-# COMPILED_JS nullJS     null #-}
{-# COMPILED_JS onString   require("libagda").onString #-}
{-# COMPILED_JS onString2  require("libagda").onString2 #-}

data Value : Set₀ where
  array  : List Value → Value
  object : List (String × Value) → Value
  string : String → Value
  number : Number  → Value
  bool   : Bool → Value
  null   : Value

postulate
    fromValue : Value → JSValue

{-# COMPILED_JS fromValue require("libagda").fromValue #-}
