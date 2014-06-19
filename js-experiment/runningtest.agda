module runningtest where

open import prelude
open import libjs
open import proto
open import proc

test-value : Value
test-value = object (("array"  , array (array [] ∷ array (array [] ∷ []) ∷ [])) ∷
                     ("object" , array (object [] ∷ object (("a", string "b") ∷ []) ∷ [])) ∷
                     ("string" , array (string "" ∷ string "a" ∷ [])) ∷
                     ("number" , array (number zero ∷ number one ∷ [])) ∷
                     ("bool"   , array (bool true ∷ bool false ∷ [])) ∷
                     ("null"   , array (null ∷ [])) ∷ [])

test =
    fromString (JSON-stringify (fromValue test-value))
    ===
    fromString "{\"array\":[[],[[]]],\"object\":[{},{\"a\":\"b\"}],\"string\":[\"\",\"a\"],\"number\":[0,1],\"bool\":[true,false],\"null\":[null]}"


merge-sort-string : String → String → String
merge-sort-string s₀ s₁ = List▹String (merge-sort-list _≤Char_ (String▹List s₀) (String▹List s₁))

reverser : JSProc
reverser = input … λ s → output … (fromString (onString reverse s)) end

adder : JSProc
adder = input … λ s₀ → input … λ s₁ → output … (s₀ +JS s₁) end

adder-client : URI → JSValue → JSValue → JSProc
adder-client d s₀ s₁ = output d s₀ (output d s₁ (input d λ _ → end))

module _ (adder-addr reverser-addr : URI)(s : JSValue) where
  adder-reverser-client : JSProc
  adder-reverser-client =
    output reverser-addr s $
    output adder-addr s $
    input reverser-addr λ rs →
    output adder-addr rs $
    input adder-addr λ res →
    end

str-sorter₀ : URI → JSProc
str-sorter₀ d = input d λ s → output d (fromString (onString sort s)) end

str-sorter-client : ∀ {D} → D → JSValue → Proc D JSValue
str-sorter-client d s = output d s $ input d λ _ → end

module _ (upstream helper₀ helper₁ : URI) where
  str-merger : JSProc
  str-merger =
    input upstream λ s →
    output helper₀ (fromString (onString take-half s)) $
    output helper₁ (fromString (onString drop-half s)) $
    input helper₀ λ ss₀ →
    input helper₁ λ ss₁ →
    output upstream (fromString (onString (onString merge-sort-string ss₀) ss₁))
    end

dyn-merger : URI → JSProc → JSProc
dyn-merger upstream helper =
  start helper λ helper₀ →
  start helper λ helper₁ →
  str-merger upstream helper₀ helper₁

str-sorter₁ : URI → JSProc
str-sorter₁ upstream = dyn-merger upstream (str-sorter₀ clientURI)

str-sorter₂ : URI → JSProc
str-sorter₂ upstream = dyn-merger upstream (str-sorter₁ clientURI)

stringifier : JSProc
stringifier = input … λ v → output … (fromString (JSON-stringify v)) end

stringifier-client : ∀ {D} → D → JSValue → Proc D JSValue
stringifier-client d v = output d v $ input d λ _ → end

main : JSCmd
main =
  assert test $
  console_log "server(adder):" $
  server "127.0.0.1" "1337" adder λ _ adder-uri →
  console_log "client(adderclient):" $
  client (adder-client adder-uri (fromString "Hello ") (fromString "World!")) $
  client (adder-client adder-uri (fromString "Bonjour ") (fromString "monde!")) $
  console_log "server(reverser):" $
  server "127.0.0.1" "1338" reverser λ _ reverser-uri →
  console_log "client(adder-reverser-client):" $
  client (adder-reverser-client adder-uri reverser-uri (fromString "red")) $

  server "127.0.0.1" "1342" (str-sorter₂ clientURI) λ http_server str-sorter₂-uri →
  console_log "str-sorter-client:" $
  client (str-sorter-client str-sorter₂-uri (fromString "Something to be sorted!")) $

  server "127.0.0.1" "1343" stringifier λ _ stringifier-uri →
  client (stringifier-client stringifier-uri (fromValue test-value)) $
  end
-- -}
-- -}
-- -}
-- -}
