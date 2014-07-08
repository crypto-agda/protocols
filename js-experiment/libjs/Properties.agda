open import libjs
open import prelude

module libjs.Properties where


postulate
  tofromObject : ∀ l → fromJSValue (fromObject l) ≡ object l
