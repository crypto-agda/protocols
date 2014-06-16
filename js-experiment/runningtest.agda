module runningtest where

data Bool : Set where
  true false : Bool

record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

------------------------------------------------------------------------
-- Operations

{-
private
 primitive
  primStringAppend   : String → String → String
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringEquality : String → String → Bool
-}

infixr 5 _++_

postulate
    _++_ : String → String → String
--_++_ = primStringAppend

{-
toList : String → List Char
toList = primStringToList

fromList : List Char → String
fromList = primStringFromList

toList∘fromList : ∀ s → toList (fromList s) ≡ s
toList∘fromList s = trustMe

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = trustMe

toVec : (s : String) → Vec Char (List.length (toList s))
toVec s = Vec.fromList (toList s)

toCostring : String → Costring
toCostring = Colist.fromList ∘ toList

unlines : List String → String
unlines []       = ""
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

-- Informative equality test.

_≟_ : Decidable {A = String} _≡_
s₁ ≟ s₂ with primStringEquality s₁ s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

-- Boolean equality test.
--
-- Why is the definition _==_ = primStringEquality not used? One
-- reason is that the present definition can sometimes improve type
-- inference, at least with the version of Agda that is current at the
-- time of writing: see unit-test below.

infix 4 _==_

_==_ : String → String → Bool
s₁ == s₂ = ⌊ s₁ ≟ s₂ ⌋
-}

★₀ = Set₀

data ℕ : ★₀ where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero  + y = y
suc x + y = suc (x + y)

data Proc (M : ★₀) : ★₀ where
  end    : Proc M
  output : M → Proc M → Proc M
  input  : (M → Proc M) → Proc M

adder : Proc ℕ
adder = input λ m → input λ n → output (m + n) end

client : Proc ℕ
client = output 31 (output 11 (input λ _ → end))

record 𝟙 : ★₀ where

seven : 𝟙 → ℕ
seven _ = 3 + 4

three : 𝟙 → ℕ
three _ = suc (suc zero) + suc zero

cater : Proc String
cater = input λ s₀ → input λ s₁ → output (s₀ ++ s₁) end

cater-client : String → String → Proc String
cater-client s₀ s₁ = output s₀ (output s₁ end)

data Value : ★₀ where
  array  : List Value → Value
  object : List (String × Value) → Value
  string : String → Value
  number : ℕ {- upgrade -} → Value
  bool   : Bool → Value
  null   : Value
-- -}
-- -}
-- -}
-- -}
