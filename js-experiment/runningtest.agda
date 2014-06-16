module runningtest where

infixr 0 _$_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

record 𝟙 : Set₀ where

data Bool : Set where
  true false : Bool

record _×_ (A B : Set) : Set where
  constructor _,_
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
    reverse : String → String
    sort : String → String
    split-half : String → String × String
    String▹List : String → List Char
    List▹String : List Char → String
    _≤Char_ : Char → Char → Bool

module _ {A : Set} (_≤_ : A → A → Bool) where

    merge-sort-list : (l₀ l₁ : List A) → List A
    merge-sort-list [] l₁ = l₁
    merge-sort-list l₀ [] = l₀
    merge-sort-list (x₀ ∷ l₀) (x₁ ∷ l₁) with x₀ ≤ x₁
    ... | true  = x₀ ∷ merge-sort-list l₀ (x₁ ∷ l₁)
    ... | false = x₁ ∷ merge-sort-list (x₀ ∷ l₀) l₁

merge-sort : String → String → String
merge-sort s₀ s₁ = List▹String (merge-sort-list _≤Char_ (String▹List s₀) (String▹List s₁))

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

data Proc (D : Set₀) (M : Set₀) : Set₀ where
  end    : Proc D M
  output : D → M → Proc D M → Proc D M
  input  : D → (M → Proc D M) → Proc D M
  start  : Proc 𝟙 M → (D → Proc D M) → Proc D M

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
  let (s₀ , s₁) = split-half s in
  output helper₀ s₀ $
  output helper₁ s₁ $
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

data Value : Set₀ where
  array  : List Value → Value
  object : List (String × Value) → Value
  string : String → Value
  -- number : ℕ {- upgrade -} → Value
  bool   : Bool → Value
  null   : Value
-- -}
-- -}
-- -}
-- -}
