open import Level.NP
open import Data.Product.NP

open import Control.Protocol.Core
open import Control.Protocol.End

module Control.Protocol.Lift a {ℓ} where
    liftᴾ : Proto_ ℓ → Proto_ (a ⊔ ℓ)
    liftᴾ end        = end
    liftᴾ (com io P) = com io λ m → liftᴾ (P (lower {ℓ = a} m))

    lift-proc : (P : Proto_ ℓ) → ⟦ P ⟧ → ⟦ liftᴾ P ⟧
    lift-proc end      end     = end
    lift-proc (send P) (m , p) = lift m , lift-proc (P m) p
    lift-proc (recv P) p       = λ { (lift m) → lift-proc (P m) (p m) }
