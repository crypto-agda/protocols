module Control.Protocol.Parametricity where

open import Type
open import Relation.Binary.Logical

data Proto : ★₁ where
  end  : Proto
  send : {M : ★}(P : M → Proto) → Proto
  recv : {M : ★}(P : M → Proto) → Proto

data ⟦Proto⟧ : ⟦★₁⟧ Proto Proto where
  ⟦end⟧  : ⟦Proto⟧ end end
  ⟦send⟧ : (∀⟨ Mᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ (Mᵣ ⟦→⟧ ⟦Proto⟧) ⟦→⟧ ⟦Proto⟧) send send
  ⟦recv⟧ : (∀⟨ Mᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ (Mᵣ ⟦→⟧ ⟦Proto⟧) ⟦→⟧ ⟦Proto⟧) recv recv

