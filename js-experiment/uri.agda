module uri where

open import prelude

abstract
  URI = String
  showURI : URI → String
  showURI = id
  readURI : String → URI
  readURI = id
  clientURI : URI
  clientURI = ""
