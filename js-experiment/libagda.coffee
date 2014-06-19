define ["exports"], (libagda) ->
  id = (x) -> x
  libagda.id = id

  foldrArray = (a, nil, cons) ->
    len = a.length
    l = nil
    i = len - 1
    while i >= 0
      l = cons a[i], l
      i--
    l
  libagda.foldrArray = foldrArray

  fromAgdaBool = (b) ->
    b
      true:  () -> true
      false: () -> false
  libagda.fromAgdaBool = fromAgdaBool

  fromList = (l0, fromElt) ->
    a = []
    i = 0
    go = (l) ->
      l
        "[]":  () -> { }
        "_∷_": (x, xs) ->
                  a[i] = fromElt x
                  i++
                  go xs
    go l0
    Object.freeze a
  libagda.fromList = fromList

  objectFromList = (l0, key, val) ->
    o = {}
    go = (l) ->
      l
        "[]":  () -> { }
        "_∷_": (x, xs) ->
                o[key x] = val x
                go xs
    go l0
    Object.freeze o
  libagda.objectFromList = objectFromList

  fromValue = (v) ->
    v
      "array":  (l) -> fromList l, fromValue
      "object": (l) -> objectFromList l, ((x) -> x["fst"]), ((x) -> fromValue x["snd"])
      "string": id
      "number": id
      "bool":   fromAgdaBool
      "null":   () -> null
  libagda.fromValue = fromValue

  tt   = (x) -> x.record()
  nil  = (l) -> l["[]"]()
  cons = (x, xs) -> (l) -> l["_∷_"](x, xs)
  libagda.tt = tt
  libagda.nil = nil
  libagda.cons = cons

  libagda.fromJSBool = (b) -> (x) -> if b then x.true() else x.false()

  libagda.onString = (f) -> (x) ->
    if typeof x is "string"
      f x
    else
      throw "onString(): not a string"

  libagda.onString2 = (f) -> (x) -> (y) ->
    if typeof x is "string" and typeof y is "string"
      f(x)(y)
    else
      throw "onString2(): not a string"

  fromJSArray = (a) -> foldrArray a, nil, cons
  libagda.fromJSArray = fromJSArray

  libagda.stringToList = (x) -> fromJSArray (x.split "")
  libagda.listToString = (x) -> (fromList x, id).join ""

  return libagda

###
  prelude = require "jAgda.prelude.js"

  prelude["Σ"]["fst"] = (x) -> (y) -> (z) -> z.fst
  prelude["Σ"]["snd"] = (x) -> (y) -> (z) -> z.snd


  prelude_Bool =
    true:  (x) -> x.true()
    false: (x) -> x.false()

  libjs["fromJSBool"] = fromJSBool
  libjs["fromValue"] = fromValue
  libjs["onString"] = onString
  libjs["onString2"] = onString2
###
