Directories are organized as follows:
  * `PTT`: This is a formalization of Process Type Theory. Some simplifications
    have been made on the way, such as binary connectives together with units
    instead of n-ary connectives. Cut-eliminitation is proved admissible on
    a particular for of processes where the cuts and tensors are splitting
    their proof immediately.

  * `SendRecv`: This is a formalization of a sub-system which does not have `⅋`
    and `⊗` but only `send` and `recv`.

  * `Control.Protocol`: Is a library based on `send`/`recv` protocols.
    Multiplicative connectives (`⅋` and `⊗`) are partially emulated.

The HTML highlighted version (not necessarily up to date):
  * http://crypto-agda.github.io/protocols/Control.Protocol.README.html

This development requires some extension to the standard libarary:
  * https://github.com/crypto-agda/agda-nplib

This development is part of a bigger project:
  * https://github.com/crypto-agda
