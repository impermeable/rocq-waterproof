(lang dune 3.21)
(using rocq 0.11)
(using directory-targets 0.1)


(package
 (name coq-waterproof)
 (version 3.1.1+dev)
 (synopsis "Coq proofs in a style that resembles non-mechanized mathematical proofs")
 (depends rocq-core rocq-stdlib))
