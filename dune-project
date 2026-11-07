(lang dune 3.8)
(using coq 0.8)
(using directory-targets 0.1)


(package
 (name rocq-waterproof)
 (version 3.1.1+9.0)
 (synopsis "Coq proofs in a style that resembles non-mechanized mathematical proofs")
 (depends rocq-core rocq-stdlib))
