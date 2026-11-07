FROM rocq/rocq-prover:9.1-ocaml-4.14-flambda

RUN opam update; \
    opam install coq-lsp.0.2.5+9.1 -y; \
    opam install ocaml-lsp-server -y
