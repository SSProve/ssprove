(lang dune 3.21)
(using coq 0.11)
(name rocq-ssprove)
(version dev)

(generate_opam_files false)

(source (github SSProve/ssprove))
(license MIT)
(authors "SSProve team")
(maintainers "philipp@haselwarter.org")

(package
 (name rocq-ssprove)
 (synopsis "A Foundational Framework for Modular Cryptographic Proofs")
 (depends (rocq-core (>= 8.20~))
   (rocq-stdlib (>= 9.0~))
   (rocq-equations (>= 1.3.1~))
   (coq-mathcomp-ssreflect (>= 2.2.0))
   (coq-mathcomp-analysis (>= 1.8.0))
   (coq-mathcomp-experimental-reals (>= 1.8.0))
   (coq-mathcomp-word (>= 3.3))
   (coq-extructures (>= 0.5.0))
   (coq-deriving (>= 0.2.0)))
)

(warnings (deprecated_coq_lang_lt_08 disabled))
