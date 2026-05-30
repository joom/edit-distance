(lang dune 3.21)
(using coq 0.9)
(name rocq-edit-distance)
(warnings (deprecated_coq_lang disabled))

(source (github joom/edit-distance))
(license MIT)
(authors "Joomy Korkut")
(maintainers "Joomy Korkut")

(package
 (name rocq-edit-distance)
 (synopsis "Verifying edit distance properties in Rocq")
 (depends
  ocaml
  (coq-core (>= 9.0.0))
  coq-vst))
