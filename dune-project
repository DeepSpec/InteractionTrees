(lang dune 3.14)
(using coq 0.7)
(name coq-itree)
(version dev)
(maintainers "Li-yao Xia <lysxia@gmail.com>")
(source (github DeepSpec/InteractionTrees))
(license MIT)

(package
  (name coq-itree)
  (synopsis "Library for representing recursive and impure programs with equational reasoning")
  (depends
    (coq (>= 8.13))
    (coq-ext-lib (>= 0.11.1))
    (coq-paco (and (>= 4.0.1) (< 4.3))))
  (tags ("org:deepspec"))
  (authors
    "Li-yao Xia"
    "Yannick Zakowski"
    "Paul He"
    "Chung-Kil Hur"
    "Gregory Malecha"
    "Steve Zdancewic"
    "Benjamin Pierce")
)

(package
  (name coq-itree-extra)
  (synopsis "Extensions to coq-itree")
  (depends
    coq
    coq-ext-lib
    coq-paco
    coq-itree)
  (tags ("org:deepspec"))
  (authors
    "Lucas Silver"
    "Irene Yoon"
    "Paul He"
    "Yannick Zakowski"
    "Steve Zdancewic")
)

(generate_opam_files true)
