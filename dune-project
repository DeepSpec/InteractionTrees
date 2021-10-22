(lang dune 2.6)
(using coq 0.2)
(name coq-itree)

(package
  (name coq-itree)
  (synopsis "Library for representing recursive and impure programs with equational reasoning")
  (depends
    (coq (>= 8.10))
    (coq-ext-lib (>= 0.11.1))
    (coq-paco (>= 4.0.1)))
)

(package
  (name coq-itree-tutorial)
  (synopsis "Example toy compiler verified using the itree library")
)
