FROM coqorg/coq:8.9
COPY --chown=coq . ITree
ENV OPAMYES true
WORKDIR "ITree/"
RUN opam update && eval $(opam env) && opam install . --deps-only
# make -j coq && make -j tutorial
