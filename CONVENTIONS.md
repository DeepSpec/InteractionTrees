# Coq Conventions

## Naming conventions:

- [python_case] for definitions
- [CamelCase] for constructors and classes

Variables:
- [E E1 E2 F F1 F2 : Type -> Type] effect types
- [X Y Z : Type] effect output types
- [e : E X] effects
- [R S : Type] return/result types ([Ret : R -> itree E R])
- [t u : itree E R] itrees
- [k h : R -> itree E S] itree continuations (iforests?)
