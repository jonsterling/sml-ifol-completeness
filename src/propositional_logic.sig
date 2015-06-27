structure PropositionalOperators =
struct
  datatype t =
      FALSE
    | TRUE
    | FORALL
    | EXISTS
    | OR
end

structure ProofOperators =
struct
  datatype t =
      TRUE_INTRO
    | FALSE_ELIM
    | FORALL_INTRO
    | FORALL_ELIM
    | EXISTS_INTRO
    | EXISTS_ELIM
    | OR_INTRO_L
    | OR_INTRO_R
    | OR_ELIM
end

signature PROPOSITIONAL_LOGIC =
sig
  structure Prop : ABT_UTIL
    where type Operator.t = PropositionalOperators.t

  structure Proof : ABT_UTIL
    where type Operator.t = ProofOperators.t
end
