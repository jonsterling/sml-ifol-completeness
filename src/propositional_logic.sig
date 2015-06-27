structure PropositionalOperators =
struct
  datatype t =
      FALSE
    | TRUE
    | AND
    | IMPLIES
    | OR
    | FORALL
    | EXISTS
    | BASE (* domain of discourse *)
end

structure ProofOperators =
struct
  datatype t =
      TRUE_INTRO
    | FALSE_ELIM
    | OR_INTRO_L
    | OR_INTRO_R
    | OR_ELIM
    | AND_INTRO
    | AND_ELIM
    | IMPLIES_INTRO
    | IMPLIES_ELIM
    | FORALL_INTRO
    | FORALL_ELIM
    | EXISTS_INTRO
    | EXISTS_ELIM
end

signature PROPOSITIONAL_LOGIC =
sig
  structure Prop : ABT_UTIL
    where type Operator.t = PropositionalOperators.t

  structure Proof : ABT_UTIL
    where type Operator.t = ProofOperators.t
end
