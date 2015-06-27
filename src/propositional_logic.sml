structure PropositionalLogic : PROPOSITIONAL_LOGIC =
struct
  structure Prop =
  struct
    structure Operator =
    struct
      open PropositionalOperators

      val eq : t * t -> bool = op=

      fun arity FALSE = #[]
        | arity TRUE = #[]
        | arity AND = #[0,0]
        | arity IMPLIES = #[0,0]
        | arity OR = #[0,0]
        | arity EXISTS = #[1]
        | arity FORALL = #[1]
        | arity BASE = #[]

      fun toString FALSE = "false"
        | toString TRUE = "true"
        | toString AND = "and"
        | toString OR = "or"
        | toString IMPLIES = "implies"
        | toString EXISTS = "exists"
        | toString FORALL = "forall"
        | toString BASE = "D"
    end

    structure Abt = AbtUtil (Abt (structure Operator = Operator and Variable = Variable))
    open Abt
  end

  structure Proof =
  struct
    structure Operator =
    struct
      open ProofOperators
      type t = Prop.t t

      fun eq (TRUE_INTRO, TRUE_INTRO) = true
        | eq (FALSE_ELIM p, FALSE_ELIM q) = Prop.eq (p, q)
        | eq (OR_INTRO_L, OR_INTRO_R) = true
        | eq (OR_ELIM p, OR_ELIM q) = Prop.eq (p, q)
        | eq (AND_INTRO, AND_INTRO) = true
        | eq (AND_ELIM p, AND_ELIM q) = Prop.eq (p, q)
        | eq (IMPLIES_INTRO p, IMPLIES_INTRO q) = Prop.eq (p, q)
        | eq (IMPLIES_ELIM, IMPLIES_ELIM) = true
        | eq (FORALL_INTRO, FORALL_INTRO) = true
        | eq (FORALL_ELIM, FORALL_ELIM) = true
        | eq (EXISTS_INTRO, EXISTS_INTRO) = true
        | eq (EXISTS_ELIM, EXISTS_ELIM) = true
        | eq _ = false

      fun arity TRUE_INTRO = #[]
        | arity (FALSE_ELIM p) = #[0]
        | arity OR_INTRO_L = #[0]
        | arity OR_INTRO_R = #[0]
        | arity (OR_ELIM p) = #[0,1,1]
        | arity AND_INTRO = #[0,0]
        | arity (AND_ELIM p) = #[0,2]
        | arity (IMPLIES_INTRO p) = #[1]
        | arity IMPLIES_ELIM = #[0,0]
        | arity FORALL_INTRO = #[1]
        | arity FORALL_ELIM = #[0,0]
        | arity EXISTS_INTRO = #[0,0]
        | arity EXISTS_ELIM = #[2]

      fun toString TRUE_INTRO = "true-intro"
        | toString (FALSE_ELIM p) = "false-elim{" ^ Prop.toString p ^ "}"
        | toString OR_INTRO_L = "or-intro-l"
        | toString OR_INTRO_R = "or-intro-r"
        | toString (OR_ELIM p) = "or-elim{" ^ Prop.toString p ^ "}"
        | toString AND_INTRO = "and-intro"
        | toString (AND_ELIM p) = "and-elim{" ^ Prop.toString p ^ "}"
        | toString (IMPLIES_INTRO p) = "implies-intro{" ^ Prop.toString p ^ "}"
        | toString IMPLIES_ELIM = "implies-elim"
        | toString FORALL_INTRO = "forall-intro"
        | toString FORALL_ELIM = "forall-elim"
        | toString EXISTS_INTRO = "exists-intro"
        | toString EXISTS_ELIM = "exists-elim"
    end

    structure Abt = AbtUtil (Abt (structure Operator = Operator and Variable = Variable))
    open Abt
  end
end
