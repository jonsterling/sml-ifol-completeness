structure EvidenceOps =
struct
  datatype t =
      AX
    | PAIR | SPREAD
    | INL | INR | DECIDE
    | LAM | AP

  val eq : t * t -> bool = op=

  fun arity AX = #[]
    | arity PAIR = #[0,0]
    | arity SPREAD = #[0,2]
    | arity INL = #[0]
    | arity INR = #[0]
    | arity DECIDE = #[0,1,1]
    | arity LAM = #[1]
    | arity AP = #[0,0]

  fun toString AX = "<>"
    | toString PAIR = "pair"
    | toString SPREAD = "spread"
    | toString INL = "inl"
    | toString INR = "inr"
    | toString DECIDE = "decide"
    | toString LAM = "lam"
    | toString AP = "ap"
end

structure Evidence : EVIDENCE =
struct
  exception Stuck

  structure Ops = EvidenceOps
  structure Abt =
    AbtUtil
      (Abt
        (structure Variable = Variable
         structure Operator = Ops))

  open Abt

  infix $ $$ \\ \ //

  structure Canon =
  struct
    datatype canonical_form =
        AX
      | PAIR of t * t
      | INL of t
      | INR of t
      | LAM of Variable.t * t

    fun into AX = Ops.AX $$ #[]
      | into (PAIR (M,N)) = Ops.PAIR $$ #[M,N]
      | into (INL M) = Ops.INL $$ #[M]
      | into (INR M) = Ops.INR $$ #[M]
      | into (LAM (x, E)) = Ops.INR $$ #[x \\ E]
  end

  datatype result =
      CANON of Canon.canonical_form
    | NONCANON of t * Variable.t

  fun compute E =
    case out E of
         Ops.AX $ #[] => CANON Canon.AX
       | Ops.PAIR $ #[M,N] => CANON (Canon.PAIR (M,N))
       | Ops.INL $ #[M] => CANON (Canon.INL M)
       | Ops.INR $ #[M] => CANON (Canon.INR M)
       | Ops.LAM $ #[xE] => CANON (Canon.LAM (unbind xE))
       | Ops.AP $ #[M,N] =>
           (case compute M of
                 CANON (Canon.LAM (x,E)) => compute (subst N x E)
               | NONCANON (R, u) => NONCANON (Ops.AP $$ #[R, N], u)
               | _ => raise Stuck)
       | Ops.SPREAD $ #[M, xyE] =>
           (case compute M of
                 CANON (Canon.PAIR (M1, M2)) => compute ((xyE // M1) // M2)
               | NONCANON (R, u) => NONCANON (Ops.SPREAD $$ #[R, xyE], u)
               | _ => raise Stuck)
       | Ops.DECIDE $ #[M, xE, yF] =>
           (case compute M of
                 CANON (Canon.INL M') => compute (xE // M')
               | CANON (Canon.INR M') => compute (yF // M')
               | NONCANON (R, u) => NONCANON (Ops.DECIDE $$ #[R, xE, yF], u)
               | _ => raise Stuck)
       | ` x => NONCANON (``x, x)
       | _ => raise Fail (toString E)
end
