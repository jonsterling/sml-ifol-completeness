structure EvidenceOps =
struct
  datatype t =
      AX
    | PAIR | SPREAD
    | INL | INR | DECIDE
    | LAM | AP
    | FREE_CHOICE

  val eq : t * t -> bool = op=

  fun arity AX = #[]
    | arity PAIR = #[0,0]
    | arity SPREAD = #[0,2]
    | arity INL = #[0]
    | arity INR = #[0]
    | arity DECIDE = #[0,1,1]
    | arity LAM = #[1]
    | arity FREE_CHOICE = #[]
    | arity AP = #[0,0]

  fun toString AX = "<>"
    | toString PAIR = "pair"
    | toString SPREAD = "spread"
    | toString INL = "inl"
    | toString INR = "inr"
    | toString DECIDE = "decide"
    | toString LAM = "lam"
    | toString FREE_CHOICE = "free-choice"
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

  datatype primary =
      AX
    | PAIR of t * t
    | INL of t
    | INR of t
    | AP of t * t
    | OTHERV of t

  datatype neutral =
      VAR of Variable.t
    | OTHER of t

  fun primary AX = Ops.AX $$ #[]
    | primary (PAIR (M,N)) = Ops.PAIR $$ #[M,N]
    | primary (INL M) = Ops.INL $$ #[M]
    | primary (INR M) = Ops.INR $$ #[M]
    | primary (AP (M,N)) = Ops.AP $$ #[M,N]
    | primary (OTHERV M) = M

  fun neutral (VAR x) = ``x
    | neutral (OTHER R) = R

  datatype result =
      PRIMARY of primary
    | NEUTRAL of neutral * Variable.t

  val switch = ref true
  fun getChoice () =
    let
      val operator = if !switch then INL else INR
    in
      switch := not (!switch);
      operator (Ops.AX $$ #[])
    end

  fun compute E =
    case out E of
         Ops.AX $ #[] => PRIMARY AX
       | Ops.PAIR $ #[M,N] => PRIMARY (PAIR (M,N))
       | Ops.INL $ #[M] => PRIMARY (INL M)
       | Ops.INR $ #[M] => PRIMARY (INR M)
       | Ops.LAM $ #[xE] => PRIMARY (OTHERV E)
       | Ops.FREE_CHOICE $ #[] => PRIMARY (OTHERV E)
       | Ops.AP $ #[M,N] =>
           (case compute M of
                 PRIMARY (OTHERV M') =>
                   (case out M' of
                        Ops.LAM $ #[xE] => compute (xE // N)
                      | Ops.FREE_CHOICE $ #[] => PRIMARY (getChoice ())
                      | _ => raise Stuck)
               | NEUTRAL (R, u) => PRIMARY (AP (neutral R,N))
               | _ => raise Stuck)
       | Ops.SPREAD $ #[M, xyE] =>
           (case compute M of
                 PRIMARY (PAIR (M1, M2)) => compute ((xyE // M1) // M2)
               | NEUTRAL (R, u) => NEUTRAL (OTHER (Ops.SPREAD $$ #[neutral R, xyE]), u)
               | _ => raise Stuck)
       | Ops.DECIDE $ #[M, xE, yF] =>
           (case compute M of
                 PRIMARY (INL M') => compute (xE // M')
               | PRIMARY (INR M') => compute (yF // M')
               | NEUTRAL (R, u) => NEUTRAL (OTHER (Ops.DECIDE $$ #[neutral R, xE, yF]), u)
               | _ => raise Stuck)
       | ` x => NEUTRAL (VAR x, x)
       | _ => raise Fail (toString E)
end
