signature EVIDENCE =
sig
  include ABT_UTIL

  (* These represent the known forms of evidence. For the evidence of a positive
   * type, this is an introduction form; for the evidence of a negative type,
   * this is an elimination form. *)
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

  val primary : primary -> t
  val neutral : neutral -> t

  datatype result =
      PRIMARY of primary
    | NEUTRAL of neutral * Variable.t

  val compute : t -> result

end

