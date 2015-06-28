signature EVIDENCE =
sig
  include ABT_UTIL

  (* These represent the known forms of evidence. For the evidence of a positive
   * type, this is an introduction form; for the evidence of a negative type,
   * this is an elimination form. *)
  datatype known_view =
      AX
    | PAIR of t * t
    | INL of t
    | INR of t
    | AP of t * t
    | VAR of Variable.t
    | OTHER of t

  val unview : known_view -> t

  datatype result =
      PRIMARY of known_view
    | NEUTRAL of known_view * Variable.t

  val compute : t -> result

end

