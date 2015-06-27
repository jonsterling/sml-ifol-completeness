signature EVIDENCE =
sig
  include ABT_UTIL
  val eval : t -> t

  val ax : t
  val pair : t * t -> t

  structure Canon :
  sig
    datatype canonical_form =
        AX
      | PAIR of t * t
      | INL of t
      | INR of t

    val into : canonical_form -> t
  end

  datatype result =
      CANON of Canon.canonical_form
    | NONCANON of t * Variable.t

  val compute : t -> result

end

