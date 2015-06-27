signature EVIDENCE =
sig
  include ABT_UTIL
  val eval : t -> t


  val ax : t
  val pair : t * t -> t

  datatype result =
      CANON of t
    | NONCANON of t * Variable.t

  val compute : t -> result
end

