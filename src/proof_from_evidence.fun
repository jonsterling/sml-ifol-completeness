functor ProofFromEvidence
  (structure PropositionalLogic : PROPOSITIONAL_LOGIC
   structure Evidence : EVIDENCE
   sharing type PropositionalLogic.Prop.Variable.t = Evidence.Variable.t
   sharing type PropositionalLogic.Proof.Variable.t = Evidence.Variable.t) =
struct
  open PropositionalOperators ProofOperators PropositionalLogic
  structure P = Prop and D = Proof and E = Evidence and V = Evidence.Variable

  structure Context = Telescope (P.Variable)
  type context = P.t Context.telescope

  fun @@ (H, p) = Context.snoc H p
  infix @@

  exception Nope

  fun proofFromEvidence (H : context, prop : P.t, evd : E.t) : D.t =
    case E.compute evd of
         E.CANON t => introductionMode (H, prop, t)
       | E.NONCANON (t, v) => eliminationMode (H, prop, t, v)

  and introductionMode (H : context, prop : P.t, evd : E.t) : D.t =
    raise Nope

  and eliminationMode (H : context, prop : P.t, evd : E.t, v : E.Variable.t) : D.t =
    case P.out (Context.lookup H v) of
         P.$ (TRUE, #[]) => proofFromEvidence (H, prop, E.subst E.ax v evd)
       | P.$ (FALSE, #[]) => D.$$ (FALSE_ELIM, #[D.``v])
       | P.$ (EXISTS, #[P,xQ]) =>
           let
             val s = Context.fresh (H, V.named "s")
             val t = Context.fresh (H, V.named "t")
             val H' = Context.empty @@ (s, P) @@ (t, P.subst1 xQ (P.`` s))
             val H'' = Context.interposeAfter H (v, raise Nope)
             val pair = E.pair (E.`` s, E.`` t)
           in
             proofFromEvidence (H'', prop, E.subst pair v evd)
           end
       | _ => raise Nope
end
