functor ProofFromEvidence
  (structure PropositionalLogic : PROPOSITIONAL_LOGIC
   structure Evidence : EVIDENCE
   sharing type PropositionalLogic.Prop.Variable.t = Evidence.Variable.t
   sharing type PropositionalLogic.Proof.Variable.t = Evidence.Variable.t) =
struct
  open PropositionalOperators ProofOperators PropositionalLogic
  structure P = Prop and D = Proof and E = Evidence
  structure V = E.Variable and EC = E.Canon

  structure Context = Telescope (P.Variable)
  type context = P.t Context.telescope

  fun @@ (H, p) = Context.snoc H p
  infix @@

  exception Nope

  fun asVariable X =
    case E.out X of
         E.` d => d
       | _ => raise Nope

  fun proofFromEvidence (H : context, prop : P.t, evd : E.t) : D.t =
    case E.compute evd of
         E.CANON t => introductionMode (H, prop, t)
       | E.NONCANON (t, v) => eliminationMode (H, prop, t, v)

  and introductionMode (H : context, prop : P.t, M : EC.canonical_form) : D.t =
    case (P.out prop, M) of
         (P.$ (TRUE, _), EC.AX) => D.$$ (TRUE_INTRO, #[])
       | (P.$ (AND, #[A,B]), EC.PAIR (N1, N2)) =>
           let
             val D1 = proofFromEvidence (H, A, N1)
             val D2 = proofFromEvidence (H, B, N2)
           in
             D.$$ (AND_INTRO, #[D1, D2])
           end
       | (P.$ (OR, #[A,B]), EC.INL N) =>
           let
             val D = proofFromEvidence (H, A, N)
           in
             D.$$ (OR_INTRO_L, #[D])
           end
       | (P.$ (OR, #[A,B]), EC.INR N) =>
           let
             val D = proofFromEvidence (H, B, N)
           in
             D.$$ (OR_INTRO_R, #[D])
           end
       | (P.$ (IMPLIES, #[A,B]), EC.LAM (z, E)) =>
           let
             val D = proofFromEvidence (H @@ (z, A), B, E)
           in
             D.$$ (IMPLIES_INTRO A, #[D.\\ (z, D)])
           end
       | (P.$ (FORALL, #[xB]), EC.LAM (z, E)) =>
           let
             val (x, B) = P.unbind xB
             val D = proofFromEvidence (H @@ (x, P.$$ (BASE, #[])), B, E.subst (E.`` x) z E)
           in
             D.$$ (FORALL_INTRO, #[D.\\ (x, D)])
           end
       | (P.$ (EXISTS, #[xB]), EC.PAIR (N1, N2)) =>
           (case E.compute N1 of
                E.NONCANON (N1', _) =>
                  let
                    val d = asVariable N1'
                  in
                    if P.eq (Context.lookup H d, P.$$ (BASE, #[])) then
                      let
                        val D = proofFromEvidence (H, P.// (xB, P.`` d), N2)
                      in
                        D.$$ (EXISTS_INTRO, #[D])
                      end
                    else
                      raise Fail "EXISTS"
                  end
              | _ => raise Nope)
       | _ => raise Fail (P.toString prop)

  and eliminationMode (H : context, prop : P.t, evd : E.t, v : E.Variable.t) : D.t =
    case P.out (Context.lookup H v) of
         P.$ (TRUE, #[]) => proofFromEvidence (H, prop, E.subst (EC.into EC.AX) v evd)
       | P.$ (FALSE, #[]) => D.$$ (FALSE_ELIM prop, #[D.``v])
       | P.$ (EXISTS, #[xQ]) =>
           let
             val s = Context.fresh (H, V.named "s")
             val t = Context.fresh (H, V.named "t")
             val H' = Context.empty @@ (s, P.$$ (BASE, #[])) @@ (t, P.subst1 xQ (P.`` s))
             val H'' = Context.interposeAfter H (v, H')
             val pair = EC.into (EC.PAIR (E.`` s, E.`` t))
             val D = proofFromEvidence (H'', prop, E.subst pair v evd)
           in
             D.$$ (EXISTS_ELIM, #[D.\\ (s, D.\\ (t, D))])
           end
       | P.$ (FORALL, #[xQ]) =>
           raise Nope
       | P.$ (BASE, _) => D.`` v (* TODO: wrong *)
       | _ => raise Fail "Catchall"
end
