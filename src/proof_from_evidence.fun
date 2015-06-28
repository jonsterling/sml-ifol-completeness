functor ProofFromEvidence
  (structure PropositionalLogic : PROPOSITIONAL_LOGIC
   structure Evidence : EVIDENCE
   sharing type PropositionalLogic.Prop.Variable.t = Evidence.Variable.t
   sharing type PropositionalLogic.Proof.Variable.t = Evidence.Variable.t) =
struct
  open PropositionalOperators ProofOperators PropositionalLogic
  structure P = Prop and D = Proof and E = Evidence
  structure V = E.Variable

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
         E.PRIMARY t => primaryMode (H, prop, t)
       | E.NEUTRAL (t, v) => eliminationMode (H, prop, t, v)

  and primaryMode (H : context, prop : P.t, M : E.primary) : D.t =
    case (P.out prop, M) of
         (P.$ (TRUE, _), E.AX) => D.$$ (TRUE_INTRO, #[])
       | (P.$ (AND, #[A,B]), E.PAIR (N1, N2)) =>
           let
             val D1 = proofFromEvidence (H, A, N1)
             val D2 = proofFromEvidence (H, B, N2)
           in
             D.$$ (AND_INTRO, #[D1, D2])
           end
       | (P.$ (OR, #[A,B]), E.INL N) =>
           let
             val D = proofFromEvidence (H, A, N)
           in
             D.$$ (OR_INTRO_L, #[D])
           end
       | (P.$ (OR, #[A,B]), E.INR N) =>
           let
             val D = proofFromEvidence (H, B, N)
           in
             D.$$ (OR_INTRO_R, #[D])
           end
       | (P.$ (IMPLIES, #[A,B]), M) =>
           let
             val z = V.named "z"
             val aptm = E.primary (E.AP (E.primary M, E.`` z))
             val D = proofFromEvidence (H @@ (z, A), B, aptm)
           in
             D.$$ (IMPLIES_INTRO A, #[D.\\ (z, D)])
           end
       (*| (P.$ (FORALL, #[zB]), M) =>
           let
             val (z, B) = P.unbind zB
             val aptm = E.primary (E.AP (M, E.`` z))
             val D = proofFromEvidence (H @@ (z, P.$$ (BASE, #[])), B, aptm)
           in
             D.$$ (FORALL_INTRO, #[D.\\ (z, D)])
           end*)
       | (P.$ (EXISTS, #[xB]), E.PAIR (N1, N2)) =>
           (case E.compute N1 of
                E.NEUTRAL (E.VAR d, _) =>
                  if P.eq (Context.lookup H d, P.$$ (BASE, #[])) then
                    let
                      val D = proofFromEvidence (H, P.// (xB, P.`` d), N2)
                    in
                      D.$$ (EXISTS_INTRO, #[D])
                    end
                  else
                    raise Fail "EXISTS"
              | _ => raise Nope)
       | _ => raise Fail ("welp " ^ P.toString prop)

  and eliminationMode (H : context, prop : P.t, R : E.neutral, v : V.t) : D.t =
    case P.out (Context.lookup H v) of
         P.$ (FALSE, #[]) => D.$$ (FALSE_ELIM prop, #[D.``v])
       | P.$ (EXISTS, #[xQ]) =>
           let
             val s = Context.fresh (H, V.named "s")
             val t = Context.fresh (H, V.named "t")
             val H' = Context.empty @@ (s, P.$$ (BASE, #[])) @@ (t, P.subst1 xQ (P.`` s))
             val H'' = Context.interposeAfter H (v, H')
             val pair = E.primary (E.PAIR (E.`` s, E.`` t))
             val D = proofFromEvidence (H'', prop, E.subst pair v (E.neutral R))
           in
             D.$$ (EXISTS_ELIM, #[D.\\ (s, D.\\ (t, D))])
           end
       | P.$ (BASE, _) => D.`` v (* TODO: wrong *)
       | _ => (case R of E.VAR x => D.`` x | _ => raise Nope)
end
