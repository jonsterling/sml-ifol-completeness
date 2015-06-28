structure ProofFromEvidence = ProofFromEvidence
  (structure PropositionalLogic = PropositionalLogic
   structure Evidence = Evidence)

structure Test =
struct
  open ProofFromEvidence

  open EvidenceOps PropositionalOperators
  structure E = Evidence and V = Variable and P = Prop

  val ax = E.$$ (AX, #[])
  fun disj p q = P.$$ (OR, #[p,q])
  fun conj p q = P.$$ (AND, #[p,q])
  val falso = P.$$ (FALSE, #[])
  val tru = P.$$ (TRUE, #[])
  fun implies p q = P.$$ (IMPLIES, #[p,q])

  fun lam x e = E.$$ (LAM, #[E.\\ (x, e)])
  fun ap f x = E.$$ (AP, #[f,x])
  val freechoice = E.$$ (FREE_CHOICE, #[])

  fun test () =
  let
    val f = V.named "f"
    val x = V.named "x"
    val evd = lam f (lam x (ap freechoice (E.``x)))
    val prop = implies (implies tru tru) (implies tru (disj tru tru))
    val proof = proofFromEvidence (Context.empty, prop, evd)
      handle E.Malformed msg => raise Fail ("Malformed evidence: " ^ msg)
  in
    print "\n";
    print (P.toString prop ^ "\n");
    print (E.toString evd ^ "\n");
    print (D.toString proof ^ "\n");
    print "\n"
  end

  val _ =
    (test ();
     test ();
     test ())
end
