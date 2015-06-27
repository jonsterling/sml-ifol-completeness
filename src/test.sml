structure ProofFromEvidence = ProofFromEvidence
  (structure PropositionalLogic = PropositionalLogic
   structure Evidence = Evidence)

structure Test =
struct
  open ProofFromEvidence

  open EvidenceOps PropositionalOperators
  structure E = Evidence and V = Variable and P = Prop

  val x = V.named "x"
  val ax = E.$$ (AX, #[])
  fun conj p q = P.$$ (AND, #[p,q])
  val falso = P.$$ (FALSE, #[])
  val tru = P.$$ (TRUE, #[])

  val evd = E.$$ (LAM, #[E.\\ (x, E.``x)])
  val prop = P.$$ (IMPLIES, #[falso, conj falso tru])
  val proof = proofFromEvidence (Context.empty, prop, evd)

  val _ = print "\n"
  val _ = print (P.toString prop ^ "\n")
  val _ = print (E.toString evd ^ "\n")
  val _ = print (D.toString proof ^ "\n")
  val _ = print "\n"
end
