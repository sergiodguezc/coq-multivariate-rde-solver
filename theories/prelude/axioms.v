
(** 
  * Axioms
  This file contains the axioms used in the development of the library.


  ** Functional extensionality 
  We assume the functional extensionality axiom, which states that two
  functions are equal if they give the same result for all arguments.
  This axiom is consistent with the calculus of inductive constructions.

  ** Proof irrelevance
  We assume the proof irrelevance axiom, which states that two proofs of the same
  proposition are equal. This axiom is consistent with the calculus of inductive
  constructions.

  ** Design choice
  These axioms simplify the treatment of equality for records and functions,
  offering a pragmatic alternative to the use of setoids and equivalence
  relations for quotient types. This approach facilitates concise proofs and
  straightforward reasoning within the Coq framework.
*) 

Require Export FunctionalExtensionality ProofIrrelevance EqdepFacts.
