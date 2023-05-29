(* Unfold hint database to unfold notations.

   User defined operation type classes should be added to this, along with user
   defined operation type class instances.
 *)
Create HintDb overload.

(* The canonicalize hint database is used to restore the custom notations after
   a simpl/cbn operation, and to convert unknown signatures into known
   signatures. *)
Create HintDb canonicalize.

(* Restores the custom notations after a simpl/cbn. Also when there are
   multiple signatures for the same overload, this rewrites the signatures to
   use the most canonical one. For example, if an operator is overloaded for
   both a known first argument and unknown first argument, this tactic will
   convert the unknown overload into the known overload.

   Of course, lemmas have to be added to the canonicalize hint database for
   each of the overloads for this tactic to work.
 *)
Ltac canonicalize := autorewrite with canonicalize.
