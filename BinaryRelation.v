Require Import Overload.Binary.
Require Import Coq.Relations.Relation_Definitions.

(* This file contains a definition of the Branch function with a type argument
  that is guaranteed to fit within a relation (if the overload is properly
  defined). The regular Binary.Branch instead has its own universe for its
  type argument. Other overloads could force the Binary.Branch type to be
  too large to fit in a relation. So the BinaryRelation.Branch is useful to
  ensure the overload continues to fit within a relation, even if other
  operators use large types. *)

(* The first parameter to relation has type
   Type@{Coq.Relations.Relation_Definitions.1}. However, because the universe
   name ends in dot number, it isn't a valid lexer token, and can't be directly
   specified. So instead declare a new universe, and use a throw away goal to
   force it to be equal to Coq.Relations.Relation_Definitions.1. *)
Universe relation.
Goal (relation : Type@{relation} -> Type) = relation.
Proof.
  reflexivity.
Qed.

Module Type TypeModule.
  Parameter P: Type@{relation}.
  Parameter T: P -> Type@{relation}.
End TypeModule.

Module Branch (Sig: SignatureTyp) (T: TypeModule).
  Module BacktrackBranch.
    Structure S (p: T.P) := {
      B: TaggedType@{relation};
      #[canonical=no] C: T.T p -> untag B -> Type;
    }.
    Arguments B {p}.
  End BacktrackBranch.
  Notation BacktrackBranch := BacktrackBranch.S.

  Definition no_match (B: TaggedType@{relation}): Type@{relation} := untag B.

  Definition A_branch (p: T.P) (sig2: BacktrackBranch p)
  : Sig.Any@{relation relation _} (T.T p) :=
  {|
    Sig.Any.B := no_match (sig2.(BacktrackBranch.B));
    Sig.Any.C := let '{| BacktrackBranch.C := C; |} := sig2 in C;
  |}.

  Canonical Structure fallback_branch (p: T.P) (sig2: Sig.Any (T.T p))
  : BacktrackBranch p :=
  {|
    BacktrackBranch.B := try_second sig2.(Sig.Any.B);
    BacktrackBranch.C := let '{| Sig.Any.C := C; |} := sig2 in C;
  |}.

  Structure S (p: T.P) := {
    B: Type@{relation};
    #[canonical=no] C: T.T p -> B -> Type;
  }.
  Arguments B {p}.

  Canonical Structure overload_branch (p: T.P) (sig2: S p)
  : BacktrackBranch p :=
  {|
    BacktrackBranch.B := try_first sig2.(B);
    BacktrackBranch.C := let '{| C := C; |} := sig2 in C;
  |}.
End Branch.
