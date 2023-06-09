Require Import Overload.SigId.

#[universes(polymorphic)]
Structure TaggedType@{U} := try_second {
  untag: Type@{U};
}.

#[universes(polymorphic)]
Canonical Structure try_first@{U} (A: Type@{U}) := try_second@{U} A.

Module Type SignatureTyp.
  Module BacktrackBranch.
    #[universes(polymorphic, cumulative)]
    Structure S@{A B C} := {
      A: TaggedType@{A};
      B: Type@{B};
      #[canonical=no] C: untag A -> B -> Type@{C};
    }.
    Arguments C : simpl never.
  End BacktrackBranch.
  Notation BacktrackBranch := BacktrackBranch.S.

  Module Any.
    #[universes(polymorphic)]
    Structure Any@{A B C} (A: Type@{A}) := {
      B: Type@{B};
      #[canonical=no] C: A -> B -> Type@{C};
    }.
    Arguments B {A}.
    Arguments C {A}.
  End Any.
  Notation Any := Any.Any.

  #[universes(polymorphic)]
  Structure S@{A B C} := {
    A: Type@{A};
    B: Type@{B};
    #[canonical=no] C: A -> B -> Type@{C};
  }.
End SignatureTyp.

Module Signature (Id: SigId) <: SignatureTyp.
  Module BacktrackBranch.
    #[universes(polymorphic, cumulative)]
    Structure S@{A B C} := {
      A: TaggedType@{A};
      B: Type@{B};
      #[canonical=no] C: untag A -> B -> Type@{C};
    }.
    Arguments C : simpl never.
  End BacktrackBranch.
  Notation BacktrackBranch := BacktrackBranch.S.

  Module Any.
    #[universes(polymorphic)]
    Structure Any@{A B C} (A: Type@{A}) := {
      B: Type@{B};
      #[canonical=no] C: A -> B -> Type@{C};
    }.
    Arguments B {A}.
    Arguments C {A}.
  End Any.
  Notation Any := Any.Any.

  #[universes(polymorphic)]
  Structure S@{A B C} := {
    A: Type@{A};
    B: Type@{B};
    #[canonical=no] C: A -> B -> Type@{C};
  }.

  #[universes(polymorphic)]
  Canonical Structure fallback_branch@{A B C} (A: Type@{A})
                                              (sig2: Any@{A B C} A)
  : BacktrackBranch :=
  {|
    BacktrackBranch.A := try_second A;
    BacktrackBranch.B := sig2.(Any.B);
    BacktrackBranch.C := let '{| Any.C := C; |} := sig2 in C;
  |}.

  #[universes(polymorphic)]
  Canonical Structure overload_branch@{A B C} (sig2: S@{A B C})
  : BacktrackBranch@{A B C} :=
  {|
    BacktrackBranch.A := try_first sig2.(A);
    BacktrackBranch.B := sig2.(B);
    BacktrackBranch.C := let '{| C := C; |} := sig2 in C;
  |}.

  #[universes(polymorphic)]
  Definition make_A_branch@{A B C} (A: Type@{A}) (packed: Any@{A B C} A)
  : S@{A B C} :=
  let '{| Any.B := B; Any.C := C; |} := packed in
  {|
    A := A;
    B := B;
    C := C;
  |}.
  Arguments make_A_branch : simpl never.
End Signature.

(* Declare these universes outside of the Branch functor for easier access.
   Even if they were declared within the functor, they would have the same
   value for all instances of the functor. *)
Universe A.
Universe B.

Module Type TypeModule.
  Parameter P: Type@{A}.
  Parameter T: P -> Type@{A}.
End TypeModule.

Module Branch (Sig: SignatureTyp) (T: TypeModule).
  Module BacktrackBranch.
    Structure S (p: T.P) := {
      B: TaggedType@{B};
      #[canonical=no] C: T.T p -> untag B -> Type;
    }.
    Arguments B {p}.
  End BacktrackBranch.
  Notation BacktrackBranch := BacktrackBranch.S.

  Definition no_match (B: TaggedType): Type := untag B.

  Definition A_branch (p: T.P) (sig2: BacktrackBranch p)
  : Sig.Any (T.T p) :=
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
    B: Type@{B};
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
