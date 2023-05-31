Require Import Overload.SigId.

#[universes(polymorphic)]
Structure TaggedType@{U} := try_second {
  untag: Type@{U};
}.

Canonical Structure try_first (A: Type) := try_second A.

Module Type SignatureTyp.
  Module BacktrackBranch.
    #[universes(polymorphic)]
    Structure S@{A B C} := {
      A: TaggedType@{A};
      B: Type@{B};
      #[canonical=no] C: untag A -> B -> Type@{C};
    }.
    Arguments C : simpl never.
  End BacktrackBranch.
  Notation BacktrackBranch := BacktrackBranch.S.

  Module Any.
    Structure Any (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments B {A}.
    Arguments C {A}.
  End Any.
  Notation Any := Any.Any.

  Structure S := {
    A: Type;
    B: Type;
    #[canonical=no] C: A -> B -> Type;
  }.
End SignatureTyp.

Module Signature (Id: SigId) <: SignatureTyp.
  Module BacktrackBranch.
    #[universes(polymorphic)]
    Structure S@{A B C} := {
      A: TaggedType@{A};
      B: Type@{B};
      #[canonical=no] C: untag A -> B -> Type@{C};
    }.
    Arguments C : simpl never.
  End BacktrackBranch.
  Notation BacktrackBranch := BacktrackBranch.S.

  Module Any.
    Structure Any (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments B {A}.
    Arguments C {A}.
  End Any.
  Notation Any := Any.Any.

  Structure S := {
    A: Type;
    B: Type;
    #[canonical=no] C: A -> B -> Type;
  }.

  Canonical Structure fallback_branch (A: Type) (sig2: Any A)
  : BacktrackBranch :=
  {|
    BacktrackBranch.A := try_second A;
    BacktrackBranch.B := sig2.(Any.B);
    BacktrackBranch.C := let '{| Any.C := C; |} := sig2 in C;
  |}.

  Canonical Structure overload_branch (sig2: S)
  : BacktrackBranch :=
  {|
    BacktrackBranch.A := try_first sig2.(A);
    BacktrackBranch.B := sig2.(B);
    BacktrackBranch.C := let '{| C := C; |} := sig2 in C;
  |}.

  Definition make_A_branch (A: Type) (packed: Any A)
  : S :=
  let '{| Any.B := B; Any.C := C; |} := packed in
  {|
    A := A;
    B := B;
    C := C;
  |}.
  Arguments make_A_branch : simpl never.
End Signature.

Module Type TypeModule.
  Parameter P: Type.
  Parameter T: P -> Type.
End TypeModule.

Module Branch (Sig: SignatureTyp) (T: TypeModule).
  Module BacktrackBranch.
    Structure S (p: T.P) := {
      B: TaggedType;
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
    B: Type;
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
