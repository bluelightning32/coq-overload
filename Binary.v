Require Import Overload.SigId.

#[universes(polymorphic, cumulative)]
Structure TaggedType@{U} := try_second {
  untag: Type@{U};
}.

Canonical Structure try_first (A: Type) := try_second A.

Module Type SignatureTyp.
  Structure S := {
    A: Type;
    B: Type;
    #[canonical=no] C: A -> B -> Type;
  }.
  Arguments C : simpl never.

  Module Any.
    Structure Any (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments B {A}.
    Arguments C {A}.
  End Any.
  Notation Any := Any.Any.

End SignatureTyp.

Module Signature (Id: SigId) <: SignatureTyp.
  Structure S := {
    A: Type;
    B: Type;
    #[canonical=no] C: A -> B -> Type;
  }.
  Arguments C : simpl never.

  Module Any.
    Structure Any (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments B {A}.
    Arguments C {A}.
  End Any.
  Notation Any := Any.Any.

  Canonical Structure any (A: Type) (sig2: Any A)
  : S :=
  {|
    A := A;
    B := sig2.(Any.B);
    C := let '{| Any.C := C; |} := sig2 in C;
  |}.

  Definition make_A_branch (A: Type) (packed: Any A)
  : S :=
  let '{| Any.B := B; Any.C := C; |} := packed in
  {|
    A := A;
    B := B;
    C := C;
  |}.
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
