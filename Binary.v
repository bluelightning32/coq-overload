#[universes(polymorphic)]
Structure TaggedType@{U} := try_second {
  untag: Type@{U};
}.

Canonical Structure try_first (A: Type) := try_second A.

Module Type SignatureTyp.
  Structure S := {
    A: TaggedType;
    B: Type;
    #[canonical=no] C: untag A -> B -> Type;
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

  Module Specific.
    Structure Specific := {
      A: Type;
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
  End Specific.
  Notation Specific := Specific.Specific.
End SignatureTyp.

Module Type Id.
End Id.

Module Signature (Id: Id) <: SignatureTyp.
  Structure S := {
    A: TaggedType;
    B: Type;
    #[canonical=no] C: untag A -> B -> Type;
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

  Module Specific.
    Structure Specific := {
      A: Type;
      #[canonical=no] B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
  End Specific.
  Notation Specific := Specific.Specific.

  Canonical Structure any (A: Type) (sig2: Any A)
  : S :=
  {|
    A := try_second A;
    B := sig2.(Any.B);
    C := let '{| Any.C := C; |} := sig2 in C;
  |}.

  Canonical Structure specific (sig2: Specific)
  : S :=
  {|
    A := try_first sig2.(Specific.A);
    B := sig2.(Specific.B);
    C := let '{| Specific.C := C; |} := sig2 in C;
  |}.

  Definition make_specific (A: Type) (packed: Any A)
  : Specific :=
  {|
    Specific.A := A;
    Specific.B := packed.(Any.B);
    Specific.C := let '{| Any.C := C; |} := packed in C;
  |}.
End Signature.

Module Type TypeModule.
  Parameter P: Type.
  Parameter T: P -> Type.
End TypeModule.

Module Overload (Sig: SignatureTyp) (T: TypeModule).
  Module Branch.
    Structure S (p: T.P) := {
      B: TaggedType;
      #[canonical=no] C: T.T p -> untag B -> Type;
    }.
    Arguments B {p}.
  End Branch.
  Notation Branch := Branch.S.

  Definition no_match (B: TaggedType): Type := untag B.

  Definition make_branch (p: T.P) (sig2: Branch p)
  : Sig.Any (T.T p) :=
  {|
    Sig.Any.B := no_match (sig2.(Branch.B));
    Sig.Any.C := let '{| Branch.C := C; |} := sig2 in C;
  |}.

  Canonical Structure fallback_branch (p: T.P) (sig2: Sig.Any (T.T p))
  : Branch p :=
  {|
    Branch.B := try_second sig2.(Sig.Any.B);
    Branch.C := let '{| Sig.Any.C := C; |} := sig2 in C;
  |}.

  Structure S (p: T.P) := {
    B: Type;
    #[canonical=no] C: T.T p -> B -> Type;
  }.
  Arguments B {p}.

  Canonical Structure overload_branch (p: T.P) (sig2: S p)
  : Branch p :=
  {|
    Branch.B := try_first sig2.(B);
    Branch.C := let '{| C := C; |} := sig2 in C;
  |}.
End Overload.
