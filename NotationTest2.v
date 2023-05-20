Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.
Require Import Constructive_sets.

(* Passes *)
Module TypeClassesTagged.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  #[universes(polymorphic)]
  Structure TaggedType@{U} := try_second {
    untag: Type@{U};
  }.

  Canonical Structure try_first (A: Type) := try_second A.

  Module Type SignatureId.
  End SignatureId.

  Module Type BinarySignatureType.
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
  End BinarySignatureType.

  Module BinarySignature (Id: SignatureId) <: BinarySignatureType.
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
  End BinarySignature.

  Module Type TypeModule.
    Parameter P: Type.
    #[universes(polymorphic)]
    Parameter T@{U}: P -> Type@{U}.
  End TypeModule.
  Print Module Type TypeModule.

  Module BinaryOverload (Sig: BinarySignatureType) (T: TypeModule).

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
  End BinaryOverload.

  Module LEId: SignatureId.
  End LEId.
  Module LESignature := BinarySignature LEId.
  Export (canonicals) LESignature.

  Class LEOperation (r: LESignature.S) :=
  le: forall (a: untag r.(LESignature.A)) (b: r.(LESignature.B)),
      (let '{| LESignature.C := C; |} := r
         return (untag r.(LESignature.A) -> r.(LESignature.B) -> Type) in C) a b.

  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  Module NatWrapper<: TypeModule.
    Definition P := unit.
    #[universes(polymorphic)]
    Definition T@{U} (_: unit) := nat.
  End NatWrapper.

  Module NatLESignature := BinaryOverload LESignature NatWrapper.
  Export (canonicals) NatLESignature.

  Canonical Structure nat_le_branch (sig2: NatLESignature.Branch tt)
  : LESignature.Specific :=
  LESignature.make_specific nat (NatLESignature.make_branch tt sig2).

  #[global]
  Canonical Structure nat_nat_le_signature: NatLESignature.S tt :=
  {|
    NatLESignature.B := nat;
    NatLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance nat_le: LEOperation _ := Nat.le.

  Module ZWrapper<: TypeModule.
    Definition P := unit.
    #[universes(polymorphic)]
    Definition T@{U} (_: unit) := Z.
  End ZWrapper.

  Module ZLESignature := BinaryOverload LESignature ZWrapper.
  Export (canonicals) ZLESignature.

  Canonical Structure Z_le_branch (sig2: ZLESignature.Branch tt)
  : LESignature.Specific :=
  LESignature.make_specific Z (ZLESignature.make_branch tt sig2).

  #[global]
  Canonical Structure Z_Z_le_signature: ZLESignature.S tt :=
  {|
    ZLESignature.B := Z;
    ZLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance Z_le: LEOperation _ := Z.le.

  #[global]
  Canonical Structure Z_nat_le_signature: ZLESignature.S tt :=
  {|
    ZLESignature.B := nat;
    ZLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation _ :=
  fun a b => (a <= Z.of_nat b)%Z.

  (* If the first argument is a relation, the second argument must also be a
     relation. This restriction is done so that an unknown second argument is
     unified to a relation. *)
  #[global]
  Canonical Structure relation_relation_le_signature (A: Type)
  : LESignature.Specific :=
  {|
    LESignature.Specific.A := relation A;
    LESignature.Specific.B := relation A;
    LESignature.Specific.C _ _:= Prop;
  |}.

  Definition relation_no_match := try_second.

  (* If the first argument is unknown and the second is a relation, then the
     first is unified to be a relation. *)
  Canonical Structure unknown_relation_le_signature (A: Type)
  : LESignature.S :=
  {|
    LESignature.A := relation_no_match (relation A);
    LESignature.B := relation A;
    LESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance relation_relation_le (A: Type)
  : LEOperation _ :=
  fun (R S: relation A) => RelationClasses.subrelation R S.

  #[global]
  #[universes(polymorphic)]
  Canonical Structure crelation_crelation_le_signature@{A1 A2 B C}
    (A: Type@{A1})
  : LESignature.Specific :=
  {|
    LESignature.Specific.A := crelation@{A1 A2} A;
    LESignature.Specific.B := crelation@{A1 A2} A;
    LESignature.Specific.C _ _ := Type@{C};
  |}.

  Definition crelation_no_match := try_second.

  #[global]
  #[universes(polymorphic)]
  Canonical Structure unknown_crelation_le_signature@{A1 A2 B C}
    (A: Type@{A1})
  : LESignature.S :=
  {|
    LESignature.A := crelation_no_match (crelation@{A1 A2} A);
    LESignature.B := crelation@{A1 A2} A;
    LESignature.C _ _ := Type@{C};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output CRelation} (A: Type@{Input})
  : LEOperation
      (LESignature.specific (crelation_crelation_le_signature@{Input Output
                                                               CRelation
                                                               Output}
                               A)) :=
  fun (R S: crelation@{Input Output} A) =>
    CRelationClasses.subrelation@{Input Output Output} R S.

  Definition compare_nats (a b: nat) := a <== b.

  Definition compare_ints (a b: Z) := a <== b.

  Definition compare_Z_nat (a: Z) (b: nat) := a <== b.

  Definition compare_relations (A: Type) (R S: relation A) :=
    R <== S.

  Definition compare_crelations (A: Type) (R: crelation A) S :=
    R <== S.

  Definition relations_reflexive (A: Type)
  : forall (R: relation A), R <== R := fun R x y Rxy => Rxy.

  Definition crelations_reflexive (A: Type)
  : forall (R: crelation A), R <== R := fun R x y Rxy => Rxy.

  Definition empty_relation (A: Type) : relation A := fun x y => False.

  (* Tests that the type of R can be inferred when it is on the left side of
     _ <== _ . *)
  Theorem R_le_empty (A: Type) R
    : R <== empty_relation A ->
      RelationClasses.relation_equivalence R (empty_relation A).
  Proof.
    intros Hempty.
    eapply RelationClasses.antisymmetry.
    - apply Hempty.
    - intros x y Hxy.
      destruct Hxy.
  Qed.

  (* Tests that the type of R can be inferred when it is on the right side of
     _ <== _ . *)
  Theorem empty_le_r (A: Type) R
    : empty_relation A <== R.
  Proof.
    intros x y Hxy.
    destruct Hxy.
  Qed.

  (* Passes *)
  Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    cbn.
    match goal with
    | |- context [a <== b] => idtac
    end.
    reflexivity.
  Qed.

  Module AddSignature.
    Structure AddSignature := {
      A: TaggedType;
      B: Type;
      #[canonical=no] C: untag A -> B -> Type;
    }.
    Arguments C : simpl never.
  End AddSignature.
  Export AddSignature(AddSignature).

  Module AnyAddSignature.
    Structure AnyAddSignature (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments B {A}.
    Arguments C {A}.
  End AnyAddSignature.
  Export AnyAddSignature(AnyAddSignature).

  Canonical Structure any_add_signature (A: Type) (sig2: AnyAddSignature A)
  : AddSignature :=
  {|
    AddSignature.A := try_second A;
    AddSignature.B := sig2.(AnyAddSignature.B);
    AddSignature.C := let '{| AnyAddSignature.C := C; |} := sig2 in C;
  |}.

  Module SpecificAddSignature.
    Structure SpecificAddSignature := {
      A: Type;
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
  End SpecificAddSignature.
  Export SpecificAddSignature(SpecificAddSignature).

  Canonical Structure specific_add_signature (sig2: SpecificAddSignature)
  : AddSignature :=
  {|
    AddSignature.A := try_first sig2.(SpecificAddSignature.A);
    AddSignature.B := sig2.(SpecificAddSignature.B);
    AddSignature.C := let '{| SpecificAddSignature.C := C; |} := sig2 in C;
  |}.

  Class AddOperation (r: AddSignature) :=
  add: forall (a: untag r.(AddSignature.A)) (b: r.(AddSignature.B)),
       (let '{| AddSignature.C := C; |} := r
            return untag r.(AddSignature.A) -> r.(AddSignature.B) -> Type in C) a b.
  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Module NatAddSignature.
    Structure NatAddSignature := {
      B: TaggedType;
      #[canonical=no] C: nat -> untag B -> Type;
    }.
  End NatAddSignature.
  Export NatAddSignature(NatAddSignature).

  (* TODO *)
  Definition nat_no_match (B: TaggedType): Type := untag B.

  Canonical Structure nat_add_signature (sig2: NatAddSignature)
  : SpecificAddSignature :=
  {|
    SpecificAddSignature.A := nat;
    SpecificAddSignature.B := nat_no_match (sig2.(NatAddSignature.B));
    SpecificAddSignature.C := let '{| NatAddSignature.C := C; |} := sig2 in C;
  |}.

  Canonical Structure nat_any_add_branch (sig2: AnyAddSignature nat)
  : NatAddSignature :=
  {|
    NatAddSignature.B := try_second sig2.(AnyAddSignature.B);
    NatAddSignature.C := let '{| AnyAddSignature.C := C; |} := sig2 in C;
  |}.

  Module NatSpecificAddSignature.
    Structure NatSpecificAddSignature := {
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
    }.
  End NatSpecificAddSignature.
  Export NatSpecificAddSignature(NatSpecificAddSignature).

  Canonical Structure nat_specific_add_signature (sig2: NatSpecificAddSignature)
  : NatAddSignature :=
  {|
    NatAddSignature.B := try_first sig2.(NatSpecificAddSignature.B);
    NatAddSignature.C := let '{| NatSpecificAddSignature.C := C; |} := sig2 in C;
  |}.

  #[global]
  Canonical Structure nat_nat_specific_add_signature: NatSpecificAddSignature :=
  {|
    NatSpecificAddSignature.B := nat;
    NatSpecificAddSignature.C _ _ := nat;
  |}.

  #[export]
  Instance nat_add: AddOperation _ := Nat.add.

  Module ZAddSignature.
    Structure ZAddSignature := {
      B: TaggedType;
      #[canonical=no] C: Z -> untag B -> Type;
    }.
  End ZAddSignature.
  Export ZAddSignature(ZAddSignature).

  (* TODO *)
  Definition Z_no_match (B: TaggedType): Type := untag B.

  Canonical Structure Z_add_signature (sig2: ZAddSignature)
  : SpecificAddSignature :=
  {|
    SpecificAddSignature.A := Z;
    SpecificAddSignature.B := Z_no_match (sig2.(ZAddSignature.B));
    SpecificAddSignature.C := let '{| ZAddSignature.C := C; |} := sig2 in C;
  |}.

  Canonical Structure Z_any_add_branch (sig2: AnyAddSignature Z)
  : ZAddSignature :=
  {|
    ZAddSignature.B := try_second sig2.(AnyAddSignature.B);
    ZAddSignature.C := let '{| AnyAddSignature.C := C; |} := sig2 in C;
  |}.

  Module ZSpecificAddSignature.
    Structure ZSpecificAddSignature := {
      B: Type;
      #[canonical=no] C: Z -> B -> Type;
    }.
  End ZSpecificAddSignature.
  Export ZSpecificAddSignature(ZSpecificAddSignature).

  Canonical Structure Z_specific_add_signature (sig2: ZSpecificAddSignature)
  : ZAddSignature :=
  {|
    ZAddSignature.B := try_first sig2.(ZSpecificAddSignature.B);
    ZAddSignature.C := let '{| ZSpecificAddSignature.C := C; |} := sig2 in C;
  |}.

  #[global]
  Canonical Structure Z_Z_specific_add_signature: ZSpecificAddSignature :=
  {|
    ZSpecificAddSignature.B := Z;
    ZSpecificAddSignature.C _ _ := Z;
  |}.

  #[export]
  Instance Z_add: AddOperation _ := Z.add.

  #[global]
  Canonical Structure Z_nat_specific_add_signature: ZSpecificAddSignature :=
  {|
    ZSpecificAddSignature.B := nat;
    ZSpecificAddSignature.C _ _ := Z;
  |}.

  #[export]
  Instance Z_nat_add: AddOperation _ :=
  fun a b => (a + Z.of_nat b)%Z.

  #[global]
  Canonical Structure nat_Z_add_signature: NatSpecificAddSignature :=
  {|
    NatSpecificAddSignature.B := Z;
    NatSpecificAddSignature.C _ _ := Z;
  |}.

  #[export]
  Instance nat_Z_add: AddOperation _ :=
  fun a b => (Z.of_nat a + b)%Z.

  Module TypeAddSignature.
    Universe B C.
    #[universes(polymorphic)]
    Structure TypeAddSignature@{U} := {
      B: TaggedType@{B};
      #[canonical=no] C: Type@{U} -> untag B -> Type@{C};
    }.
  End TypeAddSignature.
  Export TypeAddSignature(TypeAddSignature).

  Definition Type_no_match (B: TaggedType): Type := untag B.

  #[universes(polymorphic)]
  Canonical Structure Type_add_signature@{U} (sig2: TypeAddSignature)
  : SpecificAddSignature :=
  {|
    SpecificAddSignature.A := Type@{U};
    SpecificAddSignature.B := Type_no_match (sig2.(TypeAddSignature.B));
    SpecificAddSignature.C := let '{| TypeAddSignature.C := C; |} := sig2 in C;
  |}.

  #[universes(polymorphic)]
  Canonical Structure Type_any_add_branch@{U} (sig2: AnyAddSignature Type@{U})
  : TypeAddSignature :=
  {|
    TypeAddSignature.B := try_second sig2.(AnyAddSignature.B);
    TypeAddSignature.C := let '{| AnyAddSignature.C := C; |} := sig2 in C;
  |}.

  Module TypeSpecificAddSignature.
    #[universes(polymorphic)]
    Structure TypeSpecificAddSignature@{U} := {
      B: Type@{TypeAddSignature.B};
      #[canonical=no] C: Type@{U} -> B -> Type@{TypeAddSignature.C};
    }.
  End TypeSpecificAddSignature.
  Export TypeSpecificAddSignature(TypeSpecificAddSignature).

  #[universes(polymorphic)]
  Canonical Structure Type_specific_add_signature@{U} (sig2: TypeSpecificAddSignature@{U})
  : TypeAddSignature :=
  {|
    TypeAddSignature.B := try_first sig2.(TypeSpecificAddSignature.B);
    TypeAddSignature.C := let '{| TypeSpecificAddSignature.C := C; |} := sig2 in C;
  |}.

  Set Warnings "-redundant-canonical-projection".
  #[global]
  Canonical Structure set_add_signature (sig2: TypeAddSignature@{Set})
  : SpecificAddSignature := Type_add_signature@{Set} sig2.
  Set Warnings "".

  #[global]
  #[universes(polymorphic)]
  Canonical Structure Type_Type_add_signature@{U}
  : TypeSpecificAddSignature@{U} :=
  {|
    TypeSpecificAddSignature.B := Type@{U};
    TypeSpecificAddSignature.C (A B: Type@{U}) := Type@{U};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance type_type_add@{U} : AddOperation _ :=
  fun (A: Type@{U}) (B: Type@{U}) => (A + B)%type.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

  Definition add_nat_Z (a: nat) (b: Z) := a [+] b.

  (* Passes *)
  Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B) n.

  #[universes(polymorphic)]
  Definition swap_sum_type@{U} {A B: Type@{U}} (s: A [+] B) : B [+] A :=
  match s with
  | inl a => inr a
  | inr b => inl b
  end.

  Definition small_id (T: Type@{Set}) (v: T): T := v.

  Definition id_swap {A B: Type@{Set}} (s: A [+] B) : B [+] A :=
  small_id _ (swap_sum_type s).

  (* Passes *)
  Theorem cbn_keeps_add_notation: forall (a b: nat), a [+] b = a [+] b.
  Proof.
    intros.
    cbn.
    match goal with
    | |- context [a [+] b] => idtac
    end.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_simplifies_addition: forall (a b: nat), S a [+] b = S (a [+] b).
  Proof.
    intros.
    progress cbn.
    (* This makes sure that the implicit parameters matches the default ones. *)
    progress change (S (a [+] b)) with (S a [+] b).
    reflexivity.
  Qed.

  Theorem nat_add_comm: forall (m n: nat), m [+] n = n [+] m.
  Proof.
    apply Nat.add_comm.
  Qed.

  (* Passes *)
  Theorem nat_add_0_r : forall (n: nat), n [+] 0 = n.
  Proof.
    intros.
    rewrite nat_add_comm.
    reflexivity.
  Qed.

  Theorem nat_le_reflexive: forall (n: nat), n <== n.
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem nat_plus_0_r_le : forall (n: nat), n [+] 0 <== n.
  Proof.
    intros.
    rewrite Nat.add_0_r.
    reflexivity.
  Qed.

  Module ConsId : SignatureId.
  End ConsId.
  Module ConsSignature := BinarySignature ConsId.
  Export (canonicals) ConsSignature.

  Class ConsOperation (r: ConsSignature.S) :=
  cons: forall (a: untag r.(ConsSignature.A)) (b: r.(ConsSignature.B)),
        (let '{| ConsSignature.C := C; |} := r
             return untag r.(ConsSignature.A) -> r.(ConsSignature.B) -> Type
             in C)
          a b.
  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  Canonical Structure any_list_cons_signature (A: Type): ConsSignature.Any A := {|
    ConsSignature.Any.B := list A;
    ConsSignature.Any.C _ _ := list A;
  |}.

  Definition list_no_match := try_second.

  Canonical Structure list_cons_signature (A: Type)
  : ConsSignature.S :=
  {|
    ConsSignature.A := list_no_match A;
    ConsSignature.B := list A;
    ConsSignature.C _ _ := list A;
  |}.

  #[export]
  Instance any_list_cons (A: Type)
  : ConsOperation (list_cons_signature A) :=
  List.cons.

  Module NatConsSignature.
    Structure NatConsSignature := {
      B: TaggedType;
      #[canonical=no] C: nat -> untag B -> Type;
    }.
  End NatConsSignature.
  Export NatConsSignature(NatConsSignature).

  Canonical Structure nat_cons_signature (op2: NatConsSignature)
  : ConsSignature.Specific :=
  {|
    ConsSignature.Specific.A := nat;
    ConsSignature.Specific.C := op2.(NatConsSignature.C);
  |}.

  Canonical Structure nat_any_cons_branch (op2: ConsSignature.Any nat)
  : NatConsSignature :=
  {|
    NatConsSignature.B := try_second op2.(ConsSignature.Any.B);
    NatConsSignature.C := op2.(ConsSignature.Any.C);
  |}.

  Module NatSpecificConsSignature.
    Structure NatSpecificConsSignature := {
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
    }.
  End NatSpecificConsSignature.
  Export NatSpecificConsSignature(NatSpecificConsSignature).

  Canonical Structure nat_specific_cons_signature (op2: NatSpecificConsSignature)
  : NatConsSignature :=
  {|
    NatConsSignature.B := try_first op2.(NatSpecificConsSignature.B);
    NatConsSignature.C := op2.(NatSpecificConsSignature.C);
  |}.

  Canonical Structure nat_list_Z_cons_signature
  : NatSpecificConsSignature :=
  {|
    NatSpecificConsSignature.B := list Z;
    NatSpecificConsSignature.C _ _ := list Z;
  |}.

  #[export]
  Instance nat_list_Z_cons
  : ConsOperation (ConsSignature.specific (nat_cons_signature (nat_specific_cons_signature _))) :=
  fun a => List.cons (Z.of_nat a).

  Canonical Structure any_Ensemble_cons_signature (A: Type): ConsSignature.Any A := {|
    ConsSignature.Any.B := Ensemble A;
    ConsSignature.Any.C _ _ := Ensemble A;
  |}.

  Definition Ensemble_no_match (A: Type) := A.

  Canonical Structure Ensemble_cons_signature (A: Type)
  : ConsSignature.Specific :=
  {|
    ConsSignature.Specific.A := Ensemble_no_match A;
    ConsSignature.Specific.B := Ensemble A;
    ConsSignature.Specific.C _ _ := Ensemble A;
  |}.

  #[export]
  Instance any_Ensemble_cons (A: Type)
  : ConsOperation (ConsSignature.specific (Ensemble_cons_signature A)) :=
  fun a e => Add _ e a.

  Theorem list_in_cons : forall A (a: A) (l: list A), List.In a (a [::] l).
  Proof.
    intros.
    match goal with
    | |- context [a [::] l] => idtac
    end.
    cbn.
    left.
    reflexivity.
  Qed.

  Theorem list_in_cons' : forall A a (l: list A), List.In a (a [::] l).
  Proof.
    intros.
    match goal with
    | |- context [a [::] l] => idtac
    end.
    cbn.
    left.
    reflexivity.
  Qed.

  Theorem list_in_cons_nat_Z
  : forall (a: nat) (l: list Z), List.In (Z.of_nat a) (a [::] l).
  Proof.
    intros.
    match goal with
    | |- context [a [::] l] => idtac
    end.
    cbn.
    left.
    reflexivity.
  Qed.

  Theorem list_in_cons_nat_nat
  : forall (a: nat) (l: list nat), List.In a (a [::] l).
  Proof.
    intros.
    match goal with
    | |- context [a [::] l] => idtac
    end.
    cbn.
    left.
    reflexivity.
  Qed.

  Theorem ensemble_in_cons
  : forall A (a: A) (e: Ensemble A), Ensembles.In _ (a [::] e) a.
  Proof.
    intros.
    match goal with
    | |- context [a [::] e] => idtac
    end.
    apply Add_intro2.
  Qed.

  Theorem ensemble_in_cons'
  : forall A a (e: Ensemble A), Ensembles.In _ (a [::] e) a.
  Proof.
    intros.
    match goal with
    | |- context [a [::] e] => idtac
    end.
    apply Add_intro2.
  Qed.

  Theorem cbn_keeps_cons_notation: forall A a (l: list A), a [::] l = a [::] l.
  Proof.
    intros.
    cbn.
    match goal with
    | |- context [a [::] l] => idtac
    end.
    reflexivity.
  Qed.

  Theorem cbn_keeps_cons_notation': forall A (a: A) (l: list A), a [::] l = a [::] l.
  Proof.
    intros.
    cbn.
    match goal with
    | |- context [a [::] l] => idtac
    end.
    reflexivity.
  Qed.

  (* Declare nat_le as a PreOrder, which means it is reflexive and transitive.
     *)
  #[global]
  Program Instance nat_le_preorder: PreOrder nat_le.
  Next Obligation.
    unfold nat_le.
    eauto.
  Qed.
  Next Obligation.
    unfold nat_le.
    eauto with arith.
  Qed.
  Fail Next Obligation.

  (* Since nat_le was declared as a PreOrder, that means it is also Reflexive.
     However, the typeclass search fails because nat_le is a LEOperation
     instead of a relation. *)
  Fail Definition nat_refl' := (fun r : Reflexive nat_le => r) _.

  (* Declaring LEOperation as transparent to the typeclasses system allows it
     to unfold LEOperation and see that it matches the definition of a relation.
     *)
  #[export]
  Typeclasses Transparent LEOperation.

  (* Now the type class system can see that nat_le has the same type as a
     relation. So now it can cast nat_le_preorder from an instance of PreOrder
     into an instance of Reflexive. *)
  Succeed Definition nat_refl' := (fun r : Reflexive nat_le => r) _.

  Goal forall m n, S m <== S n -> m <== n.
  Proof.
    (* This fails because the auto hints for <= don't exactly match <==. *)
    Fail progress auto with arith.
  Abort.

  (* This tells auto to unfold nat_le and le when testing whether a hint
   * matches the goal. Auto only unfolds to determine if a hint can be applied.
   * The result from auto is never unfolded. autounfold can be used if one
   * wants these functions to be unfold in the goal.
   *)
  #[export]
  Hint Unfold nat_le le : core.

  Goal forall m n, S m <== S n -> m <== n.
  Proof.
    (* Now auto works because it can see that <== is <=. *)
    auto with arith.
  Qed.
End TypeClassesTagged.
