Require Import ZArith.
Require Import List.

Module NativeNotations.
  Definition add_nats (a b: nat) := a + b.

  Definition add_ints (a b: Z) := (a + b)%Z.

  Definition add_int_nat (a: Z) (b: nat) := (a + Z.of_nat b)%Z.

  Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A + B)%type n.

  Definition swap_sum_type {A B: Type} (s: A + B) : B + A :=
  match s with
  | inl a => inr a
  | inr b => inl b
  end.
End NativeNotations.

(* Fails the cbn test. *)
Module TypeClasses1.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class AddOperation (A B: Type) := {
    result: Type;
    add: A -> B -> result;
  }.
  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Universe OperationInput.
  #[universes(polymorphic)]
  Class TypeAddOperation@{Output} (A: Type@{OperationInput}) (B: Type@{OperationInput}) := {
    add_type: A -> B -> Type@{Output};
  }.
  Infix "[+]" := add_type (at level 50, left associativity) : type_scope.

  #[export]
  Instance nat_add: AddOperation nat nat := {|
    result:= nat;
    add a b := (a + b)%nat;
  |}.

  #[export]
  Instance int_add: AddOperation Z Z := {|
    result:= Z;
    add a b := (a + b)%Z;
  |}.

  #[export]
  Instance int_nat_add: AddOperation Z nat := {|
    result:= Z;
    add a b := (a + Z.of_nat b)%Z;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}: TypeAddOperation@{U} Type@{U} Type@{U} := {|
    add_type (A: Type@{U}) (B: Type@{U}) := (A + B)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_int_nat (a: Z) (b: nat) := a [+] b.

  Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B)%type n.

  #[universes(polymorphic)]
  Definition swap_sum_type@{U} {A B: Type@{U}} (s: A [+] B) : B [+] A :=
  match s with
  | inl a => inr a
  | inr b => inl b
  end.

  Definition small_id (T: Type@{Set}) (v: T): T := v.

  Definition id_swap {A B: Type@{Set}} (s: A [+] B) : B [+] A :=
  small_id _ (swap_sum_type s).

  (* Fails this test because the operator was removed by cbn. *)
  Theorem cbn_keeps_notation: forall (a b: nat), a [+] b = a [+] b.
  Proof.
    intros.
    (* Ideally this would fail. *)
    Succeed progress cbn.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_simplifies_addition: forall (a b: nat), S a [+] b = S (a [+] b).
  Proof.
    intros.
    (* Ideally this would pass. *)
    progress cbn.
    reflexivity.
  Qed.
End TypeClasses1.

(* Fails the cbn test. *)
Module TypeClasses2.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class AddOperation (A B C: Type) := {
    add: A -> B -> C;
  }.
  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Universe OperationInput.
  #[universes(polymorphic)]
  Class TypeAddOperation@{Output} (A: Type@{OperationInput}) (B: Type@{OperationInput}) := {
    add_type: A -> B -> Type@{Output};
  }.
  Infix "[+]" := add_type (at level 50, left associativity) : type_scope.

  #[export]
  Instance nat_add: AddOperation nat nat nat := {|
    add := Nat.add;
  |}.

  #[export]
  Instance int_add: AddOperation Z Z Z := {|
    add a b := (a + b)%Z;
  |}.

  #[export]
  Instance int_nat_add: AddOperation Z nat Z := {|
    add a b := (a + Z.of_nat b)%Z;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}: TypeAddOperation@{U} Type@{U} Type@{U} := {|
    add_type (A: Type@{U}) (B: Type@{U}) := (A + B)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_int_nat (a: Z) (b: nat) := a [+] b.

  Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B)%type n.

  #[universes(polymorphic)]
  Definition swap_sum_type@{U} {A B: Type@{U}} (s: A [+] B) : B [+] A :=
  match s with
  | inl a => inr a
  | inr b => inl b
  end.

  Definition small_id (T: Type@{Set}) (v: T): T := v.

  Definition id_swap {A B: Type@{Set}} (s: A [+] B) : B [+] A :=
  small_id _ (swap_sum_type s).

  (* Fails this test because the operator was removed by cbn. *)
  Theorem cbn_keeps_notation: forall (a b: nat), a [+] b = a [+] b.
  Proof.
    intros.
    (* Ideally this would fail. *)
    Succeed progress cbn.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_simplifies_addition: forall (a b: nat), S a [+] b = S (a [+] b).
  Proof.
    intros.
    (* Ideally this would pass. *)
    progress cbn.
    reflexivity.
  Qed.
End TypeClasses2.

(* Passes tests. *)
Module TypeClasses3.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class AddOperation (A B C: Type) := add: A -> B -> C.
  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Universe OperationInput.
  #[universes(polymorphic)]
  Class TypeAddOperation@{Output} (A: Type@{OperationInput}) (B: Type@{OperationInput}) :=
  add_type: A -> B -> Type@{Output}.
  Infix "[+]" := add_type (at level 50, left associativity) : type_scope.

  #[export]
  Instance nat_add: AddOperation nat nat nat := fun a b => (a + b)%nat.

  #[export]
  Instance int_add: AddOperation Z Z Z := fun a b => (a + b)%Z.

  #[export]
  Instance int_nat_add: AddOperation Z nat Z := fun a b => (a + Z.of_nat b)%Z.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}: TypeAddOperation@{U} Type@{U} Type@{U} :=
  fun (A: Type@{U}) (B: Type@{U}) => (A + B)%type.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_int_nat (a: Z) (b: nat) := a [+] b.

  Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B)%type n.

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
  Theorem cbn_keeps_notation: forall (a b: nat), a [+] b = a [+] b.
  Proof.
    intros.
    (* Ideally this would fail. *)
    Fail progress cbn.
    reflexivity.
  Qed.

  (* Half passes. The match is simplified, but without restoring the resulting notation. *)
  Theorem cbn_simplifies_addition: forall (a b: nat), S a [+] b = S (a [+] b).
  Proof.
    intros.
    cbn.
    reflexivity.
  Qed.
End TypeClasses3.

(* Fails cbn_keeps_notation. *)
Module CanonicalStructures.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Module AddOperation.
    Structure Op (B: Type) (C: Type) := {
      A: Type;
      #[canonical=no] add: A -> B -> C;
    }.
  End AddOperation.

  Definition op {B C: Type} {o: AddOperation.Op B C} := o.(AddOperation.add B C).

  Infix "[+]" := op (at level 50, left associativity) : operation_scope.

  Module NatAddOperation.
    Structure Op := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] add: nat -> B -> C;
    }.
  End NatAddOperation.
  Canonical Structure nat_add (op2: NatAddOperation.Op): AddOperation.Op op2.(NatAddOperation.B) op2.(NatAddOperation.C) := {|
    AddOperation.add:= op2.(NatAddOperation.add);
  |}.

  Canonical Structure nat_nat_add: NatAddOperation.Op := {|
    NatAddOperation.add:= Nat.add;
  |}.

  Module ZAddOperation.
    Structure Op := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] add: Z -> B -> C;
    }.
  End ZAddOperation.

  Canonical Structure Z_add (op2: ZAddOperation.Op): AddOperation.Op op2.(ZAddOperation.B) op2.(ZAddOperation.C) := {|
    AddOperation.add:= op2.(ZAddOperation.add);
  |}.

  Canonical Structure Z_Z_add: ZAddOperation.Op := {|
    ZAddOperation.add:= Z.add;
  |}.

  Canonical Structure Z_nat_add: ZAddOperation.Op := {|
    ZAddOperation.add a b := (a + Z.of_nat b)%Z;
  |}.

  Module TypeAddOperation.
    Universe B.
    Universe C.
    #[universes(polymorphic)]
    Structure Op@{U} := {
      B: Type@{B};
      #[canonical=no] C: Type@{C};
      #[canonical=no] add: Type@{U} -> B -> C;
    }.
  End TypeAddOperation.

  #[universes(polymorphic)]
  Canonical Structure type_add@{U} (op2: TypeAddOperation.Op@{U}): AddOperation.Op op2.(TypeAddOperation.B) op2.(TypeAddOperation.C) := {|
    AddOperation.A := Type@{U};
    AddOperation.add:= op2.(TypeAddOperation.add);
  |}.

  Canonical Structure set_add (op2: TypeAddOperation.Op@{Set}): AddOperation.Op op2.(TypeAddOperation.B) op2.(TypeAddOperation.C) := {|
    AddOperation.A := Type@{Set};
    AddOperation.add:= op2.(TypeAddOperation.add);
  |}.

  #[universes(polymorphic)]
  Canonical Structure type_type_add@{U}: TypeAddOperation.Op@{U} := {|
    TypeAddOperation.B := Type@{U};
    TypeAddOperation.C := Type@{U};
    TypeAddOperation.add a b:= (a + b)%type;
  |}.

  Canonical Structure set_set_add@{U}: TypeAddOperation.Op@{Set} := {|
    TypeAddOperation.B := Set;
    TypeAddOperation.C := Set;
    TypeAddOperation.add a b:= (a + b)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_int_nat (a: Z) (b: nat) := a [+] b.

  Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B)%type n.

  #[universes(polymorphic)]
  Definition swap_sum_type@{U} {A B: Type@{U}} (s: A [+] B) : B [+] A :=
  match s with
  | inl a => inr a
  | inr b => inl b
  end.

  Definition small_id (T: Type@{Set}) (v: T): T := v.

  Definition id_swap {A B: Type@{Set}} (s: A [+] B) : B [+] A :=
  small_id _ (swap_sum_type s).

  (* Fails this test because the operator was removed by cbn. *)
  Theorem cbn_keeps_notation: forall (a b: nat), a [+] b = a [+] b.
  Proof.
    intros.
    (* Ideally this would fail. *)
    progress cbn.
    reflexivity.
  Qed.

  (* Fails *)
  Theorem cbn_simplifies_addition: forall (a b: nat), S a [+] b = S (a [+] b).
  Proof.
    intros.
    (* Ideally this would pass. *)
    progress cbn.
    reflexivity.
  Qed.
End CanonicalStructures.

(* Fails cbn_simplifies_addition *)
Module CanonicalStructuresSimplNever.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Module AddOperation.
    Structure Op (B: Type) (C: Type) := {
      A: Type;
      #[canonical=no] add: A -> B -> C;
    }.
  End AddOperation.

  Definition op {B C: Type} {o: AddOperation.Op B C} := o.(AddOperation.add B C).

  Infix "[+]" := op (at level 50, left associativity) : operation_scope.

  Module NatAddOperation.
    Structure Op := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] add: nat -> B -> C;
    }.
  End NatAddOperation.
  Canonical Structure nat_add (op2: NatAddOperation.Op): AddOperation.Op op2.(NatAddOperation.B) op2.(NatAddOperation.C) := {|
    AddOperation.add:= op2.(NatAddOperation.add);
  |}.
  Arguments nat_add : simpl never.
  Arguments NatAddOperation.B : simpl never.
  Arguments NatAddOperation.C : simpl never.

  Canonical Structure nat_nat_add: NatAddOperation.Op := {|
    NatAddOperation.add:= Nat.add;
  |}.

  Module ZAddOperation.
    Structure Op := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] add: Z -> B -> C;
    }.
  End ZAddOperation.

  Canonical Structure Z_add (op2: ZAddOperation.Op): AddOperation.Op op2.(ZAddOperation.B) op2.(ZAddOperation.C) := {|
    AddOperation.add:= op2.(ZAddOperation.add);
  |}.

  Canonical Structure Z_Z_add: ZAddOperation.Op := {|
    ZAddOperation.add:= Z.add;
  |}.

  Canonical Structure Z_nat_add: ZAddOperation.Op := {|
    ZAddOperation.add a b := (a + Z.of_nat b)%Z;
  |}.

  Module TypeAddOperation.
    Universe B.
    Universe C.
    #[universes(polymorphic)]
    Structure Op@{U} := {
      B: Type@{B};
      #[canonical=no] C: Type@{C};
      #[canonical=no] add: Type@{U} -> B -> C;
    }.
  End TypeAddOperation.

  #[universes(polymorphic)]
  Canonical Structure type_add@{U} (op2: TypeAddOperation.Op@{U}): AddOperation.Op op2.(TypeAddOperation.B) op2.(TypeAddOperation.C) := {|
    AddOperation.A := Type@{U};
    AddOperation.add:= op2.(TypeAddOperation.add);
  |}.

  Canonical Structure set_add (op2: TypeAddOperation.Op@{Set}): AddOperation.Op op2.(TypeAddOperation.B) op2.(TypeAddOperation.C) := {|
    AddOperation.A := Type@{Set};
    AddOperation.add:= op2.(TypeAddOperation.add);
  |}.

  #[universes(polymorphic)]
  Canonical Structure type_type_add@{U}: TypeAddOperation.Op@{U} := {|
    TypeAddOperation.B := Type@{U};
    TypeAddOperation.C := Type@{U};
    TypeAddOperation.add a b:= (a + b)%type;
  |}.

  Canonical Structure set_set_add@{U}: TypeAddOperation.Op@{Set} := {|
    TypeAddOperation.B := Set;
    TypeAddOperation.C := Set;
    TypeAddOperation.add a b:= (a + b)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_int_nat (a: Z) (b: nat) := a [+] b.

  Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B)%type n.

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
  Theorem cbn_keeps_notation: forall (a b: nat), a [+] b = a [+] b.
  Proof.
    intros.
    (* Ideally this would fail. *)
    Fail progress cbn.
    reflexivity.
  Qed.

  (* Fails *)
  Theorem cbn_simplifies_addition: forall (a b: nat), S a [+] b = S (a [+] b).
  Proof.
    intros.
    (* Ideally this would pass. *)
    Fail progress cbn.
    (* simpl still works. *)
    progress simpl.
    reflexivity.
  Qed.
End CanonicalStructuresSimplNever.
