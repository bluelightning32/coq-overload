Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.

Module NativeNotations.
  Declare Scope nat_op_scope.
  Delimit Scope nat_op_scope with nat_op.
  Open Scope nat_op_scope.
  Bind Scope nat_op_scope with nat.

  Infix "<==" := Nat.le (at level 70, no associativity) : nat_op_scope.

  Declare Scope Z_op_scope.
  Delimit Scope Z_op_scope with Z_op.
  Open Scope Z_op_scope.

  Infix "<==" := Z.le (at level 70, no associativity) : Z_op_scope.

  Definition compare_nats (a b: nat) := (a <== b)%nat_op.

  Definition compare_ints (a b: Z) := a <== b.

  Infix "[+]" := Nat.add (at level 50, left associativity) : nat_op_scope.

  Infix "[+]" := Z.add (at level 50, left associativity) : Z_op_scope.

  Infix "[+]" := sum (at level 50, left associativity) : type_scope.

  Fail Definition add_nats (a b: nat) := a [+] b.

  Definition add_nats (a b: nat) := (a [+] b)%nat_op.

  Definition add_nats' (a b: nat) : nat := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] Z.of_nat b.

  Definition swap_sum_type {A B: Type} (s: A [+] B) : B [+] A :=
  match s with
  | inl a => inr a
  | inr b => inl b
  end.

  Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B)%type n.

  Theorem nat_plus_le_compat_r
  : forall n m p : nat,
    (
      n <== m ->
      n [+] p <== m [+] p
    )%nat_op.
  Proof.
    apply Plus.plus_le_compat_r_stt.
  Qed.

  Theorem nat_le_reflexive: forall (n: nat), (n <== n)%nat_op.
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem nat_plus_0_r_le : forall (n: nat), (n [+] 0 <== n)%nat_op.
  Proof.
    intros.
    rewrite Nat.add_0_r.
    reflexivity.
  Qed.
End NativeNotations.

(* Fails cbn_keeps_le_notation, relations_reflexive, crelations_reflexive,
   nat_le_reflexive, and nat_plus_0_r_le.
   list_of_n_sum_types half fails.
 *)
Module TypeClasses1.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class LEOperation (A B: Type) := {
    result: Type;
    le: A -> B -> result;
  }.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le: LEOperation nat nat := {|
    result := Prop;
    le := Nat.le;
  |}.

  #[export]
  Instance Z_le: LEOperation Z Z := {|
    result := Prop;
    le := Z.le;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation Z nat := {|
    result:= Prop;
    le a b := (a <= Z.of_nat b)%Z;
  |}.

  #[export]
  Instance relation_relation_le (A: Type): LEOperation (relation A) (relation A) := {|
    result:= Prop;
    le R S := RelationClasses.subrelation R S;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output} (A: Type@{Input})
  : LEOperation (crelation@{Input Output} A) (crelation@{Input Output} A) :=
  {|
    result:= Type@{Output};
    le R S := CRelationClasses.subrelation R S;
  |}.

  Definition compare_nats (a b: nat) := a <== b.

  Definition compare_ints (a b: Z) := a <== b.

  Definition compare_Z_nat (a: Z) (b: nat) := a <== b.

  Definition compare_relations (A: Type) (R S: relation A) :=
    R <== S.

  Definition compare_crelations (A: Type) (R S: crelation A) :=
    R <== S.

  Fail Definition relations_reflexive (A: Type)
  : forall (R R: relation A), R <== R.

  Fail Definition crelations_reflexive (A: Type)
  : forall (R R: crelation A), R <== R.

  (* Fails this test because the operator was removed by cbn. *)
  Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    (* Ideally this would fail. *)
    progress cbn.
    reflexivity.
  Qed.

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
  Instance Z_add: AddOperation Z Z Z := {|
    add a b := (a + b)%Z;
  |}.

  #[export]
  Instance Z_nat_add: AddOperation Z nat Z := {|
    add a b := (a + Z.of_nat b)%Z;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}: TypeAddOperation@{U} Type@{U} Type@{U} := {|
    add_type (A: Type@{U}) (B: Type@{U}) := (A + B)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

  (* (A [+] B) fails outside of the type scope. *)
  Fail Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B) n.

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
  Theorem cbn_keeps_add_notation: forall (a b: nat), a [+] b = a [+] b.
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

  Fail Theorem nat_le_reflexive: forall (n: nat), n <== n.

  Fail Theorem nat_plus_0_r_le : forall (n: nat), n [+] 0 <== n.
End TypeClasses1.

(* Fails cbn_keeps_le_notation relations_reflexive, nat_le_reflexive, and
   nat_plus_0_r_le.
   list_of_n_sum_types half fails.
 *)
Module TypeClasses2.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class LEOperation (A B C: Type) := {
    le: A -> B -> C;
  }.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le: LEOperation nat nat Prop := {|
    le := Nat.le;
  |}.

  #[export]
  Instance Z_le: LEOperation Z Z Prop := {|
    le := Z.le;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation Z nat Prop := {|
    le a b := (a <= Z.of_nat b)%Z;
  |}.

  #[export]
  Instance relation_relation_le (A: Type)
  : LEOperation (relation A) (relation A) Prop :=
  {|
    le R S := RelationClasses.subrelation R S;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output} (A: Type@{Input})
  : LEOperation (crelation@{Input Output} A) (crelation@{Input Output} A)
                Type@{Output} :=
  Build_LEOperation
    _ _ Type@{Output}
    (fun (R S: crelation@{Input Output} A) =>
       CRelationClasses.subrelation@{Input Output Output} R S).

  Definition compare_nats (a b: nat) := a <== b.

  Definition compare_ints (a b: Z) := a <== b.

  Definition compare_Z_nat (a: Z) (b: nat) := a <== b.

  Definition compare_relations (A: Type) (R S: relation A) :=
    R <== S.

  Definition compare_crelations (A: Type) (R S: crelation A) :=
    R <== S.

  Fail Definition relations_reflexive (A: Type)
  : forall (R R: relation A), R <== R.

  Definition crelations_reflexive (A: Type)
  : forall (R: crelation A), R <== R.
  Proof.
    intros.
    reflexivity.
  Qed.

  (* Fails this test because the operator was removed by cbn. *)
  Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    (* Ideally this would fail. *)
    progress cbn.
    reflexivity.
  Qed.

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
  Instance Z_add: AddOperation Z Z Z := {|
    add a b := (a + b)%Z;
  |}.

  #[export]
  Instance Z_nat_add: AddOperation Z nat Z := {|
    add a b := (a + Z.of_nat b)%Z;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}: TypeAddOperation@{U} Type@{U} Type@{U} := {|
    add_type (A: Type@{U}) (B: Type@{U}) := (A + B)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

  (* (A [+] B) fails outside of the type scope. *)
  Fail Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B) n.

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
  Theorem cbn_keeps_add_notation: forall (a b: nat), a [+] b = a [+] b.
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

  Fail Theorem nat_le_reflexive: forall (n: nat), n <== n.

  Fail Theorem nat_plus_0_r_le : forall (n: nat), n [+] 0 <== n.
End TypeClasses2.

(* Fails relations_reflexive, nat_le_reflexive, and nat_plus_0_r_le.
   list_of_n_sum_types half fails.
 *)
Module TypeClasses3.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class LEOperation (A B C: Type) := le: A -> B -> C.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le: LEOperation nat nat Prop := Nat.le.

  #[export]
  Instance Z_le: LEOperation Z Z Prop := Z.le.

  #[export]
  Instance Z_nat_le: LEOperation Z nat Prop :=
  fun a b => (a <= Z.of_nat b)%Z.

  #[export]
  Instance relation_relation_le (A: Type)
  : LEOperation (relation A) (relation A) Prop :=
  fun R S => RelationClasses.subrelation R S.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output} (A: Type@{Input})
  : LEOperation (crelation@{Input Output} A) (crelation@{Input Output} A)
                Type@{Output} :=
  fun (R S: crelation@{Input Output} A) =>
    CRelationClasses.subrelation@{Input Output Output} R S.

  Definition compare_nats (a b: nat) := a <== b.

  Definition compare_ints (a b: Z) := a <== b.

  Definition compare_Z_nat (a: Z) (b: nat) := a <== b.

  Definition compare_relations (A: Type) (R S: relation A) :=
    R <== S.

  Definition compare_crelations (A: Type) (R S: crelation A) :=
    R <== S.

  Fail Definition relations_reflexive (A: Type)
  : forall (R R: relation A), R <== R.

  Definition crelations_reflexive (A: Type)
  : forall (R: crelation A), R <== R.
  Proof.
    intros.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    (* This is supposed to fail. *)
    Fail progress cbn.
    reflexivity.
  Qed.

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
  Instance Z_add: AddOperation Z Z Z := fun a b => (a + b)%Z.

  #[export]
  Instance Z_nat_add: AddOperation Z nat Z := fun a b => (a + Z.of_nat b)%Z.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}: TypeAddOperation@{U} Type@{U} Type@{U} :=
  fun (A: Type@{U}) (B: Type@{U}) => (A + B)%type.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

  (* (A [+] B) fails outside of the type scope. *)
  Fail Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B) n.

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
  Theorem cbn_keeps_add_notation: forall (a b: nat), a [+] b = a [+] b.
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

  Fail Theorem nat_le_reflexive: forall (n: nat), n <== n.

  Fail Theorem nat_plus_0_r_le : forall (n: nat), n [+] 0 <== n.
End TypeClasses3.

(* Fails relations_reflexive, crelations_reflexive, nat_le_reflexive, and
   nat_plus_0_r_le.
   list_of_n_sum_types half fails.
 *)
Module TypeClasses4.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class LEOperationResult (A B: Type) := {
    le_result: A -> B -> Type;
  }.

  Arguments le_result : simpl never.

  Class LEOperation (A B: Type) (C: LEOperationResult A B) :=
  le: forall (a: A) (b: B), le_result a b.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le_result: LEOperationResult nat nat :=
  {|
    le_result _ _ := Prop;
  |}.

  #[export]
  Instance nat_le: LEOperation nat nat _ := Nat.le.

  #[export]
  Instance Z_le_result: LEOperationResult Z Z :=
  {|
    le_result _ _ := Prop;
  |}.

  #[export]
  Instance Z_le: LEOperation Z Z _ := Z.le.

  #[export]
  Instance Z_nat_le_result: LEOperationResult Z nat :=
  {|
    le_result _ _ := Prop;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation Z nat _ :=
  fun a b => (a <= Z.of_nat b)%Z.

  #[export]
  Instance relation_relation_le_result (A: Type)
  : LEOperationResult (relation A) (relation A) :=
  {|
    le_result _ _ := Prop;
  |}.

  #[export]
  Instance relation_relation_le (A: Type)
  : LEOperation (relation A) (relation A) _ :=
  fun R S => RelationClasses.subrelation R S.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le_result@{Input Output} (A: Type@{Input})
  : LEOperationResult (crelation@{Input Output} A)
                      (crelation@{Input Output} A) :=
  {|
    le_result _ _ := Type@{Output};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output} (A: Type@{Input})
  : LEOperation (crelation@{Input Output} A) (crelation@{Input Output} A)
                (crelation_crelation_le_result@{Input Output} A) :=
  fun (R S: crelation@{Input Output} A) =>
    CRelationClasses.subrelation@{Input Output Output} R S.

  Definition compare_nats (a b: nat) := a <== b.

  Definition compare_ints (a b: Z) := a <== b.

  Definition compare_Z_nat (a: Z) (b: nat) := a <== b.

  Definition compare_relations (A: Type) (R S: relation A) :=
    R <== S.

  Definition compare_crelations (A: Type) (R S: crelation A) :=
    R <== S.

  Fail Definition relations_reflexive (A: Type)
  : forall (R R: relation A), R <== R.

  Fail Definition crelations_reflexive (A: Type)
  : forall (R: crelation A), R <== R.

  Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    (* This is supposed to fail. *)
    Fail progress cbn.
    reflexivity.
  Qed.

  Class AddOperationResult (A B: Type) := {
    add_result: A -> B -> Type;
  }.
  Arguments add_result : simpl never.

  Class AddOperation (A B: Type) (C: AddOperationResult A B) :=
  add: forall a b, add_result a b.
  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Universe OperationInput.
  #[universes(polymorphic)]
  Class TypeAddOperation@{Output} (A: Type@{OperationInput}) (B: Type@{OperationInput}) :=
  add_type: A -> B -> Type@{Output}.
  Infix "[+]" := add_type (at level 50, left associativity) : type_scope.

  #[export]
  Instance nat_add_result: AddOperationResult nat nat := {| add_result _ _ := nat; |}.

  #[export]
  Instance nat_add: AddOperation nat nat _ := Nat.add.

  #[export]
  Instance Z_add_result: AddOperationResult Z Z := {| add_result _ _ := Z; |}.

  #[export]
  Instance Z_add: AddOperation Z Z _ := Z.add.

  #[export]
  Instance Z_nat_add_result: AddOperationResult Z nat := {| add_result _ _ := Z; |}.

  #[export]
  Instance Z_nat_add: AddOperation Z nat _ := fun a b => (a + Z.of_nat b)%Z.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}
  : TypeAddOperation@{U} Type@{U} Type@{U} :=
  fun (A: Type@{U}) (B: Type@{U}) => (A + B)%type.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

  (* (A [+] B) fails outside of the type scope. *)
  Fail Definition list_of_n_sum_types (A B: Type) (n: nat) : list Type :=
    repeat (A [+] B) n.

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
  Theorem cbn_keeps_add_notation: forall (a b: nat), a [+] b = a [+] b.
  Proof.
    intros.
    (* This should fail. *)
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

  Fail Theorem nat_le_reflexive: forall (n: nat), n <== n.

  Fail Theorem nat_plus_0_r_le : forall (n: nat), n [+] 0 <== n.
End TypeClasses4.

(* Fails cbn_keeps_le_notation, R_le_empty, and empty_le_r. *)
Module CanonicalStructures.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Module LEOperation.
    Structure LEOperation := {
      A: Type;
      B: Type;
      C: A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End LEOperation.
  Export LEOperation(LEOperation).

  Definition le {o: LEOperation} := o.(LEOperation.op).

  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  Module NatLEOperation.
    Structure NatLEOperation := {
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End NatLEOperation.
  Export NatLEOperation(NatLEOperation).

  Canonical Structure nat_le (op2: NatLEOperation)
  : LEOperation :=
  {|
    LEOperation.op:= op2.(NatLEOperation.op);
  |}.

  Canonical Structure nat_nat_le: NatLEOperation := {|
    NatLEOperation.op := Nat.le;
  |}.

  Module ZLEOperation.
    Structure ZLEOperation := {
      B: Type;
      #[canonical=no] C: Z -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End ZLEOperation.
  Export ZLEOperation(ZLEOperation).

  Canonical Structure Z_le (op2: ZLEOperation)
  : LEOperation :=
  {|
    LEOperation.op:= op2.(ZLEOperation.op);
  |}.

  Canonical Structure Z_Z_le: ZLEOperation := {|
    ZLEOperation.op := Z.le;
  |}.

  Canonical Structure Z_nat_le: ZLEOperation := {|
    ZLEOperation.op a b := (a <= Z.of_nat b)%Z;
  |}.

  Module RelationLEOperation.
    Structure RelationLEOperation (A: Type) := {
      B: Type;
      #[canonical=no] C: relation A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End RelationLEOperation.
  Export RelationLEOperation(RelationLEOperation).

  Canonical Structure relation_le (A: Type) (op2: RelationLEOperation A)
  : LEOperation :=
  {|
    LEOperation.A := relation A;
    LEOperation.op:= op2.(RelationLEOperation.op);
  |}.

  Canonical Structure relation_relation_le (A: Type)
  : RelationLEOperation A :=
  {|
    RelationLEOperation.op R S := RelationClasses.subrelation R S;
  |}.

  Module CRelationLEOperation.
    #[universes(polymorphic)]
    Structure CRelationLEOperation@{Input Output B C} (A: Type@{Input}) := {
      B: Type@{B};
      #[canonical=no] C: crelation@{Input Output} A -> B -> Type@{C};
      #[canonical=no] op: forall a b, C a b;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End CRelationLEOperation.
  Export CRelationLEOperation(CRelationLEOperation).

  #[universes(polymorphic)]
  Canonical Structure crelation_le@{Input Output B C} (A: Type@{Input})
    (op2: CRelationLEOperation@{Input Output B C} A)
  : LEOperation :=
  {|
    LEOperation.A := crelation A;
    LEOperation.op:= op2.(CRelationLEOperation.op);
  |}.

  #[universes(polymorphic)]
  Canonical Structure crelation_crelation_le@{Input Output1 CRelationB Output2
                                              Result ResultContainer}
    (A: Type@{Input})
  : CRelationLEOperation@{Input Output1 CRelationB ResultContainer} A :=
  {|
    CRelationLEOperation.C _ _ := Type@{Result};
    CRelationLEOperation.op R S := CRelationClasses.subrelation@{Input Output1 Output2} R S;
  |}.

  Definition compare_nats (a b: nat) := a <== b.

  Definition compare_ints (a b: Z) := a <== b.

  Definition compare_Z_nat (a: Z) (b: nat) := a <== b.

  Definition compare_relations (A: Type) (R S: relation A) :=
    R <== S.

  Definition compare_crelations (A: Type) (R S: crelation A) :=
    R <== S.

  Definition relations_reflexive (A: Type)
  : forall (R: relation A), R <== R := fun R x y Rxy => Rxy.

  Definition crelations_reflexive (A: Type)
  : forall (R: crelation A), R <== R := fun R x y Rxy => Rxy.

  Definition empty_relation (A: Type) : relation A := fun x y => False.

  (* Tests that the type of R can be inferred when it is on the left side of
     _ <== _ . *)
  Fail Theorem R_le_empty (A: Type) R
    : R <== empty_relation A ->
      RelationClasses.relation_equivalence R (empty_relation A).

  (* Tests that the type of R can be inferred when it is on the right side of
     _ <== _ . *)
  Fail Theorem empty_le_r (A: Type) R
    : empty_relation A <== R.

  (* Fails *)
  Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    (* Ideally this would not make progress. *)
    progress cbn.
    reflexivity.
  Qed.

  Module AddOperation.
    Structure AddOperation := {
      A: Type;
      B: Type;
      C: A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End AddOperation.
  Export AddOperation(AddOperation).

  Definition add {o: AddOperation} := o.(AddOperation.op).

  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Module NatAddOperation.
    Structure NatAddOperation := {
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End NatAddOperation.
  Export NatAddOperation(NatAddOperation).

  Canonical Structure nat_add (op2: NatAddOperation): AddOperation := {|
    AddOperation.op := op2.(NatAddOperation.op);
  |}.

  Canonical Structure nat_nat_add: NatAddOperation := {|
    NatAddOperation.op:= Nat.add;
  |}.

  Module ZAddOperation.
    Structure ZAddOperation := {
      B: Type;
      #[canonical=no] C: Z -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End ZAddOperation.
  Export ZAddOperation(ZAddOperation).

  Canonical Structure Z_add (op2: ZAddOperation): AddOperation := {|
    AddOperation.op := op2.(ZAddOperation.op);
  |}.

  Canonical Structure Z_Z_add: ZAddOperation := {|
    ZAddOperation.op:= Z.add;
  |}.

  Canonical Structure Z_nat_add: ZAddOperation := {|
    ZAddOperation.op a b := (a + Z.of_nat b)%Z;
  |}.

  Module TypeAddOperation.
    Universe B C.
    #[universes(polymorphic)]
    Structure TypeAddOperation@{A} := {
      B: Type@{B};
      #[canonical=no] C: Type@{A} -> B -> Type@{C};
      #[canonical=no] op: forall a b, C a b;
    }.
  End TypeAddOperation.
  Export TypeAddOperation(TypeAddOperation).

  #[universes(polymorphic)]
  Canonical Structure type_add@{A} (op2: TypeAddOperation@{A}): AddOperation := {|
    AddOperation.A := Type@{A};
    AddOperation.op := op2.(TypeAddOperation.op);
  |}.

  Set Warnings "-redundant-canonical-projection".
  Canonical Structure set_add (op2: TypeAddOperation@{Set}): AddOperation := {|
    AddOperation.A := Type@{Set};
    AddOperation.op := op2.(TypeAddOperation.op);
  |}.
  Set Warnings "".

  #[universes(polymorphic)]
  Canonical Structure type_type_add@{U1}: TypeAddOperation@{U1} := {|
    TypeAddOperation.B := Type@{U1};
    TypeAddOperation.C A B := Type@{U1};
    TypeAddOperation.op A B := (A + B)%type;
  |}.

  Canonical Structure set_set_add: TypeAddOperation@{Set} := {|
    TypeAddOperation.B := Set;
    TypeAddOperation.C _ _ := Set;
    TypeAddOperation.op a b:= (a + b)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

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

  (* Fails this test because the operator was removed by cbn. *)
  Theorem cbn_keeps_add_notation: forall (a b: nat), a [+] b = a [+] b.
  Proof.
    intros.
    (* Ideally this would fail. *)
    progress cbn.
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
End CanonicalStructures.

(* Fails R_le_empty, empty_le_r, and cbn_simplifies_addition. *)
Module CanonicalStructuresSimplNever.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Module LEOperation.
    Structure LEOperation := {
      A: Type;
      B: Type;
      C: A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
    Arguments C: simpl never.
    Arguments op : simpl never.
  End LEOperation.
  Export LEOperation(LEOperation).

  Definition le {o: LEOperation} := o.(LEOperation.op).

  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  Module NatLEOperation.
    Structure NatLEOperation := {
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End NatLEOperation.
  Export NatLEOperation(NatLEOperation).

  Canonical Structure nat_le (op2: NatLEOperation)
  : LEOperation :=
  {|
    LEOperation.op:= op2.(NatLEOperation.op);
  |}.

  Canonical Structure nat_nat_le: NatLEOperation := {|
    NatLEOperation.op := Nat.le;
  |}.

  Module ZLEOperation.
    Structure ZLEOperation := {
      B: Type;
      #[canonical=no] C: Z -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End ZLEOperation.
  Export ZLEOperation(ZLEOperation).

  Canonical Structure Z_le (op2: ZLEOperation)
  : LEOperation :=
  {|
    LEOperation.op:= op2.(ZLEOperation.op);
  |}.

  Canonical Structure Z_Z_le: ZLEOperation := {|
    ZLEOperation.op := Z.le;
  |}.

  Canonical Structure Z_nat_le: ZLEOperation := {|
    ZLEOperation.op a b := (a <= Z.of_nat b)%Z;
  |}.

  Module RelationLEOperation.
    Structure RelationLEOperation (A: Type) := {
      B: Type;
      #[canonical=no] C: relation A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End RelationLEOperation.
  Export RelationLEOperation(RelationLEOperation).

  Canonical Structure relation_le (A: Type) (op2: RelationLEOperation A)
  : LEOperation :=
  {|
    LEOperation.A := relation A;
    LEOperation.op:= op2.(RelationLEOperation.op);
  |}.

  Canonical Structure relation_relation_le (A: Type)
  : RelationLEOperation A :=
  {|
    RelationLEOperation.op R S := RelationClasses.subrelation R S;
  |}.

  Module CRelationLEOperation.
    #[universes(polymorphic)]
    Structure CRelationLEOperation@{Input Output B C} (A: Type@{Input}) := {
      B: Type@{B};
      #[canonical=no] C: crelation@{Input Output} A -> B -> Type@{C};
      #[canonical=no] op: forall a b, C a b;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End CRelationLEOperation.
  Export CRelationLEOperation(CRelationLEOperation).

  #[universes(polymorphic)]
  Canonical Structure crelation_le@{Input Output B C} (A: Type@{Input})
    (op2: CRelationLEOperation@{Input Output B C} A)
  : LEOperation :=
  {|
    LEOperation.A := crelation A;
    LEOperation.op:= op2.(CRelationLEOperation.op);
  |}.

  #[universes(polymorphic)]
  Canonical Structure crelation_crelation_le@{Input Output1 CRelationB Output2
                                              Result ResultContainer}
    (A: Type@{Input})
  : CRelationLEOperation@{Input Output1 CRelationB ResultContainer} A :=
  {|
    CRelationLEOperation.C _ _ := Type@{Result};
    CRelationLEOperation.op R S := CRelationClasses.subrelation@{Input Output1 Output2} R S;
  |}.

  Definition compare_nats (a b: nat) := a <== b.

  Definition compare_ints (a b: Z) := a <== b.

  Definition compare_Z_nat (a: Z) (b: nat) := a <== b.

  Definition compare_relations (A: Type) (R S: relation A) :=
    R <== S.

  Definition compare_crelations (A: Type) (R S: crelation A) :=
    R <== S.

  Definition relations_reflexive (A: Type)
  : forall (R: relation A), R <== R := fun R x y Rxy => Rxy.

  Definition crelations_reflexive (A: Type)
  : forall (R: crelation A), R <== R := fun R x y Rxy => Rxy.

  Definition empty_relation (A: Type) : relation A := fun x y => False.

  (* Tests that the type of R can be inferred when it is on the left side of
     _ <== _ . *)
  Fail Theorem R_le_empty (A: Type) R
    : R <== empty_relation A ->
      RelationClasses.relation_equivalence R (empty_relation A).

  (* Tests that the type of R can be inferred when it is on the right side of
     _ <== _ . *)
  Fail Theorem empty_le_r (A: Type) R
    : empty_relation A <== R.

  (* Passes *)
  Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    (* This is supposed to fail. *)
    Fail progress cbn.
    reflexivity.
  Qed.

  Module AddOperation.
    Structure AddOperation := {
      A: Type;
      B: Type;
      C: A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
    Arguments C: simpl never.
    Arguments op : simpl never.
  End AddOperation.
  Export AddOperation(AddOperation).

  Definition add {o: AddOperation} := o.(AddOperation.op).

  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Module NatAddOperation.
    Structure NatAddOperation := {
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End NatAddOperation.
  Export NatAddOperation(NatAddOperation).

  Canonical Structure nat_add (op2: NatAddOperation): AddOperation := {|
    AddOperation.op := op2.(NatAddOperation.op);
  |}.

  Canonical Structure nat_nat_add: NatAddOperation := {|
    NatAddOperation.op:= Nat.add;
  |}.

  Module ZAddOperation.
    Structure ZAddOperation := {
      B: Type;
      #[canonical=no] C: Z -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End ZAddOperation.
  Export ZAddOperation(ZAddOperation).

  Canonical Structure Z_add (op2: ZAddOperation): AddOperation := {|
    AddOperation.op := op2.(ZAddOperation.op);
  |}.

  Canonical Structure Z_Z_add: ZAddOperation := {|
    ZAddOperation.op:= Z.add;
  |}.

  Canonical Structure Z_nat_add: ZAddOperation := {|
    ZAddOperation.op a b := (a + Z.of_nat b)%Z;
  |}.

  Module TypeAddOperation.
    Universe B C.
    #[universes(polymorphic)]
    Structure TypeAddOperation@{A} := {
      B: Type@{B};
      #[canonical=no] C: Type@{A} -> B -> Type@{C};
      #[canonical=no] op: forall a b, C a b;
    }.
  End TypeAddOperation.
  Export TypeAddOperation(TypeAddOperation).

  #[universes(polymorphic)]
  Canonical Structure type_add@{A} (op2: TypeAddOperation@{A}): AddOperation := {|
    AddOperation.A := Type@{A};
    AddOperation.op := op2.(TypeAddOperation.op);
  |}.

  Set Warnings "-redundant-canonical-projection".
  Canonical Structure set_add (op2: TypeAddOperation@{Set}): AddOperation := {|
    AddOperation.A := Type@{Set};
    AddOperation.op := op2.(TypeAddOperation.op);
  |}.
  Set Warnings "".

  #[universes(polymorphic)]
  Canonical Structure type_type_add@{U1}: TypeAddOperation@{U1} := {|
    TypeAddOperation.B := Type@{U1};
    TypeAddOperation.C A B := Type@{U1};
    TypeAddOperation.op A B := (A + B)%type;
  |}.

  Canonical Structure set_set_add: TypeAddOperation@{Set} := {|
    TypeAddOperation.B := Set;
    TypeAddOperation.C _ _ := Set;
    TypeAddOperation.op a b:= (a + b)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

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
End CanonicalStructuresSimplNever.

(* Fails nat_add_0_r.
 *)
Module TypeClassesCanonicalSignature.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Module LESignature.
    Structure LESignature := {
      A: Type;
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments C : simpl never.
  End LESignature.
  Export LESignature(LESignature).

  Class LEOperation (r: LESignature) :=
  le: forall (a: r.(LESignature.A)) (b: r.(LESignature.B)),
      r.(LESignature.C) a b.

  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  Module NatLESignature.
    Structure NatLESignature := {
      B: Type;
      C: nat -> B -> Type;
    }.
  End NatLESignature.
  Export NatLESignature(NatLESignature).

  #[global]
  Canonical Structure nat_le_signature (sig2: NatLESignature)
  : LESignature :=
  {|
    LESignature.A := nat;
    LESignature.B := sig2.(NatLESignature.B);
    LESignature.C := sig2.(NatLESignature.C);
  |}.

  #[global]
  Canonical Structure nat_nat_le_signature: NatLESignature :=
  {|
    NatLESignature.B := nat;
    NatLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance nat_le: LEOperation _ := Nat.le.

  Module ZLESignature.
    Structure ZLESignature := {
      B: Type;
      #[canonical=no] C: Z -> B -> Type;
    }.
  End ZLESignature.
  Export ZLESignature(ZLESignature).

  #[global]
  Canonical Structure Z_le_signature (sig2: ZLESignature)
  : LESignature :=
  {|
    LESignature.A := Z;
    LESignature.B := sig2.(ZLESignature.B);
    LESignature.C := sig2.(ZLESignature.C);
  |}.

  #[global]
  Canonical Structure Z_Z_le_signature: ZLESignature :=
  {|
    ZLESignature.B := Z;
    ZLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance Z_le: LEOperation _ := Z.le.

  #[global]
  Canonical Structure Z_nat_le_signature: ZLESignature :=
  {|
    ZLESignature.B := nat;
    ZLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation _ :=
  fun a b => (a <= Z.of_nat b)%Z.

  Definition relation_no_match {A: Type} (a: A): A := a.

  (* Declares that anything that takes a relation as the first argument must
     return a Prop. The second argument is left unconstrained. *)
  #[global]
  Canonical Structure relation_le_signature1 (A: Type) (B: Type)
  : LESignature :=
  {|
    LESignature.A := relation A;
    LESignature.B := relation_no_match B;
    LESignature.C _ _:= Prop;
  |}.

  (* Declares that anything that takes a relation as the second argument must
     return a Prop. The first argument is left unconstrained. *)
  #[global]
  Canonical Structure relation_le_signature2 (A: Type) (B: Type)
  : LESignature :=
  {|
    LESignature.A := relation_no_match A;
    LESignature.B := relation B;
    LESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance relation_relation_le1 (A: Type)
  : LEOperation (relation_le_signature1 _ _) :=
  fun (R S: relation A) => RelationClasses.subrelation R S.

  #[export]
  Instance relation_relation_le2 (A: Type)
  : LEOperation (relation_le_signature2 _ _) := relation_relation_le1 A.

  Definition crelation_no_match {A: Type} (a: A): A := a.

  (* Declares that anything that takes a crelation as the first argument must
     return a Type. The second argument is left unconstrained. *)
  #[global]
  #[universes(polymorphic)]
  Canonical Structure crelation_le_signature1@{A1 A2 B C}
    (A: Type@{A1}) (B: Type@{B})
  : LESignature :=
  {|
    LESignature.A := crelation@{A1 A2} A;
    LESignature.B := crelation_no_match B;
    LESignature.C _ _ := Type@{C};
  |}.

  (* Declares that anything that takes a crelation as the second argument must
     return a Type. The first argument is left unconstrained. *)
  #[global]
  #[universes(polymorphic)]
  Canonical Structure crelation_le_signature2@{A B1 B2 C}
    (A: Type@{A}) (B: Type@{B1})
  : LESignature :=
  {|
    LESignature.A := crelation_no_match A;
    LESignature.B := crelation@{B1 B2} B;
    LESignature.C _ _ := Type@{C};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output CRelation} (A: Type@{Input})
  : LEOperation (crelation_le_signature1@{Input Output CRelation Output}
                   A (crelation@{Input Output} A)) :=
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
    (* This is supposed to fail. *)
    Fail progress cbn.
    reflexivity.
  Qed.

  Module AddSignature.
    Structure AddSignature := {
      A: Type;
      B: Type;
      C: A -> B -> Type;
    }.
    Arguments C : simpl never.
  End AddSignature.
  Export AddSignature(AddSignature).

  #[global]
  Canonical Structure add_signature (A B: Type) (C: A -> B -> Type)
  : AddSignature :=
  {|
    AddSignature.A := A;
    AddSignature.B := B;
    AddSignature.C := C;
  |}.

  Class AddOperation (r: AddSignature) :=
  add: forall (a: r.(AddSignature.A)) (b: r.(AddSignature.B)),
      r.(AddSignature.C) a b.
  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Module NatAddSignature.
    Structure NatAddSignature := {
      B: Type;
      C: nat -> B -> Type;
    }.
  End NatAddSignature.
  Export NatAddSignature(NatAddSignature).

  #[global]
  Canonical Structure nat_add_signature (sig2: NatAddSignature)
  : AddSignature :=
  {|
    AddSignature.A := nat;
    AddSignature.B := sig2.(NatAddSignature.B);
    AddSignature.C := sig2.(NatAddSignature.C);
  |}.

  #[global]
  Canonical Structure nat_nat_add_signature: NatAddSignature :=
  {|
    NatAddSignature.B := nat;
    NatAddSignature.C _ _ := nat;
  |}.

  #[export]
  Instance nat_add: AddOperation _ := Nat.add.

  #[export]
  Instance Z_add: AddOperation _ := Z.add.

  #[export]
  Instance Z_nat_add: AddOperation (add_signature Z nat (fun _ _ => Z)) :=
  fun a b => (a + Z.of_nat b)%Z.

  Module TypeAddSignature.
    Universe B C.
    #[universes(polymorphic)]
    Structure TypeAddSignature@{U} := {
      B: Type@{B};
      C: Type@{U} -> B -> Type@{C};
    }.
  End TypeAddSignature.
  Export TypeAddSignature(TypeAddSignature).

  #[global]
  #[universes(polymorphic)]
  Canonical Structure type_add_signature@{U} (sig2: TypeAddSignature@{U})
  : AddSignature :=
  {|
    AddSignature.A := Type@{U};
    AddSignature.B := sig2.(TypeAddSignature.B);
    AddSignature.C := sig2.(TypeAddSignature.C);
  |}.

  Set Warnings "-redundant-canonical-projection".
  #[global]
  Canonical Structure set_add_signature (sig2: TypeAddSignature@{Set})
  : AddSignature := type_add_signature@{Set} sig2.
  Set Warnings "".

  #[global]
  #[universes(polymorphic)]
  Canonical Structure type_type_add_signature@{U}
  : TypeAddSignature@{U} :=
  {|
    TypeAddSignature.B := Type@{U};
    TypeAddSignature.C (A B: Type@{U}) := Type@{U};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance type_type_add@{U} : AddOperation _ :=
  fun (A: Type@{U}) (B: Type@{U}) => (A + B)%type.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

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
    (* This is supposed to fail. *)
    Fail progress cbn.
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

  (* Fails *)
  Theorem nat_add_0_r : forall (n: nat), n [+] 0 = n.
  Proof.
    intros.
    Fail rewrite nat_add_comm.
  Abort.

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
End TypeClassesCanonicalSignature.

(* Passes all tests
 *)
Module TypeClassesUnfoldResult.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Module LESignature.
    Structure LESignature := {
      A: Type;
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments C : simpl never.
  End LESignature.
  Export LESignature(LESignature).

  Class LEOperation (r: LESignature) :=
  le: forall (a: r.(LESignature.A)) (b: r.(LESignature.B)),
      (let '{| LESignature.C := C; |} := r
         return (r.(LESignature.A) -> r.(LESignature.B) -> Type) in C) a b.

  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  Module NatLESignature.
    Structure NatLESignature := {
      B: Type;
      C: nat -> B -> Type;
    }.
  End NatLESignature.
  Export NatLESignature(NatLESignature).

  #[global]
  Canonical Structure nat_le_signature (sig2: NatLESignature)
  : LESignature :=
  {|
    LESignature.A := nat;
    LESignature.B := sig2.(NatLESignature.B);
    LESignature.C := let '{| NatLESignature.C := C; |} := sig2 in C;
  |}.

  #[global]
  Canonical Structure nat_nat_le_signature: NatLESignature :=
  {|
    NatLESignature.B := nat;
    NatLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance nat_le: LEOperation _ := Nat.le.

  Module ZLESignature.
    Structure ZLESignature := {
      B: Type;
      #[canonical=no] C: Z -> B -> Type;
    }.
  End ZLESignature.
  Export ZLESignature(ZLESignature).

  #[global]
  Canonical Structure Z_le_signature (sig2: ZLESignature)
  : LESignature :=
  {|
    LESignature.A := Z;
    LESignature.B := sig2.(ZLESignature.B);
    LESignature.C := let '{| ZLESignature.C := C; |} := sig2 in C;
  |}.

  #[global]
  Canonical Structure Z_Z_le_signature: ZLESignature :=
  {|
    ZLESignature.B := Z;
    ZLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance Z_le: LEOperation _ := Z.le.

  #[global]
  Canonical Structure Z_nat_le_signature: ZLESignature :=
  {|
    ZLESignature.B := nat;
    ZLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation _ :=
  fun a b => (a <= Z.of_nat b)%Z.

  Definition relation_no_match {A: Type} (a: A): A := a.

  (* Declares that anything that takes a relation as the first argument must
     return a Prop. The second argument is left unconstrained. *)
  #[global]
  Canonical Structure relation_le_signature1 (A: Type) (B: Type)
  : LESignature :=
  {|
    LESignature.A := relation A;
    LESignature.B := relation_no_match B;
    LESignature.C _ _:= Prop;
  |}.

  (* Declares that anything that takes a relation as the second argument must
     return a Prop. The first argument is left unconstrained. *)
  #[global]
  Canonical Structure relation_le_signature2 (A: Type) (B: Type)
  : LESignature :=
  {|
    LESignature.A := relation_no_match A;
    LESignature.B := relation B;
    LESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance relation_relation_le1 (A: Type)
  : LEOperation (relation_le_signature1 _ _) :=
  fun (R S: relation A) => RelationClasses.subrelation R S.

  #[export]
  Instance relation_relation_le2 (A: Type)
  : LEOperation (relation_le_signature2 _ _) := relation_relation_le1 A.

  Definition crelation_no_match {A: Type} (a: A): A := a.

  (* Declares that anything that takes a crelation as the first argument must
     return a Type. The second argument is left unconstrained. *)
  #[global]
  #[universes(polymorphic)]
  Canonical Structure crelation_le_signature1@{A1 A2 B C}
    (A: Type@{A1}) (B: Type@{B})
  : LESignature :=
  {|
    LESignature.A := crelation@{A1 A2} A;
    LESignature.B := crelation_no_match B;
    LESignature.C _ _ := Type@{C};
  |}.

  (* Declares that anything that takes a crelation as the second argument must
     return a Type. The first argument is left unconstrained. *)
  #[global]
  #[universes(polymorphic)]
  Canonical Structure crelation_le_signature2@{A B1 B2 C}
    (A: Type@{A}) (B: Type@{B1})
  : LESignature :=
  {|
    LESignature.A := crelation_no_match A;
    LESignature.B := crelation@{B1 B2} B;
    LESignature.C _ _ := Type@{C};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output CRelation} (A: Type@{Input})
  : LEOperation (crelation_le_signature1@{Input Output CRelation Output}
                   A (crelation@{Input Output} A)) :=
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
    (* This is supposed to fail. *)
    Fail progress cbn.
    reflexivity.
  Qed.

  Module AddSignature.
    Structure AddSignature := {
      A: Type;
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments C : simpl never.
  End AddSignature.
  Export AddSignature(AddSignature).

  #[global]
  Canonical Structure add_signature (A B: Type) (C: A -> B -> Type)
  : AddSignature :=
  {|
    AddSignature.A := A;
    AddSignature.B := B;
    AddSignature.C := C;
  |}.

  Class AddOperation (r: AddSignature) :=
  add: forall (a: r.(AddSignature.A)) (b: r.(AddSignature.B)),
    (let '{| AddSignature.C := C; |} := r in C) a b.
  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Module NatAddSignature.
    Structure NatAddSignature := {
      B: Type;
      C: nat -> B -> Type;
    }.
  End NatAddSignature.
  Export NatAddSignature(NatAddSignature).

  #[global]
  Canonical Structure nat_add_signature (sig2: NatAddSignature)
  : AddSignature :=
  {|
    AddSignature.A := nat;
    AddSignature.B := sig2.(NatAddSignature.B);
    AddSignature.C := let '{| NatAddSignature.C := C; |} := sig2 in C;
  |}.

  #[global]
  Canonical Structure nat_nat_add_signature: NatAddSignature :=
  {|
    NatAddSignature.B := nat;
    NatAddSignature.C _ _ := nat;
  |}.

  #[export]
  Instance nat_add: AddOperation _ := Nat.add.

  #[export]
  Instance Z_add: AddOperation _ := Z.add.

  #[export]
  Instance Z_nat_add: AddOperation (add_signature Z nat (fun _ _ => Z)) :=
  fun a b => (a + Z.of_nat b)%Z.

  Module TypeAddSignature.
    Universe B C.
    #[universes(polymorphic)]
    Structure TypeAddSignature@{U} := {
      B: Type@{B};
      C: Type@{U} -> B -> Type@{C};
    }.
  End TypeAddSignature.
  Export TypeAddSignature(TypeAddSignature).

  #[global]
  #[universes(polymorphic)]
  Canonical Structure type_add_signature@{U} (sig2: TypeAddSignature@{U})
  : AddSignature :=
  {|
    AddSignature.A := Type@{U};
    AddSignature.B := sig2.(TypeAddSignature.B);
    AddSignature.C := let '{| TypeAddSignature.C := C; |} := sig2 in C;
  |}.

  Set Warnings "-redundant-canonical-projection".
  #[global]
  Canonical Structure set_add_signature (sig2: TypeAddSignature@{Set})
  : AddSignature := type_add_signature@{Set} sig2.
  Set Warnings "".

  #[global]
  #[universes(polymorphic)]
  Canonical Structure type_type_add_signature@{U}
  : TypeAddSignature@{U} :=
  {|
    TypeAddSignature.B := Type@{U};
    TypeAddSignature.C (A B: Type@{U}) := Type@{U};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance type_type_add@{U} : AddOperation _ :=
  fun (A: Type@{U}) (B: Type@{U}) => (A + B)%type.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

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
    (* This is supposed to fail. *)
    Fail progress cbn.
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
End TypeClassesUnfoldResult.
