Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.
Require Import Constructive_sets.

Module NativeNotations.
  Declare Scope nat_op_scope.
  Delimit Scope nat_op_scope with nat_op.
  Open Scope nat_op_scope.
  Bind Scope nat_op_scope with nat.

  Infix "<==" := Nat.le (at level 70, no associativity) : nat_op_scope.

  Declare Scope Z_op_scope.
  Delimit Scope Z_op_scope with Z_op.
  Open Scope Z_op_scope.

  Declare Scope list_op_scope.
  Delimit Scope list_op_scope with list_op.
  Open Scope list_op_scope.

  Declare Scope ensemble_op_scope.
  Delimit Scope ensemble_op_scope with ensemble_op.
  Open Scope ensemble_op_scope.

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

  Definition add_nat_Z (a: nat) (b: Z) := Z.of_nat a [+] b.

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

  Infix "[::]" := cons (at level 60, right associativity) : list_op_scope.

  Definition ensemble_cons {A: Type} (a: A) (e: Ensemble A): Ensemble A :=
  Add _ e a.

  Infix "[::]" := ensemble_cons (at level 60, right associativity) : ensemble_op_scope.

  Theorem list_in_cons : forall A a (l: list A), List.In a (a [::] l)%list_op.
  Proof.
    intros.
    cbn.
    left.
    reflexivity.
  Qed.

  Theorem ensemble_in_cons
  : forall A a (e: Ensemble A), Ensembles.In _ (a [::] e)%ensemble_op a.
  Proof.
    intros.
    apply Add_intro2.
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
    le_result: A -> B -> Type;
    le a b: le_result a b;
  }.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le: LEOperation nat nat := {|
    le_result _ _ := Prop;
    le := Nat.le;
  |}.

  #[export]
  Instance Z_le: LEOperation Z Z := {|
    le_result _ _ := Prop;
    le := Z.le;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation Z nat := {|
    le_result _ _ := Prop;
    le a b := (a <= Z.of_nat b)%Z;
  |}.

  #[export]
  Instance relation_relation_le (A: Type): LEOperation (relation A) (relation A) := {|
    le_result _ _ := Prop;
    le R S := RelationClasses.subrelation R S;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output} (A: Type@{Input})
  : LEOperation (crelation@{Input Output} A) (crelation@{Input Output} A) :=
  {|
    le_result _ _ := Type@{Output};
    le R S := CRelationClasses.subrelation R S;
  |}.

  (* l1 <= l2, if l1 is a suffix of l2. *)
  #[export]
  Instance list_le (A: Type)
  : LEOperation (list A) (list A) :=
  {|
    le_result _ _ := Prop;
    le l1 l2 := l1 = skipn (length l2 - length l1) l2;
  |}.

  (* B <= C, if B is a subset of C. *)
  #[export]
  Instance ensemble_le (A: Type)
  : LEOperation (Ensemble A) (Ensemble A) :=
  {|
    le_result _ _ := Prop;
    le B C := Included _ B C;
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
    cbn.
    Fail match goal with
    | |- context [a <== b] => idtac
    end.
    reflexivity.
  Qed.

  Class AddOperation (A B: Type) := {
    add_result: A -> B -> Type;
    add a b: add_result a b;
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
    add_result _ _ := nat;
    add := Nat.add;
  |}.

  #[export]
  Instance Z_add: AddOperation Z Z := {|
    add_result _ _ := Z;
    add a b := (a + b)%Z;
  |}.

  #[export]
  Instance Z_nat_add: AddOperation Z nat := {|
    add_result _ _ := Z;
    add a b := (a + Z.of_nat b)%Z;
  |}.

  #[export]
  Instance nat_Z_add: AddOperation nat Z := {|
    add_result _ _ := Z;
    add a b := (Z.of_nat a + b)%Z;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}: TypeAddOperation@{U} Type@{U} Type@{U} := {|
    add_type (A: Type@{U}) (B: Type@{U}) := (A + B)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

  Definition add_nat_Z (a: nat) (b: Z) := a [+] b.

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
    cbn.
    Fail match goal with
    | |- context [a [+] b] => idtac
    end.
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

  Class ConsOperation (A B: Type) := {
    cons_result: A -> B -> Type;
    cons a b: cons_result a b;
  }.
  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  #[export]
  Instance list_cons (A: Type): ConsOperation A (list A) := {|
    cons_result _ _ := list A;
    cons := List.cons;
  |}.

  #[export]
  Instance nat_list_Z_cons: ConsOperation nat (list Z) := {|
    cons_result _ _ := list Z;
    cons a := List.cons (Z.of_nat a);
  |}.

  #[export]
  Instance ensemble_cons (A: Type)
  : ConsOperation A (Ensemble A) :=
  {|
    cons_result _ _ := Ensemble A;
    cons := fun a e => Add _ e a;
  |}.

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

  Fail Theorem list_cons_le : forall A a (l: list A), l <== (a [::] l).

  Fail Theorem ensemble_cons_le
  : forall A a (e: Ensemble A), e <== (a [::] e).
End TypeClasses1.

(* Fails cbn_keeps_le_notation, relations_reflexive, crelations_reflexive,
   nat_le_reflexive, and nat_plus_0_r_le.
   list_of_n_sum_types half fails.
 *)
Module TypeClasses2.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class LEOperation (A B: Type) (C: A -> B -> Type) := {
    le a b: C a b;
  }.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le: LEOperation nat nat (fun _ _ => Prop) := {|
    le := Nat.le;
  |}.

  #[export]
  Instance Z_le: LEOperation Z Z (fun _ _ => Prop) := {|
    le := Z.le;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation Z nat (fun _ _ => Prop) := {|
    le a b := (a <= Z.of_nat b)%Z;
  |}.

  #[export]
  Instance relation_relation_le (A: Type)
  : LEOperation (relation A) (relation A) (fun _ _ => Prop) :=
  {|
    le R S := RelationClasses.subrelation R S;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output} (A: Type@{Input})
  : LEOperation (crelation@{Input Output} A) (crelation@{Input Output} A)
                (fun _ _ => Type@{Output}) :=
  Build_LEOperation
    _ _ (fun _ _ => Type@{Output})
    (fun (R S: crelation@{Input Output} A) =>
       CRelationClasses.subrelation@{Input Output Output} R S).

  (* l1 <= l2, if l1 is a suffix of l2. *)
  #[export]
  Instance list_le (A: Type)
  : LEOperation (list A) (list A) (fun _ _ => Prop) :=
  {|
    le l1 l2 := l1 = skipn (length l2 - length l1) l2;
  |}.

  (* B <= C, if B is a subset of C. *)
  #[export]
  Instance ensemble_le (A: Type)
  : LEOperation (Ensemble A) (Ensemble A) (fun _ _ => Prop) :=
  {|
    le B C := Included _ B C;
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
  : forall (R: crelation A), R <== R.

  (* Fails this test because the operator was removed by cbn. *)
  Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    cbn.
    Fail match goal with
    | |- context [a <== b] => idtac
    end.
    reflexivity.
  Qed.

  Class AddOperation (A B: Type) (C: A -> B -> Type) := {
    add a b: C a b;
  }.
  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Universe OperationInput.
  #[universes(polymorphic)]
  Class TypeAddOperation@{Output} (A: Type@{OperationInput}) (B: Type@{OperationInput}) := {
    add_type: A -> B -> Type@{Output};
  }.
  Infix "[+]" := add_type (at level 50, left associativity) : type_scope.

  #[export]
  Instance nat_add: AddOperation nat nat (fun _ _ => nat) := {|
    add := Nat.add;
  |}.

  #[export]
  Instance Z_add: AddOperation Z Z (fun _ _ => Z) := {|
    add a b := (a + b)%Z;
  |}.

  #[export]
  Instance Z_nat_add: AddOperation Z nat (fun _ _ => Z) := {|
    add a b := (a + Z.of_nat b)%Z;
  |}.

  #[export]
  Instance nat_Z_add: AddOperation nat Z (fun _ _ => Z) := {|
    add a b := (Z.of_nat a + b)%Z;
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}: TypeAddOperation@{U} Type@{U} Type@{U} := {|
    add_type (A: Type@{U}) (B: Type@{U}) := (A + B)%type;
  |}.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

  Definition add_nat_Z (a: nat) (b: Z) := a [+] b.

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
    cbn.
    Fail match goal with
    | |- context [a [+] b] => idtac
    end.
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

  Class ConsOperation (A B: Type) (C: A -> B -> Type) := {
    cons a b: C a b;
  }.
  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  #[export]
  Instance list_cons (A: Type)
  : ConsOperation A (list A) (fun _ _ => list A) :=
  {|
    cons := List.cons;
  |}.

  #[export]
  Instance nat_list_Z_cons
  : ConsOperation nat (list Z) (fun _ _ => list Z) :=
  {|
    cons a := List.cons (Z.of_nat a);
  |}.

  #[export]
  Instance ensemble_cons (A: Type)
  : ConsOperation A (Ensemble A) (fun _ _ => Ensemble A) :=
  {|
    cons := fun a e => Add _ e a;
  |}.

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

  Fail Theorem list_cons_le : forall A a (l: list A), l <== (a [::] l).

  Fail Theorem ensemble_cons_le
  : forall A a (e: Ensemble A), e <== (a [::] e).
End TypeClasses2.

(* Fails relations_reflexive, crelations_relfexive, cbn_keeps_le_notation,
   nat_le_reflexive, and nat_plus_0_r_le.
   list_of_n_sum_types half fails.
 *)
Module TypeClasses3.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class LEOperation (A B: Type) (C: A -> B -> Type) := le a b: C a b.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le: LEOperation nat nat (fun _ _ => Prop) := Nat.le.

  #[export]
  Instance Z_le: LEOperation Z Z (fun _ _ => Prop) := Z.le.

  #[export]
  Instance Z_nat_le: LEOperation Z nat (fun _ _ => Prop) :=
  fun a b => (a <= Z.of_nat b)%Z.

  #[export]
  Instance relation_relation_le (A: Type)
  : LEOperation (relation A) (relation A) (fun _ _ => Prop) :=
  fun R S => RelationClasses.subrelation R S.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output} (A: Type@{Input})
  : LEOperation (crelation@{Input Output} A) (crelation@{Input Output} A)
                (fun _ _ => Type@{Output}) :=
  fun (R S: crelation@{Input Output} A) =>
    CRelationClasses.subrelation@{Input Output Output} R S.

  (* l1 <= l2, if l1 is a suffix of l2. *)
  #[export]
  Instance list_le (A: Type)
  : LEOperation (list A) (list A) (fun _ _ => Prop) :=
  fun l1 l2 => l1 = skipn (length l2 - length l1) l2.

  (* B <= C, if B is a subset of C. *)
  #[export]
  Instance ensemble_le (A: Type)
  : LEOperation (Ensemble A) (Ensemble A) (fun _ _ => Prop) :=
  fun B C => Included _ B C.

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

  Class AddOperation (A B: Type) (C: A -> B -> Type) := add a b: C a b.
  Infix "[+]" := add (at level 50, left associativity) : operation_scope.

  Universe OperationInput.
  #[universes(polymorphic)]
  Class TypeAddOperation@{Output} (A: Type@{OperationInput}) (B: Type@{OperationInput}) :=
  add_type: A -> B -> Type@{Output}.
  Infix "[+]" := add_type (at level 50, left associativity) : type_scope.

  #[export]
  Instance nat_add: AddOperation nat nat (fun _ _ => nat) := fun a b => (a + b)%nat.

  #[export]
  Instance Z_add: AddOperation Z Z (fun _ _ => Z) := fun a b => (a + b)%Z.

  #[export]
  Instance Z_nat_add: AddOperation Z nat (fun _ _ => Z) := fun a b => (a + Z.of_nat b)%Z.

  #[export]
  Instance nat_Z_add: AddOperation nat Z (fun _ _ => Z) := fun a b => (Z.of_nat a + b)%Z.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}: TypeAddOperation@{U} Type@{U} Type@{U} :=
  fun (A: Type@{U}) (B: Type@{U}) => (A + B)%type.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

  Definition add_nat_Z (a: nat) (b: Z) := a [+] b.

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
    cbn.
    match goal with
    | |- context [a [+] b] => idtac
    end.
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

  Class ConsOperation (A B: Type) (C: A -> B -> Type) := cons a b: C a b.
  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  #[export]
  Instance list_cons (A: Type)
  : ConsOperation A (list A) (fun _ _ => list A) :=
  List.cons.

  #[export]
  Instance nat_list_Z_cons
  : ConsOperation nat (list Z) (fun _ _ => list Z) :=
  fun a => List.cons (Z.of_nat a).

  #[export]
  Instance ensemble_cons (A: Type)
  : ConsOperation A (Ensemble A) (fun _ _ => Ensemble A) :=
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

  Fail Theorem list_cons_le : forall A a (l: list A), l <== (a [::] l).

  Fail Theorem ensemble_cons_le
  : forall A a (e: Ensemble A), e <== (a [::] e).
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

  #[export]
  Instance list_list_le_result (A: Type)
  : LEOperationResult (list A) (list A) :=
  {|
    le_result _ _ := Prop;
  |}.

  (* l1 <= l2, if l1 is a suffix of l2. *)
  #[export]
  Instance list_list_le (A: Type)
  : LEOperation (list A) (list A) (list_list_le_result A) :=
  fun l1 l2 => l1 = skipn (length l2 - length l1) l2.

  #[export]
  Instance ensemble_ensemble_le_result (A: Type)
  : LEOperationResult (Ensemble A) (Ensemble A) :=
  {|
    le_result _ _ := Prop;
  |}.

  (* B <= C, if B is a subset of C. *)
  #[export]
  Instance ensemble_le (A: Type)
  : LEOperation (Ensemble A) (Ensemble A) (ensemble_ensemble_le_result A) :=
  fun B C => Included _ B C.

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
    cbn.
    match goal with
    | |- context [a <== b] => idtac
    end.
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
  Instance nat_Z_add_result: AddOperationResult nat Z := {| add_result _ _ := Z; |}.

  #[export]
  Instance nat_Z_add: AddOperation nat Z _ := fun a b => (Z.of_nat a + b)%Z.

  #[export]
  #[universes(polymorphic)]
  Instance type_add@{U}
  : TypeAddOperation@{U} Type@{U} Type@{U} :=
  fun (A: Type@{U}) (B: Type@{U}) => (A + B)%type.

  Definition add_nats (a b: nat) := a [+] b.

  Definition add_ints (a b: Z) := a [+] b.

  Definition add_Z_nat (a: Z) (b: nat) := a [+] b.

  Definition add_nat_Z (a: nat) (b: Z) := a [+] b.

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
    cbn.
    match goal with
    | |- context [a [+] b] => idtac
    end.
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

  Class ConsOperationResult (A B: Type) := {
    cons_result: A -> B -> Type;
  }.
  Arguments cons_result : simpl never.

  Class ConsOperation (A B: Type) (C: ConsOperationResult A B) :=
  cons: forall a b, cons_result a b.
  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  #[export]
  Instance list_cons_result (A: Type)
  : ConsOperationResult A (list A) := {| cons_result _ _ := list A; |}.

  #[export]
  Instance list_cons (A: Type): ConsOperation A (list A) _ := List.cons.

  #[export]
  Instance nat_list_Z_cons_result: ConsOperationResult nat (list Z) := {|
    cons_result _ _ := list Z;
  |}.

  #[export]
  Instance nat_list_Z_cons: ConsOperation nat (list Z) _ :=
  fun a => List.cons (Z.of_nat a).

  #[export]
  Instance ensemble_cons_result (A: Type)
  : ConsOperationResult A (Ensemble A) := {| cons_result _ _ := Ensemble A; |}.

  #[export]
  Instance ensemble_cons (A: Type)
  : ConsOperation A (Ensemble A) _ := fun a e => Add _ e a.

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

  Fail Theorem list_cons_le : forall A a (l: list A), l <== (a [::] l).

  Fail Theorem ensemble_cons_le
  : forall A a (e: Ensemble A), e <== (a [::] e).
End TypeClasses4.

(* Fails cbn_keeps_le_notation, cbn_keeps_cons_notation, and
   cbn_keeps_cons_notation'. *)
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

  Canonical Structure relation_relation_le (A: Type)
  : LEOperation :=
  {|
    LEOperation.A := relation A;
    LEOperation.B := relation A;
    LEOperation.C _ _ := Prop;
    LEOperation.op R S := RelationClasses.subrelation R S;
  |}.

  #[universes(polymorphic)]
  Canonical Structure crelation_crelation_le@{Input Output1 CRelationB Output2
                                              Result ResultContainer}
    (A: Type@{Input})
  : LEOperation :=
  {|
    LEOperation.A := crelation A;
    LEOperation.B := crelation A;
    LEOperation.C _ _ := Type@{Result};
    LEOperation.op R S := CRelationClasses.subrelation@{Input Output1 Output2} R S;
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

  (* Fails *)
  Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    cbn.
    Fail match goal with
    | |- context [a <== b] => idtac
    end.
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

  Canonical Structure nat_Z_add: NatAddOperation := {|
    NatAddOperation.op a b := (Z.of_nat a + b)%Z;
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

  (* Fails this test because the operator was removed by cbn. *)
  Theorem cbn_keeps_add_notation: forall (a b: nat), a [+] b = a [+] b.
  Proof.
    intros.
    cbn.
    Fail match goal with
    | |- context [a [+] b] => idtac
    end.
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

  Module ConsOperation.
    Structure ConsOperation := {
      A: Type;
      B: Type;
      C: A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End ConsOperation.
  Export ConsOperation(ConsOperation).

  Definition cons {o: ConsOperation} := o.(ConsOperation.op).

  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  Module AnyConsOperation.
    Structure AnyConsOperation (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End AnyConsOperation.
  Export AnyConsOperation(AnyConsOperation).

  Canonical Structure any_cons (A: Type) (op2: AnyConsOperation A)
  : ConsOperation :=
  {|
    ConsOperation.A := A;
    ConsOperation.C := op2.(AnyConsOperation.C);
    ConsOperation.op := op2.(AnyConsOperation.op);
  |}.

  Canonical Structure any_list_cons (A: Type): AnyConsOperation A := {|
    AnyConsOperation.B := list A;
    AnyConsOperation.op := List.cons;
  |}.

  Definition list_no_match (A: Type) := A.

  Canonical Structure list_cons (A: Type)
  : ConsOperation :=
  {|
    ConsOperation.A := list_no_match A;
    ConsOperation.B := list A;
    ConsOperation.C _ _ := list A;
    ConsOperation.op := List.cons;
  |}.

  Module NatConsOperation.
    Structure NatConsOperation := {
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End NatConsOperation.
  Export NatConsOperation(NatConsOperation).

  Canonical Structure nat_cons (op2: NatConsOperation)
  : ConsOperation :=
  {|
    ConsOperation.A := nat;
    ConsOperation.C := op2.(NatConsOperation.C);
    ConsOperation.op := op2.(NatConsOperation.op);
  |}.

  Canonical Structure nat_list_Z_cons
  : NatConsOperation :=
  {|
    NatConsOperation.B := list Z;
    NatConsOperation.C _ _ := list Z;
    NatConsOperation.op a := List.cons (Z.of_nat a);
  |}.

  Canonical Structure any_Ensemble_cons (A: Type): AnyConsOperation A := {|
    AnyConsOperation.B := Ensemble A;
    AnyConsOperation.op a e := Add _ e a;
  |}.

  Definition Ensemble_no_match (A: Type) := A.

  Canonical Structure Ensemble_cons (A: Type)
  : ConsOperation :=
  {|
    ConsOperation.A := Ensemble_no_match A;
    ConsOperation.B := Ensemble A;
    ConsOperation.C _ _ := Ensemble A;
    ConsOperation.op a e := Add _ e a;
  |}.

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

  (* Fails *)
  Theorem cbn_keeps_cons_notation: forall A a (l: list A), a [::] l = a [::] l.
  Proof.
    intros.
    cbn.
    Fail match goal with
    | |- context [a [::] l] => idtac
    end.
    reflexivity.
  Qed.

  (* Fails *)
  Theorem cbn_keeps_cons_notation': forall A (a: A) (l: list A), a [::] l = a [::] l.
  Proof.
    intros.
    cbn.
    Fail match goal with
    | |- context [a [::] l] => idtac
    end.
    reflexivity.
  Qed.
End CanonicalStructures.

(* Fails cbn_simplifies_addition. *)
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

  Canonical Structure relation_relation_le (A: Type)
  : LEOperation :=
  {|
    LEOperation.A := relation A;
    LEOperation.B := relation A;
    LEOperation.C _ _ := Prop;
    LEOperation.op R S := RelationClasses.subrelation R S;
  |}.

  #[universes(polymorphic)]
  Canonical Structure crelation_crelation_le@{Input Output1 CRelationB Output2
                                              Result ResultContainer}
    (A: Type@{Input})
  : LEOperation :=
  {|
    LEOperation.A := crelation A;
    LEOperation.B := crelation A;
    LEOperation.C _ _ := Type@{Result};
    LEOperation.op R S := CRelationClasses.subrelation@{Input Output1 Output2} R S;
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

  Canonical Structure nat_Z_add: NatAddOperation := {|
    NatAddOperation.op a b := (Z.of_nat a + b)%Z;
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

  Module ConsOperation.
    Structure ConsOperation := {
      A: Type;
      B: Type;
      C: A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
    Arguments C: simpl never.
    Arguments op : simpl never.
  End ConsOperation.
  Export ConsOperation(ConsOperation).

  Definition cons {o: ConsOperation} := o.(ConsOperation.op).

  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  Module AnyConsOperation.
    Structure AnyConsOperation (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End AnyConsOperation.
  Export AnyConsOperation(AnyConsOperation).

  Canonical Structure any_cons (A: Type) (op2: AnyConsOperation A)
  : ConsOperation :=
  {|
    ConsOperation.A := A;
    ConsOperation.C := op2.(AnyConsOperation.C);
    ConsOperation.op := op2.(AnyConsOperation.op);
  |}.

  Canonical Structure any_list_cons (A: Type): AnyConsOperation A := {|
    AnyConsOperation.B := list A;
    AnyConsOperation.op := List.cons;
  |}.

  Definition list_no_match (A: Type) := A.

  Canonical Structure list_cons (A: Type)
  : ConsOperation :=
  {|
    ConsOperation.A := list_no_match A;
    ConsOperation.B := list A;
    ConsOperation.C _ _ := list A;
    ConsOperation.op := List.cons;
  |}.

  Module NatConsOperation.
    Structure NatConsOperation := {
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
      #[canonical=no] op: forall a b, C a b;
    }.
  End NatConsOperation.
  Export NatConsOperation(NatConsOperation).

  Canonical Structure nat_cons (op2: NatConsOperation)
  : ConsOperation :=
  {|
    ConsOperation.A := nat;
    ConsOperation.C := op2.(NatConsOperation.C);
    ConsOperation.op := op2.(NatConsOperation.op);
  |}.

  Canonical Structure nat_list_Z_cons
  : NatConsOperation :=
  {|
    NatConsOperation.B := list Z;
    NatConsOperation.C _ _ := list Z;
    NatConsOperation.op a := List.cons (Z.of_nat a);
  |}.

  Canonical Structure any_Ensemble_cons (A: Type): AnyConsOperation A := {|
    AnyConsOperation.B := Ensemble A;
    AnyConsOperation.op a e := Add _ e a;
  |}.

  Definition Ensemble_no_match (A: Type) := A.

  Canonical Structure Ensemble_cons (A: Type)
  : ConsOperation :=
  {|
    ConsOperation.A := Ensemble_no_match A;
    ConsOperation.B := Ensemble A;
    ConsOperation.C _ _ := Ensemble A;
    ConsOperation.op a e := Add _ e a;
  |}.

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

  #[global]
  Canonical Structure relation_le_signature (A: Type)
  : LESignature :=
  {|
    LESignature.A := relation A;
    LESignature.B := relation A;
    LESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance relation_relation_le1 (A: Type)
  : LEOperation (relation_le_signature _) :=
  fun (R S: relation A) => RelationClasses.subrelation R S.

  #[global]
  #[universes(polymorphic)]
  Canonical Structure crelation_le_signature@{A1 A2 C}
    (A: Type@{A1})
  : LESignature :=
  {|
    LESignature.A := crelation@{A1 A2} A;
    LESignature.B := crelation@{A1 A2} A;
    LESignature.C _ _ := Type@{C};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output CRelation} (A: Type@{Input})
  : LEOperation (crelation_le_signature@{Input Output Output} A) :=
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

  #[global]
  Canonical Structure nat_Z_add_signature: NatAddSignature :=
  {|
    NatAddSignature.B := Z;
    NatAddSignature.C _ _ := Z;
  |}.

  #[export]
  Instance nat_Z_add: AddOperation _ :=
  fun a b => (Z.of_nat a + b)%Z.

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

  (* Fails *)
  Theorem nat_add_0_r : forall (n: nat), n [+] 0 = n.
  Proof.
    intros.
    (* Ideally this would work. *)
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

  Module ConsSignature.
    Structure ConsSignature := {
      A: Type;
      B: Type;
      C: A -> B -> Type;
    }.
    Arguments C : simpl never.
  End ConsSignature.
  Export ConsSignature(ConsSignature).

  Class ConsOperation (r: ConsSignature) :=
  cons: forall (a: r.(ConsSignature.A)) (b: r.(ConsSignature.B)),
       r.(ConsSignature.C) a b.
  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  Module AnyConsSignature.
    Structure AnyConsSignature (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments B {A}.
    Arguments C {A}.
  End AnyConsSignature.
  Export AnyConsSignature(AnyConsSignature).

  Canonical Structure any_cons (A: Type) (op2: AnyConsSignature A)
  : ConsSignature :=
  {|
    ConsSignature.A := A;
    ConsSignature.C := op2.(AnyConsSignature.C);
  |}.

  Canonical Structure any_list_cons_signature (A: Type): AnyConsSignature A := {|
    AnyConsSignature.B := list A;
    AnyConsSignature.C _ _ := list A;
  |}.

  Definition list_no_match (A: Type) := A.

  Canonical Structure list_cons_signature (A: Type)
  : ConsSignature :=
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
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
    }.
  End NatConsSignature.
  Export NatConsSignature(NatConsSignature).

  Canonical Structure nat_cons_signature (op2: NatConsSignature)
  : ConsSignature :=
  {|
    ConsSignature.A := nat;
    ConsSignature.C := op2.(NatConsSignature.C);
  |}.

  Canonical Structure nat_list_Z_cons_signature
  : NatConsSignature :=
  {|
    NatConsSignature.B := list Z;
    NatConsSignature.C _ _ := list Z;
  |}.

  #[export]
  Instance nat_list_Z_cons
  : ConsOperation (nat_cons_signature _) :=
  fun a => List.cons (Z.of_nat a).

  Canonical Structure any_Ensemble_cons_signature (A: Type): AnyConsSignature A := {|
    AnyConsSignature.B := Ensemble A;
    AnyConsSignature.C _ _ := Ensemble A;
  |}.

  Definition Ensemble_no_match (A: Type) := A.

  Canonical Structure Ensemble_cons_signature (A: Type)
  : ConsSignature :=
  {|
    ConsSignature.A := Ensemble_no_match A;
    ConsSignature.B := Ensemble A;
    ConsSignature.C _ _ := Ensemble A;
  |}.

  #[export]
  Instance any_Ensemble_cons (A: Type)
  : ConsOperation (Ensemble_cons_signature A) :=
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
End TypeClassesCanonicalSignature.

(* Fails list_in_cons_nat_nat. *)
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

  #[global]
  Canonical Structure relation_le_signature (A: Type)
  : LESignature :=
  {|
    LESignature.A := relation A;
    LESignature.B := relation A;
    LESignature.C _ _:= Prop;
  |}.

  #[export]
  Instance relation_relation_le (A: Type)
  : LEOperation (relation_le_signature _) :=
  fun (R S: relation A) => RelationClasses.subrelation R S.

  #[global]
  #[universes(polymorphic)]
  Canonical Structure crelation_le_signature@{A1 A2 B C}
    (A: Type@{A1})
  : LESignature :=
  {|
    LESignature.A := crelation@{A1 A2} A;
    LESignature.B := crelation@{A1 A2} A;
    LESignature.C _ _ := Type@{C};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output CRelation} (A: Type@{Input})
  : LEOperation (crelation_le_signature@{Input Output CRelation Output} A) :=
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
       (let '{| AddSignature.C := C; |} := r
            return r.(AddSignature.A) -> r.(AddSignature.B) -> Type in C) a b.
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

  #[global]
  Canonical Structure nat_Z_add_signature: NatAddSignature :=
  {|
    NatAddSignature.B := Z;
    NatAddSignature.C _ _ := Z;
  |}.

  #[export]
  Instance nat_Z_add: AddOperation _ :=
  fun a b => (Z.of_nat a + b)%Z.

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

  Module ConsSignature.
    Structure ConsSignature := {
      A: Type;
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments C : simpl never.
  End ConsSignature.
  Export ConsSignature(ConsSignature).

  Class ConsOperation (r: ConsSignature) :=
  cons: forall (a: r.(ConsSignature.A)) (b: r.(ConsSignature.B)),
        (let '{| ConsSignature.C := C; |} := r
             return r.(ConsSignature.A) -> r.(ConsSignature.B) -> Type in C)
          a b.
  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  Module AnyConsSignature.
    Structure AnyConsSignature (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments B {A}.
    Arguments C {A}.
  End AnyConsSignature.
  Export AnyConsSignature(AnyConsSignature).

  Canonical Structure any_cons (A: Type) (op2: AnyConsSignature A)
  : ConsSignature :=
  {|
    ConsSignature.A := A;
    ConsSignature.C := op2.(AnyConsSignature.C);
  |}.

  Canonical Structure any_list_cons_signature (A: Type): AnyConsSignature A := {|
    AnyConsSignature.B := list A;
    AnyConsSignature.C _ _ := list A;
  |}.

  Definition list_no_match (A: Type) := A.

  Canonical Structure list_cons_signature (A: Type)
  : ConsSignature :=
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
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
    }.
  End NatConsSignature.
  Export NatConsSignature(NatConsSignature).

  Canonical Structure nat_cons_signature (op2: NatConsSignature)
  : ConsSignature :=
  {|
    ConsSignature.A := nat;
    ConsSignature.C := op2.(NatConsSignature.C);
  |}.

  Canonical Structure nat_list_Z_cons_signature
  : NatConsSignature :=
  {|
    NatConsSignature.B := list Z;
    NatConsSignature.C _ _ := list Z;
  |}.

  Canonical Structure nat_default_cons_signature (op2: AnyConsSignature nat)
  : NatConsSignature :=
  {|
    NatConsSignature.B := op2.(AnyConsSignature.B);
    NatConsSignature.C := op2.(AnyConsSignature.C);
  |}.

  #[export]
  Instance nat_list_Z_cons
  : ConsOperation (nat_cons_signature _) :=
  fun a => List.cons (Z.of_nat a).

  Canonical Structure any_Ensemble_cons_signature (A: Type): AnyConsSignature A := {|
    AnyConsSignature.B := Ensemble A;
    AnyConsSignature.C _ _ := Ensemble A;
  |}.

  Definition Ensemble_no_match (A: Type) := A.

  Canonical Structure Ensemble_cons_signature (A: Type)
  : ConsSignature :=
  {|
    ConsSignature.A := Ensemble_no_match A;
    ConsSignature.B := Ensemble A;
    ConsSignature.C _ _ := Ensemble A;
  |}.

  #[export]
  Instance any_Ensemble_cons (A: Type)
  : ConsOperation (Ensemble_cons_signature A) :=
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

  Fail Theorem list_in_cons_nat_nat
  : forall (a: nat) (l: list nat), List.In a (a [::] l).

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
End TypeClassesUnfoldResult.

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

  Module LESignature.
    Structure LESignature := {
      A: TaggedType;
      B: Type;
      #[canonical=no] C: untag A -> B -> Type;
    }.
    Arguments C : simpl never.
  End LESignature.
  Export LESignature(LESignature).

  Class LEOperation (r: LESignature) :=
  le: forall (a: untag r.(LESignature.A)) (b: r.(LESignature.B)),
      (let '{| LESignature.C := C; |} := r
         return (untag r.(LESignature.A) -> r.(LESignature.B) -> Type) in C) a b.

  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  Module AnyLESignature.
    Structure AnyLESignature (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments B {A}.
    Arguments C {A}.
  End AnyLESignature.
  Export AnyLESignature(AnyLESignature).

  Canonical Structure any_le_signature (A: Type) (sig2: AnyLESignature A)
  : LESignature :=
  {|
    LESignature.A := try_second A;
    LESignature.B := sig2.(AnyLESignature.B);
    LESignature.C := let '{| AnyLESignature.C := C; |} := sig2 in C;
  |}.

  Module SpecificLESignature.
    Structure SpecificLESignature := {
      A: Type;
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
  End SpecificLESignature.
  Export SpecificLESignature(SpecificLESignature).

  Canonical Structure specific_le_signature (sig2: SpecificLESignature)
  : LESignature :=
  {|
    LESignature.A := try_first sig2.(SpecificLESignature.A);
    LESignature.B := sig2.(SpecificLESignature.B);
    LESignature.C := let '{| SpecificLESignature.C := C; |} := sig2 in C;
  |}.

  Module NatLESignature.
    Structure NatLESignature := {
      B: TaggedType;
      #[canonical=no] C: nat -> untag B -> Type;
    }.
  End NatLESignature.
  Export NatLESignature(NatLESignature).

  Definition nat_no_match (B: TaggedType): Type := untag B.

  Canonical Structure nat_le_signature (sig2: NatLESignature)
  : SpecificLESignature :=
  {|
    SpecificLESignature.A := nat;
    SpecificLESignature.B := nat_no_match (sig2.(NatLESignature.B));
    SpecificLESignature.C := let '{| NatLESignature.C := C; |} := sig2 in C;
  |}.

  Canonical Structure nat_any_le_branch (sig2: AnyLESignature nat)
  : NatLESignature :=
  {|
    NatLESignature.B := try_second sig2.(AnyLESignature.B);
    NatLESignature.C := let '{| AnyLESignature.C := C; |} := sig2 in C;
  |}.

  Module NatSpecificLESignature.
    Structure NatSpecificLESignature := {
      B: Type;
      #[canonical=no] C: nat -> B -> Type;
    }.
  End NatSpecificLESignature.
  Export NatSpecificLESignature(NatSpecificLESignature).

  Canonical Structure nat_specific_le_signature (sig2: NatSpecificLESignature)
  : NatLESignature :=
  {|
    NatLESignature.B := try_first sig2.(NatSpecificLESignature.B);
    NatLESignature.C := let '{| NatSpecificLESignature.C := C; |} := sig2 in C;
  |}.

  #[global]
  Canonical Structure nat_nat_le_signature: NatSpecificLESignature :=
  {|
    NatSpecificLESignature.B := nat;
    NatSpecificLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance nat_le: LEOperation _ := Nat.le.

  Module ZLESignature.
    Structure ZLESignature := {
      B: TaggedType;
      #[canonical=no] C: Z -> untag B -> Type;
    }.
  End ZLESignature.
  Export ZLESignature(ZLESignature).

  Definition Z_no_match (B: TaggedType): Type := untag B.

  #[global]
  Canonical Structure Z_le_signature (sig2: ZLESignature)
  : SpecificLESignature :=
  {|
    SpecificLESignature.A := Z;
    SpecificLESignature.B := Z_no_match sig2.(ZLESignature.B);
    SpecificLESignature.C := let '{| ZLESignature.C := C; |} := sig2 in C;
  |}.

  Canonical Structure Z_any_le_branch (sig2: AnyLESignature Z)
  : ZLESignature :=
  {|
    ZLESignature.B := try_second sig2.(AnyLESignature.B);
    ZLESignature.C := let '{| AnyLESignature.C := C; |} := sig2 in C;
  |}.

  Module ZSpecificLESignature.
    Structure ZSpecificLESignature := {
      B: Type;
      #[canonical=no] C: Z -> B -> Type;
    }.
  End ZSpecificLESignature.
  Export ZSpecificLESignature(ZSpecificLESignature).

  Canonical Structure Z_specific_le_signature (sig2: ZSpecificLESignature)
  : ZLESignature :=
  {|
    ZLESignature.B := try_first sig2.(ZSpecificLESignature.B);
    ZLESignature.C := let '{| ZSpecificLESignature.C := C; |} := sig2 in C;
  |}.

  #[global]
  Canonical Structure Z_Z_le_signature: ZSpecificLESignature :=
  {|
    ZSpecificLESignature.B := Z;
    ZSpecificLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance Z_le: LEOperation _ := Z.le.

  #[global]
  Canonical Structure Z_nat_le_signature: ZSpecificLESignature :=
  {|
    ZSpecificLESignature.B := nat;
    ZSpecificLESignature.C _ _ := Prop;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation _ :=
  fun a b => (a <= Z.of_nat b)%Z.

  #[global]
  Canonical Structure relation_relation_le_signature (A: Type)
  : SpecificLESignature :=
  {|
    SpecificLESignature.A := relation A;
    SpecificLESignature.B := relation A;
    SpecificLESignature.C _ _:= Prop;
  |}.

  Definition relation_no_match := try_second.

  Canonical Structure unknown_relation_le_signature (A: Type)
  : LESignature :=
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
  : SpecificLESignature :=
  {|
    SpecificLESignature.A := crelation@{A1 A2} A;
    SpecificLESignature.B := crelation@{A1 A2} A;
    SpecificLESignature.C _ _ := Type@{C};
  |}.

  Definition crelation_no_match := try_second.

  #[global]
  #[universes(polymorphic)]
  Canonical Structure unknown_crelation_le_signature@{A1 A2 B C}
    (A: Type@{A1})
  : LESignature :=
  {|
    LESignature.A := crelation_no_match (crelation@{A1 A2} A);
    LESignature.B := crelation@{A1 A2} A;
    LESignature.C _ _ := Type@{C};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output CRelation} (A: Type@{Input})
  : LEOperation
      (specific_le_signature (crelation_crelation_le_signature@{Input Output
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

  Module ConsSignature.
    Structure ConsSignature := {
      A: TaggedType;
      B: Type;
      #[canonical=no] C: untag A -> B -> Type;
    }.
    Arguments C : simpl never.
  End ConsSignature.
  Export ConsSignature(ConsSignature).

  Class ConsOperation (r: ConsSignature) :=
  cons: forall (a: untag r.(ConsSignature.A)) (b: r.(ConsSignature.B)),
        (let '{| ConsSignature.C := C; |} := r
             return untag r.(ConsSignature.A) -> r.(ConsSignature.B) -> Type
             in C)
          a b.
  Infix "[::]" := cons (at level 60, right associativity) : operation_scope.

  Module AnyConsSignature.
    Structure AnyConsSignature (A: Type) := {
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
    Arguments B {A}.
    Arguments C {A}.
  End AnyConsSignature.
  Export AnyConsSignature(AnyConsSignature).

  Canonical Structure any_cons_signature (A: Type) (op2: AnyConsSignature A)
  : ConsSignature :=
  {|
    ConsSignature.A := try_second A;
    ConsSignature.C := op2.(AnyConsSignature.C);
  |}.

  Canonical Structure any_list_cons_signature (A: Type): AnyConsSignature A := {|
    AnyConsSignature.B := list A;
    AnyConsSignature.C _ _ := list A;
  |}.

  Definition list_no_match := try_second.

  Canonical Structure list_cons_signature (A: Type)
  : ConsSignature :=
  {|
    ConsSignature.A := list_no_match A;
    ConsSignature.B := list A;
    ConsSignature.C _ _ := list A;
  |}.

  #[export]
  Instance any_list_cons (A: Type)
  : ConsOperation (list_cons_signature A) :=
  List.cons.

  Module SpecificConsSignature.
    Structure SpecificConsSignature := {
      A: Type;
      B: Type;
      #[canonical=no] C: A -> B -> Type;
    }.
  End SpecificConsSignature.
  Export SpecificConsSignature(SpecificConsSignature).

  Canonical Structure specific_cons_signature (op2: SpecificConsSignature)
  : ConsSignature :=
  {|
    ConsSignature.A := try_first op2.(SpecificConsSignature.A);
    ConsSignature.C := op2.(SpecificConsSignature.C);
  |}.

  Module NatConsSignature.
    Structure NatConsSignature := {
      B: TaggedType;
      #[canonical=no] C: nat -> untag B -> Type;
    }.
  End NatConsSignature.
  Export NatConsSignature(NatConsSignature).

  Canonical Structure nat_cons_signature (op2: NatConsSignature)
  : SpecificConsSignature :=
  {|
    SpecificConsSignature.A := nat;
    SpecificConsSignature.C := op2.(NatConsSignature.C);
  |}.

  Canonical Structure nat_any_cons_branch (op2: AnyConsSignature nat)
  : NatConsSignature :=
  {|
    NatConsSignature.B := try_second op2.(AnyConsSignature.B);
    NatConsSignature.C := op2.(AnyConsSignature.C);
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
  : ConsOperation (specific_cons_signature (nat_cons_signature (nat_specific_cons_signature _))) :=
  fun a => List.cons (Z.of_nat a).

  Canonical Structure any_Ensemble_cons_signature (A: Type): AnyConsSignature A := {|
    AnyConsSignature.B := Ensemble A;
    AnyConsSignature.C _ _ := Ensemble A;
  |}.

  Definition Ensemble_no_match (A: Type) := A.

  Canonical Structure Ensemble_cons_signature (A: Type)
  : SpecificConsSignature :=
  {|
    SpecificConsSignature.A := Ensemble_no_match A;
    SpecificConsSignature.B := Ensemble A;
    SpecificConsSignature.C _ _ := Ensemble A;
  |}.

  #[export]
  Instance any_Ensemble_cons (A: Type)
  : ConsOperation (specific_cons_signature (Ensemble_cons_signature A)) :=
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
