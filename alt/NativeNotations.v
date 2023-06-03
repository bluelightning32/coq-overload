Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.
Require Import Constructive_sets.

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

Infix "<==" := Z.le : Z_op_scope.

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
