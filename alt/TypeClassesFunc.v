(* Fails relations_reflexive, crelations_reflexive, nat_le_reflexive,
   nat_plus_0_r_le, list_cons_le, and ensemble_cons_le.
   list_of_n_sum_types half fails.
 *)

Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.
Require Import Constructive_sets.

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

Fixpoint lexicographical_le {A: Type} (le: A -> A -> Prop) (l1 l2: list A)
: Prop :=
match l1 with
| nil => True
| h1 :: l1 =>
  match l2 with
  | nil => False
  | h2 :: l2 =>
    le h1 h2 /\ (~le h2 h1 \/ lexicographical_le le l1 l2)
  end
end.

(* l1 <= l2, if l1 is a suffix of l2. *)
#[export]
Instance list_le (A: Type) (c: LEOperation A A (fun _ _ => Prop))
: LEOperation (list A) (list A) (fun _ _ => Prop) :=
fun l1 l2 => lexicographical_le c l1 l2.

(* B <= C, if B is a subset of C. *)
#[export]
Instance ensemble_le (A: Type)
: LEOperation (Ensemble A) (Ensemble A) (fun _ _ => Prop) :=
fun B C => Included _ B C.

Definition compare_nats (a b: nat) := a <== b.

Definition compare_ints (a b: Z) := a <== b.

Definition compare_Z_nat (a: Z) (b: nat) := a <== b.

Definition compare_list_nats (a b: list nat) := a <== b.

Definition compare_list_Zs (a b: list Z) := a <== b.

Definition listZ := list Z.

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
