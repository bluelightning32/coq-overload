(* Fails nat_add_0_r, list_in_cons_nat_alias_Z, and list_in_cons_nat_nat. *)

Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.
Require Import Constructive_sets.

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

Module ListLESignature.
  Structure ListLESignature (A: Type) := {
    B: Type;
    #[canonical=no] C: list A -> B -> Type;
  }.
  Arguments B {A}.
  Arguments C {A}.
End ListLESignature.
Export ListLESignature(ListLESignature).

#[global]
Canonical Structure list_le_signature (A: Type) (sig2: ListLESignature A)
: LESignature :=
{|
  LESignature.A := list A;
  LESignature.B := sig2.(ListLESignature.B);
  LESignature.C := sig2.(ListLESignature.C);
|}.

#[global]
Canonical Structure list_list_le_signature (A: Type): ListLESignature A :=
{|
  ListLESignature.B := list A;
  ListLESignature.C _ _ := Prop;
|}.

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

#[export]
Instance list_list_le (A: Type) (c: LEOperation {|
                                                  LESignature.A := A;
                                                  LESignature.B := A;
                                                  LESignature.C _ _ := Prop;
                                                |})
: LEOperation (list_le_signature A (list_list_le_signature A)) :=
fun l1 l2 => lexicographical_le c l1 l2.

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

Definition compare_list_nats (a b: list nat) := a <== b.

Definition compare_list_Zs (a b: list Z) := a <== b.

Definition listZ := list Z.

Definition compare_listZs (a b: listZ) := a <== b.

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
  (* It does work when both arguments are explictly specified. *)
  rewrite nat_add_comm with (m:= n) (n:= 0).
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

Definition nat_alias := nat.

Fail Theorem list_in_cons_nat_alias_Z
: forall (a: nat_alias) (l: list Z), List.In (Z.of_nat a) (a [::] l).

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
