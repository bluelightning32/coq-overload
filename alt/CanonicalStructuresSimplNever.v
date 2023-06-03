(* Fails cbn_simplifies_addition, nat_add_0_r, list_in_cons_nat_alias_Z, and
   list_in_cons_nat_nat. *)

Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.
Require Import Constructive_sets.

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

Module ListLEOperation.
  Structure ListLEOperation (A: Type) := {
    B: Type;
    #[canonical=no] C: list A -> B -> Type;
    #[canonical=no] op: forall a b, C a b;
  }.
  Arguments B {A}.
  Arguments C {A}.
  Arguments op {A}.
End ListLEOperation.
Export ListLEOperation(ListLEOperation).

Canonical Structure list_le (A: Type) (op2: ListLEOperation A)
: LEOperation :=
{|
  LEOperation.op:= op2.(ListLEOperation.op);
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

Module Comparison.
  Structure Comparison := {
    A: Type;
    #[canonical=no] op: A -> A -> Prop;
  }.
End Comparison.
Export Comparison(Comparison).

Canonical Structure nat_comparison
: Comparison :=
{|
  Comparison.A:= nat;
  Comparison.op := Nat.le;
|}.

Canonical Structure Z_comparison
: Comparison :=
{|
  Comparison.A:= Z;
  Comparison.op := Z.le;
|}.

Canonical Structure list_list_le (le: Comparison): ListLEOperation le.(Comparison.A) := {|
  ListLEOperation.op l1 l2 := lexicographical_le le.(Comparison.op) l1 l2;
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

Definition compare_list_nats (a b: list nat) := a <== b.

Definition compare_list_Zs (a b: list Z) := a <== b.

Definition listZ := list Z.

Definition compare_listZs (a b: listZ) := a <== b.

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
  (* Simpl does simplify, but it also strips off the [+] notation on both
     sides. Afterwards the goal is: S (a + b) = S (a + b). *)
  simpl.
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
