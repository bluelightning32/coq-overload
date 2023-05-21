Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.
Require Import Constructive_sets.

(* Passes *)
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
