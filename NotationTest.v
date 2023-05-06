Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.

Module NativeNotations.
  Declare Scope nat_compare_scope.
  Delimit Scope nat_compare_scope with nat_compare.
  Open Scope nat_compare_scope.

  Infix "<==" := Nat.leb (at level 70, no associativity) : nat_compare_scope.

  Declare Scope Z_compare_scope.
  Delimit Scope Z_compare_scope with Z_compare.
  Open Scope Z_compare_scope.

  Infix "<==" := Z.leb (at level 70, no associativity) : Z_compare_scope.

  Definition compare_nats (a b: nat) := (a <== b)%nat_compare.

  Definition compare_ints (a b: Z) := a <== b.
End NativeNotations.

(* Fails cbn_keeps_notation, relations_reflexive, and crelations_reflexive. *)
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
    result := bool;
    le a b := (a <=? b)%nat;
  |}.

  #[export]
  Instance Z_le: LEOperation Z Z := {|
    result := bool;
    le a b := (a <=? b)%Z;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation Z nat := {|
    result:= bool;
    le a b := (a <=? Z.of_nat b)%Z;
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
  Theorem cbn_keeps_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    (* Ideally this would fail. *)
    progress cbn.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_simplifies_leb: forall (a b: nat), (S a <== S b) = (a <== b).
  Proof.
    intros.
    progress cbn.
    reflexivity.
  Qed.
End TypeClasses1.

(* Fails cbn_keeps_notation and relations_reflexive. *)
Module TypeClasses2.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class LEOperation (A B C: Type) := {
    le: A -> B -> C;
  }.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le: LEOperation nat nat bool := {|
    le a b := (a <=? b)%nat;
  |}.

  #[export]
  Instance Z_le: LEOperation Z Z bool := {|
    le a b := (a <=? b)%Z;
  |}.

  #[export]
  Instance Z_nat_le: LEOperation Z nat bool := {|
    le a b := (a <=? Z.of_nat b)%Z;
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
  Theorem cbn_keeps_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    (* Ideally this would fail. *)
    progress cbn.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_simplifies_leb: forall (a b: nat), (S a <== S b) = (a <== b).
  Proof.
    intros.
    progress cbn.
    reflexivity.
  Qed.
End TypeClasses2.

(* Fails relations_reflexive. *)
Module TypeClasses3.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class LEOperation (A B C: Type) := le: A -> B -> C.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le: LEOperation nat nat bool := fun a b => (a <=? b)%nat.

  #[export]
  Instance Z_le: LEOperation Z Z bool := fun a b => (a <=? b)%Z.

  #[export]
  Instance Z_nat_le: LEOperation Z nat bool :=
  fun a b => (a <=? Z.of_nat b)%Z.

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
  Theorem cbn_keeps_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    Fail progress cbn.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_simplifies_leb: forall (a b: nat), (S a <== S b) = (a <== b).
  Proof.
    intros.
    progress cbn.
    reflexivity.
  Qed.
End TypeClasses3.

(* Fails relations_reflexive and crelations_reflexive. *)
Module TypeClasses4.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Class LEOperationResult (A B: Type) := {
    le_result: Type;
  }.

  Arguments le_result : simpl never.

  Class LEOperation (A B: Type) (C: LEOperationResult A B) := le: A -> B -> @le_result A B C.
  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le_result: LEOperationResult nat nat := Build_LEOperationResult _ _ bool.

  #[export]
  Instance nat_le: LEOperation nat nat _ := fun a b => (a <=? b)%nat.

  #[export]
  Instance Z_le_result: LEOperationResult Z Z := Build_LEOperationResult _ _ bool.

  #[export]
  Instance Z_le: LEOperation Z Z _ := fun a b => (a <=? b)%Z.

  #[export]
  Instance Z_nat_le_result: LEOperationResult Z nat := Build_LEOperationResult _ _ bool.

  #[export]
  Instance Z_nat_le: LEOperation Z nat _ :=
  fun a b => (a <=? Z.of_nat b)%Z.

  #[export]
  Instance relation_relation_le_result (A: Type)
  : LEOperationResult (relation A) (relation A) := Build_LEOperationResult _ _ Prop.

  #[export]
  Instance relation_relation_le (A: Type)
  : LEOperation (relation A) (relation A) _ :=
  fun R S => RelationClasses.subrelation R S.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le_result@{Input Output} (A: Type@{Input})
  : LEOperationResult (crelation@{Input Output} A)
                      (crelation@{Input Output} A) :=
  Build_LEOperationResult _ _ Type@{Output}.

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

  Theorem cbn_keeps_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    Fail progress cbn.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_simplifies_leb: forall (a b: nat), (S a <== S b) = (a <== b).
  Proof.
    intros.
    progress cbn.
    reflexivity.
  Qed.
End TypeClasses4.

(* Passes tests *)
Module TypeClassesCanonicalSignature.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Module LESignature.
    Structure LESignature := {
      A: Type;
      B: Type;
      C: Type;
    }.
    Arguments C : simpl never.
  End LESignature.
  Export LESignature(LESignature).

  #[global]
  Canonical Structure signature (A B C: Type)
  : LESignature :=
  {|
    LESignature.A := A;
    LESignature.B := B;
    LESignature.C := C;
  |}.

  Class LEOperation (r: LESignature) := le: r.(LESignature.A) -> r.(LESignature.B) -> r.(LESignature.C).

  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  #[export]
  Instance nat_le: LEOperation (signature nat nat bool) :=
  fun a b => (a <=? b)%nat.

  #[export]
  Instance Z_le: LEOperation (signature Z Z bool) :=
  fun a b => (a <=? b)%Z.

  #[export]
  Instance Z_nat_le: LEOperation (signature Z nat bool) :=
  fun a b => (a <=? Z.of_nat b)%Z.

  #[global]
  Canonical Structure relation_le_signature (A: Type)
  : LESignature :=
  {|
    LESignature.A := relation A;
    LESignature.B := relation A;
    LESignature.C := Prop;
  |}.

  #[export]
  Instance relation_relation_le (A: Type)
  : LEOperation (relation_le_signature A) :=
  fun R S => RelationClasses.subrelation R S.

  #[global]
  #[universes(polymorphic)]
  Canonical Structure crelation_le_signature@{Input Output} (A: Type@{Input})
  : LESignature :=
  {|
    LESignature.A := crelation@{Input Output} A;
    LESignature.B := crelation@{Input Output} A;
    LESignature.C := Type@{Output};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output} (A: Type@{Input})
  : LEOperation (crelation_le_signature@{Input Output} A) :=
  fun (R S: crelation@{Input Output} A) =>
    CRelationClasses.subrelation@{Input Output Output} R S.

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

  (* Passes *)
  Theorem cbn_keeps_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    Fail progress cbn.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_simplifies_leb: forall (a b: nat), (S a <== S b) = (a <== b).
  Proof.
    intros.
    progress cbn.
    reflexivity.
  Qed.
End TypeClassesCanonicalSignature.

(* Fails cbn_keeps_notation. *)
Module CanonicalStructures.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Module LEOperation.
    Structure LEOperation (B: Type) (C: Type) := {
      A: Type;
      #[canonical=no] op: A -> B -> C;
    }.
  End LEOperation.
  Export LEOperation(LEOperation).

  Definition le {B C: Type} {o: LEOperation B C} := o.(LEOperation.op B C).

  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  Module NatLEOperation.
    Structure NatLEOperation := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] op: nat -> B -> C;
    }.
  End NatLEOperation.
  Export NatLEOperation(NatLEOperation).

  Canonical Structure nat_le (op2: NatLEOperation)
  : LEOperation op2.(NatLEOperation.B) op2.(NatLEOperation.C) :=
  {|
    LEOperation.op:= op2.(NatLEOperation.op);
  |}.

  Canonical Structure nat_nat_le: NatLEOperation := {|
    NatLEOperation.op a b := a <=? b;
  |}.

  Module ZLEOperation.
    Structure ZLEOperation := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] op: Z -> B -> C;
    }.
  End ZLEOperation.
  Export ZLEOperation(ZLEOperation).

  Canonical Structure Z_le (op2: ZLEOperation)
  : LEOperation op2.(ZLEOperation.B) op2.(ZLEOperation.C) :=
  {|
    LEOperation.op:= op2.(ZLEOperation.op);
  |}.

  Canonical Structure Z_Z_le: ZLEOperation := {|
    ZLEOperation.op a b := (a <=? b)%Z;
  |}.

  Canonical Structure Z_nat_le: ZLEOperation := {|
    ZLEOperation.op a b := (a <=? Z.of_nat b)%Z;
  |}.

  Module RelationLEOperation.
    Structure RelationLEOperation (A: Type) := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] op: relation A -> B -> C;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End RelationLEOperation.
  Export RelationLEOperation(RelationLEOperation).

  Canonical Structure relation_le (A: Type) (op2: RelationLEOperation A)
  : LEOperation op2.(RelationLEOperation.B) op2.(RelationLEOperation.C) :=
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
      #[canonical=no] C: Type@{C};
      #[canonical=no] op: crelation@{Input Output} A -> B -> C;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End CRelationLEOperation.
  Export CRelationLEOperation(CRelationLEOperation).

  #[universes(polymorphic)]
  Canonical Structure crelation_le@{Input Output B C} (A: Type@{Input})
    (op2: CRelationLEOperation@{Input Output B C} A)
  : LEOperation op2.(CRelationLEOperation.B) op2.(CRelationLEOperation.C) :=
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
    CRelationLEOperation.C := Type@{Result};
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

  (* Fails *)
  Theorem cbn_keeps_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    (* Ideally this would not make progress. *)
    progress cbn.
    reflexivity.
  Qed.

  (* Passes *)
  Theorem cbn_simplifies_leb: forall (a b: nat), (S a <== S b) = (a <== b).
  Proof.
    intros.
    progress cbn.
    reflexivity.
  Qed.
End CanonicalStructures.

Module CanonicalStructuresSimplNever.
  Declare Scope operation_scope.
  Delimit Scope operation_scope with operation.
  Open Scope operation_scope.

  Module LEOperation.
    Structure LEOperation (B: Type) (C: Type) := {
      A: Type;
      #[canonical=no] op: A -> B -> C;
    }.
    Arguments op: simpl never.
  End LEOperation.
  Export LEOperation(LEOperation).

  Definition le {B C: Type} {o: LEOperation B C} := o.(LEOperation.op B C).

  Infix "<==" := le (at level 70, no associativity) : operation_scope.

  Module NatLEOperation.
    Structure NatLEOperation := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] op: nat -> B -> C;
    }.
    Arguments B: simpl never.
    Arguments C: simpl never.
  End NatLEOperation.
  Export NatLEOperation(NatLEOperation).

  Canonical Structure nat_le (op2: NatLEOperation)
  : LEOperation op2.(NatLEOperation.B) op2.(NatLEOperation.C) :=
  {|
    LEOperation.op:= op2.(NatLEOperation.op);
  |}.

  Canonical Structure nat_nat_le: NatLEOperation := {|
    NatLEOperation.op a b := a <=? b;
  |}.

  Module ZLEOperation.
    Structure ZLEOperation := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] op: Z -> B -> C;
    }.
  End ZLEOperation.
  Export ZLEOperation(ZLEOperation).

  Canonical Structure Z_le (op2: ZLEOperation)
  : LEOperation op2.(ZLEOperation.B) op2.(ZLEOperation.C) :=
  {|
    LEOperation.op:= op2.(ZLEOperation.op);
  |}.

  Canonical Structure Z_Z_le: ZLEOperation := {|
    ZLEOperation.op a b := (a <=? b)%Z;
  |}.

  Canonical Structure Z_nat_le: ZLEOperation := {|
    ZLEOperation.op a b := (a <=? Z.of_nat b)%Z;
  |}.

  Module RelationLEOperation.
    Structure RelationLEOperation (A: Type) := {
      B: Type;
      #[canonical=no] C: Type;
      #[canonical=no] op: relation A -> B -> C;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End RelationLEOperation.
  Export RelationLEOperation(RelationLEOperation).

  Canonical Structure relation_le (A: Type) (op2: RelationLEOperation A)
  : LEOperation op2.(RelationLEOperation.B) op2.(RelationLEOperation.C) :=
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
      #[canonical=no] C: Type@{C};
      #[canonical=no] op: crelation@{Input Output} A -> B -> C;
    }.
    Arguments B {A}.
    Arguments C {A}.
    Arguments op {A}.
  End CRelationLEOperation.
  Export CRelationLEOperation(CRelationLEOperation).

  #[universes(polymorphic)]
  Canonical Structure crelation_le@{Input Output B C} (A: Type@{Input})
    (op2: CRelationLEOperation@{Input Output B C} A)
  : LEOperation op2.(CRelationLEOperation.B) op2.(CRelationLEOperation.C) :=
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
    CRelationLEOperation.C := Type@{Result};
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

  (* Passes *)
  Theorem cbn_keeps_notation: forall (a b: nat), (a <== b) = (a <== b).
  Proof.
    intros.
    Fail progress cbn.
    reflexivity.
  Qed.

  (* Fails *)
  Theorem cbn_simplifies_leb: forall (a b: nat), (S a <== S b) = (a <== b).
  Proof.
    intros.
    (* Ideally this would make progres. *)
    Fail progress cbn.
    reflexivity.
  Qed.
End CanonicalStructuresSimplNever.
