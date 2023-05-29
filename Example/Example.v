Require Import ZArith.
Require Import List.
Require Import Relations.
Require Import RelationClasses.
Require Import CRelationClasses.
Require Import Constructive_sets.
Require Import Overload.SigId.
Require Import Overload.Binary.

(* Passes *)
Module TypeClassesTagged.
  Declare Scope overload_scope.
  Delimit Scope overload_scope with o.
  Open Scope overload_scope.

  Module LEId: SigId.
  End LEId.
  Module LESignature := Binary.Signature LEId.
  Export (canonicals) LESignature.

  Class LEOperation (r: LESignature.S) :=
  le: forall (a: untag r.(LESignature.A)) (b: r.(LESignature.B)),
      (let '{| LESignature.C := C; |} := r
         return (untag r.(LESignature.A) -> r.(LESignature.B) -> Type) in C) a b.

  Infix "<==" := le (at level 70, no associativity) : overload_scope.

  Module NatWrapper<: TypeModule.
    Definition P := unit.
    Definition T (_: P) := nat.
  End NatWrapper.

  Module NatLESignature := Binary.Branch LESignature NatWrapper.
  Export (canonicals) NatLESignature.

  Canonical Structure nat_le_branch (sig2: NatLESignature.AnySpecificBranch tt)
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
    Definition T (_: P) := Z.
  End ZWrapper.

  Module ZLESignature := Binary.Branch LESignature ZWrapper.
  Export (canonicals) ZLESignature.

  Canonical Structure Z_le_branch (sig2: ZLESignature.AnySpecificBranch tt)
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

  Module ListWrapper<: TypeModule.
    Definition P := Type.
    Definition T (A: P) := list A.
  End ListWrapper.

  Module ListLESignature := Binary.Branch LESignature ListWrapper.
  Export (canonicals) ListLESignature.

  Canonical Structure list_le_branch
    (A: Type) (sig2: ListLESignature.AnySpecificBranch A)
  : LESignature.Specific :=
  LESignature.make_specific (list A) (ListLESignature.make_branch A sig2).

  #[global]
  Canonical Structure list_list_le_signature (A: Type) (B: Type)
  : ListLESignature.S A :=
  {|
    ListLESignature.B := list B;
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
  Instance list_list_le (A: Type)
                        (o: LEOperation {|
                                          LESignature.A := {| untag:= A; |};
                                          LESignature.B := A;
                                          LESignature.C _ _ := Prop;
                        |})
  : LEOperation _ :=
  lexicographical_le (@le _ o).

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
  Canonical Structure crelation_crelation_le_signature@{A1 A2 CRelation}
    (A: Type@{A1})
  : LESignature.Specific :=
  {|
    LESignature.Specific.A := crelation@{A1 A2} A;
    LESignature.Specific.B := crelation@{A1 A2} A;
    LESignature.Specific.C _ _ := Type@{CRelation};
  |}.

  Definition crelation_no_match := try_second.

  #[global]
  #[universes(polymorphic)]
  Canonical Structure unknown_crelation_le_signature@{A1 A2 CRelation C}
    (A: Type@{A1})
  : LESignature.S :=
  {|
    LESignature.A := crelation_no_match (crelation@{A1 A2} A);
    LESignature.B := crelation@{A1 A2} A;
    LESignature.C _ _ := Type@{CRelation};
  |}.

  #[export]
  #[universes(polymorphic)]
  Instance crelation_crelation_le@{Input Output CRelation Result} (A: Type@{Input})
  : LEOperation
      (LESignature.specific (crelation_crelation_le_signature@{Input Output
                                                               CRelation}
                               A)) :=
  fun (R S: crelation@{Input Output} A) =>
    CRelationClasses.subrelation@{Input Output Output} R S.

  Definition compare_nats (a b: nat) := a <== b.

  Definition compare_ints (a b: Z) := a <== b.

  Definition compare_Z_nat (a: Z) (b: nat) := a <== b.

  Definition compare_list_nats (a b: list nat) := a <== b.

  Definition compare_list_Zs (a b: list Z) := a <== b.

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

  Module AddId: SigId.
  End AddId.
  Module AddSignature := Binary.Signature AddId.
  Export (canonicals) AddSignature.

  Class AddOperation (r: AddSignature.S) :=
  add: forall (a: untag r.(AddSignature.A)) (b: r.(AddSignature.B)),
       (let '{| AddSignature.C := C; |} := r
            return untag r.(AddSignature.A) -> r.(AddSignature.B) -> Type in C) a b.
  Infix "[+]" := add (at level 50, left associativity) : overload_scope.

  Module NatAddSignature := Binary.Branch AddSignature NatWrapper.
  Export (canonicals) NatAddSignature.
  Canonical Structure nat_add_branch (sig2: NatAddSignature.AnySpecificBranch tt)
  : AddSignature.Specific :=
  AddSignature.make_specific nat (NatAddSignature.make_branch tt sig2).

  #[global]
  Canonical Structure nat_nat_add_signature: NatAddSignature.S tt :=
  {|
    NatAddSignature.B := nat;
    NatAddSignature.C _ _ := nat;
  |}.

  #[export]
  Instance nat_add: AddOperation _ := Nat.add.

  Module ZAddSignature := Binary.Branch AddSignature ZWrapper.
  Export (canonicals) ZAddSignature.
  Canonical Structure Z_add_branch (sig2: ZAddSignature.AnySpecificBranch tt)
  : AddSignature.Specific :=
  AddSignature.make_specific Z (ZAddSignature.make_branch tt sig2).

  #[global]
  Canonical Structure Z_Z_add_signature: ZAddSignature.S tt :=
  {|
    ZAddSignature.B := Z;
    ZAddSignature.C _ _ := Z;
  |}.

  #[export]
  Instance Z_add: AddOperation _ := Z.add.

  #[global]
  Canonical Structure Z_nat_add_signature: ZAddSignature.S tt :=
  {|
    ZAddSignature.B := nat;
    ZAddSignature.C _ _ := Z;
  |}.

  #[export]
  Instance Z_nat_add: AddOperation _ :=
  fun a b => (a + Z.of_nat b)%Z.

  #[global]
  Canonical Structure nat_Z_add_signature: NatAddSignature.S tt :=
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
      B: TaggedType@{B};
      #[canonical=no] C: Type@{U} -> untag B -> Type@{C};
    }.
  End TypeAddSignature.
  Export TypeAddSignature(TypeAddSignature).

  Definition Type_no_match (B: TaggedType): Type := untag B.

  #[universes(polymorphic)]
  Canonical Structure Type_add_signature@{U} (sig2: TypeAddSignature)
  : AddSignature.Specific :=
  {|
    AddSignature.Specific.A := Type@{U};
    AddSignature.Specific.B := Type_no_match (sig2.(TypeAddSignature.B));
    AddSignature.Specific.C := let '{| TypeAddSignature.C := C; |} := sig2 in C;
  |}.

  #[universes(polymorphic)]
  Canonical Structure Type_any_add_branch@{U} (sig2: AddSignature.Any Type@{U})
  : TypeAddSignature :=
  {|
    TypeAddSignature.B := try_second sig2.(AddSignature.Any.B);
    TypeAddSignature.C := let '{| AddSignature.Any.C := C; |} := sig2 in C;
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
  : AddSignature.Specific := Type_add_signature@{Set} sig2.
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

  Module ConsId : SigId.
  End ConsId.
  Module ConsSignature := Binary.Signature ConsId.
  Export (canonicals) ConsSignature.

  Class ConsOperation (r: ConsSignature.S) :=
  cons: forall (a: untag r.(ConsSignature.A)) (b: r.(ConsSignature.B)),
        (let '{| ConsSignature.C := C; |} := r
             return untag r.(ConsSignature.A) -> r.(ConsSignature.B) -> Type
             in C)
          a b.
  Infix "[::]" := cons (at level 60, right associativity) : overload_scope.

  Canonical Structure any_list_cons_signature (A: Type): ConsSignature.Any A := {|
    ConsSignature.Any.B := list A;
    ConsSignature.Any.C _ _ := list A;
  |}.

  Definition list_no_match := try_second.

  Canonical Structure unknown_list_cons_signature (A: Type)
  : ConsSignature.S :=
  {|
    ConsSignature.A := list_no_match A;
    ConsSignature.B := list A;
    ConsSignature.C _ _ := list A;
  |}.

  #[export]
  Instance any_list_cons (A: Type)
  : ConsOperation (unknown_list_cons_signature A) :=
  List.cons.

  Module NatConsSignature := Binary.Branch ConsSignature NatWrapper.
  Export (canonicals) NatConsSignature.
  Canonical Structure nat_cons_branch (sig2: NatConsSignature.AnySpecificBranch tt)
  : ConsSignature.Specific :=
  ConsSignature.make_specific nat (NatConsSignature.make_branch tt sig2).

  Canonical Structure nat_list_Z_cons_signature
  : NatConsSignature.S tt :=
  {|
    NatConsSignature.B := list Z;
    NatConsSignature.C _ _ := list Z;
  |}.

  #[export]
  Instance nat_list_Z_cons
  : ConsOperation _ :=
  fun a => List.cons (Z.of_nat a).

  Canonical Structure any_Ensemble_cons_signature (A: Type): ConsSignature.Any A := {|
    ConsSignature.Any.B := Ensemble A;
    ConsSignature.Any.C _ _ := Ensemble A;
  |}.

  Definition Ensemble_no_match (A: Type) := A.

  Canonical Structure unknown_Ensemble_cons_signature (A: Type)
  : ConsSignature.Specific :=
  {|
    ConsSignature.Specific.A := Ensemble_no_match A;
    ConsSignature.Specific.B := Ensemble A;
    ConsSignature.Specific.C _ _ := Ensemble A;
  |}.

  #[export]
  Instance any_Ensemble_cons (A: Type)
  : ConsOperation (ConsSignature.specific (unknown_Ensemble_cons_signature A)) :=
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

  Goal forall (m n: nat), S m <== S n -> m <== n.
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

  Goal forall (m n: nat), S m <== S n -> m <== n.
  Proof.
    (* Now auto works because it can see that <== is <=. *)
    auto with arith.
  Qed.
End TypeClassesTagged.
