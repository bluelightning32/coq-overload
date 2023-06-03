# Evolution of the Overload library

This document describes the eovlution of the Overload library as a way to
document its internal implementation. It especially describes why such a
complicated implementation is necessary.

Most sections of this document correspond to one of the .v files in the
directory.

## Native notations

The traditional way to overload a notation in Coq is to declare it in multiple
scopes. Each scope has a different overload of the notation.

The problem is that the scopes have a simple precedence, set by the Open Scope
command. So one either has to keep opening and closing scopes (adjusting their
precedence) depending on which one is needed for a specific definition, or one
needs to use the `( _ )%scope_key` syntax to specify which scope an expression
should be parsed with. In the example below, `compare_nats` has to use the
scope_key because Z_op_scope (not nat_op_scope) is at the top of the
scope stack (set with the Open Scope command).
```
Infix "<==" := Nat.le (at level 70, no associativity) : nat_op_scope.
Infix "<==" := Z.le : Z_op_scope.

Open Scope nat_op_scope.
Open Scope Z_op_scope.

Definition compare_nats (a b: nat) := (a <== b)%nat_op.

Definition compare_ints (a b: Z) := a <== b.
```

The `Bind Scope` command can be used to automatically adjust the scope stack
depending on what type the expression is expected to have. However, this cannot
differentiate between two notations that have the same output type. In the
example above, `nat <== nat` and `Z <== Z` both produce a `Prop`. So the best
one could do is bind one of them to the `Prop` type.

## Type classes

Type classes provide a great deal of flexibility, because type class resolution
uses a variant of the `eauto` algorithm. Here's the most straight forward way
to describe an overloadable operation with a type class.
```
Class LEOperation (A B: Type) := {
  le_result: A -> B -> Type;
  le a b: le_result a b;
}.
Infix "<==" := le (at level 70, no associativity) : operation_scope.
```

One problem with this simple use of type classes is that the `cbn` tactic
simplifies away the overloaded notation, instead of just simplifying under the
notation.
```
Theorem cbn_keeps_le_notation: forall (a b: nat), (a <== b) = (a <== b).
Proof.
  intros.
  (* Goal is now: (a <== b) = (a <== b) *)
  cbn.
  (* Goal is now: Nat.le a b = Nat.le a b *)
  Fail match goal with
  | |- context [a <== b] => idtac
  end.
  reflexivity.
Qed.
```

## Definitional type classes

The `cbn` problem can be solved by using a definitional type class (also called
a singleton class) instead of a record type class. The first step toward
converting to a definitional type class is change the record to only have one
field. So the output type is moved out of the record and into a parameter of
the type class (see TypeClassesOutputParam.v).
```
Class LEOperation (A B: Type) (C: A -> B -> Type) := {
  le a b: C a b;
}.
```

Now that the type class only has one field, that one field can be promoted into
the type class itself (the type class is no longer a record).
```
Class LEOperation (A B: Type) (C: A -> B -> Type) := le a b: C a b.
```

That solves the simplification problem shown above in `cbn_keeps_le_notation`.
However, it still has a problem (that the previous attempts also had). The type
class resolution. The overloaded notations do not work where a type is expected
(after the `:`), because the unification algorithm expects the expression to
resolve to `Set`, `Prop`, or `Type` before the type class resolution has run.
```
#[export]
Instance relation_relation_le (A: Type)
: LEOperation (relation A) (relation A) (fun _ _ => Prop) :=
fun R S => RelationClasses.subrelation R S.

(* Fails with:
The term "R0 <== R0" has type "?C@{R0:=R; R:=R0} R0 R0"
which should be Set, Prop or Type.
*)
Fail Definition relations_reflexive (A: Type)
: forall (R R: relation A), R <== R.
```

## Canonical structures

Canonical structures predate type classes. They are less flexible and not
documented as well as type classes. However, the canonical structure resolution
runs as part of the unification algorithm, which runs early enough to pass the
`relations_reflexive` test case shown earlier.

The `Structure` command is used to declare a record type. The canonical
structures resolution algorithm can try to find instances of that record. It
will only find record instances that are declared using the `Canonical
Structure` command. The resolution algorithm is invoked when `v1 : h1 a1 a2 ..
an` needs to be unified against `param_name : h2 a1 a2 ... an`. This typically
occurs when `v1` is passed as an argument to a function that has `param_name`
as a binder. The resolution only uses the head constant (`h1`) to find a
matching canonical instance. However, that canonical instance can take
parameters, which then also need to be solved by unification/canonical
structures resolution.

Declaring a canonical sturcture for the operation registers it as a problem
that can be solved with canonical structure resolution. Pointing the notation
to that structure tells Coq when to use the canonical structure resolution.
```
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
```

The resolution will look for an instance of `LEOperation` whose head constant
of `A` matches the type of the first argument to `<==`. Notably, the resolution
will typically ignore the `B`, `C`, and `op` fields. Of course unification
looks at those fields, and will fail to accept the command if the canonical
structure resolution picked the wrong instance.

So the trick is to have canonical instances that only resolve the type of the
first notation argument. However, picking the correct arguments for that
instance then involves resolving the type of the second notation argument. In
the below example, a branch is declared that accepts nat for the first
argument. `nat_le` registers itself as a solution to the overload when the
first type is a `nat`. `NatLEOperation` is declared as the problem of resolving
the second argument when the first argument is a nat. `nat_le` takes a
`NatLEOperation` as a parameter to link the two problems together.
```
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
  LEOperation.A:= nat;
  LEOperation.op:= op2.(NatLEOperation.op);
|}.
```

Finally an instance of `NatLEOperation` is defined to finish the overload of `nat <== nat`.
```
Canonical Structure nat_nat_le: NatLEOperation := {|
  NatLEOperation.B:= nat;
  NatLEOperation.op := Nat.le;
|}.
```

This canonical structures implemenation passes the `relations_reflexive` test
case shown earlier. However, it fails the `cbn_keeps_le_notation` test case
that passed with the definitional type class design.

## Canonical structures with simplification blocked

The previous canonical structures design simplified the notation too easily.
This can be solved by marking the output type (`C`) and the operation (`op`) as
never simplifiable.
```
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
```

This passes most tests. However, now it does not simplify the operation under
the notation. In the below example, `nat [+] nat => nat` is defined as standard
`nat` addition. Ideally `cbn` would simplify the `S a [+] b` into
`S (a [+] b)`. The `simpl` tactic still simplifies `S a [+] b`, but it goes too
far and strips off the `[+]` notation and leaves `S (a + b)`.
```
Theorem cbn_simplifies_addition: forall (a b: nat), S a [+] b = S (a [+] b).
Proof.
  intros.
  (* Ideally this would pass. *)
  Fail progress cbn.
  (* Afterwards the goal is: S (a + b) = S (a + b). *)
  simpl.
  reflexivity.
Qed.
```

## Type classes for operation with canonical structures for the signature

The type classes design passed the `cbn_simplifies_addition` test but failed
the `relations_reflexive` test which canonical structures passed. Combining the
two designs allows both tests to pass. Canonical structures can be used to
declare a signature for the overload, which determines the type of the
arguments and type of the result of the notation. Those are the parts that
needed to run early to pass the `relations_reflexive` test. The actual
operation can be performed later by type classes. Using type classes for the
operation brings their better expression simplification behavior.

```
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
```

The output type (`C`) is dependent (it may depend on the values of the first
two parameters). This causes a problem for rewrite lemmas. In the below
example, the resulting types of `n [+] 0` and `m [+] n` both evaluate to `nat`.
However, the `rewrite` tactic sees them as syntactically different:
`AddSignature.C (nat_add_signature nat_nat_add_signature) n O` and
`AddSignature.C (nat_add_signature nat_nat_add_signature) m n`. As such, the
rewrite tactic fails unless the arguments are explicitly specified.
```
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
  (* Works when the arguments are explicitly specified. *)
  rewrite nat_add_comm with (m:= n) (n:= 0).
Abort.
```

## Type classes and canonical structures with a destructuring let

The unification algorithm can be cajoled into performing a little
simplification on the output type before entering proof mode, by declaring the
output type of the operation with a destructing let instead of a projection.
```
Class LEOperation (r: LESignature) :=
le: forall (a: r.(LESignature.A)) (b: r.(LESignature.B)),
    (let '{| LESignature.C := C; |} := r
       return (r.(LESignature.A) -> r.(LESignature.B) -> Type) in C) a b.
```

Now in `nat_add_0_r`, instead of a goal of `@eq (AddSignature.C ...) ... ...`
it is `@eq nat ... ...`. Now that it is no longer a dependent type, the
`rewrite` tactic works.
```
Theorem nat_add_0_r : forall (n: nat), n [+] 0 = n.
Proof.
  intros.
  rewrite nat_add_comm.
  reflexivity.
Qed.
```
