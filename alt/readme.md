# Evolution of the Overload library

This document describes the eovlution of the Overload library as a way to
document its internal implementation. It especially describes why such a
complicated implementation is necessary.

Each section of this document corresponds to one of the .v files in this
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
Structure` command. The resolution algorithm is invoked during function
application. Roughly, when `v1 : h1 a1 a2 ... an` is applied to `f: forall
(param: S.(h2) b1 b2 ... bn)` (that is `f v1`), then the resolution tries to
find a value for `S` with hope that `h1 a1 a2 ... an` unifies with `S.(h2) b1
b2 ... bn`.

Declaring a canonical structure for the operation registers it as a problem
that can be solved with canonical structure resolution. Pointing the notation
to that structure tells Coq to canonical structure resolution to determine the
types and operation of the notation.
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

When the notation is used, unification will look for an instance `o` of type
`LEOperation` whose head constant of `o.(A)` matches the type of the first
argument to `<==`. Notably, unification always starts with the `A` field, which
means that `o` is chosen without first checking whether fields `B`, `C`, and
`op` match the notation. However, those fields are checked after the fact, and
the type checking will fail if the fields do not match for the chosen `o`. With
a naive implementation, `B` would be checked too late to allow overloading the
notation's second argument.

So the trick is to ensure that the canonical instances of `LEOperation` only
resolve the first notation argument. However, that chosen `LEOperation`
instance actually takes another canonical structure as a parameter. Resolving
that parameter to the canonical structure also results in resolving the second
argument of the notation overload.

In the below example, `nat_le` is chosen when the first argument of the
notation is a `nat`. However, `nat_le` takes a parameter `op2` of type
`NatLEOperation`, which resolves the second argument of the notation, only
after the first argument is already known to have type `nat`.
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

As an example, let's walk through how
`Definition compare_nats (a b: nat) := a <== b.` is type checked.
1. The notation is parsed, and placeholders are added for implicit arguments:
   `Definition compare_nats (m n: nat) : ?o.(LEOperation.C) m n := @le ?o m n.`
2. `@le ?o m` is a function application. `@le ?o` has type `forall (a:
   ?o.(LEOperation.A)), ...`, where the type of the `a` is a projection of a
   canonical structure. So canonical structure resolution is invoked.
3. `Print Canonical Projections.` reports `nat <- LEOperation.A ( nat_le )`. So
   since `m` has type `nat` and it's being unified with the `LEOperation.A`
   field of `?o`, `nat_le` is chosen for `?o`. With `?o` substituted, the new command is
   `Definition compare_nats (m n: nat) : (nat_le ?op2).(LEOperation.C) m n  := @le (nat_le ?op2) m n.`
4. `@le (nat_le ?op2) m n` is a function application. `@le (nat_le ?op2) m` has
   type `forall (b: ?op2.(NatLEOperation.B)), ...`, where the type of the `b`
   is a projection of a canonical structure. So canonical structure resolution
   is invoked.
5. `Print Canonical Projections.` reports
   `nat <- NatLEOperation.B ( nat_nat_le )`. So since `n` has type `nat` and
   it's being unified with the `NatLEOperation.B` field of `?op2`, `nat_nat_le`
   is chosen for `?op2`. With `?op2` substituted, all of the unification
   variables are resolved. The new command is:
   `Definition compare_nats (m n: nat) : (nat_le nat_nat_le).(LEOperation.C) m n  := @le (nat_le nat_nat_le) m n.`

Note that the resolution only uses the head constant to find a matching
canonical instance. For example, the following canonical instance sets the
`NatConsOperation.B` field to `list Z`. However, as shown by `Print Canonical
Projections`, canonical structures resolution only uses the head constant,
which is `list`.
```
Canonical Structure nat_list_Z_cons
: NatConsOperation :=
{|
  NatConsOperation.B := list Z;
  NatConsOperation.C _ _ := list Z;
  NatConsOperation.op a := List.cons (Z.of_nat a);
|}.

(* Prints:
   list <- NatConsOperation.B ( nat_list_Z_cons )
 *)
Print Canonical Projections.
```

This canonical structures implemenation passes the `relations_reflexive` test
case shown earlier. However, it fails the `cbn_keeps_le_notation` test case
that passed with the definitional type class design.

## Canonical structures with simplification blocked

The previous canonical structures design simplified the notation too easily.
This can be solved by marking the output type `C` and the operation `op` as
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

This design stilll has a problem. The problem is shared will all previous
canonical structure based designs. To explain the problem, first the cons
notation needs to be explained. The following two overloads are enough to
demonstrate the problem.

| First argument  | Infix operator | Second argument  | Result type | Operation |
| --------------- | -------------- | ---------------- | ----------- | --------- |
| `?A`            | `[::]`         | `list ?A`        | `list ?A`   | `List.cons` |
| `nat`           | `[::]`         | `list Z`         | `list Z`    | `List.cons (Z.of_nat a) b` |

If the type of the first argument matches the type of the list, then the first
overload should be used. If the first argument is a `nat` and the second
argument is a `list Z`, then the second overload should be used. Note that
`nat [::] list nat` should use the first overload.

The type of the first argument could be anything. Declaring a new canonical
instance for every possible type would be too tedious. Instead a special
canonical instance is used that acts like a wildcard. The wildcard behavior is
engaged by setting a field equal to a parameter of the instance. Below,
`ConsSignature.A` is a wildcard field, because it is set to the `A` parameter.
```
Canonical Structure any_cons (A: Type) (op2: AnyConsSignature A)
: ConsSignature :=
{|
  ConsSignature.A := A;
  ConsSignature.C := op2.(AnyConsSignature.C);
|}.
```

`Print Canonical Projections` shows the wildcard as `_`.
```
(* Prints: _ <- ConsSignature.A ( any_cons ) *)
Print Canonical Projections.
```

The first argument is also overloaded differently when it is a `nat`.
```
Canonical Structure nat_cons_signature (op2: NatConsSignature)
: ConsSignature :=
{|
  ConsSignature.A := nat;
  ConsSignature.C := op2.(NatConsSignature.C);
|}.
```

So the canonical structures resolution has to decide whether to take the
`nat_cons_signature` branch (that can only accept `nat`) or the wildcard branch
(that can accept everything). The `nat_cons_signature` branch takes precedence
when the type of the first argument is syntactically equal to `nat`. However,
there are two cases where the wrong branch is taken.

One case is for the `nat [::] list nat` overload. The `nat_cons_signature`
branch is taken. However, the only `NatConsSignature` instance takes a `list Z`
as the second argument (not `list nat`). The unification algorithm does not
backtrack and change to the `any_cons` branch. Instead it just fails:
```
(* Fails with:
    The term "l" has type "list nat" while it is expected to have type
     "ConsSignature.B (nat_cons_signature ?n)".
*)
Fail Theorem list_in_cons_nat_nat
: forall (a: nat) (l: list nat), List.In a (a [::] l).
```

It would be possible to solve this by adding a `NatConsSignature` instance that
takes a `list nat` and redirects back to the correct `AnyConsSignature`
instance. However, this gets tedious if more notation overload are added that
take a wildcard for the first argument and something else for the second
argument, such as `?A [::] Ensemble ?A`.

The second case where the wrong branch is taken is when the first argument has
a type that is an alias of `nat`. The type is convertible to `nat`, but it is
not syntactically equaly to `nat`. So the `any_cons` branch is incorrectly
taken. The canonical structure resolution fails instead of backtracking.
```
Definition nat_alias := nat.

(* Fails with:
    The term "l" has type "list Z" while it is expected to have type
     "ConsSignature.B (any_cons nat_alias ?a)".
*)
Fail Theorem list_in_cons_nat_alias_Z
: forall (a: nat_alias) (l: list Z), List.In (Z.of_nat a) (a [::] l).
```

## Type classes and canonical structures with tagging

This approach uses "tagging" from
[How to make ad hoc proof automation less ad hoc](https://dl.acm.org/doi/10.1145/2034773.2034798)
to provide more control over how the canonical structures resolution fallsback
from the branch for a specific type to the wildcard branch.

`TaggedType` is basically a wrapper around `Type`. It has exactly one field,
called `untag`, which is the wrapped type. The reason its constructor is called
`try_second` will be explained shortly.
```
#[universes(polymorphic)]
Structure TaggedType@{U} := try_second {
  untag: Type@{U};
}.
```

Only one canonical instance for `TaggedType` is defined. The canonical instance
is called `try_first`, and it is an alias for the real constructor,
`try_second`. When `a : T` needs to be unified against `b : untag ?U`, the
canonical structure resolution will first try to set `?U` to `try_first T`,
replacing the first expression with `a : untag (try_first T)`. Later if the
canonical structure resolution fails on `untag (try_first T)`, unification will
go back and unfold `try_first` to replace the original expression with
`a : untag (try_second T)`, then try canonical structure resolution again.
Hence, the reason for the names `try_first` and `try_second`.
```
Canonical Structure try_first (A: Type) := try_second A.
```

A tagged type is used for the first argument of the signature to solve the
`list_in_cons_nat_alias_Z` problem. Unification will unfold `nat_alias` to
`nat` and try the primary branch again. If it failed after unfolding (it
succeeds in the case of `list_in_cons_nat_alias_Z`), then only then it would
fallback to the wildcard `try_second` branch.
```
Module LESignature.
  Structure LESignature := {
    A: TaggedType;
    B: Type;
    #[canonical=no] C: untag A -> B -> Type;
  }.
  Arguments C : simpl never.
End LESignature.
Export LESignature(LESignature).
```

The signatures that determine the notation's second argument also use tagged
types.
```
Module NatLESignature.
  Structure NatLESignature := {
    B: TaggedType;
    #[canonical=no] C: nat -> untag B -> Type;
  }.
End NatLESignature.
Export NatLESignature(NatLESignature).
```

The overloaded signatures use tagged types so that they can first look for a
fully resolved overload (matches the type of the first argument and the type of
second argument). If that fails, it can fallback to using the wildcard branch
for the first argument (`nat_any_le_branch` does the fallback in the example
below). Tagged types are necessary for this fallback, because the standard
canonical structures wildcard can only be used to match everything, whereas
here it only matches type that are the second argument of a wildcard branch
from the first argument (`sig2.(AnyLESignature.B)` in the example below.
```
Canonical Structure nat_any_le_branch (sig2: AnyLESignature nat)
: NatLESignature :=
{|
  NatLESignature.B := try_second sig2.(AnyLESignature.B);
  NatLESignature.C := let '{| AnyLESignature.C := C; |} := sig2 in C;
|}.
```
