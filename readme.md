# Overloadable Notations for Coq

## Overview

This project provides overloadable notations in Coq. Declaring a notation as
overloadable only attaches the bare minimum semantics to the notation:
* Notation symbol
* Notation precedence
* Right/left/none associativity for parsing the notation
* Coq notation scope

The goal is that after a notation has been declared as overloadable, its
overloads can be defined independently. So one project could declare the
notation, then a child project could add more overloads to the notation without
having to update the parent project. This goal is mostly achieved with some
small caveats.

The notations are unbundled in the sense that declaring the notation as
overloadable does not impose any semantic requirements on the overloads of the
notation. For instance, declaring a notation such as `===` that looks like an
equivalence relation does not force all of the overloads to be equivalence
relations for various types.

To show the flexiblity of this library, the following overloads are defined in
`Example.v`, all in the same scope.

| First argument  | Infix operator | Second argument  | Result type | Operation |
| --------------- | -------------- | ---------------- | ----------- | --------- |
| nat             | <==            | nat              | Prop        | Nat.le    |
| Z               | <==            | Z                | Prop        | Z.le      |
| Z               | <==            | nat              | Prop        | (a <= Z.of_nat b)%Z |
| list ?A         | <==            | list ?A          | Prop        | lexicographical_le |
| relation ?A     | <==            | `?` unified to `relation ?A` | Prop      | RelationClasses.subrelation |
| `?` unified to `relation ?A` | <== | relation ?A    | Prop        | RelationClasses.subrelation |
| crelation ?A    | <==            | `?` unified to `crelation ?A` | Type      | CRelationClasses.subrelation |
| `?` unified to `crelation ?A` | <== | crelation ?A  | Type        | CRelationClasses.subrelation |
| nat             | [+]            | nat              | nat         | Nat.add   |
| Z               | [+]            | Z                | Z           | Z.add     |
| Z               | [+]            | nat              | Z           | (a + Z.of_nat b)%Z |
| nat             | [+]            | Z                | Z           | (Z.of_nat a + b)%Z |
| Type            | [+]            | Type             | Type        | sum       |
| Set             | [+]            | Set              | Set         | sum       |
| ?A              | [::]           | list ?A          | list ?A     | List.cons |
| nat             | [::]           | list Z           | list Z      | List.cons (Z.of_nat a) b |
| ?A              | [::]           | Ensemble ?A      | Ensemble ?A | Ensembles.Add _ b a |

`Example/Example.v` includes the final library. The `alt` directory shows the
evolution of the internals of the library through simpler attempts fail in some
way. [alt/readme.md](alt/readme.md) uses this evolution to explain the
internals of the final library.

The rest of this file serves as a guide on how to use the library rather than
an explanation of the internals.

## Declaring the notation scope

Typically a single scope will be used for all overloadable notations within a
project. The only reason to create multiple scopes would be if one wanted some
overloads be unavailable in some contexts.

The recommendation is to open the scope after declaring it and leaving it open.
That anything that imports the module that declared the scope will use that
scope before attempting other scopes. Note that even though `Open Scope` sounds
like it is pushing the scope on to a stack, it really just removes the scope
from the scope list (if it was already present), then adds it to the front of
the list. So it is safe to open the same scope multiple times.

In the below code, replace "overload" and "o" with names specific to your
project.
```
Declare Scope overload_scope.
Delimit Scope overload_scope with o.
Open Scope overload_scope.
```

## Declaring an overloadable notation

Import the `SigId` module, which is needed to instantiate the other overload
modules. Import the `Binary` module that assists in declaring overloaded binary
notations. Note that currently only binary notations (notations with 2
operands) are supported. It would be possible to support operations with
different numbers of operands, I have not because I cannot think of good
examples of how they would be used.
```
Require Import Overload.SigId.
Require Import Overload.Binary.
```

Create an instance of the `SigId` module type. Create an instance of the
`Binary.Signature` by passing it the SigId. The SigId is used to ensure the
module system considers each copy of Binary.Signature unique.

The overload library makes heavy use of canonical structures. So export the
canonical structure instances from the copy of Binary.Signature. Exporting them
makes them available in the module declaring the notation and modules that
import that module.

Replace `LE` in the below code with an abbreviation that better describes your
overloadable notation.
```
Module LEId: SigId.
End LEId.
Module LESignature := Binary.Signature LEId.
Export (canonicals) LESignature.
```

In addition to the overload signature, an overload type class must be declared.
Replace `LE` and `le` with abbreviations that match the signature name above.
```
Class LEOperation (r: LESignature.BacktrackBranch) :=
le: forall (a: untag r.(LESignature.BacktrackBranch.A))
           (b: r.(LESignature.BacktrackBranch.B)),
    (let '{| LESignature.BacktrackBranch.C := C; |} := r
       return (untag r.(LESignature.BacktrackBranch.A) ->
               r.(LESignature.BacktrackBranch.B) ->
               Type)
       in C) a b.
```

Finally declare the notation itself, and have it call the function from the
type class above. If the notation is new, then the level and associativity
information must be provided as shown below. The easiest way to determine them
is to look up a similar existing notation, such as by running
`Print Notation "_ <= _".`.
```
Infix "<==" := le (at level 70, no associativity) : overload_scope.
```

However, if the notation already exists for other scopes, then leave out the level and associativity.
```
Infix "<=" := le : overload_scope.
```

## Branching on the first argument with a known head constant

Declaring a branch is necessary precursor for defining overloads where the type
of the first argument has a known head constant. It can either be a fully
specified type, or a type family. The below table summarizes the kinds of
overloads that require a branch. `T` is a placeholder for some type and `U` is
a placeholder for some type family. `?` represent parts of the overload that
will be filled later, after the branch is defined.

| First argument  | Infix operator | Second argument  | Result type | Operation |
| --------------- | -------------- | ---------------- | ----------- | --------- |
| T               | Op             | ?                | ?           | ?         |
| U ?A            | Op             | ?                | ?           | ?         |

Declaring a branch on the first argument allows a full overload to later be
defined. For instance, declaring a branch on `nat` for the first argument of
`<=` would allow for overloads like `(_ <= _) : nat -> Z -> Prop` or
`(_ <= _) : nat -> nat -> Prop` to later be defined. To declare the branch, the
overload type must have a head constant. `nat` and `Ensemble ?A` are examples
of types with a head constant. `forall A, list A` is an example of a type
without a head constant.

First, either define a type module for the overload type, or reuse an existing
one. In this case it does not hurt to have duplicate instances of the
TypeModule across different overloaded operators. The example below is for
`nat`. For a simple type (not type family), use this example as a template and
replace `nat` and `Nat` with your type.
```
Module NatWrapper<: TypeModule.
  Definition P := unit.
  Definition T (_: P) := nat.
End NatWrapper.
```

The above example only works for simple types, not type families. For type
families, use the following example instead as a template. Pack all of the type
family parameters into the `P` type, then define `T` to unpack them and return
an instance of the type family. Replace `list` and `List` with a description of
your type.
```
Module ListWrapper<: TypeModule.
  Definition P := Type.
  Definition T (A: P) := list A.
End ListWrapper.
```

Pass the operator signature and the type module defined above as arguments to
the `Binary.Branch` module functor. This module defines canonical structures,
so those must be exported. One of the canonical structures cannot be correctly
defined using `T` from the type module, so it must be manually defined after
exporting the module. Replace `Z`, `LE`, `le`, and `tt` as appropriate in the
below example.
```
Module ZLESignature := Binary.Branch LESignature ZWrapper.
Export (canonicals) ZLESignature.

Canonical Structure Z_le_branch (sig2: ZLESignature.BacktrackBranch tt)
: LESignature.S :=
LESignature.make_A_branch Z (ZLESignature.A_branch tt sig2).
```

## Overloading the operator with known head constants

Define the signature for the overload. The signature defines which types the
overload takes as input and what output type it produces, but it does not
define the actual operation that is performed. The type of the first argument
is defined by which branch is instantiated (see previous section). The type of
the second argument is specified through the `B` field. The `C` field defines
the output type. Specifically the `C` field is a function that takes the first
two arguments of the overload as parameters, which is how dependent output
types are supported. The below example has a non-dependent output type, which
is why the first two parameters are discarded by using `_`. In the below
example, replace `LE` with the operator name, `Z` with the type of the first
argument, `nat` with the type of the second, and `Prop` with the output type.
```
Canonical Structure Z_nat_le_signature: ZLESignature.S tt :=
{|
  ZLESignature.B := nat;
  ZLESignature.C _ _ := Prop;
|}.
```

Next declare the operation, which specifies which function to run when the
overload is used. The operation type class takes a signature as the first
argument. Typically this is automatically filled in by the canonical
structures system when `_` is given. With all of the canonical structures
unfolded, the type of operation is roughly: `signature -> forall (a:
first_parameter) (b: second_parameter) -> output_type a b`. Replace `Z` with
the type of the first argument, `nat` with the type of the second, `LE` with
the overloaded notation name, and the function body with your overloaded
operation.
```
#[export]
Instance Z_nat_le: LEOperation _ :=
fun a b => (a <= Z.of_nat b)%Z.
```

## Overloading the operator with a wildcard for the first argument

If the first argument is a wildcard, then use the `Any` branch instead of the
`S` branch shown above. This is used to define overloads like the following:

| First argument  | Infix operator | Second argument  | Result type | Operation |
| --------------- | -------------- | ---------------- | ----------- | --------- |
| `?A`            | `[::]`         | `list ?A`        | `list ?A`   | `List.cons` |

First declare the signature for the overload. In the below example, replace
`list` with the type of the second argument, `cons` with the operator name,
and `Cons` with the operator name. Set `C` to the output type of the overload.
```
Canonical Structure any_list_cons_signature (A: Type): ConsSignature.Any A := {|
  ConsSignature.Any.B := list A;
  ConsSignature.Any.C _ _ := list A;
|}.
```

Next define the overload for the operator, using the previously declared
signature. Replace `list` with the type of the second argument, `cons` with
the operator name, `Cons` with the operator name, and `List.cons` with the
operation.
```
#[export]
Instance any_list_cons (A: Type)
: ConsOperation (ConsSignature.fallback_branch A _) :=
List.cons.
```

Note that even though the first argument is a wildcard, sometimes the
unification algorithm will refuse to take the any branch if the type of the
first argument is unknown. For example, with the above overload, the first
following command succeeds because `a`'s type is known, but the second fails
because `a`'s type is unknown.
```
Succeed Theorem list_in_cons : forall A (a: A) (l: list A), List.In a (a [::] l).
Fail Theorem list_in_cons' : forall A (a: A) (l: list A), List.In a (a [::] l).
```

## Overloading the operator when the type of the first argument is unknown

When the type of the first argument is unknown, the unification algorithm often
fails to use the specific or any branches described in the previous sections.
To handle this, the signature should first be declared for when the type of the
first argument is known (as described in the previous sections), then an
additional signature should be created for when the type of the first argument
is unknown.

In the below example, `list_no_match` is used to prevent the
unification algorithm from matching on the first argument when its type is
known, so that it only matches using the second argument. Replace `list` with
the type of the first argument, second argument, or output type where
appropriate. Replace `Cons` and `cons` with the name of your operator.
```
Definition list_no_match := try_second.

Canonical Structure unknown_list_cons_signature (A: Type)
: ConsSignature.BacktrackBranch :=
{|
  ConsSignature.BacktrackBranch.A := list_no_match A;
  ConsSignature.BacktrackBranch.B := list A;
  ConsSignature.BacktrackBranch.C _ _ := list A;
|}.
```

Typically the unknown signature is added in addition to another signature for
when the type is known. As such, a new Operation type class instance should not
be created. The unknown signature will resolve to the type class instance for
when the type is known.

Adding an unknown overload presents a minor problem. The unification algorithm
will now pick one of two different signatures, depending on whether the type of
the first argument is known or not. Those two structures are judgementally
equal, but not syntactically equal. This means the `rewrite` tactic will fail
if the lemma used a different signature than the goal.

In the following example, the first theorem is defined using the known
signature (because the type of `a` is explictly specified). The second theorem
uses the unknown signature (because the type of `a` is not explicitly
specified). The second theorem tries to rewrite using the first, but that fails
because the implicit signature argument hidden under the [::] notation does not
match.
```
Theorem list_tail_eq (A: Type)
: forall (a: A) (l1 l2: list A),
  l1 = l2 ->
  a [::] l1 = a [::] l2.
Proof.
  intros * Heq.
  rewrite Heq.
  reflexivity.
Qed.

Theorem list_tail_eq' (A: Type)
: forall a (l1 l2: list A),
  l1 = l2 ->
  a [::] l1 = a [::] l2.
Proof.
  intros * Heq.
  Fail erewrite list_tail_eq.
Abort.
```

To fix this, a rewrite lemma should be added to the `canonicalize` hint
database. The rewrite lemma should convert from the unknown overload to the
known overload.
```
Theorem cons_list_unknown_to_any
: forall A (a: A) (l: list A),
  cons (r:= unknown_list_cons_signature A) a l =
    cons (r:= ConsSignature.fallback_branch A (any_list_cons_signature A)) a l.
Proof.
  reflexivity.
Qed.

#[export]
Hint Rewrite cons_list_unknown_to_any : canonicalize.
```

Now the theorem can call the `canonicalize` tactic (just an ltac macro for
`autorewrite using canonicalize`) to switch to the canonical overload before
using rewrite.
```
Theorem list_tail_eq' (A: Type)
: forall a (l1 l2: list A),
  l1 = l2 ->
  a [::] l1 = a [::] l2.
Proof.
  intros * Heq.
  canonicalize.
  erewrite list_tail_eq by eassumption.
  reflexivity.
Qed.
```

## Overloading the operator when the type of the second argument is unknown

A limitation of the system is that in order to overload an unknown second
argument, only one overload is possible per type of the first argument. For
instance, without supporting an unknown type of the second argument, the
following two overloads are possible. However, if an unknown second argument is
to supported, then only one of the overloads is allowed (either one can be
chosen).

| First argument  | Infix operator | Second argument  | Result type | Operation |
| --------------- | -------------- | ---------------- | ----------- | --------- |
| `Z`             | `<==`          | `Z`              | `Prop`      | `Z.le`    |
| `Z`             | `<==`          | `nat`            | `Prop`      | `(a <= Z.of_nat b)%Z` |

First declare the signature. In the following example, replace `le` and `LE`
with name of the operator. Replace `relation` with the type of the first and
second arguments. Replace `Prop` with the output type.
```
Canonical Structure relation_relation_le_signature (A: Type)
: LESignature.S :=
{|
  LESignature.A := relation A;
  LESignature.B := relation A;
  LESignature.C _ _ := Prop;
|}.
```

Next define the overload. Replace `le` and `LE` with name of the operator.
Replace `relation` with the type of the first and second arguments. Replace the
body of the function with the overloaded behavior.
```
#[export]
Instance relation_relation_le (A: Type)
: LEOperation _ :=
fun (R S: relation A) => RelationClasses.subrelation R S.
```

## Universe polymorphic overloads

The `Binary.Branch` module functor is used to overload an operator based on the
type of first argument. That type must be in the `Binary.A` universe. It
furthermore restricts the type of the second argument to be in the `Binary.B`
universe.

There is no way to create a module functor that accepts an arbitrary universe
as input. If one tries to add a universe to a module type, it ends up being
defined within the module type instead of defined by each module that
implements the module type. That is, every instance of the module type would
end up with the same universe.

If `Binary.Branch` needs to be used with specific universes, but does not need
to be fully polymorphic, then make a copy of it, like the
`BinaryRelation.Branch` module functor.

The `Binary.Branch` module functor cannot be used for fully polymorphic types.
So to overload an operator with a universe polymorphic type, one has to
essentially make a copy of the `Branch` module with the correct polymorhpism
added. The below example does that and specializes an add operator for
`Type@{U}` for the first argument.
```
Module TypeAddSignature.
  Universe C.
  #[universes(polymorphic)]
  Structure S@{A B} := {
    B: TaggedType@{B};
    #[canonical=no] C: Type@{A} -> untag B -> Type@{C};
  }.
End TypeAddSignature.

Definition Type_no_match (B: TaggedType): Type := untag B.

Universe Type_A.
#[universes(polymorphic)]
Canonical Structure Type_add_signature@{A B} (sig2: TypeAddSignature.S)
: AddSignature.S@{Type_A B TypeAddSignature.C} :=
{|
  AddSignature.A := Type@{A};
  AddSignature.B := Type_no_match (sig2.(TypeAddSignature.B));
  AddSignature.C := let '{| TypeAddSignature.C := C; |} := sig2 in C;
|}.

#[universes(polymorphic)]
Canonical Structure Type_any_add_branch@{A1 A2 B C}
  (sig2: AddSignature.Any@{A2 B C} Type@{A1})
: TypeAddSignature.S :=
{|
  TypeAddSignature.B := try_second sig2.(AddSignature.Any.B);
  TypeAddSignature.C := let '{| AddSignature.Any.C := C; |} := sig2 in C;
|}.

Module TypeBacktrackAddBranch.
  #[universes(polymorphic)]
  Structure TypeBacktrackAddBranch@{A B} := {
    B: Type@{B};
    #[canonical=no] C: Type@{A} -> B -> Type@{TypeAddSignature.C};
  }.
End TypeBacktrackAddBranch.
Export TypeBacktrackAddBranch(TypeBacktrackAddBranch).

#[universes(polymorphic)]
Canonical Structure Type_overload_add_signature@{A B} (sig2: TypeBacktrackAddBranch@{A B})
: TypeAddSignature.S :=
{|
  TypeAddSignature.B := try_first sig2.(TypeBacktrackAddBranch.B);
  TypeAddSignature.C := let '{| TypeBacktrackAddBranch.C := C; |} := sig2 in C;
|}.

Set Warnings "-redundant-canonical-projection".
#[universes(polymorphic)]
Canonical Structure set_add_signature@{B} (sig2: TypeAddSignature.S@{Set B})
: AddSignature.S := Type_add_signature@{Set B} sig2.
Set Warnings "".
```

Next, use the branch declared above (which added support for overloading the
first argument) to declare the signature for the combination of the types in
the first and second arguments.
```
#[universes(polymorphic)]
Canonical Structure Type_Type_add_signature@{A1 A2}
: TypeBacktrackAddBranch@{A1 A2} :=
{|
  TypeBacktrackAddBranch.B := Type@{A1};
  TypeBacktrackAddBranch.C (A B: Type@{A1}) := Type@{A1};
|}.
```

Finally define the overload that describes what operation is performed when the
specific types are passed to the operator.
```
#[export]
#[universes(polymorphic)]
Instance type_type_add@{U} : AddOperation _ :=
fun (A: Type@{U}) (B: Type@{U}) => (A + B)%type.
```

## Defining an inductive type constructor that is an overloaded operator

It is possible to define a type constructor directly as an instance of the
overloaded operation. The operation type usually takes a signature. That
signature is usually declared ahead of time using canonical structures.
However, in this case it is not possible to define the canonical structure
beforehand, because it would reference the inductive type which is not defined
until all of the constructors are defined. So instead a hand crafte instance of
the signature can be passed to the operation when declaring the type
constructor. After the inductive type is defined, the type class instance can
be registered using `Existing Instance`. Example:
```
Inductive AltList (A: Type): Type :=
| alt_nil: AltList A
| alt_cons: ConsOperation
            {|
              ConsSignature.A:= {| untag:= A; |};
              ConsSignature.B:= AltList A;
              ConsSignature.C _ _ := AltList A;
            |}.
Arguments alt_nil {A}.
Arguments alt_cons {A}.
#[export]
Existing Instance alt_cons.
```

Finally the signature can be defined after the inductive type definition.
Example:
```
Canonical Structure any_AltList_cons_signature (A: Type)
: ConsSignature.Any A :=
{|
  ConsSignature.Any.B := AltList A;
  ConsSignature.Any.C _ _ := AltList A;
|}.
```

Unfortunately, the overloaded notation does not work for patterns in the match
construct. The constructor name has to be used instead. Example:
```
Fixpoint alt_reverse_aux {A: Type} (l: AltList A) (acc: AltList A)
: AltList A :=
match l with
| alt_nil => acc
| (* Can't use: h [::] l *) alt_cons h l => alt_reverse_aux l (h [::] acc)
end.
```

## Transparency for the `auto` tactic

In the following example uses an overloaded `<==` notation that does the same
thing as the standard `<=` notation in the nat scope. If the lemma were defined
using `<=` instead, `auto with arith` would be able to solve it. However, when
the goal uses `<==`, `auto with arith` fails to solve it, because the standard
library lemmas are defined using `<=` which does not match `<==`.
```
Goal forall (m n: nat), S m <== S n -> m <== n.
Proof.
  Fail progress auto with arith.
Abort.
```

To solve this, mark the `<==` operator and its specific overload as transparent
so that auto can unfold them and match the standard library lemmas.
```
#[export]
Hint Unfold nat_le le : overload.

Goal forall (m n: nat), S m <== S n -> m <== n.
Proof.
  auto with arith overload.
Qed.
```

## Type class transparency for overloads that are relations

In the following example, the type of `nat_le` is judgementally equal to
`relation nat`. As such `nat_le` can be defined as a `PreOrder` like other
relations.
```
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
```

However, sometimes the type class resolution algorithm will fail to find the
`Reflexive` instance defined above, because the type of `nat_le` is not
syntactically equal to `relation nat`.
```
Fail Definition nat_refl' := (fun r : Reflexive nat_le => r) _.
```

Declaring the operation as transparent allows the type class resolution
algorithm to unfold it and discover that `nat_le`'s type is equal to `relation
nat`.
```
#[export]
Typeclasses Transparent LEOperation.

Goal forall (m n: nat), S m <== S n -> m <== n.
Proof.
  (* Now auto works because it can see that <== is <=. *)
  auto with arith.
Qed.
```

## Limitations

The overloaded notations can be used to define inductive constructors, but they
are not understood by the match construct. As such, the constructor name (not
notation) has to be used in match constructs.

The only way to support overloading a second argument of unknown type is to
force the second argument to always have the same type (depending on the type
of the first argument). It is not possible to overload the second argument
multiple times but have a default branch for when the type is unknown.

Overloading an operator based on the type of the first argument involves
instantiating the `Binary.Branch` functor module. However, the functor should
only be instantiated once for a given argument type/operator combination.
Instantiating it a second time breaks the overloads that use the previous
instantiation. This is a minor problem in the following scenario: project A
defines an overloadable operator. Project B imports project A and instantiates
`Binary.Branch` for type T. Project C also imports project A. Project C does
not know about project B, so it also instantiates `Binary.Branch` for type T.
Project D imports project B and project C, but only one set of the overloads
work. This is a small problem, because in practice it is rare for two different
projects to overload the same operator with the same type for the first
argument.

## Installation and distribution

At this point, Overload is not available as an opam package. If there is
an enough interest, I will look into creating one.

The Overload library may be manually installed by running `./build.sh
install`. That will install it into the `user-contrib` directory of the coq
installation.

However, at this point the recommendation is to either add coq-overload as a
git submodule to your project, or to directly copy it into your project, then
build it along with your project.

## Licensing

The Overload library is mostly documentation and examples. The examples are
intended to be copied used as templates for overloads within your project. It
is licensed with 0BSD so that the examples can be copied into your project
without having to add a copyright notice pointing back to Overload.
