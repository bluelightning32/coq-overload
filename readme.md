# Overloadable Notations for Coq

## Overview

This project provides overloadable notations in Coq. Declaring a notation as
overloadable only attaches the bare minimum semantics to the notation:
* Notation symbol
* Notation precedence
* Associativity for parsing the notation (not necessarily the same as the
  associativity of the operation that the overload actually performs)
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

| First parameter | Infix operator | Second parameter | Result type | Operation |
| --------------- | -------------- | ---------------- | ----------- | --------- |
| `nat`           | `<==`          | `nat`            | `Prop`      | `Nat.le`  |
| `Z`             | `<==`          | `Z`              | `Prop`      | `Z.le`    |
| `Z`             | `<==`          | `nat`            | `Prop`      | `(a <= Z.of_nat b)%Z` |
| `relation ?A`   | `<==`          | `?` unified to `relation ?A` | `Prop`      | `RelationClasses.subrelation` |
| `?` unified to `relation ?A` | `<==`          | `relation ?A` | `Prop`      | `RelationClasses.subrelation` |
| `crelation ?A`   | `<==`          | `?` unified to `crelation ?A` | `Type`      | `CRelationClasses.subrelation` |
| `?` unified to `crelation ?A` | `<==`          | `crelation ?A` | `Type`      | `CRelationClasses.subrelation` |
| `nat`           | `[+]`          | `nat`            | `nat`       | `Nat.add` |
| `Z`             | `[+]`          | `Z`              | `Z`         | `Z.add`   |
| `Z`             | `[+]`          | `nat`            | `Z`         | `(a + Z.of_nat b)%Z` |
| `nat`           | `[+]`          | `Z`              | `Z`         | `(Z.of_nat a + b)%Z` |
| `Type`          | `[+]`          | `Type`           | `Type`      | `sum`     |
| `Set`           | `[+]`          | `Set`            | `Set`       | `sum`     |
| `?A`            | `[::]`         | `list ?A`        | `list ?A`   | `List.cons` |
| `nat`           | `[::]`         | `list Z`         | `list Z`    | `List.cons (Z.of_nat a) b` |
| `?A`            | `[::]`         | `Ensemble ?A`    | `Ensemble ?A` | `Ensembles.Add _ b a` |

`Example.v` includes the final library. The `Alt` directory contains alternate
simpler attempts to build the library, along with tests from `Example.v` that
fail in some way, because the simpler attempts were insufficient.
[Alt/readme.md](Alt/readme.md) explains the internals of the library by
explaining its evolution through those simpler attempts.

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
  Class LEOperation (r: LESignature.S) :=
  le: forall (a: untag r.(LESignature.A)) (b: r.(LESignature.B)),
      (let '{| LESignature.C := C; |} := r
         return (untag r.(LESignature.A) -> r.(LESignature.B) -> Type) in C) a b.
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

## Branching on the first parameter with a known head constant

Declaring a branch on the first parameter allows a full overload to later be
defined. For instance, declaring a branch on `nat` for the first parameter of
`<=` would allow for overloads like `(_ <= _) : nat -> Z -> Prop` to be
defined afterwards. To declare the branch, the overload type must have a head
constant. `nat` and `Ensemble ?A` are examples of types with a head constant.
`forall A, list A` is an example of a type without a head constant.

Either define a type module for the overload type, or reuse an existing one. In
this case it does not hurt to have duplicate instances of the TypeModule across
different overloaded operators. The example below is for `nat`. For a simple
type (not type family), use this example as a template and replace `nat` and
`Nat` with your type.
```
Module NatWrapper<: TypeModule.
Definition P := unit.
Definition T (_: unit) := nat.
End NatWrapper.
```
