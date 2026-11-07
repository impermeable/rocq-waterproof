[![Build][build-badge]][build-link]
[![Documentation][documentation-badge]][documentation-link]

[build-badge]: https://github.com/impermeable/rocq-waterproof/workflows/Build/badge.svg
[documentation-badge]: https://github.com/impermeable/rocq-waterproof/workflows/Documentation/badge.svg

[build-link]: https://github.com/impermeable/rocq-waterproof/actions?query=workflow:"Build"
[documentation-link]: https://github.com/impermeable/rocq-waterproof/actions?query=workflow:"Documentation"

# The Waterproof plugin for the Rocq proof assistant

The Waterproof plugin for the Rocq proof assistant (`rocq-waterproof`) allows you to write Rocq proofs in **a style that resembles handwritten mathematical proofs**, designed to help university
students with learning how to prove mathematical statements.
Mathematicians unfamiliar with the Rocq syntax are able to read the resulting proof scripts. The plugin can be used directly in combination with the Rocq proof assistant, but it may be worth checking out
the related [vscode extension](https://marketplace.visualstudio.com/items?itemName=waterproof-tue.waterproof) as well.

## Installation

### Through the vscode extension

The easiest way to start using the `rocq-waterproof` plugin is to install it through the [vscode extension](https://marketplace.visualstudio.com/items?itemName=waterproof-tue.waterproof).

### Basic installation with opam

If you prefer to use the plugin directly with the Rocq theorem prover without the vscode extension for Waterproof, for instance, one can install the `rocq-waterproof` plugin in the following way.

First one needs a working [`opam`](https://opam.ocaml.org/) installation (in Linux, WSL or on MacOS).

Then, one can install the `rocq-waterproof` plugin by:

```bash
$ opam install rocq-waterproof
```
or, in the transition period in the Coq -> Rocq namechange for `rocq-waterproof`, by
```bash
$ opam install coq-waterproof
```

This will install the latest release of rocq-waterproof.

## Example
The following snippet from gives a taste of a proof written using rocq-waterproof.
```rocq
Goal 2 is the infimum of [2, 5).
Proof.
We need to show that (2 is a _lower bound_ for [2, 5)
  ∧ (∀ l ∈ ℝ, l is a _lower bound_ for [2, 5) ⇨ l ≤ 2)).
We show both statements.
  - We need to show that (2 is a lower bound for [2, 5)).
    We need to show that (∀ c ∈ [2, 5), 2 ≤ c).
    Take c ∈ [2, 5).
    We conclude that (2 ≤ c).
  - We need to show that
      (∀ l ∈ ℝ, l is a lower bound for [2, 5) ⇒ l ≤ 2).
    Take l ∈ ℝ. Assume that (l is a lower bound for [2, 5)).
    We conclude that (l ≤ 2).
Qed.
```

## Features

* Less cryptic, **controlled natural language formulations for built-in Rocq tactics**.
* Commonplace **mathematical notation** such as `ℝ` or `A is closed`.
* **Enforced signposting:** after a case distinction, for example, one **has** to state which case is to be shown.
* Allows for reasoning with **chains of (in)equalities**.
* Automation to **hide details not used in written proofs**.
* **Help messages** and more **elaborate error messages**.
* **Runtime-configurable presets of hint databases** used by the automation.

## Usage
To use the tactics in a `.v` file, use the import:
```rocq
Require Import Waterproof.Waterproof.
```

To use the automation system, add:
```rocq
Require Import Waterproof.Automation.
```

To use the tactics system, add:
```rocq
Require Import Waterproof.Tactics.
```

To use the notations defined, add:
```rocq
Require Import Waterproof.Notations.
```



## Automation

The more advanced tactics rely on automation. The automation function is called `waterprove`, which employs `wp_auto` and `wp_eauto`, together with a customizable set of hint-databases.

`wp_auto` and `wp_eauto` are rewrite of `auto` and `eauto` with better backtracking support, which can be use to retrieve the full backtrace during the execution of those functions, which allows to have a better control on the execution flow of the hints. For example, it can be used to reject a complete proof if certain lemmas are not used and continue to search for a new one.

### Configuration

The behavior of the automation tactics can be configured by importing specific files.

* **Adding a Database**: Example:
    ```rocq
    Require Import Waterproof.Automation.

    Waterproof Enable Automation RealsAndIntegers.
    ```

* **Removing a Database**: Example:
    ```rocq
    Require Import Waterproof.Automation.

    Waterproof Enable Automation RealsAndIntegers.
    Waterproof Disable Automation RealsAndIntegers.
    ```

* **Clearing every Databases**: Example:
    ```rocq
    Require Import Waterproof.Automation.

    Waterproof Enable Automation RealsAndIntegers.
    Waterproof Enable Automation Intuition.
    Waterproof Clear Automation.
    ```

* **Declaring a new automation dataset**: Example:
  ```rocq
  Require Import Waterproof.Automation.

  Waterproof Declare Automation Foo.
  Waterproof Set Main Databases Foo core, wp_core.
  Waterproof Set Decidability Databases Foo wp_decidability_classical.
  Waterproof Set Shorten Databases Foo core.
  ```

* **Turn debugging of automation on**: Example:
  ```rocq
  Waterproof Enable Debug Automation.
  ```

* **Turn debugging of automation off**: Example:
  ```rocq
  Waterproof Disable Debug Automation.
  ```

## Chains of (in)equalities
In written proofs, one often uses a chain of (in)equalities to explain why more complicated (in)equalities hold.
Waterproof allows you to use a similar notation in Rocq.
For example

```rocq
We conclude that (& -r < -r/2 = 1 - r/2 - 1 ≤ Rmax(1/2, 1 - r/2) - 1 = x - 1).
```
The chain of inequalities is used to show that `-r < x - 1`.

## Library documentation

Autogenerated documentation for the rocq-waterproof library can be found
[here](https://impermeable.github.io/rocq-waterproof/).

## Background

The rocq-waterproof library is developed as part of the educational [Waterproof](https://github.com/impermeable/waterproof) editor for Rocq.
The tactics are designed to be used by first-year mathematics students who are unfamiliar with Rocq. This is also why the tactics require the user to be explicit: the students have to learn to write readable proofs.

The library was originally written by Jim Portegies in Ltac1. It was extended and ported to Ltac2 by Cosmin Manea, Lulof Pirée, Adrian Vrămuleţ and Tudor Voicu as part of the 'Waterfowl' bachelor Software Engineering Project at the [Eindhoven University of Technology](https://www.tue.nl/en/) (in May-June 2021). Since then it has been under further development by Jelle Wemmenhove and Jim Portegies. In April-June 2023, Balthazar Patiachvili improved the automation, and converted parts of the library to an OCaml plugin.

Please also note that a very nice project with many similarities exists for the Lean theorem prover as well: [lean-verbose](https://github.com/PatrickMassot/verbose-lean4).

## Developer instructions

Developers of the `rocq-waterproof` library might find useful in formation in the [developer instructions](Developer-instructions.md)
