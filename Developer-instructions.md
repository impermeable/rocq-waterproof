# Developer instructions

## Recommended setup

Our recommended setup for working on the library is by using vscode on Linux, MacOS, or WSL, with
the rocq-lsp and ocaml extensions. We will now describe more extensively how to achieve this setup.

### Installation of opam

A more extensive description can be found [here](https://ocaml.org/docs/installing-ocaml).
This is a short description.

On some versions of Linux and WSL, you can install opam with
```
apt-get install opam
```
On MacOs, you can either use homebrew
```
brew install gpatch
brew install opam
```
or macports
```
port install opam
```

### Creating the desired opam environment: simplified version
When we develop, we need to be aware of the version of Rocq (formerly Coq) we develop for.
Most development is done based off the main branch, and then the following setup will suffice.

```
opam init
eval $(opam env)
opam install coq-lsp.0.2.5+9.1
opam install ocaml-lsp-server
```
replacing 9.1 with the desired version of Rocq, or more generally, replacing
0.2.5+9.1 by the desired version of rocq-lsp.

### Creating the desired opam environment: advanced version for supporting multiple versions of Rocq

When we bring changes into different versions of Rocq (for instance for the branches 9.0, 9.1...)
it is convenient to have multiple opam environement, i.e. switches, available. If you prefer to start
with such a setup anyway, you can run
```
opam init --bare
```
Regardless of how you initialized opam, you can now add a new switch with
```
opam switch create your_preferred_switch_name ocaml-base-compiler.4.14.1
```
Next you can install the background libraries again
```
opam install coq-lsp.0.2.4+9.0
opam install ocaml-lsp-server
```
again replacing 9.0 with the desired version of Rocq

### Caveat: locally compiling the coq-master branch

The above only works partially when checking work for `coq-master`,  which is a very important
branch for us because it is checked in Rocq's CI. To just check locally whether the code works on the
`coq-master` branch, we can setup
```
opam switch create your_preferred_switch_name ocaml-base-compiler.4.14.1
```
Now, we need to add a remote repository to get the development version of coq from.
```
opam repo add coq-dev https://coq.inria.fr/opam/core-dev
opam update
```
Now we can install
```
opam install coq.dev
```

## Building with dune

Our go-to way for compiling `rocq-waterproof` while working on the library is by using dune. To do so, from the project's
root (i.e. inside the directory `...some-path.../rocq-waterproof/`), run
```
dune build -p rocq-waterproof
```
To then install the library so it is available from other projects, you can run
```
dune install -p rocq-waterproof
```

## Building with opam

The above method does not pin `rocq-waterproof` to the local version in the working
directory. Instead, one can run, from the root directory,
```
opam install .
```
and `rocq-waterproof` _will_ be pinned to the local version, and will
be installed (in the current opam switch).

## Warning

When importing Waterproof in a .v file when using rocq-lsp, we standard get the following warning

```
Serlib plugin: rocq-waterproof.plugin is not available: serlib support is missing. Incremental checking for commands in this plugin will be impacted.
```

This is not a problem.

## Testing

We aim to test every feature that we implement. Currently we test almost
all functionality present in `.v` files. Note for instance that tactics
such as `Choose`, `Assume`, both have a file that defines them, and a file
that tests them. The tests are run automatically when compiling the library, i.e.
when running
```
dune build -p rocq-waterproof
```

## Running external tests

The `test-exercises` folder exists to facilitate external tests.
Any `.mv` files located there, that do not end in `.notest.mv`,
will be ran and any errors will be reported.

The recommended way to use this is to symlink folders or files you want
to be tested to any name in the `test-exercises` folder.


```
dune build -p rocq-waterproof @runtest
```

## Setting up VSCode

If you use VSCode, we recommend installing the [OCaml Platform](https://marketplace.visualstudio.com/items?itemName=ocamllabs.ocaml-platform) and [Rocq LSP](https://marketplace.visualstudio.com/items?itemName=ejgallego.coq-lsp) plugins.

## Making Ocaml functions available from Ltac2: Using the foreign function interface (ffi)

One can make Ocaml functions available for use in Ltac2 by using the
foreign function interface (ffi). For now, we gather all such
definitions in `wp_ffi.ml`.

Note that with Coq v8.19, using the ffi got a lot easier.
It may be possible to just look at the examples in `wp_ffi.ml`.
This process is also explained in [tuto2](https://github.com/rocq-prover/rocq/tree/master/doc/plugin_tutorial/tuto4) of the [Rocq plugin tutorial](https://github.com/rocq-prover/rocq/tree/master/doc/plugin_tutorial).
The documentation in the file `Tac2externals.mli` may also help.

A few remarks:
- For passing variables through the ffi, one needs to convert them to an intermediate datatype: namely `valexpr`.
  For existing datatypes these conversion functions exist and can be used conveniently.
  With some syntactic sugar from `Tac2externals`, there's really nothing to do.
  For inductive datatypes, it is relatively easy to create new conversion functions.
  This process is explained in the tutorial mentioned above.
- Although this is not really necessary for the ffi anymore, an element of type `'a` can be converted into an `'a`-valued tactic by using `tclUNIT`.
- To make a tactic available from Ltac2, one needs to use the `Ltac2 @ external` syntax. It may be best to look for examples in the code.
