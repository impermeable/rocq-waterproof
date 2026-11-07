# Change log for the rocq-waterproof library

## Version 3.1.1+9.0

- Name change to rocq-waterproof
- Fix confusing absolute value notation
- Add support for finite sums
- Add a tactic for arguing by contraposition
- Make automation in `Help` customizable (`Waterproof Set Help Automation Depth n`, `Waterproof Enable/Disable Help Automation`), and lower the default depth from 5 to 2
- Fix bug in expanding definitions when multiple goals are open
- Fix bug in negation of a disjunction
- Fix bug (state handling) in unfold framework

## Version 3.1.0+9.0

- No longer throw an error if there are unused lemmas (this speeds up automation when using `By ... it holds that ...`)
- Remove parentheses in suggestions
- Fix issue with keywords
- Allow for multiple reasons in `By ...`-clause
- Add framework for registering definitions and alternative characterizations
- Add Expand All functionality to Help
- Simplify ffi mechanism

## Version 3.0.0+9.0

- Remove need for parentheses in many places
- Add theory for exercises for the book _An Infinite Descent into Pure Mathematics_ written by Clive Newstead
- Remove make build
- Small update 'By/Since .. it holds that' tactic
- More natural formulation for assuming multiple premises at once
- Add new behavior, more relaxed, for bullets
- Improve infrastructure for testing

## Version 2.2.0+9.0

- Allow for standard math notation
- No longer automatically replace terms introduced by choose in the goal
- Add bullets and curly brackets to wrappers
- Update the induction tactic, so that the variable needs to be introduced in the induction step
- Allow for obtaining multiple variables
- Test warning and error messages
- Update documentation and add developer documentation
- Simplify the build proces
- Create a devcontainer
- Warn on unexpected variable names by comparing to binder names
- Refactor the ffi
- Change expand definition tactic so it unfolds in all statements
- Add possibility to postpone proofs
- Quickfix for using Qed as variable name
- Allow for choosing blanks
- Add custom version of the specialize tactic
- Allow for boolean statements in tactics

## Version 2.1.1+9.0

- Compatibility with Coq dev
- Compatibility with earlier OCaml compilers
- Fixes for the strong induction tactic

## Version 2.1.0+8.17

- Improve the `Either` tactic: now proves and destructs ordinary 'ors' when the goal is a proposition
- Improve some mathematical definitions
- Add vernacular for debugging automation

## Version 2.0.2+8.17

- Improve errors and warnings
- Rework expanding definitions
- Deal better with Rabs, Rmax, Rmin

## Version 2.0.1+8.17

- Build the plugin with dune

## Version 2.0.0

- Converted coq library to coq plugin
- Automation procedures are now handled internally in the plugin, so that they can be customized and so that one can check the use of certain lemmas within the automation

## Version 1.2.4

- Added and updated theory files.
- Improved notation for (in)equality chains, e.g. (& a < b <= c = d).
- Bug fixes.

## Version 1.1.2

- Added and updated theory files.
- Reorganized automation libraries.
- Added goal wrappers that force user to write sentences that make proofscript more readable.
- Support chains of (in)equalities for `=`, `<` and `<=` in naturals and reals.
- Fixed issues with several tactics, including `Take ...`.
- Rephrased multiple tactics like `Obtain ... according to ..., ...`.
- For propositions, have user specify types rather than labels in tactics. Labeling is now optional.
- Added some shielding for use of automation, e.g. statements starting with quantifiers cannot be proved automatically.

## Version 1.0.0

- Ported the original library written in ltac to Ltac2.
