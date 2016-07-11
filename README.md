# KappaF

This repository contains the Coq sources for the formalisation of
KappaF and the proof of its type soundness. There is a Makefile
for compiling the scripts (cleaning the produced files). It also
has a rule "make count" to show the number of lines for
definitions and properties/proofs respectively. The source files
are the following:

## Definitions

* [Meta.v](KappaF/Meta.v) - Definitions of identifiers and partial maps

* [Syntax.v](KappaF/Syntax.v) - The syntax of KappaF

* [Dynamic.v](KappaF/Dynamic.v) - The dynamic semantics of KappaF

* [Types.v](KappaF/Types.v) - The static semantics of KappaF

* [WellFormedness.v](KappaF/WellFormedness.v) - The definitions of well-formed configurations


## Properties and proofs

* [MetaProp - Properties](KappaF/MetaProp - Properties) of identifiers and maps, and their proofs

* [SyntaxProp - Properties](KappaF/SyntaxProp - Properties) of the syntax their proofs

* [DynamicProp - Properties](KappaF/DynamicProp - Properties) of the dynamic semantics the their proofs

* [TypesProp - Properties](KappaF/TypesProp - Properties) of the static semantics and their proofs

* [WellFormednessProp - Properties](KappaF/WellFormednessProp - Properties) of well-formedness rules and their proofs

* [Locking.v](KappaF/Locking.v) - Lemmas and theorems about locking

* [Progress.v](KappaF/Progress.v) - The proof of progress

* [Preservation.v](KappaF/Preservation.v) - The proof of preservation

* [Soundness.v](KappaF/Soundness.v) - The proof of type soundness


## Miscellaneous

* [ListExtras.v](KappaF/ListExtras.v) - Various useful lemmas about lists

* [Shared.v](KappaF/Shared.v) - Various tactics used by several files


## Libraries

* [CpdtTactics.v](KappaF/CpdtTactics.v) - The tactics library of Adam Chlipala's [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/)

* [LibTactics.v](KappaF/LibTactics.v) - The tactics library of Benjamin Pierce et al's [Software Foundations](https://www.cis.upenn.edu/~bcpierce/sf/)