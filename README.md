Presentation
=======

This repo contains formalisation work on implementing a logical relation over MLTT with one universe.
This formalisation follows the [work done by Abel et al.]((https://github.com/mr-ohman/logrel-mltt/)) (described in [Decidability of conversion for Type Theory in Type Theory, 2018](https://dl.acm.org/doi/10.1145/3158111)), and [Loïc Pujet's work](https://github.com/loic-p/logrel-mltt) on removing induction-recursion from the previous formalization, making it feasible to translate it from Agda to Coq.

The definition of the logical relation (**LR**) ressembles Loïc's in many ways, but also had to be modified for a few reasons :
- Because of universe constraints and the fact that functors cannot be indexed by terms in Coq whereas it is possible in Agda, the relevant structures had to be parametrized by a type level and a recursor, and the module system had to be dropped out entirely.
- Since Coq and Agda's positivity checking for inductive types is different, it turns out that **LR**'s definition, even though it does not use any induction-induction or induction-recursion in Agda, is not accepted in Coq. As such, the predicate over Π-types for **LR** has been modified compared to Agda. You can find a MWE of the difference in positivity checking in the two systems in [Positivity.v] and [Positivity.agda].

In order to avoid some work on the syntax, this project uses the [AutoSubst](https://github.com/uds-psl/autosubst-ocaml) project to generate syntax-related boilerplate.

Building
===========

The project builds with Coq version `8.19.0`. It needs the opam package `coq-smpl`. Once these have been installed, you can simply issue `make` in the root folder.

The `make depgraph` recipe can be used to generate the [dependency graph](https://coqhott.github.io/logrel-coq/dependency_graph.png).

Browsing the development
==================

The development, rendered using `coqdoc`, can be [browsed online](https://coqhott.github.io/logrel-coq/). A dependency graph for the project is available [here](https://coqhott.github.io/logrel-coq/dependency_graph.png).

Syntax regeneration
====================

For simplicity, we include the syntax file (`Ast.v`) generated using [autosubst-ocaml](https://github.com/uds-psl/autosubst-ocaml).

It can be re-generated using the `make autosubst` recipe, once `autosubst-ocaml` has been installed. Note that we include modified versions of the `core` and `unscoped` files, which fix their dependency inclusion. Thus, when the recipe offers to overwrite these, one should choose __not to__, and only let AutoSubst overwrite `Ast.v`.

Getting started with using the development
=================

A few things to get accustomed to if you want to use the development.

Notations and refolding
-----------

In a style somewhat similar to the [Math Classes](https://math-classes.github.io/) project,
generic notations for typing, conversion, renaming, etc. are implemented using type-classes.
While some care has been taken to try and respect the abstractions on which the notations are
based, they might still be broken by carefree reduction performed by tactics. In this case,
the `refold` tactic can be used, as the name suggests, to refold all lost notations.

Induction principles
----------

The development relies on large, mutually-defined inductive relations. To make proofs by induction
more tractable, functions `XXXInductionConcl` are provided. These take the predicates
to be mutually proven, and construct the type of the conclusion of a proof by mutual induction.
Thus, a typical induction proof looks like the following:

``` coq-lang
Section Foo.

Let P := … .
…

Theorem Foo : XXXInductionConcl P … .
Proof.
  apply XXXInduction.

End Section.
```
The names of the arguments printed when querying `About XXXInductionConcl` should make it clear 
to which mutually-defined relation each predicate corresponds.

[Utils]: ./theories/Utils.v
[BasicAst]: ./theories/BasicAst.v
[Context]: ./theories/Context.v
[AutoSubst/]: ./theories/AutoSubst/
[AutoSubst/Extra]: ./theories/AutoSubst/Extra.v
[Notations]: ./theories/Notations.v
[Automation]: ./theories/Automation.v
[NormalForms]: ./theories/NormalForms.v
[UntypedReduction]: ./theories/UntypedReduction.v
[GenericTyping]: ./theories/GenericTyping.v
[DeclarativeTyping]: ./theories/DeclarativeTyping.v
[Properties]: ./theories/Properties.v
[DeclarativeInstance]: ./theories/DeclarativeInstance.v
[LogicalRelation]: ./theories/LogicalRelation.v
[Induction]: ./theories/LogicalRelation/Induction.v
[Escape]: ./theories/Escape.v
[Reflexivity]: ./theories/Reflexivity.v
[Irrelevance]: ./theories/Irrelevance.v
[ShapeView]: ./theories/ShapeView.v
[Positivity.v]: ./theories/Positivity.v
[Weakening]: ./theories/Weakening.v
[Substitution]: ./theories/Substitution.v
[AlgorithmicTyping]: ./theories/AlgorithmicTyping.v
[AlgorithmicConvProperties]: ./theories/AlgorithmicConvProperties.v
[AlgorithmicTypingProperties]: ./theories/AlgorithmicTypingProperties.v
[LogRelConsequences]: ./theories/LogRelConsequences.v
[BundledAlgorithmicTyping]: ./theories/BundledAlgorithmicTyping.v

[autosubst-ocaml]: https://github.com/uds-psl/autosubst-ocaml
[Positivity.agda]: ./theories/Positivity.agda
