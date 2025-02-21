Presentation
=======

This branch contains the formalisation accompanying the paper *What does it take to certify a conversion checker?*.

Building
===========

The project builds with Coq version `8.20.0`. It needs the opam package `coq-smpl` and `coq-equations`. If you already have an opam set-up, they can be installed by simply using `opam install . --deps-only`.

Once the dependencies have been installed, you can simply issue `make` in the root folder to
build the whole development.

The `make depgraph` recipe can be used to generate the [dependency graph](https://coqhott.github.io/logrel-coq/dependency_graph.png).

Syntax regeneration
====================

For simplicity, we include the syntax file (`Ast.v`) generated using [autosubst-ocaml](https://github.com/uds-psl/autosubst-ocaml).

Correspondence with the paper
=====================================

Section 2
----------

[DeclarativeTyping] contains the definition of the specification, [NormalForms] that of
normal forms (Fig 2) and [UntypedReduction] that of reduction (Fig 3).

All properties defined in Section 2.2 are defined in [PropertiesDefinition]. The proofs
of Corollaries 2 and 3 are in [TypeConstructorsInj]. Neutral comparison is defined in
[DeclarativeTyping], and Proposition 8 is proven in [NeutralConvProperties]. Deep normalisation
is defined in [Normalisation].

Proofs of the properties that are direct consequences of the logical relation are gathered
in [LogRelConsequences]. A proof of full completeness of neutral comparison is obtained at 
the end of [UntypedAlgorithmicConversion].

Section 3
----------------------

The definition of typed algorithmic conversion and bidirectional typing are given in
[AlgorithmicTyping], and that of untyped algorithmic conversion is in [UntypedAlgorithmicConversion].
The definitions of the functions are respectively in [Functions] and [UntypedFunctions].
Figure 3 corresponds to the definition of "bundled" typing judgments, defined in 
[BundledAlgorithmicTyping].

Section 4
-------------------

Proofs of section 4.1 and 4.2
are gathered in the [Decidability](./theories/Decidability/) subfolder.
Those of section 4.3 are in [UntypedAlgorithmicConversion].

[DeclarativeTyping]: ./theories/DeclarativeTyping.v
[NormalForms]: ./theories/Syntax/NormalForms.v
[UntypedReduction]: ./theories/Syntax/UntypedReduction.v
[PropertiesDefinition]: ./theories/TypingProperties/PropertiesDefinition.v
[TypeConstructorsInj]: ./theories/TypingProperties/TypeConstructorsInj.v
[NeutralConvProperties]: ./theories/TypingProperties/NeutralConvProperties.v
[Normalisation]: ./theories/TypingProperties/Normalisation.v
[LogRelConsequences]: ./theories/TypingProperties/LogRelConsequences.v
[UntypedAlgorithmicConversion]: ./theories/Algorithmic/UntypedAlgorithmicConversion.v
[AlgorithmicTyping]: ./theories/AlgorithmicTyping.v
[Functions]: ./theories/Decidability/Functions.v
[UntypedFunctions]: ./theories/Decidability/UntypedFunctions.v
[BundledAlgorithmicTyping]: ./theories/Algorithmic/BundledAlgorithmicTyping.v

[autosubst-ocaml]: https://github.com/uds-psl/autosubst-ocaml
[Positivity.agda]: ./theories/Positivity.agda
