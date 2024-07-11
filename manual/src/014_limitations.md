
Limitations {#sec:limitations}
===========

Tamarin operates in the symbolic model and thus can only capture attacks within 
that model, and given a certain equational theory. Currently, apart from the 
builtins, only subterm-convergent theories are supported. The underlying 
verification problems are undecidable in general, so Tamarin is not guaranteed 
to terminate.

In contrast to the trace mode, which is sound and complete, the observational 
equivalence mode currently only (soundly) approximates observational equivalence 
by requiring a strict one-to-one mapping between rules, which is too strict for 
some applications. Moreover, the support of restrictions in this mode is rather 
limited.

<!--
TODO:
  * Warning - Virtualized Tamarin has significant overhead due to Haskell
    virtualization 'bad stuff' (seems to make a lot of system calls) [Ask Cas/Dennis/Kevin for more on this]

-->
