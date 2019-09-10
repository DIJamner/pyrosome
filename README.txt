Extension-Proof Compiler Correctness
Dustin Jamner, SSIRF 2019

See the file `ExpLang.agda` for the most current results. Of particular note
are the following:
1. The definition of programming language `Lang I` on line 82.
2. The definition of language summation on line 132.
3. The automatic derivation of congruence rules on line 173
4. The definition of a compiler on line 430
5. Compiler vertical and horizontal composition on lines 443 and 448 respectively
6. Example compilers on lines 451-486 demonstrating how such compilers should work

To summarize the current state of the project, I have developed a model of
programming languages, assuming for now a common type system, that can be used
to describe the semantic properties of a syntax. I have also developed a model
of a compiler that can be composed both vertically, as in a chain of consecutive
compilation steps, and horizontally, by merging disjoint source languages.
I have demonstrated this model on small languages.

Currently, I am working on the correct definition of equivalence preservation.
My choice of axiomatic semantics preservation rather than contextual
equivalence preservation should make it possible to come up with a compositional
definition that allows for general theorems about horizontal and vertical compiler
combination, but I have yet to finalize this definition.
