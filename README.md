Must be built with Coq 8.14 or higher. Only tested on Coq master, commit 2ac6eec2fe66341548879369882f0b79faaf1375.

Important/representative files:

Metatheory:
Term.v - contains basic term syntax definitions
Rule.v - contains basic rule and language syntax definitions
Core.v - contains judgment forms and monotonicity properties
CompilerDefs.v - contains definitions related to compiler metatheory
Compilers.v - contains the proof of the inductive-implies-semantic theorem

Case Study:
SimpleVSubst.v - the substitution calculus
SimpleVCPS.v - the CPS transformation for STLC
SimpleVCC.v - the core closure conversion pass
SimpleVCPSHeap.v - the CPS transformation for heap operations
CombinedThm.v - The combined corectness result about the full compiler