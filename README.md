#TODOs

* restructure/rename file layout
  + remove named/ hierarchy level
  + clear old files in other dirs
  + move IndependentJudgment out of ICore
  + rename/expand or at least roadmap Decidable
* Fully switch to independent judgment (no elab) for all existing languages? (currently reconsidering)
* Relate independent judgment to original via elab to port theorems (or is it easier to replicate them?)
* Clear admits in Decidable
* Extend Decidable to work for compilers when possible
* Fix reduction lemma to be sound
* Improve automation to be consistent across all uses
* determine whether there is an issue w/ current lax typing on le judgments (probably)
* Either: remove IExp and use Exp for everything (this one I think)
* Or: implement equality? and fill admits in subst lemmas for IExp
* fill admits (or remove lemmas) for identity operation in Tactics