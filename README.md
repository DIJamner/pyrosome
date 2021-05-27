#TODOs

* restructure/rename file layout
  + remove named/ hierarchy level
  + clear old files in other dirs
* Rename ARule to Rule
* Rename anything with exp to term
  + Fix variable conventions simultaneously?
* reassess exp(term)/sort distinction
  + no distinction?
  + use a newtype wrapper rather than repeating top level constr?
  + downside of above options: dealing with vars as sorts
* generalize base framework forms with prefixes a la ElabWithPrefix
* write function from elab'ed objects to pre-elab
  + use to imply elab judgments from wfness
  + use to show elab judgments are functions
* assess whether final induction of inductive_implies_semantic is necessary
* work out bookkeeping for semantic_implies_inductive