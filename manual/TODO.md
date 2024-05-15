TODO items to add to the manual
===============================

From Kevin Milner and Dennis Jackson:



  * A general style recommendation for .spthy files (indentation, line breaks,
    commenting guidelines, ‘good’ naming of facts/actions/variables)

  * General tips, like:

      * including an ‘exists trace’ (and that it can be useful to use
        authenticated message facts to prove that if necessary)

      * writing actions so that when they’re referenced in lemmas they are as
	constrained as possible (to prevent creating a ton of branching cases
        to prove)

      * useful patterns for reused lemmas like establishing invariants and
	avoiding things that will cause huge disjunctions for tamarin to split
        on.

      * Maybe some recommended implementations of common patterns of rules,
	for things like agent key registration, conditional rules (using
	restrictions, like we have in the detection stuff), maybe how we pass both
	agents long term keys around to make writing signature verification
        easier (and why that’s sound as long as you don’t do anything silly)



  * Discussion on system requirements. Perhaps Tamarin should warn the user
    when it exceeds available RAM? 
    **NOTE** Cas: the second is a feature request.



  * The differing heuristics for GUI and CLI 
 [there is supposedly a difference here, check the issue tracker as well, not sure where to document this]




----------------------------

  * Unintentionally writing a rule with an unbound variable. It noted that
    the well formedness check fails. But its not clear whether this is a
    warning or a critical error or to what it pertains. (From my memory of the
    CLI). Also this warning is entirely absent in the GUI? 
  [this only creates a warning, only on initial load on the command line, this needs to be made clear as a problem]

```
theory ATTEMPT 
begin

rule test: 
  [] --> [ Fact(X)]

end
```


/*
WARNING: the following wellformedness checks failed!

unbound:
  rule `test' has unbound variables: 
    X
*/


  * TODO: Maybe variables and sort annotations should be introduced by Cas in
    005.

------------------------------
