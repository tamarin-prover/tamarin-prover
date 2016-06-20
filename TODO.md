TODO items to add to the manual
===============================

From Kevin Milner and Dennis Jackson:

  * A complete list of the builtins and exactly what symbols/functions they
    add (e.g. some parts of the term grammar in the current manual only
    actually exist with particular builtins, I believe)

  * A complete list of the things that can annotate lemmas and what they do

      * Typing lemmas in particular - how to tell when one would help, the
        best way to write one, and what you can’t prove in a typing lemma

  * An explanation/examples of the difference between K, KU, and KD, and when
    you would use each.

  * When to annotate variables with symbols e.g. ~,$,'

  * Example use-cases for variable annotations ($ ~), and any caveats that
    might come with them (like if incorrect ~ use can make things unsound)

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
	axioms, like we have in the detection stuff), maybe how we pass both
	agents long term keys around to make writing signature verification
        easier (and why that’s sound as long as you don’t do anything silly)

  * The differing heuristics for GUI and CLI 

  * Unintentionally writing a rule with an unbound variable. It noted that
    the well formedness check fails. But its not clear whether this is a
    warning or a critical error or to what it pertains. (From my memory of the
    CLI). Also this warning is entirely absent in the GUI? 

  * A standard package of axioms e.g. Unique, Eq, Neq, and so on. 
    **NOTE** Cas: perhaps this is more like a feature request?

  * Discussion on system requirements. Perhaps Tamarin should warn the user
    when it exceeds available RAM? 
    **NOTE** Cas: the second is a feature request.

  * A standard package of lemmas .e.g Secrecy and so on? 
    **NOTE** feature request; also very model-specific.

  * Warning - Virtualised Tamarin has significant overhead due to Haskell
    virtualisation 'bad stuff' (seems to make a lot of system calls)

  * Shortcomings - A list of things you definitely can't ever get Tamarin to
    do / what you can't get it to do yet. A useful section in any software.

