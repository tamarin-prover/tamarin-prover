
Modeling Issues {#sec:modeling-issues}
===============

First-time users
----------------
In this section we discuss some problems that a first-time user might face.
This includes error messages and how one might fix them.
We also discuss how certain 'sanity' lemmas can be proven
to provide some confidence in the protocol specification.

To illustrate these concepts, consider the following protocol, where an
initiator `$I` and a receiver `$R` share a symmetric key `~k`.
`$I` then sends the message `~m`, encrypted with their shared key `~k` to `$R`.

~~~~ {.tamarin slice="code/FirstTimeUser.spthy" lower=12 upper=33}
~~~~

With the lemma `nonce_secret`, we examine if the message is secret from
the receiver's perspective.


### Exist-Trace Lemmas ###

Imagine that in the setup rule you forgot the agent state fact for the receiver
`AgSt($R,~k)` as follows:

~~~~ {.tamarin slice="code_ERRORexamples/FirstTimeUser_Error1.spthy" lower=16 upper=20}
~~~~

With this omission, Tamarin verifies the lemma `nonce_secret`.  The
lemma says that whenever the action `Secret(m)` is reached in a trace,
then the adversary does not learn `m`. However, in the modified
specification, the rule `R_1` will never be executed. Consequently there
will never be an action `Secret(m)` in the trace. For this reason, the
lemma is vacuously true and verifying the lemma does not mean
that the intended protocol has this property.  To avoid
proving lemmas in such degenerate ways, we first prove `exist-trace`
lemmas.

With an exist-trace lemma, we prove, in essence, that our protocol
can be executed.   In the above example, the goal is that first an
initiator sends a message and that then the receiver receives the same
message.  We express this as follows:

~~~~ {.tamarin slice="code/FirstTimeUser.spthy" lower=34 upper=38}
~~~~

If we try to prove this with Tamarin in the model with the error, the
lemma statement will be falsified. This indicates that there exists no
trace where the initiator sends a message to the receiver.
Such errors arise, for example, when we forget to add a fact that connects
several rules and some rules can never be reached.  Generally it is recommended
first to prove an `exists-trace` lemma before other properties are examined.

### Error Messages ###
In this section, we review common error messages produced by Tamarin.
To this end, we will intentionally add mistakes to the above protocol,
presenting a modified rule and explaining the corresponding error message.

### Inconsistent Fact usage ###

First we change the setup rule as follows:

~~~~ {.tamarin slice="code_ERRORexamples/FirstTimeUser_Error2.spthy" lower=16 upper=20}
~~~~

Note that the first `AgSt(...)` in the conclusion has arity three, with
variables `$I,~k,~m`, rather than the original arity two, with variables
`$I,<~k,~m>` where the second argument is paired.

The following statement that some wellformedness check failed will
appear at the very end of the text when loading this theory.

	WARNING: 1 wellformedness check failed!

Such a wellformedness warning appears in many different error messages at the
bottom and indicates that there might be a problem. However, to get
further information, one must scroll up in the command line to look at the more
detailed error messages.

	/*
	WARNING: the following wellformedness checks failed!

	Fact arity issues
	=================

	Same fact is used with different arities, i.e., Fact('A','B') is different from 
	Fact('A'). 
	Check the arguments of your facts.
	

	Fact `agst':

		1. Rule `setup', arity 3
			AgSt( $I, ~k, ~m )
		
		2. Rule `setup', arity 2
			AgSt( $R, ~k )
		
		3. Rule `I_1', arity 2
			AgSt( $I, <~k, ~m> )
		
		4. Rule `R_1', arity 2
			AgSt( $R, ~k )
	
	*/


The problem lists all the fact usages issues of fact `AgSt`.
Here, we are told that we are dealing with an `arity` issue and all the usages of fact `AgSt` are displayed under the explanation, along with their locations. For example, ``1.Rule `setup', arity 3`` and ``2. Rule `setup', arity 2`` indicate that `AgSt` is both used with 2 and 3 arguments in the `setup` rule.
To solve this problem we must ensure that we only use the same fact with
the same number of arguments.

Same goes if we would have changed the setup rule introducing `capitalization` issues (notice the `AGSt` instead of `AgSt`) :

~~~~ {.tamarin slice="code_ERRORexamples/FirstTimeUser_Error2_Caps.spthy" lower=16 upper=20}
~~~~

Resulting in the following error message :

	/*
	WARNING: the following wellformedness checks failed!

	Fact capitalization issues
	==========================

	Fact names are case-sensitive, different capitalizations are considered as
	different facts, i.e., Fact() is different from FAct(). 
	Check the capitalization of your fact names.
	

	Fact `agst':

		1. Rule `setup', capitalization "AgSt"
			AgSt( $I, <~k, ~m> )
		
		2. Rule `setup', capitalization "AGSt"
			AGSt( $R, ~k )
		
		3. Rule `I_1', capitalization "AgSt"
			AgSt( $I, <~k, ~m> )
		
		4. Rule `R_1', capitalization "AgSt"
			AgSt( $R, ~k )
	
	*/

Or introducing `multiplicity` (i.e. `persistence`) issues (notice the `!AgSt`) :

~~~~ {.tamarin slice="code_ERRORexamples/FirstTimeUser_Error2_Multip.spthy" lower=16 upper=20}
~~~~
Resulting in :

	/*
	WARNING: the following wellformedness checks failed!

	Fact multiplicity issues
	========================

	Same fact is used with different multiplicities, i.e., !Fact() (Persistent fact) 
	exists along with Fact() (Linear) in your rules. 
	Check the multiplicity (persistence) of your facts.
	

	Fact `agst':

		1. Rule `setup', multiplicity (persistence) Linear
			AgSt( $I, <~k, ~m> )
		
		2. Rule `setup', multiplicity (persistence) Persistent
			!AgSt( $R, ~k )
		
		3. Rule `I_1', multiplicity (persistence) Linear
			AgSt( $I, <~k, ~m> )
		
		4. Rule `R_1', multiplicity (persistence) Linear
			AgSt( $R, ~k )
	
	*/


### Unbound variables ###

If we change the rule `R_1` to

~~~~ {.tamarin slice="code_ERRORexamples/FirstTimeUser_Error3.spthy" lower=26 upper=30}
~~~~

we get the error message

	/*
	WARNING: the following wellformedness checks failed!

	Unbound variables
	=================

	rule `R_1' has unbound variables:
		~n
	*/

The warning `unbound variables` indicates that there is a term, here the fresh
`~n`, in the action or conclusion that never appeared in the premise.
Here this is the case because we mistyped `~n` instead of `~m`. Generally,
when such a warning appears, you should check that all the fresh variables
already occur in the premise. If it is a fresh variable that appears
for the first time in this rule, a `Fr(~n)` fact should be added to the
premise.

### Free Term in formula ###

Next, we change the functional lemma as follows

~~~~ {.tamarin slice="code_ERRORexamples/FirstTimeUser_Error4.spthy" lower=34 upper=38}
~~~~

This causes the following warning:

	/*
	WARNING: the following wellformedness checks failed!

	Formula terms
	=============

	lemma `functional' uses terms of the wrong form: `Free m', `Free m'

	The only allowed terms are public names and bound node and message
	variables. If you encounter free message variables, then you might
	have forgotten a #-prefix. Sort prefixes can only be dropped where
	this is unambiguous. Moreover, reducible function symbols are
	disallowed.
	*/

The warning indicates that in this lemma the term `m` occurs free. This
means that it is not bound to any quantifier. Often such an error occurs
when
one forgets to list all the variables that are used in the formula after the
`Ex` or `All` quantifier. In our example, the problem occurred because we deleted the `m` in `Ex I R m #i #j.`

### Undefined Action Fact in Lemma ###

Next, we change the lemma `nonce_secret`.

~~~~ {.tamarin slice="code_ERRORexamples/FirstTimeUser_Error5.spthy" lower=31 upper=33}
~~~~

We get the following warning:

	/*
	WARNING: the following wellformedness checks failed!

	Inexistant lemma actions
	========================

	lemma `nonce_secret' references action
		fact "Secr" (arity 2, Linear)
	but no rule has such an action.
	*/

Such a warning always occurs when a lemma uses a fact that never appears as an
action fact in any rule.
The cause of this is either that the fact is spelled differently (here
`Secr` instead of `Secret`) or that one forgot to add the action fact to the
protocol rules.
Generally, it is good practice to double check that the facts that are used in
the lemmas appear in the relevant protocol rules as actions.

### Undeclared function symbols ###

If we omit the line

~~~~ {.tamarin slice="code/FirstTimeUser.spthy" lower=12 upper=12}
~~~~

the following warning will be output

	unexpected "("
	expecting letter or digit, ".", "," or ")"

The warning indicates that Tamarin did not expect opening brackets. This
means that a function is used that Tamarin does not recognize.
This can be the case if a function `f` is used that has not been declared with
`functions: f/1`. Also, this warning occurs when a built-in function is used but
not declared.
In this example, the problem arises because we used the symmetric
encryption `senc`, but omitted the line where we declare that we use this
built-in function.

### Inconsistent sorts ###

If we change the `setup` rule to

~~~~ {.tamarin slice="code_ERRORexamples/FirstTimeUser_Error7.spthy" lower=16 upper=20}
~~~~

we get the error message

	/*
	Unbound variables
	=================

	rule `setup' has unbound variables:
		m

	Variable with mismatching sorts or capitalization
	=================================================

	Possible reasons:
	1. Identifiers are case sensitive, i.e.,'x' and 'X' are considered to be different.
	2. The same holds for sorts:, i.e., '$x', 'x', and '~x' are considered to be different.

	rule `setup':
		1. ~m, m
	*/

This indicates that the sorts of a message were inconsistently used.
In the rule `setup`, this is the case because we used m once as a fresh value
`~m` and another time without the `~`.

### Subterm Convergence Warning ###

The equational theory used by Tamarin must always be convergent, meaning that any sequence of rewriting steps must eventually terminate, and have the finite variant property. Tamarin verifies if the equational theory is subterm convergent. If it is subterm convergent, it is guaranteed to be convergent an to have the finite variant property. However, if it is not subterm convergent, it does not necessarily imply non-convergence; it only indicates a potential risk of non-convergence. Non-convergence of an equation can result in infinite loops or incorrect results.

An equation is subterm convergent if the right-hand side is a constant (such as `true` or `false`) or a subterm of the left-hand side. For instance, the equation `f(g(x)) = x` is subterm convergent since the right-hand side is a subterm of the left-hand side. Conversely, the equation `f(x) = g(x)` is not subterm convergent.

Consider the following example from the warning:

	/*
	Subterm Convergence Warning
	===========================

  	User-defined equations must be convergent and have the finite variant property. The following equations are not subterm convergent. If you are sure that the set of equations is nevertheless convergent and has the finite variant property, you can ignore this warning and continue 

    unblind(sign(blind(m, r), sk), r) = sign(m, sk)
   
 	For more information, please refer to the manual : https://tamarin-prover.com/manual/master/book/010_modeling-issues.html 
	*/

If you are sure that your equational theory is convergent and has the finite variant theory you can deactivate the warning using the annotation `convergent` as follows:

	equations [convergent]: ...

### Message derivation errors

It is good modelling practice to write our rules in such a way that they do not give participants any additional capabilities, and modify the equational theory for the express purpose of modifying capabilities. Using rules for this is ill-advised, as it is easy to unintentionally make a protocol not adhere to an underlying model or make the adversary weaker than intended. Because of this, Tamarin automatically checks if any rules may introduce such capabilities.


Consider for example what happens if we change the rule `R_1` to

~~~~ {.tamarin slice="code_ERRORexamples/FirstTimeUser_Error8.spthy" lower=26 upper=31}
~~~~

we get the error message

    /*
	Message Derivation Checks
	=========================

	The variables of the following rule(s) are not derivable from their premises, you may be performing unintended pattern matching.

	Rule R_1:
	Failed to derive Variable(s): ~k, m
    */

This warning indicates that in the rule `R_1`, we introduce additional capabilities, namely, the derivation of both `~k` and `m`.

If this is intentional, the rule can be annotated with `[no_derivcheck]`, which will make Tamarin ignore that rule during derivation checks. The behaviour of these derivation checks can be further modified with the `--derivcheck-timeout` (or `-d`) flag. By default, it is set to a value of `5` seconds. Setting it to `0` disables derivation checks.

### What to do when Tamarin does not terminate ###
Tamarin may fail to terminate when it automatically constructs proofs.
One reason for this is that there are open chains.
For advice on how to find and remove open chains, see [open chains](009_precomputation.html#sec:openchains).
