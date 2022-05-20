Accountability {#sec:accountability}
====================================

In this section, we give a high-level overview of the accountability framework first proposed by @kunnemann2019 and revised by @morio2021 that is implemented in Tamarin.


Accountability in a Nutshell {#sec:accountability-nutshell}
-----------------------------------------------------------

The accountability definition of @kunnemann2019 holds parties of a protocol accountable for violations of a security property expressed by a trace property $φ$.
If a violation occurred, at least one party must have deviated from the protocol.
Each party is either _honest_ and follows the protocol or _dishonest_ and may deviate.
An honest party $A$ becomes dishonest when the event `Corrupted(A)` occurs in the trace and stays dishonest for the rest of the protocol execution.
A dishonest party does not have to deviate and may behave in a way that is indistinguishable from its intended behavior.

The accountability definition focus on parties that are the actual cause of a violation.
This requires protocols to be defined in such a way that deviating parties leave publicly observable evidence for security violations.
In this sense, a protocol provides accountability with respect to a security property $φ$ if we can determine all parties for which the fact that they are deviating at all is a cause for the violation of $φ$.
The decision of whether all such parties can be detected in a protocol is deferred to a _verdict function_, stating which parties should be held accountable, and a set of _verification conditions_ providing soundness and completeness: If and only if the verification conditions hold with respect to a security property $φ$ and verdict function $f$, the verdict function provides the protocol with accountability for $φ$.


Specifying Accountability in Tamarin {#sec:spec-acc}
----------------------------------------------------

The verdict function and verification conditions do not have to be defined explicitly in Tamarin.
Instead, the implementation adds two new syntactic constructs to Tamarin---case tests and accountability lemmas---which define the verdict function and verification conditions implicitly.

Let us first lay down an example protocol to which we can come back to demonstrate the process of specifying and verifying accountability in Tamarin.

### Running Example {#sec:example-1}

We consider a scenario in which access to a central user database is logged.
There are two types of parties involved: managers and employees.
Managers can directly access the database, while an employee needs to be supported by another employee to gain access.

We are interested in holding parties accountable for the case where user data is leaked by either managers or employees.
We model this protocol using [multiset-rewrite rules](#sec:model-specification).

The database is abstracted by using a fresh variable for the user data.

    rule Database:
        [ Fr(~userData) ]
      --[ Database(~userData) ]->
        [ !DB(~userData) ]

The party identities are represented by public variables.
To know if a party is a manager or an employee, they need to be registered.
We use a restriction action to ensure that the type of a party (manager or employee) is distinct.

    rule RegisterManager:
        [ In($x) ]
      --[ IsManager($x)
        , _restrict( not Ex #i. IsEmployee($x)@i ) ]->
        [ !Manager($x) ]

    rule RegisterEmployee:
        [ In($x) ]
      --[ IsEmployee($x)
        , _restrict( not Ex #i. IsManager($x)@i ) ]->
        [ !Employee($x) ]

A manager can access and leak the user data in the database on its own.
Note that the manager leaking the data has to be corrupted since leaking data is not their normative behavior.

    rule ManagerLeak:
        [ !Manager($x)
        , !DB(~userData) ]
      --[ LeakManager($x, ~userData)
        , LeakData(~userData)
        , Corrupted($x) ]->
        [ Out(~userData) ]

Similarly, two employees can access and leak the user data.
Again both employees need to be corrupted and they must be distinct entities.

    rule EmployeesLeak:
       [ !Employee($x)
       , !Employee($y)
       , !DB(~userData) ]
     --[ LeakEmployees($x, $y, ~userData)
       , LeakData(~userData)
       , Corrupted($x)
       , Corrupted($y)
       , _restrict( not ($x = $y) ) ]->
       [ Out(~userData) ]

**Remark:** The protocol allows an unbounded number of participants for each of the two roles and an unbounded number of (concurrent) sessions.
With the example setup, we continue by explaining case tests.

### Case Tests {#sec:case-tests}

Case tests are named (trace properties)[#sec:property_specification] with free variables.
Each free variable is instantiated with a party that should be blamed for a violation.

Case tests take the form of

    test ⟨name⟩:
      "⟨formula⟩"

where `⟨name⟩` is the name of the case test and "⟨formula⟩" its formula.
A case test ought to have at least one free variable and there should be at least one trace where it applies.

In our example, we are interested in holding managers solely and employees jointly accountable for leaks.
Hence, we define two case tests, one for each role:

    test leak_manager:
      "Ex data #i. LeakManager(m, data)@i"

    test leak_employees:
      "Ex data #i. LeakEmployees(x, y, data)@i"

Note that the identifiers of the manager (`m`) and employees (`x`, `y`) are free.
Intuitively, a case test may be seen as a specific manifestation or kind of a security violation.

In the following, we may say that a case test _matches_ a trace if there exists some instantiation of the free variables of the case test, such that the formula holds on the trace.
Moreover, we may say that a case test is _single-matching_ if it is the only case test matching a trace and there exists only one possible instantiation.


Accountability Lemmas {#sec:accountability-lemmas}
--------------------------------------------------

Accountability lemmas are specified similarly to standard lemmas:

    lemma ⟨name⟩:
      ⟨name₁⟩,...,⟨nameₙ⟩ account(s) for "⟨formula⟩"

where `⟨name⟩` is the name of the lemma, `⟨name₁⟩` to `⟨nameₙ⟩` are the names of previously defined case tests, and `⟨formula⟩` is the security property.

Coming back to our example, we can state the accountability lemma holding parties accountable for leaking the user data:

    lemma acc:
      leak_manager, leak_employees account for
        "All data #i. Database(data)@i ==> not Ex #j. LeakData(data)@j"

The complete example can be found [here](../code/userdata-leak.spthy).

Each accountability lemma is translated to a set of $(6n + 1)$ standard lemmas where $n$ is the number of case tests in the lemma.
Each generated lemma corresponds to a verification condition in the accountability framework of [@morio2021].

When loading our example in Tamarin, the accountability lemma `acc` is translated into the following 13 regular lemmas:

    acc_leak_manager_suff (exists-trace)
    acc_leak_employees_suff (exists-trace)
    acc_verif_empty (all-traces)
    acc_leak_manager_verif_nonempty (all-traces)
    acc_leak_employees_verif_nonempty (all-traces)
    acc_leak_manager_min (all-traces)
    acc_leak_employees_min (all-traces)
    acc_leak_manager_uniq (all-traces)
    acc_leak_employees_uniq (all-traces)
    acc_leak_manager_inj (all-traces)
    acc_leak_employees_inj (all-traces)
    acc_leak_manager_single (exists-trace)
    acc_leak_employees_single (exists-trace)

The naming of the lemmas follows the pattern `[acc. lemma name]_[case test name]_[condition]`, where `condition` is one of `suff`, `verif_empty`, `verif_nonempty`, `min`, `uniq`, `inj`, and `single`.

Let us now get a better intuition for the lemmas.
We limit ourselves to the lemmas of the case test `leak_employees` as well the lemma `acc_verif_empty` which is only generated per accountability lemma.
Intuition for the remaining lemmas is obtained by simply switching the roles of managers and employees in the above explanations.

`acc_leak_employees_suff`

: This lemma ensures the existence of a trace in which exactly one pair of employees and no manager leak the data.
  Moreover, only the two employees may be corrupted in the trace.

`acc_verif_empty`

: If neither a manager nor employees leak data, no data is leaked.

`acc_leak_employees_verif_nonempty`

: If a pair of employees leak data, data is leaked.

`acc_leak_employees_min`

: If a pair of employees leak data, there does not exist a prober subset of them that also leads to a leak.

`acc_leak_employees_uniq`

: If a pair of employees leak data, both of them are corrupted.

`acc_leak_employees_inj`

: The free variables in `leak_employees` are instantiated with distinct values.
  In this case, this means that the employees are distinct which is ensured by the restriction in the rule `EmployeesLeak`.

`acc_leak_employees_single`

: This is a simpler version of `'acc_leak_employees_suff` where no requirements on the corrupted parties are made.


Verification of Accountability Lemmas {#sec:verification-accountability}
------------------------------------------------------------------------

The generated lemmas can be verified by Tamarin as any other lemma.
An accountability lemma is said to hold for a theory if Tamarin can successfully verify all generated lemmas and the so-called [replacement property](#sec:replacement-property) holds.

Coming back to our example, we can tell Tamarin to verify the lemmas by executing

    tamarin-prover --prove userdata-leak.spthy

 and get the desired result:

    acc_leak_manager_suff (exists-trace): verified (4 steps)
    acc_leak_employees_suff (exists-trace): verified (5 steps)
    acc_verif_empty (all-traces): verified (4 steps)
    acc_leak_manager_verif_nonempty (all-traces): verified (4 steps)
    acc_leak_employees_verif_nonempty (all-traces): verified (5 steps)
    acc_leak_manager_min (all-traces): verified (4 steps)
    acc_leak_employees_min (all-traces): verified (20 steps)
    acc_leak_manager_uniq (all-traces): verified (2 steps)
    acc_leak_employees_uniq (all-traces): verified (4 steps)
    acc_leak_manager_inj (all-traces): verified (1 steps)
    acc_leak_employees_inj (all-traces): verified (4 steps)
    acc_leak_manager_single (exists-trace): verified (4 steps)
    acc_leak_employees_single (exists-trace): verified (5 steps)

If we are not so lucky and a lemma is falsified, the originating accountability lemma may still hold.
The following list can help us to better understand the consequences of a falsified lemma and gives us a hint on how we could solve the problem. Let `ct` be an arbitrary case test. We leave out the name of the accountability lemma.

#### `_ct_suff` falsified

There does not exist a single-matched trace for `ct` in which only a subset of the blamed parties is corrupted.
At least one party, which is needed to cause a violation, is not blamed.
_Accountability may still be provided._

**Hint:** We assume that `_ct_verif_nonempty` is verified.
If `_ct_single` is also falsified, then we should solve this problem first.
Otherwise, there exists at least one corrupted party in all single-matched traces of `ct`, which is not one of the instantiated free variables of `ct`.
It may be possible to revise `ct` by adding additional free variables and action constraints such that all parties needed for a violation are blamed by `ct`.

#### `_verif_empty` falsified

The security property is violated but no case test matches.
This indicates that the case tests are not exhaustive, that is, capture all possible ways to cause a violation.
_Accountability is not provided._

**Hint:** The trace found by Tamarin as a counterexample may give a clue for an additional case test or shows that the security property can be violated in an unintended way.

#### `_ct_verif_nonempty` falsified

The case test `ct` matches but the security property is not violated.
This indicates that there exists a trace where the parties blamed by `ct` are not sufficient to cause a violation.
_Accountability is not provided._

**Hint:** The trace found by Tamarin as a counterexample may give a clue for revising `ct` such that for all traces in which it matches, the security property is violated.

#### `_ct_min` falsified

There exists an instantiation of a case test `cs` in which strictly fewer parties than in an instantiation of `ct` in the same trace are blamed.
_Accountability is not provided._

**Hint:** We assume that `_ct_verif_nonempty` and `_cs_verif_nonempty` are verified.
If both `ct` and `cs` are necessary for `_verif_empty` to be verified, they need to be separated such that they do not match simultaneously.
This can be accomplished by replacing `ct` with `ct ∧ ¬(cs ∧ fv(cs) ⊊ fv(ct))` where `fv(c)` denotes the free variables of case test `c`.

#### `_ct_uniq` falsified

A party is blamed by an instantiation of `ct` but it has not been corrupted, thereby holding an honest party accountable.
_Accountability is not provided._

**Hint:** We assume `_ct_verif_nonempty` is verified.
If `_ct_min` is also falsified, we should solve this problem first.
The trace found by Tamarin as a counterexample shows which party is blamed unwarranted.
If the corresponding instantiated free variable can never be corrupted, it can be quantified in `ct` to avoid being blamed.
If it can be corrupted for some traces, a closer look on `ct` and the protocol is necessary.

#### `_ct_single` falsified

There does not exist a single-matched trace for `ct`.
Either

1. there does not exist a trace where `ct` matches, or
2. `ct` always matches with multiple instantiations simultaneously, or
3. for all traces there exists another case test which matches at the time.
_Accountability may still be provided._

**Hint:** We assume `_ct_verif_nonempty` is verified.
In case 1, `ct` may be ill-defined or contains a logic error.
In case 2, if all the instantiations are permutations of each other, a single-matched trace may be obtained by making `ct` antisymmetric.
This ensures that whenever the instantiated free variables of two instantiations are the same, then the instantiations are equivalent.
If the instantiations are not permutations, at least two disjoint groups of parties are always blamed.
This requires a closer look on `ct` and the protocol.
In case 3, it may be possible to merge multiple case tests together for which then a single-matched trace exists.

#### `_ct_inj` falsified

The case test `ct` is not injective.
There exists an instantiation mapping distinct free variables to the same party.
_Accountability may still be provided._

**Hint:** `ct` can be split into multiple case tests for which `_inj` holds.
Assume that `fv(ct) = {x, y, z}` and all free variables coincide in any combination.
These are given by the partitions of the free variables:

* `{{x, y, z}}`
* `{{x}, {y, z}}`
* `{{y}, {x, z}}`
* `{{z}, {x, y}}`
* `{{x}, {y}, {z}}`

We then need to split `ct` into five case tests in which the variables in each group are replaced by a single variable.
For example, in the second case above, we replace each occurrence of `y` and `z` by a new variable `v`.

Note that for the conditions `_ct_suff`, `_ct_min`, and `_ct_single` we assumed above that the case tests satisfy `_ct_verif_nonempty`.
If this is not the case, then the case test has a fatal error---it does not always lead to a violation---which renders the other conditions meaningless

In summary, the consequences of falsified lemmas are shown in the following table, where a ✗ indicates that accountability is not provided and a (✓) that accountability may still be provided.

| Falsified lemma      | Accountability provided |
|----------------------|:-----------------------:|
| `_ct_suff`           | (✓)                     |
| `_verif_empty`       |  ✗                      |
| `_ct_verif_nonempty` |  ✗                      |
| `_ct_min`            |  ✗                      |
| `_ct_uniq`           |  ✗                      |
| `_ct_single`         | (✓)                     |
| `_ct_inj`            | (✓)                     |


Replacement Property {#sec:replacement-property}
------------------------------------------------

The replacement property (RP) is used to ensure that there is a decomposition of each trace that separates interleaving causally relevant events so they can be regarded in isolation.
Intuitively, RP says that when we have a single-matched trace for a case test (ensured by '_single`), then we can replace its parties by any other parties allowed by the theory.

Let us consider an example to better understand what this means in practice.

    test A:
      "Ex #i. A(x, y)@i

    test B:
      "Ex #i. B(x, y)@i

We have two case tests `A` and `B` each blaming the two parties (free variables) `x` and `y`.
Assume that there exist the following traces in our theory:

    t1 = A('S', 'T'); B('S', 'T')
    t2 = B('C', 'D')

In `t1` both case test `A` and `B` match with the instantiation `[x → 'S', y → 'T]`.
In `t2` only case test 'B' matches with the instantiation `[x → 'C', y → 'D']`.
The replacement property now requires that there exists a trace `t3` in which only case test `B` matches with its instantiation from `t1`:

    t3 = B('S', 'T')

In fact, we replaced the parties of `B` in `t2` with the parties of `B` in `t1`.
Observe that this is the reason why the `_inj` lemma is necessary.
We can see the replacement as first applying the inverse instantiation of the single-matched trace (here in `t2` with `['C' → x, 'D' → y]) and then applying the instantiation of the other (possibly multi-matched) trace (here in't1` with `[x → 'S', y → 'T]`).

A sufficient criterion implying RP is that traces are closed under bijective renaming.
The implementation features a coarse syntactical check by ensuring that

1. the theory includes no restriction,
2. the theory uses no public names, and
3. the free variables of case tests can only be instantiated by public variables.

If any of these conditions is not satisfied, a wellformedness warning is shown stating that RP has to be checked manually.

Note that in our example, when executing Tamarin to verify the lemmas, we get such a warning:

    The specification contains at least one restriction.

Hence, we need to ensure that the restrictions do not limit our ability to rename parties.
Our theory contains three restrictions.
Two for ensuring that managers and employees are distinct and one for ensuring that an employee cannot take a double role when leaking data:

    restriction Restr_RegisterManager_1:
      "∀ x #NOW.
        (Restr_RegisterManager_1( x ) @ #NOW) ⇒ (¬(∃ #i. IsEmployee( x ) @ #i))"

    restriction Restr_RegisterEmployee_1:
      "∀ x #NOW.
        (Restr_RegisterEmployee_1( x ) @ #NOW) ⇒ (¬(∃ #i. IsManager( x ) @ #i))"

    restriction Restr_EmployeeLeak_1:
      "∀ x #NOW x.1. (Restr_EmployeeLeak_1( x, x.1 ) @ #NOW) ⇒ (¬(x = x.1))"

In the first two cases, if we have a single-matched trace where some manager or employee registers and their role is distinct, then that is also the case when we rename the party in any conceivable way.
There is no possibility of a role to lose their distinctiveness due to the absence of public names.
In the third case, when two employees are distinct in one trace, they remain distinct after bijective renaming.
So in our example, the restrictions are unproblematic for RP and our verification result is valid.


References
----------

::: {#refs}
:::
