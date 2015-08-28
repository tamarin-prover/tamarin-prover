<TeXmacs|1.0.7.1>

<style|article>

<\body>
  <doc-data|<doc-title|Protocol Analysis with equational theories
  (Notes)>|<doc-author-data|<author-name|Benedikt Schmidt>>>

  \;

  <section|Operational Semantics>

  <\itemize>
    <item>Facts = Protocol state + Send Messages + Known messages

    <item>enforce <strong|learn only once>, so send messages have to be
    explicitly learned

    <item>Protocol rules + messages derivation rules = Set rewriting rules

    <item>trace of reachable states starting with <math|\<emptyset\>>.

    <item>security properties = sets of reachable states that can be
    described in a certain way
  </itemize>

  <subsection|Rules>

  <\itemize-dot>
    <item>Partition set of rules in protocol rules send rules <math|RS>,
    forward rules <math|RF>, and backward rules <math|RB>.

    <item>In some sense, RF corresponds to analz and RB to synth.
  </itemize-dot>

  <section|Derivation Graphs>

  <\itemize>
    <item>identify traces that only differ in <strong|unneccessary
    permutations>

    <item><strong|partial order reduction> for protocol state transitions

    <item>reachable states are <strong|identical> to set rewriting
  </itemize>

  <subsection|Normal Forms of Derivation Graphs>

  <\itemize>
    <item>derivation graphs allow <strong|too many ways> to derive the same
    message (<strong|learn-only-once> helps, but <strong|not sufficient> for
    all equational theories)

    <item><strong|1-1> correspondence between <strong|message derivation
    subgraphs> and <strong|recipes>

    <item>we only allow subgraphs that correspond to normalized recipes

    <item><strong|correctness>: <strong|translate> normalized recipe to
    graph, <strong|introduce sharing>
  </itemize>

  <section|Patterns and Pattern Transformations>

  <\itemize-dot>
    <item>Patterns are symbolic (include variables, not ground) derivation
    graphs with some additional information. The additional information is a
    set of chain constraints.

    <item>the models of patterns are derivation graphs

    <item>We write <math|c\<rightsquigarrow\>a> for a conclusion occurence
    <math|c> and an assumption occurence <math|a>. The constraint is true for
    all derivation graphs with a path from <math|c> to <math|a> that includes
    only main assumption occurences for <math|RF> rule instances. We define
    the function <math|chain(G)> that returns all chains in a derivation
    graph <math|G>.

    <item>main assumptions will we defined later, but think ciphertext
    assumption, not key for decryption rule now.

    <item>an assumption occurence <math|a> is <strong|open> if there is no
    incoming arrow and no chain constraint with target <math|a>.
  </itemize-dot>

  <subsection|Patterns and their Models>

  <\enumerate-numeric>
    <item><math|\<vdash\>G;C> with <math|G> a graph over terms with variables
    and <math|C> a set of chain constraints.

    <math|<left|llbracket> \<vdash\>G<right|rrbracket> = {<wide|G|~> \|
    <wide|G|~> \<in\> NDG \<wedge\> (\<exists\>\<sigma\>. nodes(G)\<sigma\>
    \<subseteq\> nodes(<wide|G|~>) \<wedge\> edges(G)\<sigma\> \<subseteq\>
    edges(<wide|G|~>)\<wedge\>C\<sigma\>\<subseteq\>chains(<wide|G|~>)}>
  </enumerate-numeric>

  <subsection|Transformations of Patterns>

  Here we give a number of rules of rules that transform a pattern into a set
  of covering patterns. This is similar to the constraint system
  transformation description of unification. We later on try to give a
  terminating control for the <strong|decidable subproblems> of
  <strong|ground deducibility> and <strong|bounded session analysis> for
  <strong|weakly typed protocols>.

  <\enumerate-numeric>
    <item><strong|Source>(a): <math|\<vdash\><rsup|>G;S\<Rightarrow\>
    backwardsResolve(G,S,a)\<cup\>chains(G,S,a)>

    <no-indent>where

    <no-indent><math|a=(r<rsub|a>,i<rsub|a>)> is an occurence of an
    <strong|open assumption>. Which <math|a> to focus on is a <strong|don't
    care choice> that we can do ourselves.

    <no-indent>and

    <math|<no-indent>backwardsResolve(G,S,a)={(\<vdash\>G,r,(r,i)<rsub|>\<rightarrow\>a;S)\<sigma\>
    \| r \<in\>RB \<wedge\>i\<in\>concIndices(r)\<wedge\> \<sigma\> \<in\>
    unifs(conc(r,i),assm(a))}>

    <no-indent>and

    <no-indent><math|chains(G,S,a)={\<vdash\>G,r;S,(r,i)\<rightsquigarrow\>a\|
    r \<in\>RS \<wedge\>i \<in\>concIndices(r)}>

    <item><strong|Forward(<math|c\<rightsquigarrow\>a>)>:
    <math|\<vdash\><rsup|>G;S,c\<rightsquigarrow\>a\<Rightarrow\>solveDirect(G,S,a,c)
    \<cup\> \ forwardResolve(G,S,c,a)>

    <no-indent>where

    <no-indent><math|c\<rightsquigarrow\>a> is a a chain. Which chain we try
    to solve is a <strong|don't care choice>.

    <no-indent>and

    <no-indent><math|solveDirect(G,S,a,c)={(\<vdash\>G,c\<rightarrow\>a;S)\<sigma\>
    \| \<sigma\> \<in\> unifs(c,a)}>

    <no-indent>and

    <no-indent><math|forwardResolve(G,S,c,a)={(\<vdash\>G,r,c\<rightarrow\>a<rprime|'>;S,c<rprime|'>\<rightsquigarrow\>a
    \| r\<in\>RF\<wedge\>\<sigma\>\<in\>unifs(c,a<rprime|'>)\<wedge\>a<rprime|'>=mainInput(r)\<wedge\>c<rprime|'>=concl(r)}>
  </enumerate-numeric>

  A solved pattern is a pattern with no chain constraints where all open
  assumptions are variables. (TODO: add all terms normalized, types?)\ 

  <subsection|Correctness of the Transformations>

  Has to be sound and complete:

  <strong|Soundness> clear

  <strong|completeness> follows from <strong|chain property> for rule
  partition in <math|R=RF\<cup\>RS\<cup\>RB>.

  \;

  <no-indent><strong|Chain property>: every knowledge assumption has a chain
  that <strong|starts> with a rule from <strong|RS> and the rest of the path
  can be split into a first part with <strong|one or more> <strong|RF> rules
  and a second part with <strong|zero or more> <strong|RB> rules. For the RF
  rules, the path includes only main assumptions.

  \;

  <no-indent>The chain property is something we have to prove for a message
  theory that we want to use. I.e., given a set of rules, we have to find a
  partitioning s.t. the chain property holds.

  <section|The Analysis Algorithm>

  Only transformations with <strong|don't care choice> is <strong|focus>
  which takes an open assumption occurence. So we need a good
  <strong|heuristics> to find open goals that can be used to get
  <strong|contradictions>.

  We would like the patterns to have <strong|nice properties> that help us
  with the <strong|proof search>. Since the problem is <strong|undecidable>,
  there is no hope to have properties that allow us to to <strong|decide> the
  problem.

  But there are certain decidable subclasses of the problem that our
  algorithm should decide:

  <\enumerate-numeric>
    <item>Ground message deducibility = a protocol that just sends the ground
    messages in <math|\<Gamma\>> for <math|\<Gamma\>\<vdash\>s>.

    <item>Bounded sessions = no rule for thread creation, but ground thread
    creation <strong|rule instances> for the <strong|sessions> under
    consideration.
  </enumerate-numeric>

  Bounded chain length:\ 

  <\itemize>
    <item>If we have a weak typing assumption and the standard DY theory, we
    \ have bounded length for forward chains. For backward chains, this is
    not so easy. I think it boils down to the fact that only solveDirect
    applies a substitution to the graph. resolveBackward and resolveForward
    either do not unify or ony specialized the assumptions/conclusions of the
    newly added rule. It should be possible to find a measure that decreases
    as long as #threads is constant.
  </itemize>

  <subsection|Termination for standard DY theory>

  We now consider the following setting: standard DY theory (symmetric
  encryption, hash, pair) as a subterm theory. No error terms, bounded number
  of protocol instances. We have to find a measure that decreases for every
  transformation that does not introduce a new protocol rule instance.

  \;

  The rules in <math|RF> all have the following property: The conclusion is
  just a variable, the main assumption has the form <math|encS(k,m)> or
  <math|pair(x<rsub|1>,x<rsub|2>)>. For the rules in <math|RB>, the
  assumptions are just variables and the conclusion has the same above form.
  So when we unify a conclusion from <math|RB> or the main assumption from RF
  with a term that is <strong|not> a variable, this corresponds to matching
  the term with <math|encS(k,m)> or <math|pair(x<rsub|1>,x<rsub|2>)> and the
  corresponding substitution only instantiates variables in the rule we use
  for forward resolve/backward resolve.

  So specialized to this message theory, we have the following system:

  <\enumerate-numeric>
    <item><strong|Focus(a)>: <math|\<vdash\>G;C\<Rightarrow\>{\<vdash\><rsup|a>G;C}>

    <no-indent><math|a=(r<rsub|a>,i<rsub|a>)> is an occurence of an
    <strong|open assumption>. Which <math|a> to focus on is a <strong|don't
    care choice> that we can do ourselves.

    <item><strong|Source>: <math|\<vdash\><rsup|a>G;S\<Rightarrow\>
    backwardsResolve(G,S,a)\<cup\>chains(G,S,a)>

    <no-indent>where

    <no-indent><math|backwardsResolve(G,S,a)={\<vdash\>G,r\<sigma\>,(r\<sigma\>,i)<rsub|>\<rightarrow\>a;S
    \| r \<in\>RB \<wedge\>i\<in\>concIndices(r)\<wedge\> \<sigma\> \<in\>
    unifs(conc(r,i),assm(a))}>

    <no-indent>and

    <no-indent><math|chains(G,S,a)={\<vdash\>G,r;S,(r,i)\<rightsquigarrow\>a\|
    r \<in\>RS \<wedge\>i \<in\>concIndices(r)}>

    <item><strong|Forward>: <math|\<vdash\><rsup|>G;S,c\<rightsquigarrow\>a\<Rightarrow\>solveDirect(G,S,a,c)
    \<cup\> \ forwardResolve(G,S,c,a)>

    <no-indent>where

    <no-indent><math|solveDirect(G,S,a,c)={(\<vdash\>G,c\<rightarrow\>a;S)\<sigma\>
    \| \<sigma\> \<in\> unifs(c,a)}>

    <no-indent>and

    <no-indent><math|forwardResolve(G,S,c,a)={(\<vdash\>G,r\<sigma\>,c\<rightarrow\>a<rprime|'>\<sigma\>;S,c<rprime|'>\<sigma\>\<rightsquigarrow\>a
    \| r\<in\>RF\<wedge\>\<sigma\>\<in\>unifs(c,a<rprime|'>)\<wedge\>a<rprime|'>=mainInput(r)\<wedge\>c<rprime|'>=concl(r)}>
  </enumerate-numeric>

  The measures we consider are <math|tsmax>, the maximal size of a term in
  the pattern.\ 

  <subsection|Multiplication>

  For DH, the problem is slightly different because of associativity and
  commutativity. First, we can ensure that there are never two exp rules in a
  row since two exps can be replaced by one exp + one mult. Then we only have
  to handle mult. Since we can assume that a protocol never sends a product
  in an extractable position, we will never have to use a multiplication in a
  forward rule.

  I think we have two choices:

  <\enumerate-numeric>
    <item>Only take variants of rules that have one non-product input. This
    corresponds to left-nested normalized recipes.

    <item>Use the same normal form of DH terms as elsewhere. So normalized
    recipe for multiplication is:

    <math|((\<ldots\>(x<rsub|1>\<times\>x<rsub|2>)\<ldots\>)\<times\>\<ldots\>)\<times\>x<rsub|k>)\<times\>((\<ldots\>(y<rsub|1>\<times\>y<rsub|2>)\<ldots\>)\<times\>\<ldots\>)\<times\>y<rsub|l>)<rsup|-1>>

    and all the <math|x<rsub|i>> and <math|y<rsub|i>> are neither products
    nor inverses and they are also sorted (I'm not so sure about this, this
    could make some things harder) and for all <math|i>,<math|j>:
    <math|x<rsub|i>\<neq\>y<rsub|j>>. So we first have a product non-inverted
    and inverted and then we have products of nonproducts on the right and
    products or nonproducts on the left.

    <tabular|<tformat|<table|<row|<cell|<math|x>
    \ <math|y>>>|<row|<cell|<emdash><emdash>>>|<row|<cell|<math|x\<times\>(y)<rsup|-1>>>>>>>[*]

    <math|<with|mode|text|<tabular|<tformat|<table|<row|<cell|<math|x>
    \ <math|y>>>|<row|<cell|<emdash><emdash>>>|<row|<cell|<math|x\<times\>y>>>>>>>>[<math|y>
    nonproduct, <math|x> product or not]

    \;

    [*] no variants required since all products are intruder built, so he can
    directly ``build the normal form'''

    <item>It might make more sense to just go for
    <math|x<rsub|1><rsup|e<rsub|1>>\<ldots\> x<rsub|k><rsup|e<rsub|k>>>. But
    this also makes everything more complicated. The question is how many
    patterns do we need to represent a certain state. E.g., if we want to
    allow the adversary to send a1*y for any y that does not cancel a1 out,
    even for y=a1, then it would be nice to represent this with a single
    pattern.\ 
  </enumerate-numeric>

  <subsection|Case split on equality of thread ids when adding protocol
  steps>

  Simon and my algorithm do not perform a case split on the fact if the
  protocol step that is added by a chain is new or equal to an existing step.
  We are lazy and only make protocol steps equal when it is inevitable
  (unification with an open assumption).

  \;

  How would I perform the case split in my setting:

  Chains can start from existing protocol steps and from new protocol steps.
  For new protocol steps, we can add an inequality constraint on the threadid
  of the step. New steps = instances with new threadid and with old threadid
  for steps that are not already in there. Unification occurs when closing
  the open <math|\<cal-P\>> assumptions of the newly added rules. The obvious
  adding prefix steps can be done just by the standard rules and defining a
  suitable strategy.

  \;

  Concrete change:

  First, add inequality constraints for thread ids (or rigid variables, check
  relation).

  <item><strong|Source>: <math|\<vdash\><rsup|a>G;S\<Rightarrow\>
  backwardsResolve(G,S,a)\<cup\>chainsNew(G,S,a)\<cup\>chainsExisting(G,S,a)>

  <no-indent>where

  <no-indent><math|backwardsResolve(G,S,a)={(\<vdash\>G,r,(r,i)<rsub|>\<rightarrow\>a;S)\<sigma\>
  \| r \<in\>RB \<wedge\>i\<in\>concIndices(r)\<wedge\> \<sigma\> \<in\>
  unifs(conc(r,i),assm(a))}>

  <no-indent>and

  <no-indent><math|chainsNewThread(G,S,a)={\<vdash\>G,r;S,(r,i)\<rightsquigarrow\>a;
  threadvar(r) \<notin\>threadvar(protoSteps(G)) \| r \<in\>RS \<wedge\>i
  \<in\>concIndices(r)\<wedge\>}>

  <no-indent>and

  <no-indent><math|chainsExThreadNewStep(G,S,a)={\<vdash\>G,r;S,(r,i)
  \<rightsquigarrow\>a\| <wide|r|~> \<in\>RS\<wedge\>i
  \<in\>concIndices(r)\<wedge\>tidvar\<in\>threads(G)\<wedge\>(tidvar,step(<wide|r|~>))
  \<notin\>steps(G)\<wedge\>r=<wide|r|~>{tidvar/tid}}>

  <no-indent>and

  <no-indent><no-indent><math|chainsExistingStep(G,S,a)={\<vdash\>G,r;S,(r,i)
  \<rightsquigarrow\>a\| r \<in\>protoSteps(G) \<wedge\>i
  \<in\>concIndices(r)}>

  \;

  Pros of case split:

  <\itemize-dot>
    <item>for bounded verification, the number of protocol steps in the
    pattern corresponds directly to the number of protocol steps in all
    represented traces because all steps are inequal (different threadid and
    stepcounter)

    <item>termination for the bounded case is easier to show
  </itemize-dot>

  Cons of case split:

  <\itemize-dot>
    <item>Algorithm more complicated, I need inequalities for threadids or
    make threadids special and do it like Cas.

    <item>Might be less efficient because the case split occurs earlier, but
    I'm not sure if it really makes a big difference. Have to ask Simon about
    this.

    <item>We assume less about protocol and have to make threadids somewhat
    special. But I have the feeling we have to do this anyways.
  </itemize-dot>

  <subsection|Termination for bounded sessions>

  We have three parameters that we can vary when reasoning about termination:

  <\itemize-dot>
    <item>typing:

    <\itemize-minus>
      <item>strictly typed a la Scyther: Protocol variables can only be
      instantiated with values of the right type. This means all decryption
      chains can be precomputed and \ instantiations with terms of another
      type can not occur. This approach basically bounds the message size. It
      has untyped variables, but the algorithm loses many of its nice
      properties when these occur in a protocol description, e.g., it is not
      a decision procedure for bounded sessions anymore.

      This requires something like Lowe's typing result, i.e., for every
      attack that exploits a type flaw, there is also a well-typed attack.

      <item>weakly typed a la Simon: Protocol variables that are instantiated
      with the wrong type are already known to the adversary. So the
      decryption chains can be precomputed. But as long as the intruder does
      not extract the protocol variables, they can be instantiated by values
      of arbitrary type. I.e., for decryption chains of nonmaximal length, we
      can not say anything about how protocol variables are instantiated.

      This requires that we prove weak typing in a separate step. This is
      also a reachability property (protocol variable instantiated with value
      wrong type and value not known to adversary) that we can prove by
      running the algorithm.

      <item>untyped: protocol variables can be instantiated with arbitrary
      values. Seems to require some degree of forward search in most
      situations. E.g., find a <strong|first> protocol step and go from
      there.\ 
    </itemize-minus>

    <item>Equational theory: Of course simpler for free theory with
    encryption, pairing, and hashes (DY theory). I want to also reason about
    DH theory and other interesting ones (Xor).

    <item>case split when adding protocol step on equality with existing step
    (see above)
  </itemize-dot>

  <subsubsection|Strictly/Weakly Typed + DY + splitEqual>

  <paragraph|Problems with existing Proofs>

  Approach in Cas' thesis (and even more in CCS paper) has some flaws since
  the lex order on rnk(P)=(bound - threadCount(P), enc(P), og(P)) where
  enc(P) is the number of encryption in the open goals and og(P) is the
  number of open goals in P does not decrease with every transformation.

  If a thread is added, the first component decreases and we don't care about
  the others. If a backwards (encrypt) step is done, the first component is
  constant and the second decreases strictly since the two open goals are
  strict subterms of the old open goal (the plaintext and the key). For a
  decrypt step, the first component is constant, but the second and the third
  might increase since there are new open goals for all keys that have to
  used for decryption. These keys might be composed and contain new
  encryptions and there might be more such new open goals than the one closed
  goal such that og(P) also increases. In a weakly typed setting, the
  unification might also increase enc(P) since a variable might be
  instantiated with an encryption.

  <paragraph|Ideas on fixing the Proof>

  Should be possible to reduce weak typing (disjunction of message patterns
  with atomic vars for protocol variable instantiations) can be reduced to
  weak atomicity and different protocol step rule variants.

  I think there are two things that the measure does not account for: the
  number of variables in the problem and the fact that there is only a
  bounded number of decryption chains starting from a certain sent message.
  The number of chains corresponds to the number of positions for extractable
  subterms. For all instantiations, this corresponds to the extractable
  positions in the message templates since weak atomicity disallows
  extracting something from a nonatomically instantiated protocol variable.

  Measure functions:

  <\itemize-dot>
    <item>stepsLeft(P) returns the number of protocol steps in the pattern

    <item>vars(P) returns the number of variables that occur in P

    <item>unusedPositions(P) returns the multiset of extractable subterm
    positions in sent terms

    <item>openAssumptionSizes(P)

    <item>openConclusionSizes(P)
  </itemize-dot>

  Then we have the following situation:

  <\itemize-dot>
    <item><strong|chainExistingThreadNewStep> and <strong|chainNewThread>:
    decreases stepsLeft(P)

    <item><strong|solveDirect>: unifies a conclusion with an assumption

    <\enumerate-alpha>
      <item>unifier gets rid of a variable in P when applied to P,
      stepsLeft(P) equal and vars(P) decreases.

      <item>unifier does not get rid of a variable <math|\<Rightarrow\>>
      <math|\<sigma\>=id>, therefore openConclusionSizes(P) decreases and
      openAssumptionSizes is equal. stepsLeft(P),vars(P) and
      unusedPositions(P) equal.
    </enumerate-alpha>

    <item><strong|chainExistingStep>: either position new and the set of
    unused chains for given conclusion decreases or position old and
    therefore no new open assumption added and therefore
    \ openAssumptionSizes equal and openConclusionSizes decreases.

    <\enumerate-alpha>
      <item>Conclusion not used yet, therefore unusedPositions decreases.
      stepsLeft(P) and vars(P) equal.

      <item>Conclusion already used, therefore everything
      openAssumptionSizes(P) decreases, openConclusionSizes(P) increases.\ 
    </enumerate-alpha>

    <item><strong|backwardResolve>: decrease openAssumptionSizes, everything
    else equal.

    <item><strong|forwardResolve>:

    <\enumerate-alpha>
      <item>forward step is new, then unusedPositions decreases

      <item>forward step is old, then openConclusionSizes decreases and
      stepsLeft, vars, openAssumptionSize equal.
    </enumerate-alpha>
  </itemize-dot>

  So the measure is the lex product of the two times the order on
  <math|\<bbb-N\>>, and 3 times the multiset order on (stepsLeft(P), vars(P),
  unusedPositions(P),openAssumptionSizes(P),openConclusionSizes(P)).

  <tabular|<tformat|<table|<row|<cell|>|<cell|stepsLeft>|<cell|vars>|<cell|unusedPositions>|<cell|openAssmSizes>|<cell|openConcsSizes>>|<row|<cell|chainExistingThreadNewStep>|<cell|->|<cell|+>|<cell|+>|<cell|+>|<cell|+>>|<row|<cell|chainNewThread>|<cell|->|<cell|+>|<cell|+>|<cell|+>|<cell|+>>|<row|<cell|chainExisting
  a)>|<cell|=>|<cell|=>|<cell|->|<cell|->|<cell|+>>|<row|<cell|chainExisting
  b)>|<cell|=>|<cell|=>|<cell|=>|<cell|->|<cell|+>>|<row|<cell|solveDirect
  a)>|<cell|=>|<cell|->|<cell|=>|<cell|+>|<cell|+>>|<row|<cell|backwardResolve>|<cell|=>|<cell|=>|<cell|=>|<cell|->|<cell|=>>|<row|<cell|forwardResolve
  a)>|<cell|=>|<cell|=>|<cell|->|<cell|+>|<cell|->>|<row|<cell|forwardResolve
  b)>|<cell|=>|<cell|=>|<cell|=>|<cell|=>|<cell|->>>>>

  \;

  <subsubsection|Untyped + DY + splitEqual>

  For the untyped setting, the problem is that we cannot bound
  unusedPositions a priori since a protocol variable might be instantiated
  with an encryption and then the adversary must be allowed to decrypt it
  since he could learn something new. But if we solve the system in a certain
  order, more precisely starting with the first protocol step, then we know
  what structure has been added by the adversary.

  <subsubsection|Strictly/Weakly Typed + DH + splitEqual>

  The problem might be that Mult can introduce new variables, so
  backwardResolve in combination with solveDirect might become a problem.

  <subsubsection|Strictly Typed + DY + noSplit>

  <subsubsection|Weakly Typed + DY + noSplit>

  <subsubsection|Untyped + DY + splitEqual>

  <section|Problem with not forcing unpairing>

  For unbounded verification, the algorithm might not terminate in some cases
  without forced unpairing. If there is an infinite sequence of pairs
  <math|(a,x<rsub|1>)>, <math|(a,x<rsub|2>)>, .. that the intruder could have
  known before <math|a>, then the algorithm loops.

  There are two ways to enforce pairing. Hard forcing where whenever the
  intruder encounters a pair, he has to learn all the components. The other
  alternative is soft forcing where the intruder learns the components when
  he uses a pair. ...

  With forced unpairing, we have that if the intruder knows
  <math|(a,x<rsub|>)> at some point and <math|(a,y)> before that, then he
  must have known \ 
</body>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-10|<tuple|4.1|3>>
    <associate|auto-11|<tuple|4.2|3>>
    <associate|auto-12|<tuple|4.3|?>>
    <associate|auto-13|<tuple|4.4|?>>
    <associate|auto-14|<tuple|4.4.1|?>>
    <associate|auto-15|<tuple|4.4.1.1|?>>
    <associate|auto-16|<tuple|4.4.1.2|?>>
    <associate|auto-17|<tuple|4.4.2|?>>
    <associate|auto-18|<tuple|4.4.3|?>>
    <associate|auto-19|<tuple|4.4.4|?>>
    <associate|auto-2|<tuple|1.1|1>>
    <associate|auto-20|<tuple|4.4.5|?>>
    <associate|auto-21|<tuple|4.4.6|?>>
    <associate|auto-22|<tuple|5|?>>
    <associate|auto-3|<tuple|2|1>>
    <associate|auto-4|<tuple|2.1|1>>
    <associate|auto-5|<tuple|3|1>>
    <associate|auto-6|<tuple|3.1|2>>
    <associate|auto-7|<tuple|3.2|2>>
    <associate|auto-8|<tuple|3.3|2>>
    <associate|auto-9|<tuple|4|2>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Operational
      Semantics> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|1.1<space|2spc>Rules
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Derivation
      Graphs> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|2.1<space|2spc>Normal Forms of Derivation
      Graphs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Patterns
      and Pattern Transformations> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|3.1<space|2spc>Patterns and their Models
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|1.5fn>|3.2<space|2spc>Transformations of Patterns
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|1.5fn>|3.3<space|2spc>Correctness of the
      Transformations <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>The
      Analysis Algorithm> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|4.1<space|2spc>Termination for standard DY
      theory <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <with|par-left|<quote|1.5fn>|4.2<space|2spc>Multiplication
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <with|par-left|<quote|1.5fn>|4.3<space|2spc>Case split on equality of
      thread ids when adding protocol steps
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12>>

      <with|par-left|<quote|1.5fn>|4.4<space|2spc>Termination for bounded
      sessions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <with|par-left|<quote|3fn>|4.4.1<space|2spc>Strictly/Weakly Typed + DY
      + splitEqual <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|6fn>|Problems with existing Proofs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15><vspace|0.15fn>>

      <with|par-left|<quote|6fn>|Ideas on fixing the Proof
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16><vspace|0.15fn>>

      <with|par-left|<quote|3fn>|4.4.2<space|2spc>Untyped + DY + splitEqual
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17>>

      <with|par-left|<quote|3fn>|4.4.3<space|2spc>Strictly/Weakly Typed + DH
      + splitEqual <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18>>

      <with|par-left|<quote|3fn>|4.4.4<space|2spc>Strictly Typed + DY +
      noSplit <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>>

      <with|par-left|<quote|3fn>|4.4.5<space|2spc>Weakly Typed + DY + noSplit
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <with|par-left|<quote|3fn>|4.4.6<space|2spc>Untyped + DY + splitEqual
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21>>
    </associate>
  </collection>
</auxiliary>