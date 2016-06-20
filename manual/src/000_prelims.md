<p class="halfbreak">
</p>

Preliminaries
=============

Please ensure that all of us follow these instructions, so we end up
with a document that is consistent and as easy to read as possible.

We aim to write this document using American English.


Notation in general
-------------------

Take a look at the notation.sty file which contains a lot of the
abbreviations and keywords we will likely need for the document.
Rather than defining new commands in your section, put them there so
everyone can use them and there is one single spot to look for them.

For LaTeX labels use the label's type as the start: sec:introduction,
fig:example, def:syntax, etc.

Protocol notation
-----------------

We will use spthy description for all protocols. In the introduction,
we can additionally(!), give mathematical notation for the first few
examples. Also ensure all protocols are available as executable spthy
files, and are stored in a sub-directory of the repository for easy
distribution. The best way to ensure everything fits together is to
*autognp* on the spthy files.

~~~~ {.autognp include="code/example.spthy"}
~~~~

You can also include a slice of a file.

~~~~ {.autognp slice="code/example.spthy" lower=12 upper=13}
~~~~


Indexing
--------

Use LaTeX's indexing capability with the keyword \textbackslash
index\{Index\}. For example, we talk about makeindex\index{makeindex}
here.


Intended Audience
-----------------

This is a user manual, not a scientific paper. The goal is not to
explain the scientific merits of Tamarin, but to explain how to use
Tamarin to somebody that has not used Tamarin before, or somebody that
has used it before and wants to know about more advanced features. We
assume that the reader is a computer scientist and has some basic
background knowledge in logic and programming, but is not an expert in
formal methods or security. This includes students, people from
industry and researchers.


