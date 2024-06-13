
Preliminaries
=============

Please ensure that all of us follow these instructions, so we end up
with a document that is consistent and as easy to read as possible.

We aim to write this document using American English.


Protocol notation
-----------------

We will use spthy description for all protocols. In the introduction,
we can additionally(!), give mathematical notation for the first few
examples. Also ensure all protocols are available as executable spthy
files, and are stored in the sub-directory `code` of the repository for easy
distribution. The best way to ensure everything fits together is to
include the spthy files as follows.

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


