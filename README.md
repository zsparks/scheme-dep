scheme-dep
==========

A scheme port of the Haskell code from "A Tutorial Implementation of a Dependently Typed Lambda Calculus"

All of this code (except for pmatch.scm) is a direct port of the implementation
of the Haskell code from "A Tutorial Implementation of a Dependently Typed
Lambda Calculus". The scheme code is original, but the ideas are not, and it is
as close to the original implementation as possible, mostly for ease of writing.

The original paper's homepage, with links to the paper & associated code
(neither of which I am affiliated with), is http://www.andres-loeh.de/LambdaPi/

indep.scm: the original, non-dependently-typed language

dep.scm: the base dependently-typed language

rich-dep.scm: dep.scm augmented with natural numbers & vectors, and an
implementation of plus & append. Only this file is actively maintained.
