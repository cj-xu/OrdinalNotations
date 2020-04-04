-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

       Fredrik Nordvall Forsberg  and  Chuangjie Xu

We present three ordinal notation systems representing ordinals below
ε₀ in type theory, using recent type-theoretical innovations such as
mutual inductive-inductive definitions and higher inductive types.  As
case studies, we show how basic ordinal arithmetic can be developed
for these systems, and how they admit a transfinite induction
principle.  We prove that all three notation systems are equivalent,
so that we can transport results between them using the univalence
principle.

All the files are tested with

• Agda development version 2.6.2
  (commit: 292237b2da99a57cb2bef78ab38d5d45f9fb316c)

• Cubical Agda library
  (commit: 233263c7e13bc987382f92c47922820fdcffdb81)

\begin{code}

{-# OPTIONS --cubical --safe #-}

module index where

-----------------------
-- Table of contents --
-----------------------

-- §2 Cubical Agda
import Preliminaries

-- §3 Notation systems for ordinals below ε₀

-- §3.1 The subset approach
import SigmaOrd

-- §3.2 The mutual approach
import MutualOrd

-- MutualOrd can also be defined without nested and
-- inductive-recursive definitions
import MutualOrdWithoutNestednessAndRecursion

-- §3.3 The higher inductive approach
import HITOrd

-- §3.4 Equivalences between the three approaches
import Equivalences

-- §4 Ordinal arithmetic
import Arithmetic

-- §5 Transfinite induction
import TransfiniteInduction

\end{code}
