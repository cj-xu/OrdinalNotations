
        --------------------------------------------------
          Ordinal notations via simultaneous definitions
        --------------------------------------------------

            Fredrik Nordvall Forsberg and Chuangjie Xu


We define a notation system for the ordinals below ε₀ simultaneously
with its ordering.  Our simultaneous definitions generate only the
ordinal terms in Cantor normal form which are in one-to-one
correspondence with the ordinals below ε₀.  We implement the ordinal
notation system as inductive-inductive-recursive definitions in Agda.

The source files are available at

    https://github.com/cj-xu/OrdinalNotations



■ An inductive-inductive-recursive definition of ordinal notations

Our ordinal notations are nested weakly decreasing lists.  When
inserting a new element x in front of an already constructed list xs,
we need to ensure that x is greater than or equal to the head of xs.
Therefore, we simultaneously define an inductive type 𝒪 of ordinal
notations, an inductive family of types a < b indexed by a,b : 𝒪, and
a head function fst: 𝒪 → 𝒪.

\begin{code}

import OrdinalNotations

\end{code}

■ Ordinal arithmetic

We define ordinal arithmetic operations for our ordinal notations
including addition, subtraction, multiplication and exponentiation.

\begin{code}

import OrdinalArithmetic

\end{code}

■ An equivalent inductive-inductive definition of ordinal notations

The head function fst : 𝒪 → 𝒪 is only used strictly positively in 𝒪
and <, which means that its graph can be defined inductive-inductively
and in turn used instead of the recursively defined fst.  This reduces
the above inductive-inductive-recursive construction to an
inductive-inductive one.

\begin{code}

import OrdinalNotationsWithoutRecursion

\end{code}
