
      ---------------------------------------------------
        An equivalent inductive-inductive definition of
                      ordinal notations
      ---------------------------------------------------

            Fredrik Nordvall Forsberg, April 2019


The metatheory of inductive-recursive definitions (A, f), where the
recursive function f : A → A is an endofunction on the inductively
defined type A (e.g. (𝒪, fst) here) is in general not well explored.
However, in this case fst is only used strictly positively in 𝒪 and <,
which means that its graph can be defined inductive-inductively, and
in turn used instead of the recursively defined fst.  This reduces the
inductive-inductive-recursive construction to an inductive-inductive
one, which is known to be sound.

\begin{code}

module OrdinalNotationsWithoutRecursion where

open import Agda.Builtin.Equality
open import Data.Empty.Irrelevant
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong₂)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _∨_)
open import Data.Product

import OrdinalNotations as O

infix 30 _<_
infix 30 _≥fst_

\end{code}

We inductively define the type of ordinal notations 𝒪, the order
relation _<_ on 𝒪, and the relation _≡fst_ representing the graph of
the function fst simultaneously. This is thus an instance of an
inductive-inductive definition, since the latter relations are indexed
by the former type, and they all refer to each other.

\begin{code}

mutual

 data 𝒪 : Set where
  𝟎 : 𝒪
  ω^_+_[_] : (a b : 𝒪) → .(a ≥fst b) → 𝒪

 data _<_ : 𝒪 → 𝒪 → Set where
  <₁ : {a : 𝒪}
     → a ≢ 𝟎 → 𝟎 < a
  <₂ : {a b c d : 𝒪} .{r : a ≥fst c} .{s : b ≥fst d}
     → a < b → ω^ a + c [ r ] < ω^ b + d [ s ]
  <₃ : {a b c : 𝒪} .{r : a ≥fst b} .{s : a ≥fst c}
     → b < c → ω^ a + b [ r ] < ω^ a + c [ s ]

 -- The graph of fst
 data _≡fst_ : 𝒪 → 𝒪 → Set where
   -- fst 𝟎 = 𝟎
   fst𝟎         : 𝟎 ≡fst 𝟎
   -- fst (ω^ b + d [ s ]) = b
   fst[ω^b+[…]] : {b d : 𝒪} .{s : b ≥fst d}
                → b ≡fst (ω^ b + d [ s ])

 fst_<_ : 𝒪 → 𝒪 → Set
 fst a < b = Σ[ c ∈ 𝒪 ] ((c ≡fst a) × c < b)

 _≥fst_ : 𝒪 → 𝒪 → Set
 a ≥fst b = fst b < a ∨ a ≡fst b
\end{code}

Note that the last two definitions are abbreviations for convenience
only, since they make no use of recursion or pattern matching.

We can now define fst as an ordinary function, after the definition of
𝒪, and show that the graph relation really represents the graph of
fst.

\begin{code}

fst : 𝒪 → 𝒪
fst  𝟎               = 𝟎
fst (ω^ a + _ [ _ ]) = a

sound-≡fst : (a b : 𝒪) -> a ≡fst b -> a ≡ fst b
sound-≡fst .𝟎 𝟎                fst𝟎          = refl
sound-≡fst a .(ω^ a + _ [ _ ]) fst[ω^b+[…]] = refl

complete-≡fst : (a b : 𝒪) -> a ≡ fst b -> a ≡fst b
complete-≡fst .𝟎 𝟎                refl = fst𝟎
complete-≡fst .b (ω^ b + c [ r ]) refl = fst[ω^b+[…]]

\end{code}

Similarly, we can show that fst_<_ adequately represents the relation
λ a b → (fst a) < b:

\begin{code}

sound-fst< : (a b : 𝒪) -> fst_<_ a b -> (fst a) < b
sound-fst< .𝟎                b (.𝟎 , fst𝟎 , q)         = q
sound-fst< .(ω^ d + _ [ _ ]) b (d , fst[ω^b+[…]] , q) = q

complete-fst< : (a b : 𝒪) -> (fst a) < b -> fst_<_ a b
complete-fst< 𝟎                b p = 𝟎 , fst𝟎 , p
complete-fst< (ω^ a + c [ r ]) b p = a , fst[ω^b+[…]] , p

\end{code}

We can prove that 𝒪 defined simultaneously with fst is isomorphic to 𝒪
defined simultaneously with the graph of fst. Because of the
simultaneous definition of 𝒪 and <, we have to prove that the
functions between the types preserve the relation < at the same time.

\begin{code}

mutual

  to : O.𝒪 -> 𝒪
  to O.𝟎                = 𝟎
  to (O.ω^ a + b [ r ]) = ω^ (to a) + (to b) [ to-≥ r ]

  to-< : {a b : O.𝒪} -> a O.< b -> (to a) < (to b)
  to-< {b = O.𝟎}              (O.<₁ p) = ⊥-elim (p refl)
  to-< {b = O.ω^ a + c [ r ]} (O.<₁ p) = <₁ (λ ())
  to-<                        (O.<₂ p) = <₂ (to-< p)
  to-<                        (O.<₃ p) = <₃ (to-< p)

  to-≥ : {a b : O.𝒪} -> a O.≥ O.fst b -> (to a) ≥fst (to b)
  to-≥ {b = O.𝟎}               (inj₁ p)    = inj₁ (_ , fst𝟎 , to-< p)
  to-≥ {b = O.ω^ b + b₁ [ x ]} (inj₁ p)    = inj₁ (_ , fst[ω^b+[…]] , to-< p)
  to-≥ {b = O.𝟎}               (inj₂ refl) = inj₂ fst𝟎
  to-≥ {b = O.ω^ b + c [ r ]}  (inj₂ refl) = inj₂ (fst[ω^b+[…]] {s = to-≥ r})

mutual

  from : 𝒪 -> O.𝒪
  from 𝟎                = O.𝟎
  from (ω^ a + b [ r ]) = O.ω^ (from a) + (from b) [ from-≥ r ]

  from-< : {a b : 𝒪} -> a < b -> (from a) O.< (from b)
  from-< {b = 𝟎}              (<₁ p) = ⊥-elim (p refl)
  from-< {b = ω^ b + c [ r ]} (<₁ p) = O.<₁ (λ ())
  from-<                      (<₂ p) = O.<₂ (from-< p)
  from-<                      (<₃ p) = O.<₃ (from-< p)

  from-≥ : {a b : 𝒪} -> a ≥fst b -> (from a) O.≥ O.fst (from b)
  from-≥ {b = 𝟎}              (inj₁ (𝟎 , fst𝟎 , p))           = inj₁ (from-< p)
  from-≥ {b = ω^ b + c [ r ]} (inj₁ (.b , fst[ω^b+[…]] , p)) = inj₁ (from-< p)
  from-≥                      (inj₂ fst𝟎)                     = inj₂ refl
  from-≥ (inj₂ fst[ω^b+[…]])                                 = inj₂ refl

\end{code}

An isomorphism is especially easy to establish, because of the
irrelevant equations.

\begin{code}

ω^_+_[_]-equal : ∀ {a b a' b'} .{r r'} → (a ≡ a') → (b ≡ b') →
                  (𝒪.ω^ a + b [ r ]) ≡ (ω^ a' + b' [ r' ])
ω^_+_[_]-equal refl refl = refl

Oω^_+_[_]-equal : ∀ {a b a' b'} .{r r'} → (a ≡ a') → (b ≡ b') →
                 (O.𝒪.ω^ a + b [ r ]) ≡ (O.ω^ a' + b' [ r' ])
Oω^_+_[_]-equal refl refl = refl

to-from : (a : 𝒪) -> to (from a) ≡ a
to-from 𝟎                = refl
to-from (ω^ a + b [ r ]) = ω^_+_[_]-equal (to-from a) (to-from b)

from-to : (b : O.𝒪) -> from (to b) ≡ b
from-to O.𝟎                = refl
from-to (O.ω^ a + b [ r ]) = Oω^_+_[_]-equal (from-to a) (from-to b)

\end{code}
