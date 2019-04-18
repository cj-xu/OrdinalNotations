
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
open import Data.Product -- using (Σ; Σ-syntax; _×_)

open import OrdinalNotations

infix 30 _<'_
infix 30 _≥'fst_

mutual

 data 𝒪' : Set where
  𝟎 : 𝒪'
  ω^_+_[_] : (a b : 𝒪') → .(a ≥'fst b) → 𝒪'

 data _<'_ : 𝒪' → 𝒪' → Set where
  <₁ : {a : 𝒪'}
     → a ≢ 𝟎 → 𝟎 <' a
  <₂ : {a b c d : 𝒪'} .{r : a ≥'fst c} .{s : b ≥'fst d}
     → a <' b → ω^ a + c [ r ] <' ω^ b + d [ s ]
  <₃ : {a b c : 𝒪'} .{r : a ≥'fst b} .{s : a ≥'fst c}
     → b <' c → ω^ a + b [ r ] <' ω^ a + c [ s ]

 data _≡fst_ : 𝒪' → 𝒪' → Set where
   𝟎≡𝟎 : 𝟎 ≡fst 𝟎
   b≡fst[ω^b+[…]] : {b d : 𝒪'} .{s : b ≥'fst d} -> b ≡fst (ω^ b + d [ s ])

 _fst<'_ : 𝒪' → 𝒪' → Set
 a fst<' b = Σ[ c ∈ 𝒪' ] ((c ≡fst a) × c <' b)

 _≥'fst_ : 𝒪' → 𝒪' → Set
 a ≥'fst b = b fst<' a ∨ a ≡fst b

fst' : 𝒪' → 𝒪'
fst'  𝟎               = 𝟎
fst' (ω^ a + _ [ _ ]) = a

sound-≡fst : (a b : 𝒪') -> a ≡fst b -> a ≡ fst' b
sound-≡fst .𝟎 𝟎                𝟎≡𝟎            = refl
sound-≡fst a .(ω^ a + _ [ _ ]) b≡fst[ω^b+[…]] = refl

complete-≡fst : (a b : 𝒪') -> a ≡ fst' b -> a ≡fst b
complete-≡fst .𝟎 𝟎                refl = 𝟎≡𝟎
complete-≡fst .b (ω^ b + c [ r ]) refl = b≡fst[ω^b+[…]]

sound-fst<' : (a b : 𝒪') -> a fst<' b -> fst' a <' b
sound-fst<' .𝟎                b (.𝟎 , 𝟎≡𝟎 , q)            = q
sound-fst<' .(ω^ d + _ [ _ ]) b (d , b≡fst[ω^b+[…]] , q) = q

complete-fst<' : (a b : 𝒪') -> fst' a <' b -> a fst<' b
complete-fst<' 𝟎                b p = 𝟎 , 𝟎≡𝟎 , p
complete-fst<' (ω^ a + c [ r ]) b p = a , b≡fst[ω^b+[…]] , p

\end{code}

We can prove that 𝒪 defined simultaneously with fst is isomorphic to
𝒪' defined simultaneously with the graph of fst.

\begin{code}

mutual

  to : 𝒪 -> 𝒪'
  to 𝟎                = 𝟎
  to (ω^ a + b [ r ]) = ω^ (to a) + (to b) [ to-≥ r ]

  to-< : {a b : 𝒪} -> a < b -> (to a) <' (to b)
  to-< {b = 𝟎}              (<₁ p) = ⊥-elim (p refl)
  to-< {b = ω^ a + c [ r ]} (<₁ p) = <₁ (λ ())
  to-<                      (<₂ p) = <₂ (to-< p)
  to-<                      (<₃ p) = <₃ (to-< p)

  to-≥ : {a b : 𝒪} -> a ≥ fst b -> (to a) ≥'fst (to b)
  to-≥ {b = 𝟎}              (inj₁ p) = inj₁ (_ , 𝟎≡𝟎 , to-< p)
  to-≥ {b = ω^ b + c [ r ]} (inj₁ p) = inj₁ (_ , b≡fst[ω^b+[…]] , to-< p)
  to-≥ {b = 𝟎}              (inj₂ refl) = inj₂ 𝟎≡𝟎
  to-≥ {b = ω^ b + c [ r ]} (inj₂ refl) = inj₂ b≡fst[ω^b+[…]]

mutual

  from : 𝒪' -> 𝒪
  from 𝟎                = 𝟎
  from (ω^ a + b [ r ]) = ω^ (from a) + (from b) [ from-≥ r ]

  from-< : {a b : 𝒪'} -> a <' b -> (from a) < (from b)
  from-< {b = 𝟎}              (<₁ p) = ⊥-elim (p refl)
  from-< {b = ω^ b + c [ r ]} (<₁ p) = <₁ (λ ())
  from-<                      (<₂ p) = <₂ (from-< p)
  from-<                      (<₃ p) = <₃ (from-< p)

  from-≥ : {a b : 𝒪'} -> a ≥'fst b -> (from a) ≥ fst (from b)
  from-≥ {b = 𝟎}              (inj₁ (𝟎 , 𝟎≡𝟎 , p))             = inj₁ (from-< p)
  from-≥ {b = ω^ b + c [ r ]} (inj₁ (.b , b≡fst[ω^b+[…]] , p)) = inj₁ (from-< p)
  from-≥                      (inj₂ 𝟎≡𝟎)                       = inj₂ refl
  from-≥ (inj₂ b≡fst[ω^b+[…]])                                 = inj₂ refl

-- An isomorphism is especially easy to establish, because of the
-- irrelevant equations

ω'^_+_[_]-equal : ∀ {a b a' b'} .{r r'} → (a ≡ a') → (b ≡ b') →
                  (𝒪'.ω^ a + b [ r ]) ≡ (ω^ a' + b' [ r' ])
ω'^_+_[_]-equal refl refl = refl

ω^_+_[_]-equal : ∀ {a b a' b'} .{r r'} → (a ≡ a') → (b ≡ b') →
                 (𝒪.ω^ a + b [ r ]) ≡ (ω^ a' + b' [ r' ])
ω^_+_[_]-equal refl refl = refl


to-from : (a : 𝒪') -> to (from a) ≡ a
to-from 𝟎                = refl
to-from (ω^ a + b [ r ]) = ω'^_+_[_]-equal (to-from a) (to-from b)

from-to : (b : 𝒪) -> from (to b) ≡ b
from-to 𝟎                = refl
from-to (ω^ a + b [ r ]) = ω^_+_[_]-equal (from-to a) (from-to b)

\end{code}
