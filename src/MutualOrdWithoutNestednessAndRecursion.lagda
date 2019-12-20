-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

-- Remark 3.1: an equivalent definition of MutualOrd

The metatheory of inductive-recursive definitions (A, f), where the
recursive function f : A → A is an endofunction on the inductively
defined type A (e.g. (MutualOrd, fst) here) is in general not well
explored.  However, in this case fst is only used strictly positively
in MutualOrd and <, which means that its graph can be defined
inductive-inductively, and in turn used instead of the recursively
defined fst.  This reduces the inductive-inductive-recursive
construction to an inductive-inductive one, which is known to be
sound.

\begin{code}

{-# OPTIONS --cubical --safe #-}

module MutualOrdWithoutNestednessAndRecursion where

open import Preliminaries

import Agda.Builtin.Equality as P

\end{code}

■ Ordinal notations and their ordering

\begin{code}

infix 30 _<_ _>_ _>fst_ _≥fst_

data MutualOrd : Type₀
data _<_ : MutualOrd → MutualOrd → Type₀
data _≡fst_ : MutualOrd → MutualOrd → Type₀

_>_ _>fst_ _≥fst_ : MutualOrd → MutualOrd → Type₀

data MutualOrd where
 𝟎 : MutualOrd
 ω^_+_≡[_] : (a b : MutualOrd) → a ≡fst b → MutualOrd
 ω^_+_>[_] : (a b : MutualOrd) → a >fst b → MutualOrd

private
 variable
  a a' b b' c d : MutualOrd
  r : a ≡fst b
  s : c ≡fst d
  r' : a >fst b
  s' : c >fst d


data _<_ where
 <₁≡ : 𝟎 < ω^ a + b ≡[ r ]
 <₁> : 𝟎 < ω^ a + b >[ r' ]
 <₂≡≡ : a < c → ω^ a + b ≡[ r ] < ω^ c + d ≡[ s ]
 <₂≡> : a < c → ω^ a + b ≡[ r ] < ω^ c + d >[ s' ]
 <₂>≡ : a < c → ω^ a + b >[ r' ] < ω^ c + d ≡[ s ]
 <₂>> : a < c → ω^ a + b >[ r' ] < ω^ c + d >[ s' ]
 <₃≡≡ : a ≡ c → b < d → ω^ a + b ≡[ r ] < ω^ c + d ≡[ s ]
 <₃≡> : a ≡ c → b < d → ω^ a + b ≡[ r ] < ω^ c + d >[ s' ]
 <₃>≡ : a ≡ c → b < d → ω^ a + b >[ r' ] < ω^ c + d ≡[ s ]
 <₃>> : a ≡ c → b < d → ω^ a + b >[ r' ] < ω^ c + d >[ s' ]

data _≡fst_ where
  fst𝟎 : 𝟎 ≡fst 𝟎
  fst≡ : a ≡ a' → a ≡fst (ω^ a' + b ≡[ r ])
  fst> : a ≡ a' → a ≡fst (ω^ a' + b >[ r' ])
\end{code}


Note that the following definitions are abbreviations for convenience
only, since they make no use of recursion or pattern matching.

\begin{code}
a > b = b < a
a >fst b = Σ λ c → ((c ≡fst b) × a > c)
a ≥fst b = (a >fst b) ⊎ (a ≡fst b)
\end{code}


For convenience, we can define the old constructors as functions:

\begin{code}
ω^_+_[_] : (a b : MutualOrd) → a ≥fst b → MutualOrd
ω^ a + b [ inj₁ r ] = ω^ a + b >[ r ]
ω^ a + b [ inj₂ r ] = ω^ a + b ≡[ r ]

<₁ : ∀ {r} → 𝟎 < ω^ a + b [ r ]
<₁ {r = inj₁ r}  = <₁>
<₁ {r = inj₂ r'} = <₁≡

<₂ : ∀ {r s} → a < c → ω^ a + b [ r ] < ω^ c + d [ s ]
<₂ {r = inj₁ r}  {inj₁ s}  = <₂>>
<₂ {r = inj₁ r}  {inj₂ s'} = <₂>≡
<₂ {r = inj₂ r'} {inj₁ s'} = <₂≡>
<₂ {r = inj₂ r'} {inj₂ s'} = <₂≡≡

<₃ : ∀ {r s} → a ≡ c → b < d → ω^ a + b [ r ] < ω^ c + d [ s ]
<₃ {r = inj₁ r}  {inj₁ s}  = <₃>>
<₃ {r = inj₁ r}  {inj₂ s'} = <₃>≡
<₃ {r = inj₂ r'} {inj₁ s'} = <₃≡>
<₃ {r = inj₂ r'} {inj₂ s'} = <₃≡≡

fstω : ∀ {r} → a ≡fst (ω^ a + b [ r ])
fstω {r = inj₁ x} = fst> refl
fstω {r = inj₂ x} = fst≡ refl
\end{code}

We can now define fst as an ordinary function, after the definition of
𝒪, and show that the graph relation really represents the graph of
fst.

\begin{code}
fst : MutualOrd -> MutualOrd
fst 𝟎 = 𝟎
fst ω^ a + b ≡[ r ] = a
fst ω^ a + b >[ r' ] = a

sound-≡fst : a ≡fst b → a ≡ fst b
sound-≡fst fst𝟎 = refl
sound-≡fst (fst≡ p) = p
sound-≡fst (fst> p) = p

complete-≡fst : a ≡ fst b → a ≡fst b
complete-≡fst p with PropEqfromPath p
complete-≡fst {b = 𝟎} p | P.refl = fst𝟎
complete-≡fst {b = ω^ _ + _ ≡[ _ ]} p | P.refl = fst≡ p
complete-≡fst {b = ω^ _ + _ >[ _ ]} p | P.refl = fst> p

sound-complete-retract : ∀ p → complete-≡fst (sound-≡fst {a} {b} p) ≡ p
sound-complete-retract p with PropEqfromPath (sound-≡fst p)
sound-complete-retract fst𝟎 | P.refl = refl
sound-complete-retract (fst≡ x) | P.refl = refl
sound-complete-retract (fst> x) | P.refl = refl

sound-injective : ∀ p q → (sound-≡fst {a} {b} p) ≡ (sound-≡fst {a} {b} q) → p ≡ q
sound-injective p q eq = (sound-complete-retract p) ⁻¹ ∙ cong complete-≡fst eq ∙ sound-complete-retract q

sound->fst : a >fst b → a > fst b
sound->fst (b , x , p) with PropEqfromPath (sound-≡fst x)
... | P.refl = p

\end{code}

We can prove that MutualOrd defined simultaneously with fst is
isomorphic to MutualOrd defined simultaneously with the graph of
fst. Because of the simultaneous definition of MutualOrd and <, we
have to prove that the functions between the types preserve the
relation < at the same time.

\begin{code}
import MutualOrd as M

to : M.MutualOrd → MutualOrd
to-> : {a b : M.MutualOrd} -> a M.> b -> (to a) > (to b)
to-≥ : {a b : M.MutualOrd} -> a M.≥ M.fst b -> (to a) ≥fst (to b)

to M.𝟎 = 𝟎
to (M.ω^ a + b [ r ]) = ω^ (to a) + (to b) [ to-≥ {b = b} r ]

to-> M.<₁ = <₁
to-> (M.<₂ r) = <₂ (to-> r)
to-> (M.<₃ p r) = <₃ (cong to p) (to-> r)

to-≥ {b = M.𝟎} (inj₁ M.<₁) = inj₁ (_ , fst𝟎 , <₁)
to-≥ {b = M.ω^ b + c [ r ]} (inj₁ p) = inj₁ (_ , fstω , to-> p)
to-≥ {b = M.𝟎} (inj₂ r') with PropEqfromPath r'
... | P.refl = inj₂ fst𝟎
to-≥ {b = M.ω^ b + c [ r ]} (inj₂ p)  with PropEqfromPath p
... | P.refl = inj₂ fstω

from : MutualOrd → M.MutualOrd
from-> : a > b -> (from a) M.> (from b)
from-≥ : a ≥fst b -> (from a) M.≥ M.fst (from b)

from 𝟎 = M.𝟎
from (ω^ a + b ≡[ r ]) = M.ω^ (from a) + (from b) [ from-≥ {b = b} (inj₂ r) ]
from (ω^ a + b >[ r' ]) = M.ω^ (from a) + (from b) [ from-≥ {b = b} (inj₁ r') ]

from-> <₁≡ = M.<₁
from-> <₁> = M.<₁
from-> (<₂≡≡ r) = M.<₂ (from-> r)
from-> (<₂≡> r) = M.<₂ (from-> r)
from-> (<₂>≡ r) = M.<₂ (from-> r)
from-> (<₂>> r) = M.<₂ (from-> r)
from-> (<₃≡≡ p r) = M.<₃ (cong from p) (from-> r)
from-> (<₃≡> p r) = M.<₃ (cong from p) (from-> r)
from-> (<₃>≡ p r) = M.<₃ (cong from p) (from-> r)
from-> (<₃>> p r) = M.<₃ (cong from p) (from-> r)

from-≥ {b = 𝟎} (inj₁ (._ , fst𝟎 , p)) = inj₁ (from-> p)
from-≥ {a} {b = ω^ b + c ≡[ r ]} (inj₁ (b' , fst≡ q , p)) with PropEqfromPath q
... | P.refl = inj₁ (from-> p)
from-≥ {b = ω^ b + c >[ r ]} (inj₁ (b' , fst> q , p))  with PropEqfromPath q
...| P.refl = inj₁ (from-> p)
from-≥ {b = 𝟎} (inj₂ fst𝟎) = inj₂ refl
from-≥ {b = ω^ b + c ≡[ r ]} (inj₂ (fst≡ q)) = inj₂ (cong from q)
from-≥ {b = ω^ b + c >[ r ]} (inj₂ (fst> q)) = inj₂ (cong from q)
\end{code}

Finally, we want to check that we have an isomorphism. We first
establish that again _<_ is Prop-valued. The proof is the same as
before, and so not very interesting.

\begin{code}
rest : MutualOrd → MutualOrd
rest  𝟎               = 𝟎
rest (ω^ _ + b ≡[ _ ]) = b
rest (ω^ _ + b >[ _ ]) = b

caseMutualOrd : {A : Type ℓ} (x y z : A) → MutualOrd → A
caseMutualOrd x y z  𝟎               = x
caseMutualOrd x y z (ω^ _ + _ ≡[ _ ]) = y
caseMutualOrd x y z (ω^ _ + _ >[ _ ]) = z

𝟎≢ω : {r : a ≥fst b} → ¬ (𝟎 ≡ ω^ a + b [ r ])
𝟎≢ω {r = inj₁ r} e = subst (caseMutualOrd MutualOrd ⊥ ⊥) e 𝟎
𝟎≢ω {r = inj₂ r} e = subst (caseMutualOrd MutualOrd ⊥ ⊥) e 𝟎

ω≢𝟎 : {r : a ≥fst b} → ¬ (ω^ a + b [ r ] ≡ 𝟎)
ω≢𝟎 {r = inj₁ r} e = subst (caseMutualOrd ⊥ MutualOrd MutualOrd) e 𝟎
ω≢𝟎 {r = inj₂ r} e = subst (caseMutualOrd ⊥ MutualOrd MutualOrd) e 𝟎

ω≡≢ω> : {r : a ≡fst b}{r' : a' >fst b'} → ¬ (ω^ a + b ≡[ r ] ≡ ω^ a' + b' >[ r' ])
ω≡≢ω> e = subst (caseMutualOrd MutualOrd MutualOrd ⊥) e 𝟎

ω>≢ω≡ : {r : a ≡fst b}{r' : a' >fst b'} → ¬ (ω^ a' + b' >[ r' ] ≡ ω^ a + b ≡[ r ])
ω>≢ω≡ e = subst (caseMutualOrd MutualOrd ⊥ MutualOrd) e 𝟎

<-irrefl : ¬ a < a
<-irrefl (<₂≡≡ r) = <-irrefl r
<-irrefl (<₂>> r) = <-irrefl r
<-irrefl (<₃≡≡ x r) = <-irrefl r
<-irrefl (<₃>> x r) = <-irrefl r

<-irreflexive : a ≡ b → ¬ a < b
<-irreflexive {a} e = subst (λ x → ¬ a < x) e <-irrefl


<IsPropValued : isProp (a < b)
>fstIsPropValued : isProp (a >fst b)
≡fstIsPropValued : isProp (a ≡fst b)
≤IsPropValued : {a b : MutualOrd} → isProp (a ≥fst b)
MutualOrdIsDiscrete : Discrete MutualOrd
MutualOrdIsSet : isSet MutualOrd
MutualOrd⁼ : {r : a ≥fst b} {s : c ≥fst d} → a ≡ c → b ≡ d
           → ω^ a + b [ r ] ≡ ω^ c + d [ s ]

<IsPropValued <₁≡ <₁≡ = refl
<IsPropValued <₁> <₁> = refl
<IsPropValued (<₂≡≡ p) (<₂≡≡ q) = cong <₂≡≡ (<IsPropValued p q)
<IsPropValued (<₂≡> p) (<₂≡> q) = cong <₂≡> (<IsPropValued p q)
<IsPropValued (<₂>≡ p) (<₂>≡ q) = cong <₂>≡ (<IsPropValued p q)
<IsPropValued (<₂>> p) (<₂>> q) = cong <₂>> (<IsPropValued p q)
<IsPropValued (<₃≡≡ x p) (<₃≡≡ x' q) = cong₂ <₃≡≡ (MutualOrdIsSet x x') (<IsPropValued p q)
<IsPropValued (<₃≡> x p) (<₃≡> x' q) = cong₂ <₃≡> (MutualOrdIsSet x x') (<IsPropValued p q)
<IsPropValued (<₃>≡ x p) (<₃>≡ x' q) = cong₂ <₃>≡ (MutualOrdIsSet x x') (<IsPropValued p q)
<IsPropValued (<₃>> x p) (<₃>> x' q) = cong₂ <₃>> (MutualOrdIsSet x x') (<IsPropValued p q)
<IsPropValued (<₂≡≡ p) (<₃≡≡ x q) = ⊥-elim (<-irreflexive x p)
<IsPropValued (<₂≡> p) (<₃≡> x q) = ⊥-elim (<-irreflexive x p)
<IsPropValued (<₂>≡ p) (<₃>≡ x q) = ⊥-elim (<-irreflexive x p)
<IsPropValued (<₂>> p) (<₃>> x q) = ⊥-elim (<-irreflexive x p)
<IsPropValued (<₃≡≡ x p) (<₂≡≡ q) = ⊥-elim (<-irreflexive x q)
<IsPropValued (<₃>> x p) (<₂>> q) = ⊥-elim (<-irreflexive x q)
<IsPropValued (<₃>≡ x p) (<₂>≡ q) = ⊥-elim (<-irreflexive x q)
<IsPropValued (<₃≡> x p) (<₂≡> q) = ⊥-elim (<-irreflexive x q)


>fstIsPropValued (.𝟎 , fst𝟎 , p) (.𝟎 , fst𝟎 , p') = cong (λ z → (_ , _ , z)) (<IsPropValued p p')
>fstIsPropValued (b , fst≡ x , p) (b' , fst≡ x' , p')
  with PropEqfromPath x | PropEqfromPath x'
... | P.refl | P.refl = cong (λ z → (b' , z))
                             (cong₂ _,_ (cong fst≡ (MutualOrdIsSet x x'))
                                        (<IsPropValued p p'))
>fstIsPropValued (b , fst> x , p) (b' , fst> x' , p')
  with PropEqfromPath x | PropEqfromPath x'
... | P.refl | P.refl = cong (λ z → (b' , z))
                             (cong₂ _,_ (cong fst> (MutualOrdIsSet x x'))
                                        (<IsPropValued p p'))

≡fstIsPropValued p q = sound-injective p q (MutualOrdIsSet _ _)

≤IsPropValued (inj₁ p) (inj₁ q) = cong inj₁ (>fstIsPropValued p q)
≤IsPropValued (inj₁ p) (inj₂ q) = ⊥-elim (<-irreflexive ((sound-≡fst q) ⁻¹) (sound->fst p))
≤IsPropValued (inj₂ p) (inj₁ q) = ⊥-elim (<-irreflexive ((sound-≡fst p) ⁻¹) (sound->fst q))
≤IsPropValued (inj₂ p) (inj₂ q) = cong inj₂ (≡fstIsPropValued p q)

MutualOrdIsDiscrete 𝟎 𝟎 = yes refl
MutualOrdIsDiscrete (ω^ a + b ≡[ r ]) (ω^ a' + b' ≡[ r' ]) with MutualOrdIsDiscrete a a'
MutualOrdIsDiscrete ω^ a + b ≡[ r ] ω^ a' + b' ≡[ r' ] | yes a≡a' with MutualOrdIsDiscrete b b'
MutualOrdIsDiscrete ω^ a + b ≡[ r ] ω^ a' + b' ≡[ r' ] | yes a≡a' | yes b≡b' = yes (MutualOrd⁼ a≡a' b≡b')
MutualOrdIsDiscrete ω^ a + b ≡[ r ] ω^ a' + b' ≡[ r' ] | yes p | no b≠b' = no λ e → b≠b' (cong rest e)
MutualOrdIsDiscrete ω^ a + b ≡[ r ] ω^ a' + b' ≡[ r' ] | no a≠a' = no λ e → a≠a' (cong fst e)
MutualOrdIsDiscrete (ω^ a + b >[ r ]) (ω^ a' + b' >[ r' ]) with MutualOrdIsDiscrete a a'
MutualOrdIsDiscrete ω^ a + b >[ r ] ω^ a' + b' >[ r' ] | yes a≡a' with MutualOrdIsDiscrete b b'
MutualOrdIsDiscrete ω^ a + b >[ r ] ω^ a' + b' >[ r' ] | yes a≡a' | yes b≡b' = yes (MutualOrd⁼ a≡a' b≡b')
MutualOrdIsDiscrete ω^ a + b >[ r ] ω^ a' + b' >[ r' ] | yes p | no b≠b' = no λ e → b≠b' (cong rest e)
MutualOrdIsDiscrete ω^ a + b >[ r ] ω^ a' + b' >[ r' ] | no a≠a' = no λ e → a≠a' (cong fst e)
MutualOrdIsDiscrete (ω^ a + b ≡[ r ]) (ω^ a' + b' >[ r' ]) = no ω≡≢ω>
MutualOrdIsDiscrete (ω^ a + b >[ r ]) (ω^ a' + b' ≡[ r' ]) = no ω>≢ω≡
MutualOrdIsDiscrete 𝟎 (ω^ b + c ≡[ r ]) = no 𝟎≢ω
MutualOrdIsDiscrete 𝟎 (ω^ b + c >[ r ]) = no 𝟎≢ω
MutualOrdIsDiscrete (ω^ a + b ≡[ r ]) 𝟎 = no ω≢𝟎

MutualOrdIsDiscrete (ω^ a + b >[ r ]) 𝟎 = no ω≢𝟎

≡-normalise : a ≡ b → a ≡ b
≡-normalise {a} {b} a≡b with MutualOrdIsDiscrete a b
... | yes p = p
... | no ¬p = ⊥-elim (¬p a≡b)

≡-normalise-constant : (p q : a ≡ b) → ≡-normalise p ≡ ≡-normalise q
≡-normalise-constant {a} {b} p q with MutualOrdIsDiscrete a b
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)

≡-canonical : (p : a ≡ b)
            → (≡-normalise refl) ⁻¹ ∙ (≡-normalise p) ≡ p
≡-canonical = J (λ y p → (≡-normalise refl) ⁻¹ ∙ (≡-normalise p) ≡ p)
                (lCancel (≡-normalise refl))

MutualOrdIsSet p q =
  ((≡-canonical p) ⁻¹) ∙
  cong ((≡-normalise refl) ⁻¹ ∙_) (≡-normalise-constant p q) ∙
  ≡-canonical q

MutualOrd⁼ {a} {b} a≡c b≡d with PropEqfromPath a≡c | PropEqfromPath b≡d
... | P.refl | P.refl = cong (ω^ a + b [_]) (≤IsPropValued _ _)

\end{code}

Using this, it is easy to check that the roundtrips are identities:

\begin{code}

from-to : ∀ a → from (to a) ≡ a
from-to M.𝟎 = refl
from-to (M.ω^ a + b [ r ]) with to-≥ {b = b} r
from-to M.ω^ a + b [ r ] | inj₁ x = M.MutualOrd⁼ (from-to a) (from-to b)
from-to M.ω^ a + b [ r ] | inj₂ x = M.MutualOrd⁼ (from-to a) (from-to b)

to-from : ∀ a → to (from a) ≡ a
to-from 𝟎 = refl
to-from ω^ a + b ≡[ r ] = MutualOrd⁼ (to-from a) (to-from b)
to-from ω^ a + b >[ r ] = MutualOrd⁼ (to-from a) (to-from b)
\end{code}
