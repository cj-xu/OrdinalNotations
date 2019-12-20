-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

§3.2  The mutual approach

We use Agda’s support for mutual definitions to directly generate
trees in Cantor normal form only, by simultaneously defining ordinal
terms and an ordering on them.

\begin{code}

{-# OPTIONS --cubical --safe #-}

module MutualOrd where

open import Preliminaries

\end{code}

■ Ordinal notations and their ordering

\begin{code}

infix 30 _<_ _≤_ _>_ _≥_

data MutualOrd : Type₀
data _<_ : MutualOrd → MutualOrd → Type₀
fst : MutualOrd → MutualOrd

_>_ _≥_ _≤_ : MutualOrd → MutualOrd → Type₀
a > b = b < a
a ≥ b = a > b ⊎ a ≡ b
a ≤ b = b ≥ a

data MutualOrd where
 𝟎 : MutualOrd
 ω^_+_[_] : (a b : MutualOrd) → a ≥ fst b → MutualOrd

private
 variable
  a b c d : MutualOrd
  r : a ≥ fst b
  s : c ≥ fst d

data _<_ where
 <₁ : 𝟎 < ω^ a + b [ r ]
 <₂ : a < c → ω^ a + b [ r ] < ω^ c + d [ s ]
 <₃ : a ≡ c → b < d → ω^ a + b [ r ] < ω^ c + d [ s ]

fst  𝟎               = 𝟎
fst (ω^ a + _ [ _ ]) = a

rest : MutualOrd → MutualOrd
rest  𝟎               = 𝟎
rest (ω^ _ + b [ _ ]) = b

caseMutualOrd : {A : Type ℓ} (x y : A) → MutualOrd → A
caseMutualOrd x y  𝟎               = x
caseMutualOrd x y (ω^ _ + _ [ _ ]) = y

𝟎≢ω : {r : a ≥ fst b} → ¬ (𝟎 ≡ ω^ a + b [ r ])
𝟎≢ω e = subst (caseMutualOrd MutualOrd ⊥) e 𝟎

ω≢𝟎 : {r : a ≥ fst b} → ¬ (ω^ a + b [ r ] ≡ 𝟎)
ω≢𝟎 e = subst (caseMutualOrd ⊥ MutualOrd) e 𝟎

<-irrefl : ¬ a < a
<-irrefl (<₂ r)     = <-irrefl r
<-irrefl (<₃ a=a r) = <-irrefl r

<-irreflexive : a ≡ b → ¬ a < b
<-irreflexive {a} e = subst (λ x → ¬ a < x) e <-irrefl

{----------------------------------------------------------------}
{-------- The following facts are proved simultaneously ---------}

<IsPropValued : isProp (a < b)
≤IsPropValued : {a b : MutualOrd} → isProp (a ≤ b)
MutualOrdIsDiscrete : Discrete MutualOrd
MutualOrdIsSet : isSet MutualOrd
MutualOrd⁼ : {r : a ≥ fst b} {s : c ≥ fst d} → a ≡ c → b ≡ d
           → ω^ a + b [ r ] ≡ ω^ c + d [ s ]

<IsPropValued  <₁       <₁       = refl
<IsPropValued (<₂ p)   (<₂ q)    = cong <₂ (<IsPropValued p q)
<IsPropValued (<₂ p)   (<₃ e _)  = ⊥-elim (<-irreflexive e p)
<IsPropValued (<₃ e _) (<₂ q)    = ⊥-elim (<-irreflexive e q)
<IsPropValued (<₃ e p) (<₃ e' q) = cong₂ <₃ (MutualOrdIsSet e e') (<IsPropValued p q)

≤IsPropValued (inj₁ p) (inj₁ q) = cong inj₁ (<IsPropValued p q)
≤IsPropValued (inj₁ p) (inj₂ e) = ⊥-elim (<-irreflexive (e ⁻¹) p)
≤IsPropValued (inj₂ e) (inj₁ q) = ⊥-elim (<-irreflexive (e ⁻¹) q)
≤IsPropValued (inj₂ p) (inj₂ q) = cong inj₂ (MutualOrdIsSet p q)

MutualOrdIsDiscrete  𝟎                𝟎               = yes refl
MutualOrdIsDiscrete  𝟎               (ω^ b + d [ s ]) = no 𝟎≢ω
MutualOrdIsDiscrete (ω^ a + b [ r ])  𝟎               = no ω≢𝟎
MutualOrdIsDiscrete (ω^ a + b [ r ]) (ω^ c + d [ s ]) with MutualOrdIsDiscrete a c
MutualOrdIsDiscrete (ω^ a + b [ r ]) (ω^ c + d [ s ]) | yes a≡c with MutualOrdIsDiscrete b d
MutualOrdIsDiscrete (ω^ a + b [ r ]) (ω^ c + d [ s ]) | yes a≡c | yes b≡d = yes (MutualOrd⁼ a≡c b≡d)
MutualOrdIsDiscrete (ω^ a + b [ r ]) (ω^ c + d [ s ]) | yes a≡c | no  b≢d = no (λ e → b≢d (cong rest e))
MutualOrdIsDiscrete (ω^ a + b [ r ]) (ω^ c + d [ s ]) | no  a≢c = no (λ e → a≢c (cong fst e))

{-- Inlining the proof of "Discrete→isSet MutualOrdIsDiscrete" --}

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
{--  MutualOrdIsSet = Discrete→isSet MutualOrdIsDiscrete _ _   --}

{--------------------- End of the inlining ----------------------}

import Agda.Builtin.Equality as P

MutualOrd⁼ {a} {b} a≡c b≡d with PropEqfromPath a≡c | PropEqfromPath b≡d
... | P.refl | P.refl = cong (ω^ a + b [_]) (≤IsPropValued _ _)

{---------------- End of the simultaneous proofs ----------------}
{----------------------------------------------------------------}

\end{code}

Agda reports a termination error if we prove MutualOrdIsSet directly
using Discrete→isSet from the cubical library.  So we have to inline
the proof of "Discrete→isSet MutualOrdIsDiscrete".

Agda reports another termination error when we prove MutualOrd⁼ using
the cubical subst function, e.g.

----------------- Begin of code -----------------

MutualOrd⁼ {a} a≡c = subst P a≡c pa
 where
  P : MutualOrd → Type₀
  P x = ∀ {b d r s} → b ≡ d → ω^ a + b [ r ] ≡ ω^ x + d [ s ]
  pa : P a
  pa {b} b≡d = subst Q b≡d qb
   where
    Q : MutualOrd → Type₀
    Q y = ∀ {r s} → ω^ a + b [ r ] ≡ ω^ a + y [ s ]
    qb : Q b
    qb = cong (ω^ a + b [_]) (≤IsPropValued _ _)

------------------ End of code ------------------

We instead convert paths to Agda's propositional equality which we can
pattern match on directly.

\begin{code}

<-tri : (a b : MutualOrd) → a < b ⊎ a ≥ b
<-tri  𝟎                𝟎               = inj₂ (inj₂ refl)
<-tri  𝟎               (ω^ b + d [ _ ]) = inj₁ <₁
<-tri (ω^ a + c [ _ ])  𝟎               = inj₂ (inj₁ <₁)
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) with <-tri a b
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₁       a<b  = inj₁ (<₂ a<b)
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₁ a>b) = inj₂ (inj₁ (<₂ a>b))
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₂ a=b) with <-tri c d
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₂ a=b) | inj₁       c<d  = inj₁ (<₃ a=b c<d)
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₂ a=b) | inj₂ (inj₁ c>d) = inj₂ (inj₁ (<₃ (a=b ⁻¹) c>d))
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₂ a=b) | inj₂ (inj₂ c=d) = inj₂ (inj₂ (MutualOrd⁼ a=b c=d))

<-trans : a < b → b < c → a < c
<-trans  <₁      (<₂ _)   = <₁
<-trans  <₁      (<₃ _ _) = <₁
<-trans (<₂ r)   (<₂ s)   = <₂ (<-trans r s)
<-trans (<₂ r)   (<₃ p _) = <₂ (subst (λ x → _ < x) p r)
<-trans (<₃ p _) (<₂ s)   = <₂ (subst (λ x → x < _) (p ⁻¹) s)
<-trans (<₃ p r) (<₃ q s) = <₃ (p ∙ q) (<-trans r s)

≤-trans : a ≤ b → b ≤ c → a ≤ c
≤-trans (inj₁ a<b) (inj₁ b<c) = inj₁ (<-trans a<b b<c)
≤-trans (inj₁ a<b) (inj₂ c=b) = inj₁ (subst (λ x → _ < x) (c=b ⁻¹) a<b)
≤-trans (inj₂ b=a) (inj₁ b<c) = inj₁ (subst (λ x → x < _) b=a b<c)
≤-trans (inj₂ b=a) (inj₂ c=b) = inj₂ (c=b ∙ b=a)

<≤-trans : a < b → b ≤ c → a < c
<≤-trans a<b (inj₁ b<c) = <-trans a<b b<c
<≤-trans a<b (inj₂ c≡b) = subst (_ <_) (c≡b ⁻¹) a<b

Lm[≥→¬<] : a ≥ b → ¬ a < b
Lm[≥→¬<] (inj₁ b<a) a<b = <-irrefl (<-trans a<b b<a)
Lm[≥→¬<] (inj₂ a=b)     = <-irreflexive a=b


Lm[<→¬≥] : a < b → ¬ a ≥ b
Lm[<→¬≥] a<b (inj₁ a>b) = <-irrefl (<-trans a<b a>b)
Lm[<→¬≥] a<b (inj₂ a=b) = <-irreflexive a=b a<b

Lm[¬<→≥] : ¬ a < b → a ≥ b
Lm[¬<→≥] f with <-tri _ _
Lm[¬<→≥] f | inj₁       a<b  = ⊥-elim (f a<b)
Lm[¬<→≥] f | inj₂ (inj₁ a>b) = inj₁ a>b
Lm[¬<→≥] f | inj₂ (inj₂ a=b) = inj₂ a=b

<-dec : (a b : MutualOrd) → a < b ⊎ ¬ a < b
<-dec a b with <-tri a b
<-dec a b | inj₁ a<b = inj₁ a<b
<-dec a b | inj₂ a≥b = inj₂ (Lm[≥→¬<] a≥b)

<-≡ : {a b c : MutualOrd} → a < b → b ≡ c → a < c
<-≡ {a} e r = subst (a <_) r e

≤≥→≡ : a ≤ b → a ≥ b → a ≡ b
≤≥→≡ a≤b (inj₁ a>b) = ⊥-elim (Lm[<→¬≥] a>b a≤b)
≤≥→≡ a≤b (inj₂ a=b) = a=b

≮𝟎 : ¬ a < 𝟎
≮𝟎 ()

≥𝟎 : a ≥ 𝟎
≥𝟎 {𝟎}              = inj₂ refl
≥𝟎 {ω^ a + b [ _ ]} = inj₁ <₁

fst< : (a b : MutualOrd) (r : a ≥ fst b)
     → a < ω^ a + b [ r ]
fst<  𝟎               b r = <₁
fst< (ω^ a + c [ s ]) b r = <₂ (fst< a c s)

rest< : (a b : MutualOrd) (r : a ≥ fst b)
      → b < ω^ a + b [ r ]
rest< a  𝟎                _       = <₁
rest< a (ω^ b + c [ s ]) (inj₁ r) = <₂ r
rest< a (ω^ b + c [ s ]) (inj₂ e) = <₃ (e ⁻¹) (rest< b c s)

\end{code}

■ Some simple examples of ordinal notations

\begin{code}

ω^⟨_⟩ : MutualOrd → MutualOrd
ω^⟨ a ⟩ = ω^ a + 𝟎 [ ≥𝟎 ]

𝟏 ω : MutualOrd
𝟏 = ω^⟨ 𝟎 ⟩
ω = ω^⟨ 𝟏 ⟩

\end{code}
