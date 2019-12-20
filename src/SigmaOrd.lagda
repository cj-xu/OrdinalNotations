-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

§3.1  The subset approach

Following the traditional subset approach, we construct a notation
system of ordinals below ε₀ as a Σ-type.

\begin{code}

{-# OPTIONS --cubical --safe #-}

module SigmaOrd where

open import Preliminaries

\end{code}

■ Binary trees (ordinal terms)

\begin{code}

infix 40 ω^_+_

data Tree : Type₀ where
 𝟎 : Tree
 ω^_+_ : Tree → Tree → Tree

private
 variable a b c d : Tree

caseTree : {A : Type ℓ} (x y : A) → Tree → A
caseTree x y  𝟎         = x
caseTree x y (ω^ _ + _) = y

𝟎≢ω^+ : ¬ (𝟎 ≡ ω^ a + b)
𝟎≢ω^+ e = subst (caseTree Tree ⊥) e 𝟎

ω^+≢𝟎 : ¬ (ω^ a + b ≡ 𝟎)
ω^+≢𝟎 e = subst (caseTree ⊥ Tree) e 𝟎

fst : Tree → Tree
fst 𝟎 = 𝟎
fst (ω^ a + _) = a

rest : Tree → Tree
rest  𝟎         = 𝟎
rest (ω^ _ + b) = b

TreeIsDiscrete : Discrete Tree
TreeIsDiscrete  𝟎          𝟎         = yes refl
TreeIsDiscrete  𝟎         (ω^ _ + _) = no 𝟎≢ω^+
TreeIsDiscrete (ω^ _ + _)  𝟎         = no ω^+≢𝟎
TreeIsDiscrete (ω^ a + c) (ω^ b + d) with TreeIsDiscrete a b
TreeIsDiscrete (ω^ a + c) (ω^ b + d) | yes a=b with TreeIsDiscrete c d
TreeIsDiscrete (ω^ a + c) (ω^ b + d) | yes a=b | yes c=d = yes (cong₂ ω^_+_ a=b c=d)
TreeIsDiscrete (ω^ a + c) (ω^ b + d) | yes a=b | no  c≠d = no (λ e → c≠d (cong rest e))
TreeIsDiscrete (ω^ a + c) (ω^ b + d) | no  a≠b = no (λ e → a≠b (cong fst e))

TreeIsSet : isSet Tree
TreeIsSet = Discrete→isSet TreeIsDiscrete _ _

\end{code}

■ Ordering on trees

\begin{code}

infix  30 _<_ _≤_ _>_ _≥_

data _<_ : Tree → Tree → Type₀ where
 <₁ : 𝟎 < ω^ a + b
 <₂ : a < c → ω^ a + b < ω^ c + d
 <₃ : a ≡ c → b < d → ω^ a + b < ω^ c + d

_>_ _≥_ _≤_ : Tree → Tree → Type₀
a > b = b < a
a ≥ b = a > b ⊎ a ≡ b
a ≤ b = b ≥ a

≥𝟎 : a ≥ 𝟎
≥𝟎 {𝟎}        = inj₂ refl
≥𝟎 {ω^ a + b} = inj₁ <₁

<-irrefl : ¬ a < a
<-irrefl (<₂ r)   = <-irrefl r
<-irrefl (<₃ _ r) = <-irrefl r

<-irreflexive : a ≡ b → ¬ a < b
<-irreflexive {a} p = subst (λ x → ¬ a < x) p <-irrefl

<IsPropValued : isProp (a < b)
<IsPropValued  <₁       <₁      = refl
<IsPropValued (<₂ r)   (<₂ s)   = cong <₂ (<IsPropValued r s)
<IsPropValued (<₂ r)   (<₃ q s) = ⊥-elim (<-irreflexive q r)
<IsPropValued (<₃ p r) (<₂ s)   = ⊥-elim (<-irreflexive p s)
<IsPropValued (<₃ p r) (<₃ q s) = cong₂ <₃ (TreeIsSet p q) (<IsPropValued r s)

≤IsPropValued : isProp (a ≤ b)
≤IsPropValued (inj₁ r) (inj₁ s) = cong inj₁ (<IsPropValued r s)
≤IsPropValued (inj₁ r) (inj₂ q) = ⊥-elim (<-irreflexive (q ⁻¹) r)
≤IsPropValued (inj₂ p) (inj₁ s) = ⊥-elim (<-irreflexive (p ⁻¹) s)
≤IsPropValued (inj₂ p) (inj₂ q) = cong inj₂ (TreeIsSet p q)

\end{code}

■ Cantor normal form

\begin{code}

data isCNF : Tree → Type₀ where
 𝟎IsCNF : isCNF 𝟎
 ω^+IsCNF : isCNF a → isCNF b → a ≥ fst b
          → isCNF (ω^ a + b)

isCNFIsPropValued : isProp (isCNF a)
isCNFIsPropValued  𝟎IsCNF              𝟎IsCNF             = refl
isCNFIsPropValued (ω^+IsCNF pa pb ra) (ω^+IsCNF qa qb rb) =
  λ i → ω^+IsCNF (isCNFIsPropValued pa qa i) (isCNFIsPropValued pb qb i) (≤IsPropValued ra rb i)

\end{code}

■ Subset of trees in Cantor normal form

\begin{code}

SigmaOrd : Type₀
SigmaOrd = Σ \(a : Tree) → isCNF a

SigmaOrd⁼ : {x y : SigmaOrd} → pr₁ x ≡ pr₁ y → x ≡ y
SigmaOrd⁼ {a , p} e = subst P e pa
 where
  P : (b : Tree) → Type₀
  P b = {q : isCNF b} → (a , p) ≡ (b , q)
  pa : P a
  pa {q} i = a , isCNFIsPropValued p q i

\end{code}
