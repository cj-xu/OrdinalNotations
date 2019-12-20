-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

§5  Transfinite induction

We prove transfinite induction for MutualOrd, and then transport it to
transfinite induction for HITOrd.  Then we consider a simple
application of transfinite induction - to prove that all strictly
descending sequences of ordinals below ε₀ are finite.

\begin{code}

{-# OPTIONS --cubical --safe #-}

module TransfiniteInduction where

open import Preliminaries
open import MutualOrd as M
open import HITOrd as H
open import Equivalences
open import Arithmetic

\end{code}

§5.1  The transported ordering on HITOrd

■ Ordering on HITOrd

\begin{code}

_<ᴴ_ : HITOrd → HITOrd → Type₀
_<ᴴ_ = transport (λ i → M≡H i → M≡H i → Type₀) _<_

<Path : PathP (λ i → M≡H i → M≡H i → Type₀) _<_ _<ᴴ_
<Path i = transp (λ j → M≡H (i ∧ j) → M≡H (i ∧ j) → Type₀) (~ i) _<_

\end{code}

■ Decidability of _<ᴴ_

\begin{code}

DEC : (A : Type ℓ) → (A → A → Type ℓ') → Type (ℓ ⊔ ℓ')
DEC A _<_ = (x y : A) → x < y ⊎ ¬ x < y

<ᴴ-dec : DEC HITOrd _<ᴴ_
<ᴴ-dec = transport (λ i → DEC (M≡H i) (<Path i)) <-dec

\end{code}

■ The transported property <ᴴ-dec computes.

\begin{code}

-- To simplify the examples, we turn <ᴴ-dec into a boolean-valued function.

open import Agda.Builtin.Bool

⊎2Bool : {A : Type ℓ} {B : Type ℓ'} → A ⊎ B → Bool
⊎2Bool (inj₁ _) = true
⊎2Bool (inj₂ _) = false

lt : HITOrd → HITOrd → Bool
lt a b = ⊎2Bool (<ᴴ-dec a b)

Ex[<ᴴ-decComp] :
   lt 𝟎 𝟎 ≡ false
 × lt H.ω ((H.𝟏 ⊕ H.𝟏) ⊗ H.ω) ≡ true
 × lt H.ω^⟨ H.ω ⟩ H.ω^⟨ H.𝟏 +ᴴ H.ω ⟩ ≡ false
 × lt H.ω^⟨ H.ω ⟩ H.ω^⟨ H.𝟏 ⊕ H.ω ⟩ ≡ true
Ex[<ᴴ-decComp] = refl , refl , refl , refl

\end{code}

§5.2  Transfinite induction

■ Principle of transfinite induction

\begin{code}

TI : (A : Type ℓ) → (A → A → Type ℓ') →
     ∀ ℓ'' → Type (ℓ ⊔ ℓ' ⊔ lsuc ℓ'')
TI A _<_ ℓ'' = (P : A → Type ℓ'')
             → (∀ x → (∀ y → y < x → P y) → P x)
             → ∀ x → P x

\end{code}

■ Accessibility

\begin{code}

module Acc (A : Type ℓ) (_<_ : A → A → Type ℓ') where

 data isAccessible (x : A) : Type (ℓ ⊔ ℓ') where
  next : (∀ y → y < x → isAccessible y) → isAccessible x

 accInd : (P : A → Type ℓ'')
        → (∀ x → (∀ y → y < x → P y) → P x)
        → ∀ x → isAccessible x → P x
 accInd P step x (next δ) =
   step x (λ y r → accInd P step y (δ y r))

\end{code}

■ All elements of MutualOrd are accessible.

\begin{code}

open Acc MutualOrd _<_

𝟎Acc : isAccessible 𝟎
𝟎Acc = next (λ x x<𝟎 → ⊥-elim (≮𝟎 x<𝟎))

-- fstAcc and sndAcc are proved simultaneously.

fstAcc : ∀ {a a'} → isAccessible a' → a ≡ a'
  → ∀ {b x} → isAccessible b → x < a' → (r : x ≥ fst b)
  → isAccessible (ω^ x + b [ r ])
sndAcc : ∀ {a a'} → isAccessible a' → a ≡ a'
  → ∀ {c y} → isAccessible c → y < c → (r : a ≥ fst y)
  → isAccessible (ω^ a + y [ r ])

fstAcc {a} {a'} (next ξ) a=a' {b} {x} acᵇ x<a r = next goal
  where
   goal : ∀ z → z < ω^ x + b [ r ] → isAccessible z
   goal 𝟎 <₁ = 𝟎Acc
   goal (ω^ c + d [ s ]) (<₂ c<y) = fstAcc (ξ x x<a) refl (goal d (<-trans (rest< c d s) (<₂ c<y))) c<y s
   goal (ω^ c + d [ s ]) (<₃ c=y d<b) = sndAcc (ξ x x<a) c=y acᵇ d<b s

sndAcc {a} {a'} acᵃ a=a' {c} {y} (next ξᶜ) y<c r = next goal
  where
   goal : ∀ z → z < ω^ a + y [ r ] → isAccessible z
   goal 𝟎 <₁ = 𝟎Acc
   goal (ω^ b + d [ t ]) (<₂ b<a) = fstAcc acᵃ a=a' (goal d (<-trans (rest< b d t) (<₂ b<a))) (subst (b <_) a=a' b<a) t
   goal (ω^ b + d [ t ]) (<₃ b=a d<y) = sndAcc acᵃ (b=a ∙ a=a') (ξᶜ y y<c) d<y t

ω+Acc : (a b : MutualOrd) (r : a ≥ fst b)
      → isAccessible a → isAccessible b → isAccessible (ω^ a + b [ r ])
ω+Acc a b r acᵃ acᵇ = next goal
 where
  goal : ∀ z → z < ω^ a + b [ r ] → isAccessible z
  goal 𝟎 <₁ = 𝟎Acc
  goal (ω^ c + d [ s ]) (<₂ c<a) = fstAcc acᵃ refl (goal d (<-trans (rest< c d s) (<₂ c<a))) c<a s
  goal (ω^ c + d [ s ]) (<₃ c=a d<b) = sndAcc acᵃ c=a acᵇ d<b s

WF : (x : MutualOrd) → isAccessible x
WF 𝟎 = 𝟎Acc
WF (ω^ a + b [ r ]) = ω+Acc a b r (WF a) (WF b)

\end{code}

■ Transfinite induction for MutualOrd

\begin{code}

MTI : TI MutualOrd _<_ ℓ
MTI P step x = accInd P step x (WF x)

\end{code}

■ Transfinite induction for HITOrd

\begin{code}

HTI : TI HITOrd _<ᴴ_ ℓ
HTI = transport (λ i → TI (M≡H i) (<Path i) _) MTI

\end{code}

§5.3  All strictly descending sequences are finite

■ Definitions

\begin{code}

pseudo-descending : (ℕ → MutualOrd) → Type₀
pseudo-descending f =
  ∀ i → f i > f (suc i) ⊎ (f i ≡ 𝟎 × f (suc i) ≡ 𝟎)

strictly-descending : (ℕ → MutualOrd) → Set
strictly-descending f = ∀ i → f i > f (suc i)

eventually-zero : (ℕ → MutualOrd) → Type₀
eventually-zero f = Σ \(n : ℕ) → ∀ i → i ≥ᴺ n → f i ≡ 𝟎

\end{code}

■ Some facts of pseudo-descendingness and eventual zeroness

\begin{code}

zeroPoint : ∀ {f} → pseudo-descending f
  → ∀ {i} → f i ≡ 𝟎 → ∀ j → j ≥ᴺ i → f j ≡ 𝟎
zeroPoint df f0=0   0      z≤n                   = f0=0
zeroPoint df f0=0  (suc j) z≤n with df 0
zeroPoint df f0=0  (suc j) z≤n | inj₁ f1<f0      = ⊥-elim (≮𝟎 (<-≡ f1<f0 f0=0))
zeroPoint df f0=0  (suc j) z≤n | inj₂ (_ , f1=0) = zeroPoint (df ∘ suc) f1=0  j z≤n
zeroPoint df fsi=0 (suc j) (s≤s i≤j)             = zeroPoint (df ∘ suc) fsi=0 j i≤j

nonzeroPoint : ∀ {f} → pseudo-descending f
  → ∀ {i} → f i > 𝟎 → f i > f (suc i)
nonzeroPoint df fi>0 with df _
nonzeroPoint df fi>0 | inj₁ fi+1<fi    = fi+1<fi
nonzeroPoint df fi>0 | inj₂ (fi=0 , _) = ⊥-elim (≮𝟎 (<-≡ fi>0 fi=0))

eventually-zero-cons :
  ∀ f → eventually-zero (f ∘ suc) → eventually-zero f
eventually-zero-cons f (n , p) = suc n , p'
 where
  p' : (i : ℕ) → i ≥ᴺ suc n → f i ≡ 𝟎
  p' (suc i) (s≤s r) = p i r

\end{code}

■ All pseudo-descending sequences are eventually zero.

\begin{code}

PD2EZ : ∀ f → pseudo-descending f → eventually-zero f
PD2EZ f df = MTI P step (f 0) f df refl
 where
  P : MutualOrd → Type₀
  P a = ∀ f → pseudo-descending f → f 0 ≡ a → eventually-zero f
  step : ∀ x → (∀ y → y < x → P y) → P x
  step x h f df f0=x with ≥𝟎 {f 0}
  step x h f df f0=x | inj₁ f0>0 = goal
   where
    f1<x : f 1 < x
    f1<x = subst (f 1 <_) f0=x (nonzeroPoint df f0>0)
    ezfs : eventually-zero (f ∘ suc)
    ezfs = h (f 1) f1<x (f ∘ suc) (df ∘ suc) refl
    goal : eventually-zero f
    goal = eventually-zero-cons f ezfs
  step x h f df f0=x | inj₂ f0=0 = goal
   where
    fi=0 : ∀ i → f i ≡ 𝟎
    fi=0 i = zeroPoint df f0=0 i z≤n
    goal : eventually-zero f
    goal = 0 , λ i _ → fi=0 i

\end{code}

■ There is no strictly descending sequence.

\begin{code}

NSDS : ∀ f → strictly-descending f → ⊥
NSDS f sd = <-irreflexive fn+1=fn fn+1<fn
 where
  ez : eventually-zero f
  ez = PD2EZ f (inj₁ ∘ sd)
  n : ℕ
  n = pr₁ ez
  prf : ∀ i → i ≥ᴺ n → f i ≡ 𝟎
  prf = pr₂ ez
  fn+1=fn : f (suc n) ≡ f n
  fn+1=fn = prf (suc n) n≤1+n ∙ (prf n ≤ᴺ-refl) ⁻¹
  fn+1<fn : f (suc n) < f n
  fn+1<fn = sd n

\end{code}
