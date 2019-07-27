
               -----------------------------
                   Transfinite induction 
               -----------------------------

                  Chuangjie Xu, June 2019


We tried to adapt Grimm's (Coq) proof to show the well-foundedness of
our ordinal notations.  The following two statements

 - if a and b are accessible and x < a, then ω^x+b is accessible

 - if a and b are accessible and y < b, then ω^a+y is accessible

are used as assumptions in Grimm's proof. But we cannot see why such
assumptions are allowed.  We instead consider them as lemmas and prove
them simultaneously.

From the well-foundedness, we derive the transfinite induction
principle for 𝒪.  Then we use it to prove a stronger and computational
version of the well-known statement

  there is no infinite descending sequence of ordinals below ε₀.


References.

□ José Grimm. Implementation of three types of ordinals in Coq.
  Technical Report RR-8407, INRIA, 2013. Available at
  https://hal.inria.fr/hal-00911710.

\begin{code}

{-# OPTIONS --safe #-}

module TransfiniteInduction where

open import Agda.Builtin.Equality
open import Data.Empty.Irrelevant
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _∨_)

open import OrdinalNotations

\end{code}

■ Some lemmas

We can make irrelevant a ≥ b relevant because of the trichotomy.

\begin{code}

relevant : {a b : 𝒪} → .(a ≥ b) → a ≥ b
relevant {a} {b} r with <-tri {a} {b}
...                | inj₁ a<b = ⊥-elim (Lm[<→¬≥] a<b r)
...                | inj₂ a≥b = a≥b

fst< : ∀ a b → .(r : a ≥ fst b) → a < ω^ a + b [ r ]
fst< 𝟎 b r = <₁ (λ ())
fst< (ω^ a + c [ s ]) b r = <₂ (fst< a c s)

snd< : ∀ a b → .(r : a ≥ fst b) → b < ω^ a + b [ r ]
snd< a 𝟎 r = <₁ (λ ())
snd< a ω^ b + d [ s ] r with relevant r
snd< a ω^ b + d [ s ] r | inj₁ a>b  = <₂ a>b
snd< a ω^ a + d [ s ] r | inj₂ refl = <₃ (snd< a d (relevant s))

\end{code}

■ Well-foundedness of 𝒪

\begin{code}

data is-accessible (x : 𝒪) : Set where
 next : (∀ y → y < x → is-accessible y) → is-accessible x

0-is-accessible : is-accessible 𝟎
0-is-accessible = next (λ _ r → ⊥-elim (Lm[≮0] r))

mutual

 --
 -- Grimm's assumption Hb
 --
 Lm[fst-acc] : ∀ a → is-accessible a
             → ∀ y b → y < a → .(r : y ≥ fst b) → is-accessible b
             → is-accessible (ω^ y + b [ r ])
 Lm[fst-acc] a (next ξ) y b y<a r acᵇ = next goal
  where
   goal : ∀ x → x < ω^ y + b [ r ] → is-accessible x
   goal 𝟎 (<₁ _) = 0-is-accessible
   goal (ω^ c + d [ s ]) (<₂ c<y) = Lm[fst-acc] y (ξ y y<a) c d c<y s IH
    where
     IH : is-accessible d
     IH = goal d (<-trans (snd< c d s) (<₂ c<y))
   goal (ω^ a + d [ s ]) (<₃ d<b) = Lm[snd-acc] y (ξ y y<a) b acᵇ d d<b s

 --
 -- Grimm's assumption qb
 --
 Lm[snd-acc] : ∀ a → is-accessible a
             → ∀ c → is-accessible c
             → ∀ y → y < c → .(r : a ≥ fst y) → is-accessible (ω^ a + y [ r ])
 Lm[snd-acc] a acᵃ c (next ξᶜ) y y<c r = next goal
  where
   goal : ∀ x → x < ω^ a + y [ r ] → is-accessible x
   goal 𝟎 (<₁ x) = 0-is-accessible
   goal (ω^ b + d [ t ]) (<₂ b<a) = Lm[fst-acc] a acᵃ b d b<a t IH
    where
     IH : is-accessible d
     IH = goal d (<-trans (snd< b d t) (<₂ b<a))
   goal (ω^ a + d [ t ]) (<₃ d<y) = Lm[snd-acc] a acᵃ y (ξᶜ y y<c) d d<y t

--
-- 𝒪 is well-founded
--
WF : ∀ x → is-accessible x
WF  𝟎               = 0-is-accessible
WF (ω^ a + b [ r ]) = next goal
 where
  goal : ∀ y → y < ω^ a + b [ r ] → is-accessible y
  goal  𝟎               (<₁ _)   = 0-is-accessible
  goal (ω^ c + d [ s ]) (<₂ c<a) = Lm[fst-acc] a (WF a) c d c<a s IH
   where
    IH : is-accessible d
    IH = goal d (<-trans (snd< c d s) (<₂ c<a))
  goal (ω^ a + d [ s ]) (<₃ d<b) = Lm[snd-acc] a (WF a) b (WF b) d d<b s

\end{code}

■ Transfinite induction for 𝒪

\begin{code}

TIᵃ : (P : 𝒪 → Set)
    → (∀ x → (∀ y → y < x → P y) → P x)
    → ∀ x → is-accessible x → P x
TIᵃ P step x (next δ) = step x (λ y r → TIᵃ P step y (δ y r))

TI : (P : 𝒪 → Set)
   → (∀ x → (∀ y → y < x → P y) → P x)
   → ∀ x → P x
TI P step x = TIᵃ P step x (WF x)

\end{code}

■ No infinite descending sequence of ordinals below ε₀

We prove a computational version using transfinite induction.

\begin{code}

open import Data.Nat using (ℕ ; suc ; z≤n ; s≤s)
                     renaming (_≥_ to _≥ᴺ_ ; _>_ to _>ᴺ_ ; _<_ to _<ᴺ_ ; _≤_ to _≤ᴺ_)
open import Data.Nat.Properties using (≤-refl ; n≤1+n)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂) renaming (_×_ to _∧_)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (sym ; trans)

<-≡ : {a b c : 𝒪} → a < b → b ≡ c → a < c
<-≡ r refl = r

descending : (ℕ → 𝒪) → Set
descending f = ∀ i → f i > f (suc i) ∨ (f i ≡ 𝟎 ∧ f (suc i) ≡ 𝟎)

descending-fact₀ : ∀{f} → descending f
                 → ∀{i} → f i ≡ 𝟎 → ∀ j → j ≥ᴺ i → f j ≡ 𝟎
descending-fact₀ df f0=0   0      z≤n                   = f0=0
descending-fact₀ df f0=0  (suc j) z≤n with df 0
descending-fact₀ df f0=0  (suc j) z≤n | inj₁ f1<f0      = ⊥-elim (Lm[≮0] (<-≡ f1<f0 f0=0))
descending-fact₀ df f0=0  (suc j) z≤n | inj₂ (_ , f1=0) = descending-fact₀ (df ∘ suc) f1=0  j z≤n
descending-fact₀ df fsi=0 (suc j) (s≤s i≤j)             = descending-fact₀ (df ∘ suc) fsi=0 j i≤j

descending-fact₁ : ∀{f} → descending f
                 → ∀{i} → f i > 𝟎 → f i > f (suc i)
descending-fact₁ df fi>0 with df _
descending-fact₁ df fi>0 | inj₁ fi+1<fi    = fi+1<fi
descending-fact₁ df fi>0 | inj₂ (fi=0 , _) = ⊥-elim (Lm[≮0] (<-≡ fi>0 fi=0))

eventually-zero : (ℕ → 𝒪) → Set
eventually-zero f = ∃ \n → ∀ i → i ≥ᴺ n → f i ≡ 𝟎

P : 𝒪 → Set
P a = (f : ℕ → 𝒪) → descending f → f 0 ≡ a → eventually-zero f

step : ∀ x → (∀ y → y < x → P y) → P x
step .(f 0) h f df refl with Lm[≥𝟎] {f 0}
step .(f 0) h f df refl | inj₁ f0>0 = suc n , goal
 where
  claim : eventually-zero (f ∘ suc)
  claim = h (f 1) (descending-fact₁ df f0>0) (f ∘ suc) (df ∘ suc) refl
  n : ℕ
  n = proj₁ claim
  goal : ∀ i → i ≥ᴺ suc n → f i ≡ 𝟎
  goal 0 ()
  goal (suc i) (s≤s r) = proj₂ claim i r
step .(f 0) h f df refl | inj₂ f0=0 = 0 , λ i _ → descending-fact₀ df f0=0 i z≤n

Theorem : (f : ℕ → 𝒪) → descending f → eventually-zero f
Theorem f df = TI P step (f 0) f df refl

strictly-descending : (ℕ → 𝒪) → Set
strictly-descending f = ∀ i → f i > f (suc i)

Corollary : ¬ (∃ \(f : ℕ → 𝒪) → strictly-descending f)
Corollary (f , sd) = <-irrefl' fn+1=fn fn+1<fn
 where
  ez : eventually-zero f
  ez = Theorem f (inj₁ ∘ sd)
  n : ℕ
  n = proj₁ ez
  pr : ∀ i → i ≥ᴺ n → f i ≡ 𝟎
  pr = proj₂ ez
  fn+1=fn : f (suc n) ≡ f n
  fn+1=fn = trans (pr (suc n) (n≤1+n n)) (sym (pr n ≤-refl))
  fn+1<fn : f (suc n) < f n
  fn+1<fn = sd n
  <-irrefl' : {a b : 𝒪} → a ≡ b → ¬ (a < b)
  <-irrefl' refl = <-irrefl

\end{code}
