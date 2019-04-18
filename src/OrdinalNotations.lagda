
        --------------------------------------------------
          An inductive-inductive-recursive definition of
                       ordinal notations
        --------------------------------------------------

                          Chuangjie Xu
               August 2018, updated in April 2019


Each ordinal α can be uniquely written as the sum ωᵃ⁰ + ... + ωᵃⁱ⁻¹
where a₀ ≥ ... ≥ aᵢ₋₁ are also ordinals. Hence α can equivalently be
represented by the weakly decreasing list a₀, ... , aᵢ₋₁; in
particular 0 is represented by the empty list.  Because the elements
of such a decreasing list are also decreasing lists, an ordering on
them has to be defined simultaneously with the definition of the list.
Moreover, when inserting a new element x in front of an already
constructed list xs, we need to ensure that x is greater than or equal
to the head of xs in order to not violate the order invariant, which
requires us to also simultaneously define a head function for such
lists.  Therefore, we end up with an inductive-inductive-recursive
definition of ordinal notations.

\begin{code}

module OrdinalNotations where

open import Agda.Builtin.Equality
open import Data.Empty hiding (⊥-elim)
open import Data.Empty.Irrelevant
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; cong)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _∨_)
open import Data.String.Base as String using (String; primStringAppend)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show renaming (show to showℕ)

\end{code}

■ Ordinal terms

We simultaneously define:
(1) an inductive type 𝒪 of ordinal terms,
(2) an inductive family of types a < b indexed by a,b : 𝒪, and
(3) a head function fst : 𝒪 → 𝒪.

\begin{code}

infix 30 _<_
infix 30 _≤_
infix 30 _>_
infix 30 _≥_

mutual 

 data 𝒪 : Set where
  𝟎 : 𝒪
  ω^_+_[_] : (a b : 𝒪) → .(a ≥ fst b) → 𝒪

 data _<_ : 𝒪 → 𝒪 → Set where
  <₁ : {a : 𝒪}
     → a ≢ 𝟎 → 𝟎 < a
  <₂ : {a b c d : 𝒪} .{r : a ≥ fst c} .{s : b ≥ fst d}
     → a < b → ω^ a + c [ r ] < ω^ b + d [ s ]
  <₃ : {a b c : 𝒪} .{r : a ≥ fst b} .{s : a ≥ fst c}
     → b < c → ω^ a + b [ r ] < ω^ a + c [ s ]

 fst : 𝒪 → 𝒪
 fst  𝟎               = 𝟎
 fst (ω^ a + _ [ _ ]) = a

 _>_ _≥_ _≤_ : 𝒪 → 𝒪 → Set
 a > b =  b < a
 a ≥ b = (a > b) ∨ (a ≡ b)
 a ≤ b =  b ≥ a

\end{code}

■ Finite, successor and limit ordinal terms

Because each ordinal term is a list, we can compute its length and
access its last element if it's not zero.  These operations allow us
to characterize ordinal terms.

\begin{code}

∣_∣ : 𝒪 → ℕ
∣ 𝟎 ∣ = 0
∣ ω^ a + b [ _ ] ∣ = suc ∣ b ∣

lst : 𝒪 → 𝒪
lst  𝟎               = 𝟎
lst (ω^ a + 𝟎 [ _ ]) = a
lst (ω^ a + b [ _ ]) = lst b

isFin : 𝒪 → Set
isFin a = fst a ≡ 𝟎

isSuc : 𝒪 → Set
isSuc 𝟎 = ⊥
isSuc a = lst a ≡ 𝟎

isLim : 𝒪 → Set
isLim 𝟎 = ⊥
isLim a = lst a ≢ 𝟎

toℕ : (a : 𝒪) → isFin a → ℕ
toℕ a _ = ∣ a ∣

\end{code}

■ Showing ordinals

\begin{code}

infixl 10 _++_

_++_ : String → String → String
_++_ = primStringAppend

mutual
 show : 𝒪 → String
 show 𝟎 = "0"
 show a @ (ω^ 𝟎 + _ [ _ ]) = showℕ (toℕ a refl)
 show ω^ (ω^ 𝟎 + 𝟎 [ _ ]) + b [ _ ] = "ω" ++ end b
 show ω^ (ω^ a + c [ r ]) + b [ _ ] = "ω^" ++ bracket (ω^ a + c [ r ]) ++ end b

 end : 𝒪 → String
 end 𝟎 = ""
 end a = " + " ++ show a

 bracket : 𝒪 → String
 bracket 𝟎 = "0"
 bracket a @ (ω^ 𝟎 + _ [ _ ]) = show a
 bracket a @ (ω^ _ + 𝟎 [ _ ]) = show a
 bracket a @ (ω^ _ + ω^ _ + _ [ _ ] [ _ ]) = "(" ++ show a ++ ")"

\end{code}

■ _<_ is a strict total order on 𝒪.

\begin{code}

<₃' : {a b c d : 𝒪} .{r : a ≥ fst c} .{s : b ≥ fst d}
    → a ≡ b → c < d → ω^ a + c [ r ] < ω^ b + d [ s ]
<₃' refl = <₃

𝒪⁼ : {a b c d : 𝒪} .{r : a ≥ fst c} .{s : b ≥ fst d}
   → a ≡ b → c ≡ d → ω^ a + c [ r ] ≡ ω^ b + d [ s ]
𝒪⁼ refl refl = refl

Lm[≮0] : {a : 𝒪} → ¬ (a < 𝟎)
Lm[≮0] (<₁ x) = x refl

--
-- _<_ is irreflexive
--
<-irrefl : {a : 𝒪} → ¬ (a < a)
<-irrefl (<₁ f) = f refl
<-irrefl (<₂ r) = <-irrefl r
<-irrefl (<₃ r) = <-irrefl r

--
-- _<_ is transitive
--
<-trans : {a b c : 𝒪} → a < b → b < c → a < c
<-trans (<₁ f) (<₁ g) = <₁ g
<-trans (<₁ f) (<₂ s) = <₁ (λ ())
<-trans (<₁ f) (<₃ s) = <₁ (λ ())
<-trans (<₂ r) (<₂ s) = <₂ (<-trans r s)
<-trans (<₂ r) (<₃ s) = <₂ r
<-trans (<₃ r) (<₂ s) = <₂ s
<-trans (<₃ r) (<₃ s) = <₃ (<-trans r s)

--
-- _<_ is trichotomous
--
<-tri : {a b : 𝒪} → (a < b) ∨ (a > b) ∨ (a ≡ b)
<-tri {𝟎}              {𝟎}              = inj₂ (inj₂ refl)
<-tri {𝟎}              {ω^ b + d [ _ ]} = inj₁ (<₁ (λ ()))
<-tri {ω^ a + c [ _ ]} {𝟎}              = inj₂ (inj₁ (<₁ (λ ())))
<-tri {ω^ a + c [ _ ]} {ω^ b + d [ _ ]} with <-tri
...                                     | inj₁       a<b                    = inj₁ (<₂ a<b)
...                                     | inj₂ (inj₁ a>b)                   = inj₂ (inj₁ (<₂ a>b))
...                                     | inj₂ (inj₂ a=b) with <-tri
...                                                       | inj₁       c<d  = inj₁ (<₃' a=b c<d)
...                                                       | inj₂ (inj₁ c>d) = inj₂ (inj₁ (<₃' (sym a=b) c>d))
...                                                       | inj₂ (inj₂ c=d) = inj₂ (inj₂ (𝒪⁼ a=b c=d))

Lm[<→¬≥] : {a b : 𝒪} → a < b → ¬ (a ≥ b)
Lm[<→¬≥] a<b (inj₁ a>b)  = <-irrefl (<-trans a<b a>b)
Lm[<→¬≥] a<b (inj₂ refl) = <-irrefl a<b

Lm[≥→¬<] : {a b : 𝒪} → a ≥ b → ¬ (a < b)
Lm[≥→¬<] (inj₁ b<a) a<b = <-irrefl (<-trans a<b b<a)
Lm[≥→¬<] (inj₂ refl) = <-irrefl

Lm[¬<→≥] : {a b : 𝒪} → ¬ (a < b) → a ≥ b
Lm[¬<→≥] {a} {b} f with <-tri
...                | inj₁       a<b  = ⊥-elim (f a<b)
...                | inj₂ (inj₁ a>b) = inj₁ a>b
...                | inj₂ (inj₂ a=b) = inj₂ a=b

--
-- _<_ is decidable
--
<-dec : (a b : 𝒪) → (a < b) ∨ ¬ (a < b)
<-dec a b with <-tri
...       | inj₁ a<b = inj₁ a<b
...       | inj₂ a≥b = inj₂ (Lm[≥→¬<] a≥b)

\end{code}

■ Examples of ordinals

\begin{code}

Lm[≥𝟎] : {a : 𝒪} → a ≥ 𝟎
Lm[≥𝟎] {𝟎}              = inj₂ refl
Lm[≥𝟎] {ω^ a + b [ _ ]} = inj₁ (<₁ (λ ()))

ω^⟨_⟩ : 𝒪 → 𝒪
ω^⟨ a ⟩ = ω^ a + 𝟎 [ Lm[≥𝟎] ]

𝟏 : 𝒪
𝟏 = ω^⟨ 𝟎 ⟩

ω : 𝒪
ω = ω^⟨ 𝟏 ⟩

\end{code}
