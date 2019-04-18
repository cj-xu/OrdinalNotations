
                   --------------------------
                       Ordinal arithmetic 
                   --------------------------

                          Chuangjie Xu
               August 2018, updated in April 2019


We define ordinal arithmetic operations for our ordinal notations
including addition, subtraction, multiplication and exponentiation.

\begin{code}

module OrdinalArithmetic where

open import Agda.Builtin.Equality
open import Data.Empty.Irrelevant
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _∨_; [_,_]′ to case)
open import Data.Nat using (ℕ; suc)

open import OrdinalNotations

\end{code}

■ Preliminaries

\begin{code}

case-spec₀ : {A B C : Set} {f : .A → C} {g : .B → C}
           → .(A → ¬ B) → (w : A ∨ B) .(a : A) → case f g w ≡ f a
case-spec₀ h (inj₁ _) _ = refl
case-spec₀ h (inj₂ b) a = ⊥-elim (h a b)

case-spec₁ : {A B C : Set} {f : .A → C} {g : .B → C}
           → .(A → ¬ B) → (w : A ∨ B) .(b : B) → case f g w ≡ g b
case-spec₁ h (inj₁ a) b = ⊥-elim (h a b)
case-spec₁ h (inj₂ _) _ = refl

\end{code}

■ Addition

Because of the mutual definition, we have to simultaneously define
addition of ordinals and prove a lemma of a property of addition.

\begin{code}

infixl 35 _+_

mutual

 _+_ : 𝒪 → 𝒪 → 𝒪
 𝟎                + b                = b
 a                + 𝟎                = a
 (ω^ a + c [ r ]) + (ω^ b + d [ s ]) = case u₀ u₁ <-tri
  where
   u₀ : .(a < b) → 𝒪
   u₀ _ = ω^ b + d [ s ]
   u₁ : .(a ≥ b) → 𝒪
   u₁ h = ω^ a + (c + ω^ b + d [ s ]) [ Lm[≥+] a c _ r h ]

 {-# TERMINATING #-}
 Lm[≥+] : (a b c : 𝒪) → a ≥ fst b → a ≥ fst c → a ≥ fst (b + c)
 Lm[≥+] a  𝟎                c               r s = s
 Lm[≥+] a (ω^ b + d [ u ])  𝟎               r s = r
 Lm[≥+] a (ω^ b + d [ u ]) (ω^ c + e [ v ]) r s = case w₀ w₁ <-tri
  where
   lemma : {x y z : 𝒪} → x ≥ y → z ≡ y → x ≥ z
   lemma r refl = r 
   w₀ : b < c → a ≥ fst (ω^ b + d [ u ] + ω^ c + e [ v ])
   w₀ w = lemma s (cong fst p)
    where
     p : ω^ b + d [ u ] + ω^ c + e [ v ] ≡ ω^ c + e [ v ]
     p = case-spec₀ Lm[<→¬≥] <-tri w
   w₁ : b ≥ c → a ≥ fst (ω^ b + d [ u ] + ω^ c + e [ v ])
   w₁ w = lemma r (cong fst p)
    where
     p : ω^ b + d [ u ] + ω^ c + e [ v ] ≡ ω^ b + _ [ _ ]
     p = case-spec₁ Lm[<→¬≥] <-tri w

--
-- Embedding of ℕ into 𝒪
--
to𝒪 : ℕ → 𝒪
to𝒪  0      = 𝟎
to𝒪 (suc n) = to𝒪 n + 𝟏

\end{code}

■ Subtraction

\begin{code}

infixl 35 _-_

_-_ : 𝒪 → 𝒪 → 𝒪
𝟎 - b = 𝟎
a - 𝟎 = a
(ω^ a + c [ r ]) - (ω^ b + d [ s ]) with <-tri {a} {b}
...                                 | inj₁       a<b  = 𝟎
...                                 | inj₂ (inj₁ a>b) = ω^ a + c [ r ]
...                                 | inj₂ (inj₂ a=b) = c - d

\end{code}

■ Multiplication

\begin{code}

infixl 40 _·_

_·_ : 𝒪 → 𝒪 → 𝒪
𝟎              · b              = 𝟎
a              · 𝟎              = 𝟎
a              · ω^ 𝟎 + d [ _ ] = a + a · d
ω^ a + c [ r ] · ω^ b + d [ _ ] = ω^⟨ a + b ⟩ + (ω^ a + c [ r ]) · d

\end{code}

■ Exponentiation

We adapt Castéran’s definition of exponentiation in his development of
ordinal notations in Coq which is available at

    http://coq.inria.fr/V8.2pl1/contribs/Cantor.html

\begin{code}

_^_ : 𝒪 → 𝒪 → 𝒪
x                    ^ 𝟎                               = 𝟏
𝟎                    ^ y                               = 𝟎
(ω^ 𝟎 + 𝟎 [ _ ])     ^ y                               = 𝟏
x                    ^ (ω^ 𝟎 + z [ _ ])                = x · (x ^ z)
x @ (ω^ 𝟎 + c [ _ ]) ^ (ω^ (ω^ 𝟎 + 𝟎 [ _ ]) + z [ _ ]) = ω · (x ^ z)
x @ (ω^ 𝟎 + c [ _ ]) ^ (ω^ b + z [ _ ])                = ω^⟨ b - 𝟏 ⟩ · (x ^ z)
x @ (ω^ a + c [ _ ]) ^ (ω^ b + z [ _ ])                = ω^⟨ a · ω^⟨ b ⟩ ⟩ · (x ^ z)

\end{code}
